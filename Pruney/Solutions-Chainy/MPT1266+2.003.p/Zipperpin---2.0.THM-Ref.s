%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qf3CpuWmQI

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:04:12 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  204 (2821 expanded)
%              Number of leaves         :   33 ( 890 expanded)
%              Depth                    :   25
%              Number of atoms          : 1760 (26270 expanded)
%              Number of equality atoms :  108 (1396 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v2_tops_1_type,type,(
    v2_tops_1: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v1_tops_1_type,type,(
    v1_tops_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X19: $i,X21: $i] :
      ( ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d3_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_tops_1 @ B @ A )
          <=> ( ( k2_pre_topc @ A @ B )
              = ( k2_struct_0 @ A ) ) ) ) ) )).

thf('4',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( v1_tops_1 @ X35 @ X36 )
      | ( ( k2_pre_topc @ X36 @ X35 )
        = ( k2_struct_0 @ X36 ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('6',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d4_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v2_tops_1 @ B @ A )
          <=> ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) )).

thf('7',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( v2_tops_1 @ X37 @ X38 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X38 ) @ X37 ) @ X38 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) @ X0 )
      | ~ ( v2_tops_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X6 @ X7 )
        = ( k4_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('13',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('16',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('22',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('23',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X11 @ ( k3_subset_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t31_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ C )
          <=> ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('27',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X13 @ X12 ) @ ( k3_subset_1 @ X13 @ X14 ) )
      | ( r1_tarski @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t31_subset_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X0 @ ( k4_xboole_0 @ X1 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ ( k4_xboole_0 @ X1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('30',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( r1_tarski @ X0 @ ( k4_xboole_0 @ X1 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['28','31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['11','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( v2_tops_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['8','36'])).

thf('38',plain,(
    ! [X18: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v2_tops_1 @ B @ A ) ) ) ) )).

thf('39',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( v2_tops_1 @ X31 @ X32 )
      | ~ ( v1_xboole_0 @ X31 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[cc2_tops_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v2_tops_1 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('41',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( v2_tops_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( v1_tops_1 @ ( u1_struct_0 @ X0 ) @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['37','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['5','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('46',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X25 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['5','43'])).

thf('53',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('54',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( r1_tarski @ X29 @ ( k2_pre_topc @ X30 @ X29 ) )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

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

thf('62',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('63',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( l1_pre_topc @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X39 @ X40 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('64',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X11 @ ( k3_subset_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('68',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('70',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X6 @ X7 )
        = ( k4_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('71',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) )
    = ( k1_tops_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['68','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X8 @ X9 ) @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('75',plain,(
    m1_subset_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X6 @ X7 )
        = ( k4_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('78',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ~ ( v1_tops_1 @ X35 @ X36 )
      | ( ( k2_pre_topc @ X36 @ X35 )
        = ( k2_struct_0 @ X36 ) )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('81',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','78'])).

thf('85',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X25 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('86',plain,
    ( ( m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    m1_subset_1 @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_subset_1 @ X11 @ ( k3_subset_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('90',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('92',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( ( k1_tops_1 @ X34 @ X33 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X34 ) @ ( k2_pre_topc @ X34 @ ( k3_subset_1 @ ( u1_struct_0 @ X34 ) @ X33 ) ) ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('93',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('96',plain,
    ( ( k1_tops_1 @ sk_A @ sk_B_1 )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['90','96'])).

thf('98',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('99',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['83','99'])).

thf('101',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
    | ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['101'])).

thf('103',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( v2_tops_1 @ X37 @ X38 )
      | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X38 ) @ X37 ) @ X38 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('105',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('108',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['105','106','107'])).

thf('109',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
   <= ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['102','108'])).

thf('110',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
    | ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['110'])).

thf('112',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['101'])).

thf('113',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','78'])).

thf(projectivity_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) )
        = ( k2_pre_topc @ A @ B ) ) ) )).

thf('114',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( l1_pre_topc @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( k2_pre_topc @ X27 @ ( k2_pre_topc @ X27 @ X28 ) )
        = ( k2_pre_topc @ X27 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k2_pre_topc])).

thf('115',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
      = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ( k2_pre_topc @ sk_A @ ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) )
    = ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['115','116'])).

thf('118',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('119',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('120',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['117','118','119'])).

thf('121',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) )
      = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['112','120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','34'])).

thf('123',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['101'])).

thf('124',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','34'])).

thf('125',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['121','122','123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['5','43'])).

thf('127',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
        = ( k2_struct_0 @ sk_A ) )
      | ~ ( l1_pre_topc @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['125','126'])).

thf('128',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X38 ) ) )
      | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ X38 ) @ X37 ) @ X38 )
      | ( v2_tops_1 @ X37 @ X38 )
      | ~ ( l1_pre_topc @ X38 ) ) ),
    inference(cnf,[status(esa)],[d4_tops_1])).

thf('132',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['130','131'])).

thf('133',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('135',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['132','133','134'])).

thf('136',plain,
    ( ( ~ ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
      | ( v2_tops_1 @ sk_B_1 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['129','135'])).

thf('137',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['101'])).

thf('138',plain,(
    m1_subset_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','78'])).

thf('139',plain,(
    ! [X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X36 ) ) )
      | ( ( k2_pre_topc @ X36 @ X35 )
       != ( k2_struct_0 @ X36 ) )
      | ( v1_tops_1 @ X35 @ X36 )
      | ~ ( l1_pre_topc @ X36 ) ) ),
    inference(cnf,[status(esa)],[d3_tops_1])).

thf('140',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['140','141'])).

thf('143',plain,
    ( ( k2_pre_topc @ sk_A @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) )
    = ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('144',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
    | ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
     != ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['142','143'])).

thf('145',plain,
    ( ( ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['137','144'])).

thf('146',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','34'])).

thf('147',plain,
    ( ( ( ( u1_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('149',plain,
    ( ( ( u1_struct_0 @ sk_A )
      = ( k2_struct_0 @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('150',plain,
    ( ( ( ( k2_struct_0 @ sk_A )
       != ( k2_struct_0 @ sk_A ) )
      | ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ) )
   <= ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['147','148','149'])).

thf('151',plain,
    ( ( v1_tops_1 @ ( k4_xboole_0 @ ( k2_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['136','151'])).

thf('153',plain,
    ( ~ ( v2_tops_1 @ sk_B_1 @ sk_A )
   <= ~ ( v2_tops_1 @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['110'])).

thf('154',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,
    ( ( v2_tops_1 @ sk_B_1 @ sk_A )
    | ( ( k1_tops_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['101'])).

thf('156',plain,(
    v2_tops_1 @ sk_B_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['111','154','155'])).

thf('157',plain,(
    v1_tops_1 @ ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ sk_B_1 ) @ sk_A ),
    inference(simpl_trail,[status(thm)],['109','156'])).

thf('158',plain,
    ( ( k4_xboole_0 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['100','157'])).

thf('159',plain,
    ( ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
    = ( k1_tops_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['72','158'])).

thf('160',plain,
    ( ( ( k3_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) )
      = ( k1_tops_1 @ sk_A @ sk_B_1 ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['61','159'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k4_xboole_0 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('162',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','34'])).

thf('163',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( k1_xboole_0
    = ( k1_tops_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['160','163','164'])).

thf('166',plain,
    ( ( ( k1_tops_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 )
   <= ( ( k1_tops_1 @ sk_A @ sk_B_1 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['110'])).

thf('167',plain,(
    ( k1_tops_1 @ sk_A @ sk_B_1 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['111','154'])).

thf('168',plain,(
    ( k1_tops_1 @ sk_A @ sk_B_1 )
 != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['166','167'])).

thf('169',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['165','168'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.qf3CpuWmQI
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:25:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.91/1.10  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.91/1.10  % Solved by: fo/fo7.sh
% 0.91/1.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.10  % done 1755 iterations in 0.653s
% 0.91/1.10  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.91/1.10  % SZS output start Refutation
% 0.91/1.10  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.91/1.10  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.91/1.10  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.91/1.10  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.91/1.10  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.91/1.10  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.91/1.10  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.10  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.91/1.10  thf(v2_tops_1_type, type, v2_tops_1: $i > $i > $o).
% 0.91/1.10  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.91/1.10  thf(v1_tops_1_type, type, v1_tops_1: $i > $i > $o).
% 0.91/1.10  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.10  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.91/1.10  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.91/1.10  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.91/1.10  thf(d10_xboole_0, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.91/1.10  thf('0', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.91/1.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.91/1.10  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.91/1.10      inference('simplify', [status(thm)], ['0'])).
% 0.91/1.10  thf(t3_subset, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.91/1.10  thf('2', plain,
% 0.91/1.10      (![X19 : $i, X21 : $i]:
% 0.91/1.10         ((m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X21)) | ~ (r1_tarski @ X19 @ X21))),
% 0.91/1.10      inference('cnf', [status(esa)], [t3_subset])).
% 0.91/1.10  thf('3', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['1', '2'])).
% 0.91/1.10  thf(d3_tops_1, axiom,
% 0.91/1.10    (![A:$i]:
% 0.91/1.10     ( ( l1_pre_topc @ A ) =>
% 0.91/1.10       ( ![B:$i]:
% 0.91/1.10         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.10           ( ( v1_tops_1 @ B @ A ) <=>
% 0.91/1.10             ( ( k2_pre_topc @ A @ B ) = ( k2_struct_0 @ A ) ) ) ) ) ))).
% 0.91/1.10  thf('4', plain,
% 0.91/1.10      (![X35 : $i, X36 : $i]:
% 0.91/1.10         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.91/1.10          | ~ (v1_tops_1 @ X35 @ X36)
% 0.91/1.10          | ((k2_pre_topc @ X36 @ X35) = (k2_struct_0 @ X36))
% 0.91/1.10          | ~ (l1_pre_topc @ X36))),
% 0.91/1.10      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.91/1.10  thf('5', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (~ (l1_pre_topc @ X0)
% 0.91/1.10          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.91/1.10          | ~ (v1_tops_1 @ (u1_struct_0 @ X0) @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['3', '4'])).
% 0.91/1.10  thf(t4_subset_1, axiom,
% 0.91/1.10    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.91/1.10  thf('6', plain,
% 0.91/1.10      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 0.91/1.10      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.91/1.10  thf(d4_tops_1, axiom,
% 0.91/1.10    (![A:$i]:
% 0.91/1.10     ( ( l1_pre_topc @ A ) =>
% 0.91/1.10       ( ![B:$i]:
% 0.91/1.10         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.10           ( ( v2_tops_1 @ B @ A ) <=>
% 0.91/1.10             ( v1_tops_1 @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) @ A ) ) ) ) ))).
% 0.91/1.10  thf('7', plain,
% 0.91/1.10      (![X37 : $i, X38 : $i]:
% 0.91/1.10         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.91/1.10          | ~ (v2_tops_1 @ X37 @ X38)
% 0.91/1.10          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X38) @ X37) @ X38)
% 0.91/1.10          | ~ (l1_pre_topc @ X38))),
% 0.91/1.10      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.91/1.10  thf('8', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (~ (l1_pre_topc @ X0)
% 0.91/1.10          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0) @ X0)
% 0.91/1.10          | ~ (v2_tops_1 @ k1_xboole_0 @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['6', '7'])).
% 0.91/1.10  thf('9', plain,
% 0.91/1.10      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 0.91/1.10      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.91/1.10  thf(d5_subset_1, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.91/1.10       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.91/1.10  thf('10', plain,
% 0.91/1.10      (![X6 : $i, X7 : $i]:
% 0.91/1.10         (((k3_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))
% 0.91/1.10          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.91/1.10      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.91/1.10  thf('11', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['9', '10'])).
% 0.91/1.10  thf('12', plain,
% 0.91/1.10      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 0.91/1.10      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.91/1.10  thf(dt_k3_subset_1, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.91/1.10       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.91/1.10  thf('13', plain,
% 0.91/1.10      (![X8 : $i, X9 : $i]:
% 0.91/1.10         ((m1_subset_1 @ (k3_subset_1 @ X8 @ X9) @ (k1_zfmisc_1 @ X8))
% 0.91/1.10          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.91/1.10      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.91/1.10  thf('14', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (m1_subset_1 @ (k3_subset_1 @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['12', '13'])).
% 0.91/1.10  thf('15', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['9', '10'])).
% 0.91/1.10  thf('16', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (m1_subset_1 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.91/1.10      inference('demod', [status(thm)], ['14', '15'])).
% 0.91/1.10  thf('17', plain,
% 0.91/1.10      (![X19 : $i, X20 : $i]:
% 0.91/1.10         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.91/1.10      inference('cnf', [status(esa)], [t3_subset])).
% 0.91/1.10  thf('18', plain,
% 0.91/1.10      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ X0)),
% 0.91/1.10      inference('sup-', [status(thm)], ['16', '17'])).
% 0.91/1.10  thf('19', plain,
% 0.91/1.10      (![X0 : $i, X2 : $i]:
% 0.91/1.10         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.91/1.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.91/1.10  thf('20', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (~ (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0))
% 0.91/1.10          | ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['18', '19'])).
% 0.91/1.10  thf('21', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['1', '2'])).
% 0.91/1.10  thf('22', plain,
% 0.91/1.10      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 0.91/1.10      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.91/1.10  thf(involutiveness_k3_subset_1, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.91/1.10       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.91/1.10  thf('23', plain,
% 0.91/1.10      (![X10 : $i, X11 : $i]:
% 0.91/1.10         (((k3_subset_1 @ X11 @ (k3_subset_1 @ X11 @ X10)) = (X10))
% 0.91/1.10          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.91/1.10      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.91/1.10  thf('24', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['22', '23'])).
% 0.91/1.10  thf('25', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['9', '10'])).
% 0.91/1.10  thf('26', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.91/1.10      inference('demod', [status(thm)], ['24', '25'])).
% 0.91/1.10  thf(t31_subset_1, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.91/1.10       ( ![C:$i]:
% 0.91/1.10         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.91/1.10           ( ( r1_tarski @ B @ C ) <=>
% 0.91/1.10             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.91/1.10  thf('27', plain,
% 0.91/1.10      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.91/1.10         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.91/1.10          | ~ (r1_tarski @ (k3_subset_1 @ X13 @ X12) @ 
% 0.91/1.10               (k3_subset_1 @ X13 @ X14))
% 0.91/1.10          | (r1_tarski @ X14 @ X12)
% 0.91/1.10          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.91/1.10      inference('cnf', [status(esa)], [t31_subset_1])).
% 0.91/1.10  thf('28', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         (~ (r1_tarski @ k1_xboole_0 @ (k3_subset_1 @ X1 @ X0))
% 0.91/1.10          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.91/1.10          | (r1_tarski @ X0 @ (k4_xboole_0 @ X1 @ k1_xboole_0))
% 0.91/1.10          | ~ (m1_subset_1 @ (k4_xboole_0 @ X1 @ k1_xboole_0) @ 
% 0.91/1.10               (k1_zfmisc_1 @ X1)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['26', '27'])).
% 0.91/1.10  thf('29', plain,
% 0.91/1.10      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 0.91/1.10      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.91/1.10  thf('30', plain,
% 0.91/1.10      (![X19 : $i, X20 : $i]:
% 0.91/1.10         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.91/1.10      inference('cnf', [status(esa)], [t3_subset])).
% 0.91/1.10  thf('31', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.91/1.10      inference('sup-', [status(thm)], ['29', '30'])).
% 0.91/1.10  thf('32', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (m1_subset_1 @ (k4_xboole_0 @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.91/1.10      inference('demod', [status(thm)], ['14', '15'])).
% 0.91/1.10  thf('33', plain,
% 0.91/1.10      (![X0 : $i, X1 : $i]:
% 0.91/1.10         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.91/1.10          | (r1_tarski @ X0 @ (k4_xboole_0 @ X1 @ k1_xboole_0)))),
% 0.91/1.10      inference('demod', [status(thm)], ['28', '31', '32'])).
% 0.91/1.10  thf('34', plain,
% 0.91/1.10      (![X0 : $i]: (r1_tarski @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['21', '33'])).
% 0.91/1.10  thf('35', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.91/1.10      inference('demod', [status(thm)], ['20', '34'])).
% 0.91/1.10  thf('36', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.91/1.10      inference('demod', [status(thm)], ['11', '35'])).
% 0.91/1.10  thf('37', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (~ (l1_pre_topc @ X0)
% 0.91/1.10          | (v1_tops_1 @ (u1_struct_0 @ X0) @ X0)
% 0.91/1.10          | ~ (v2_tops_1 @ k1_xboole_0 @ X0))),
% 0.91/1.10      inference('demod', [status(thm)], ['8', '36'])).
% 0.91/1.10  thf('38', plain,
% 0.91/1.10      (![X18 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X18))),
% 0.91/1.10      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.91/1.10  thf(cc2_tops_1, axiom,
% 0.91/1.10    (![A:$i]:
% 0.91/1.10     ( ( l1_pre_topc @ A ) =>
% 0.91/1.10       ( ![B:$i]:
% 0.91/1.10         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.10           ( ( v1_xboole_0 @ B ) => ( v2_tops_1 @ B @ A ) ) ) ) ))).
% 0.91/1.10  thf('39', plain,
% 0.91/1.10      (![X31 : $i, X32 : $i]:
% 0.91/1.10         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.91/1.10          | (v2_tops_1 @ X31 @ X32)
% 0.91/1.10          | ~ (v1_xboole_0 @ X31)
% 0.91/1.10          | ~ (l1_pre_topc @ X32))),
% 0.91/1.10      inference('cnf', [status(esa)], [cc2_tops_1])).
% 0.91/1.10  thf('40', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (~ (l1_pre_topc @ X0)
% 0.91/1.10          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.91/1.10          | (v2_tops_1 @ k1_xboole_0 @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['38', '39'])).
% 0.91/1.10  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.91/1.10  thf('41', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.91/1.10      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.91/1.10  thf('42', plain,
% 0.91/1.10      (![X0 : $i]: (~ (l1_pre_topc @ X0) | (v2_tops_1 @ k1_xboole_0 @ X0))),
% 0.91/1.10      inference('demod', [status(thm)], ['40', '41'])).
% 0.91/1.10  thf('43', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         ((v1_tops_1 @ (u1_struct_0 @ X0) @ X0) | ~ (l1_pre_topc @ X0))),
% 0.91/1.10      inference('clc', [status(thm)], ['37', '42'])).
% 0.91/1.10  thf('44', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.91/1.10          | ~ (l1_pre_topc @ X0))),
% 0.91/1.10      inference('clc', [status(thm)], ['5', '43'])).
% 0.91/1.10  thf('45', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['1', '2'])).
% 0.91/1.10  thf(dt_k2_pre_topc, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( ( l1_pre_topc @ A ) & 
% 0.91/1.10         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.91/1.10       ( m1_subset_1 @
% 0.91/1.10         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.91/1.10  thf('46', plain,
% 0.91/1.10      (![X25 : $i, X26 : $i]:
% 0.91/1.10         (~ (l1_pre_topc @ X25)
% 0.91/1.10          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.91/1.10          | (m1_subset_1 @ (k2_pre_topc @ X25 @ X26) @ 
% 0.91/1.10             (k1_zfmisc_1 @ (u1_struct_0 @ X25))))),
% 0.91/1.10      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.91/1.10  thf('47', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         ((m1_subset_1 @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 0.91/1.10           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.91/1.10          | ~ (l1_pre_topc @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['45', '46'])).
% 0.91/1.10  thf('48', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         ((m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.91/1.10           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.91/1.10          | ~ (l1_pre_topc @ X0)
% 0.91/1.10          | ~ (l1_pre_topc @ X0))),
% 0.91/1.10      inference('sup+', [status(thm)], ['44', '47'])).
% 0.91/1.10  thf('49', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (~ (l1_pre_topc @ X0)
% 0.91/1.10          | (m1_subset_1 @ (k2_struct_0 @ X0) @ 
% 0.91/1.10             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.91/1.10      inference('simplify', [status(thm)], ['48'])).
% 0.91/1.10  thf('50', plain,
% 0.91/1.10      (![X19 : $i, X20 : $i]:
% 0.91/1.10         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.91/1.10      inference('cnf', [status(esa)], [t3_subset])).
% 0.91/1.10  thf('51', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (~ (l1_pre_topc @ X0)
% 0.91/1.10          | (r1_tarski @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X0)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['49', '50'])).
% 0.91/1.10  thf('52', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.91/1.10          | ~ (l1_pre_topc @ X0))),
% 0.91/1.10      inference('clc', [status(thm)], ['5', '43'])).
% 0.91/1.10  thf('53', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['1', '2'])).
% 0.91/1.10  thf(t48_pre_topc, axiom,
% 0.91/1.10    (![A:$i]:
% 0.91/1.10     ( ( l1_pre_topc @ A ) =>
% 0.91/1.10       ( ![B:$i]:
% 0.91/1.10         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.10           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.91/1.10  thf('54', plain,
% 0.91/1.10      (![X29 : $i, X30 : $i]:
% 0.91/1.10         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 0.91/1.10          | (r1_tarski @ X29 @ (k2_pre_topc @ X30 @ X29))
% 0.91/1.10          | ~ (l1_pre_topc @ X30))),
% 0.91/1.10      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.91/1.10  thf('55', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (~ (l1_pre_topc @ X0)
% 0.91/1.10          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.91/1.10             (k2_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 0.91/1.10      inference('sup-', [status(thm)], ['53', '54'])).
% 0.91/1.10  thf('56', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         ((r1_tarski @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 0.91/1.10          | ~ (l1_pre_topc @ X0)
% 0.91/1.10          | ~ (l1_pre_topc @ X0))),
% 0.91/1.10      inference('sup+', [status(thm)], ['52', '55'])).
% 0.91/1.10  thf('57', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (~ (l1_pre_topc @ X0)
% 0.91/1.10          | (r1_tarski @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0)))),
% 0.91/1.10      inference('simplify', [status(thm)], ['56'])).
% 0.91/1.10  thf('58', plain,
% 0.91/1.10      (![X0 : $i, X2 : $i]:
% 0.91/1.10         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.91/1.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.91/1.10  thf('59', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (~ (l1_pre_topc @ X0)
% 0.91/1.10          | ~ (r1_tarski @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X0))
% 0.91/1.10          | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['57', '58'])).
% 0.91/1.10  thf('60', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (~ (l1_pre_topc @ X0)
% 0.91/1.10          | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0))
% 0.91/1.10          | ~ (l1_pre_topc @ X0))),
% 0.91/1.10      inference('sup-', [status(thm)], ['51', '59'])).
% 0.91/1.10  thf('61', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0)) | ~ (l1_pre_topc @ X0))),
% 0.91/1.10      inference('simplify', [status(thm)], ['60'])).
% 0.91/1.10  thf(t84_tops_1, conjecture,
% 0.91/1.10    (![A:$i]:
% 0.91/1.10     ( ( l1_pre_topc @ A ) =>
% 0.91/1.10       ( ![B:$i]:
% 0.91/1.10         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.10           ( ( v2_tops_1 @ B @ A ) <=>
% 0.91/1.10             ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.91/1.10  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.10    (~( ![A:$i]:
% 0.91/1.10        ( ( l1_pre_topc @ A ) =>
% 0.91/1.10          ( ![B:$i]:
% 0.91/1.10            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.10              ( ( v2_tops_1 @ B @ A ) <=>
% 0.91/1.10                ( ( k1_tops_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.91/1.10    inference('cnf.neg', [status(esa)], [t84_tops_1])).
% 0.91/1.10  thf('62', plain,
% 0.91/1.10      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf(dt_k1_tops_1, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( ( l1_pre_topc @ A ) & 
% 0.91/1.10         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.91/1.10       ( m1_subset_1 @
% 0.91/1.10         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.91/1.10  thf('63', plain,
% 0.91/1.10      (![X39 : $i, X40 : $i]:
% 0.91/1.10         (~ (l1_pre_topc @ X39)
% 0.91/1.10          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 0.91/1.10          | (m1_subset_1 @ (k1_tops_1 @ X39 @ X40) @ 
% 0.91/1.10             (k1_zfmisc_1 @ (u1_struct_0 @ X39))))),
% 0.91/1.10      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 0.91/1.10  thf('64', plain,
% 0.91/1.10      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 0.91/1.10         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.10        | ~ (l1_pre_topc @ sk_A))),
% 0.91/1.10      inference('sup-', [status(thm)], ['62', '63'])).
% 0.91/1.10  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('66', plain,
% 0.91/1.10      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 0.91/1.10        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.10      inference('demod', [status(thm)], ['64', '65'])).
% 0.91/1.10  thf('67', plain,
% 0.91/1.10      (![X10 : $i, X11 : $i]:
% 0.91/1.10         (((k3_subset_1 @ X11 @ (k3_subset_1 @ X11 @ X10)) = (X10))
% 0.91/1.10          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.91/1.10      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.91/1.10  thf('68', plain,
% 0.91/1.10      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.10         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B_1)))
% 0.91/1.10         = (k1_tops_1 @ sk_A @ sk_B_1))),
% 0.91/1.10      inference('sup-', [status(thm)], ['66', '67'])).
% 0.91/1.10  thf('69', plain,
% 0.91/1.10      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B_1) @ 
% 0.91/1.10        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.10      inference('demod', [status(thm)], ['64', '65'])).
% 0.91/1.10  thf('70', plain,
% 0.91/1.10      (![X6 : $i, X7 : $i]:
% 0.91/1.10         (((k3_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))
% 0.91/1.10          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.91/1.10      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.91/1.10  thf('71', plain,
% 0.91/1.10      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B_1))
% 0.91/1.10         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['69', '70'])).
% 0.91/1.10  thf('72', plain,
% 0.91/1.10      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.10         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B_1)))
% 0.91/1.10         = (k1_tops_1 @ sk_A @ sk_B_1))),
% 0.91/1.10      inference('demod', [status(thm)], ['68', '71'])).
% 0.91/1.10  thf('73', plain,
% 0.91/1.10      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('74', plain,
% 0.91/1.10      (![X8 : $i, X9 : $i]:
% 0.91/1.10         ((m1_subset_1 @ (k3_subset_1 @ X8 @ X9) @ (k1_zfmisc_1 @ X8))
% 0.91/1.10          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X8)))),
% 0.91/1.10      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.91/1.10  thf('75', plain,
% 0.91/1.10      ((m1_subset_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.91/1.10        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['73', '74'])).
% 0.91/1.10  thf('76', plain,
% 0.91/1.10      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('77', plain,
% 0.91/1.10      (![X6 : $i, X7 : $i]:
% 0.91/1.10         (((k3_subset_1 @ X6 @ X7) = (k4_xboole_0 @ X6 @ X7))
% 0.91/1.10          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6)))),
% 0.91/1.10      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.91/1.10  thf('78', plain,
% 0.91/1.10      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 0.91/1.10         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.91/1.10      inference('sup-', [status(thm)], ['76', '77'])).
% 0.91/1.10  thf('79', plain,
% 0.91/1.10      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.91/1.10        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.10      inference('demod', [status(thm)], ['75', '78'])).
% 0.91/1.10  thf('80', plain,
% 0.91/1.10      (![X35 : $i, X36 : $i]:
% 0.91/1.10         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.91/1.10          | ~ (v1_tops_1 @ X35 @ X36)
% 0.91/1.10          | ((k2_pre_topc @ X36 @ X35) = (k2_struct_0 @ X36))
% 0.91/1.10          | ~ (l1_pre_topc @ X36))),
% 0.91/1.10      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.91/1.10  thf('81', plain,
% 0.91/1.10      ((~ (l1_pre_topc @ sk_A)
% 0.91/1.10        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.91/1.10            = (k2_struct_0 @ sk_A))
% 0.91/1.10        | ~ (v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.91/1.10      inference('sup-', [status(thm)], ['79', '80'])).
% 0.91/1.10  thf('82', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('83', plain,
% 0.91/1.10      ((((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.91/1.10          = (k2_struct_0 @ sk_A))
% 0.91/1.10        | ~ (v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.91/1.10      inference('demod', [status(thm)], ['81', '82'])).
% 0.91/1.10  thf('84', plain,
% 0.91/1.10      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.91/1.10        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.10      inference('demod', [status(thm)], ['75', '78'])).
% 0.91/1.10  thf('85', plain,
% 0.91/1.10      (![X25 : $i, X26 : $i]:
% 0.91/1.10         (~ (l1_pre_topc @ X25)
% 0.91/1.10          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.91/1.10          | (m1_subset_1 @ (k2_pre_topc @ X25 @ X26) @ 
% 0.91/1.10             (k1_zfmisc_1 @ (u1_struct_0 @ X25))))),
% 0.91/1.10      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.91/1.10  thf('86', plain,
% 0.91/1.10      (((m1_subset_1 @ 
% 0.91/1.10         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.91/1.10         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 0.91/1.10        | ~ (l1_pre_topc @ sk_A))),
% 0.91/1.10      inference('sup-', [status(thm)], ['84', '85'])).
% 0.91/1.10  thf('87', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('88', plain,
% 0.91/1.10      ((m1_subset_1 @ 
% 0.91/1.10        (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1)) @ 
% 0.91/1.10        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.10      inference('demod', [status(thm)], ['86', '87'])).
% 0.91/1.10  thf('89', plain,
% 0.91/1.10      (![X10 : $i, X11 : $i]:
% 0.91/1.10         (((k3_subset_1 @ X11 @ (k3_subset_1 @ X11 @ X10)) = (X10))
% 0.91/1.10          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.91/1.10      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.91/1.10  thf('90', plain,
% 0.91/1.10      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.10         (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.10          (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))))
% 0.91/1.10         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['88', '89'])).
% 0.91/1.10  thf('91', plain,
% 0.91/1.10      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf(d1_tops_1, axiom,
% 0.91/1.10    (![A:$i]:
% 0.91/1.10     ( ( l1_pre_topc @ A ) =>
% 0.91/1.10       ( ![B:$i]:
% 0.91/1.10         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.91/1.10           ( ( k1_tops_1 @ A @ B ) =
% 0.91/1.10             ( k3_subset_1 @
% 0.91/1.10               ( u1_struct_0 @ A ) @ 
% 0.91/1.10               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.91/1.10  thf('92', plain,
% 0.91/1.10      (![X33 : $i, X34 : $i]:
% 0.91/1.10         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.91/1.10          | ((k1_tops_1 @ X34 @ X33)
% 0.91/1.10              = (k3_subset_1 @ (u1_struct_0 @ X34) @ 
% 0.91/1.10                 (k2_pre_topc @ X34 @ (k3_subset_1 @ (u1_struct_0 @ X34) @ X33))))
% 0.91/1.10          | ~ (l1_pre_topc @ X34))),
% 0.91/1.10      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.91/1.10  thf('93', plain,
% 0.91/1.10      ((~ (l1_pre_topc @ sk_A)
% 0.91/1.10        | ((k1_tops_1 @ sk_A @ sk_B_1)
% 0.91/1.10            = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.10               (k2_pre_topc @ sk_A @ 
% 0.91/1.10                (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)))))),
% 0.91/1.10      inference('sup-', [status(thm)], ['91', '92'])).
% 0.91/1.10  thf('94', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('95', plain,
% 0.91/1.10      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 0.91/1.10         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.91/1.10      inference('sup-', [status(thm)], ['76', '77'])).
% 0.91/1.10  thf('96', plain,
% 0.91/1.10      (((k1_tops_1 @ sk_A @ sk_B_1)
% 0.91/1.10         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 0.91/1.10            (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))))),
% 0.91/1.10      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.91/1.10  thf('97', plain,
% 0.91/1.10      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B_1))
% 0.91/1.10         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.91/1.10      inference('demod', [status(thm)], ['90', '96'])).
% 0.91/1.10  thf('98', plain,
% 0.91/1.10      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B_1))
% 0.91/1.10         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['69', '70'])).
% 0.91/1.10  thf('99', plain,
% 0.91/1.10      (((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.91/1.10         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 0.91/1.10      inference('sup+', [status(thm)], ['97', '98'])).
% 0.91/1.10  thf('100', plain,
% 0.91/1.10      ((((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B_1))
% 0.91/1.10          = (k2_struct_0 @ sk_A))
% 0.91/1.10        | ~ (v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.91/1.10      inference('demod', [status(thm)], ['83', '99'])).
% 0.91/1.10  thf('101', plain,
% 0.91/1.10      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))
% 0.91/1.10        | (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('102', plain,
% 0.91/1.10      (((v2_tops_1 @ sk_B_1 @ sk_A)) <= (((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.91/1.10      inference('split', [status(esa)], ['101'])).
% 0.91/1.10  thf('103', plain,
% 0.91/1.10      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('104', plain,
% 0.91/1.10      (![X37 : $i, X38 : $i]:
% 0.91/1.10         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.91/1.10          | ~ (v2_tops_1 @ X37 @ X38)
% 0.91/1.10          | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X38) @ X37) @ X38)
% 0.91/1.10          | ~ (l1_pre_topc @ X38))),
% 0.91/1.10      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.91/1.10  thf('105', plain,
% 0.91/1.10      ((~ (l1_pre_topc @ sk_A)
% 0.91/1.10        | (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.91/1.10        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.91/1.10      inference('sup-', [status(thm)], ['103', '104'])).
% 0.91/1.10  thf('106', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('107', plain,
% 0.91/1.10      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 0.91/1.10         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.91/1.10      inference('sup-', [status(thm)], ['76', '77'])).
% 0.91/1.10  thf('108', plain,
% 0.91/1.10      (((v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.91/1.10        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.91/1.10      inference('demod', [status(thm)], ['105', '106', '107'])).
% 0.91/1.10  thf('109', plain,
% 0.91/1.10      (((v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))
% 0.91/1.10         <= (((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['102', '108'])).
% 0.91/1.10  thf('110', plain,
% 0.91/1.10      ((((k1_tops_1 @ sk_A @ sk_B_1) != (k1_xboole_0))
% 0.91/1.10        | ~ (v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('111', plain,
% 0.91/1.10      (~ (((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))) | 
% 0.91/1.10       ~ ((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.91/1.10      inference('split', [status(esa)], ['110'])).
% 0.91/1.10  thf('112', plain,
% 0.91/1.10      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.91/1.10         <= ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('split', [status(esa)], ['101'])).
% 0.91/1.10  thf('113', plain,
% 0.91/1.10      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.91/1.10        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.10      inference('demod', [status(thm)], ['75', '78'])).
% 0.91/1.10  thf(projectivity_k2_pre_topc, axiom,
% 0.91/1.10    (![A:$i,B:$i]:
% 0.91/1.10     ( ( ( l1_pre_topc @ A ) & 
% 0.91/1.10         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.91/1.10       ( ( k2_pre_topc @ A @ ( k2_pre_topc @ A @ B ) ) =
% 0.91/1.10         ( k2_pre_topc @ A @ B ) ) ))).
% 0.91/1.10  thf('114', plain,
% 0.91/1.10      (![X27 : $i, X28 : $i]:
% 0.91/1.10         (~ (l1_pre_topc @ X27)
% 0.91/1.10          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.91/1.10          | ((k2_pre_topc @ X27 @ (k2_pre_topc @ X27 @ X28))
% 0.91/1.10              = (k2_pre_topc @ X27 @ X28)))),
% 0.91/1.10      inference('cnf', [status(esa)], [projectivity_k2_pre_topc])).
% 0.91/1.10  thf('115', plain,
% 0.91/1.10      ((((k2_pre_topc @ sk_A @ 
% 0.91/1.10          (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.91/1.10          = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.91/1.10        | ~ (l1_pre_topc @ sk_A))),
% 0.91/1.10      inference('sup-', [status(thm)], ['113', '114'])).
% 0.91/1.10  thf('116', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('117', plain,
% 0.91/1.10      (((k2_pre_topc @ sk_A @ 
% 0.91/1.10         (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1)))
% 0.91/1.10         = (k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1)))),
% 0.91/1.10      inference('demod', [status(thm)], ['115', '116'])).
% 0.91/1.10  thf('118', plain,
% 0.91/1.10      (((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.91/1.10         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 0.91/1.10      inference('sup+', [status(thm)], ['97', '98'])).
% 0.91/1.10  thf('119', plain,
% 0.91/1.10      (((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.91/1.10         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 0.91/1.10      inference('sup+', [status(thm)], ['97', '98'])).
% 0.91/1.10  thf('120', plain,
% 0.91/1.10      (((k2_pre_topc @ sk_A @ 
% 0.91/1.10         (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B_1)))
% 0.91/1.10         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 0.91/1.10      inference('demod', [status(thm)], ['117', '118', '119'])).
% 0.91/1.10  thf('121', plain,
% 0.91/1.10      ((((k2_pre_topc @ sk_A @ 
% 0.91/1.10          (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ k1_xboole_0))
% 0.91/1.10          = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B_1))))
% 0.91/1.10         <= ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('sup+', [status(thm)], ['112', '120'])).
% 0.91/1.10  thf('122', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.91/1.10      inference('demod', [status(thm)], ['20', '34'])).
% 0.91/1.10  thf('123', plain,
% 0.91/1.10      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.91/1.10         <= ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('split', [status(esa)], ['101'])).
% 0.91/1.10  thf('124', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.91/1.10      inference('demod', [status(thm)], ['20', '34'])).
% 0.91/1.10  thf('125', plain,
% 0.91/1.10      ((((k2_pre_topc @ sk_A @ (u1_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A)))
% 0.91/1.10         <= ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('demod', [status(thm)], ['121', '122', '123', '124'])).
% 0.91/1.10  thf('126', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         (((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.91/1.10          | ~ (l1_pre_topc @ X0))),
% 0.91/1.10      inference('clc', [status(thm)], ['5', '43'])).
% 0.91/1.10  thf('127', plain,
% 0.91/1.10      (((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)) | ~ (l1_pre_topc @ sk_A)))
% 0.91/1.10         <= ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('sup+', [status(thm)], ['125', '126'])).
% 0.91/1.10  thf('128', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('129', plain,
% 0.91/1.10      ((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))
% 0.91/1.10         <= ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('demod', [status(thm)], ['127', '128'])).
% 0.91/1.10  thf('130', plain,
% 0.91/1.10      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('131', plain,
% 0.91/1.10      (![X37 : $i, X38 : $i]:
% 0.91/1.10         (~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (u1_struct_0 @ X38)))
% 0.91/1.10          | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ X38) @ X37) @ X38)
% 0.91/1.10          | (v2_tops_1 @ X37 @ X38)
% 0.91/1.10          | ~ (l1_pre_topc @ X38))),
% 0.91/1.10      inference('cnf', [status(esa)], [d4_tops_1])).
% 0.91/1.10  thf('132', plain,
% 0.91/1.10      ((~ (l1_pre_topc @ sk_A)
% 0.91/1.10        | (v2_tops_1 @ sk_B_1 @ sk_A)
% 0.91/1.10        | ~ (v1_tops_1 @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.91/1.10      inference('sup-', [status(thm)], ['130', '131'])).
% 0.91/1.10  thf('133', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('134', plain,
% 0.91/1.10      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B_1)
% 0.91/1.10         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))),
% 0.91/1.10      inference('sup-', [status(thm)], ['76', '77'])).
% 0.91/1.10  thf('135', plain,
% 0.91/1.10      (((v2_tops_1 @ sk_B_1 @ sk_A)
% 0.91/1.10        | ~ (v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A))),
% 0.91/1.10      inference('demod', [status(thm)], ['132', '133', '134'])).
% 0.91/1.10  thf('136', plain,
% 0.91/1.10      (((~ (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.91/1.10         | (v2_tops_1 @ sk_B_1 @ sk_A)))
% 0.91/1.10         <= ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('sup-', [status(thm)], ['129', '135'])).
% 0.91/1.10  thf('137', plain,
% 0.91/1.10      ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))
% 0.91/1.10         <= ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('split', [status(esa)], ['101'])).
% 0.91/1.10  thf('138', plain,
% 0.91/1.10      ((m1_subset_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ 
% 0.91/1.10        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 0.91/1.10      inference('demod', [status(thm)], ['75', '78'])).
% 0.91/1.10  thf('139', plain,
% 0.91/1.10      (![X35 : $i, X36 : $i]:
% 0.91/1.10         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (u1_struct_0 @ X36)))
% 0.91/1.10          | ((k2_pre_topc @ X36 @ X35) != (k2_struct_0 @ X36))
% 0.91/1.10          | (v1_tops_1 @ X35 @ X36)
% 0.91/1.10          | ~ (l1_pre_topc @ X36))),
% 0.91/1.10      inference('cnf', [status(esa)], [d3_tops_1])).
% 0.91/1.10  thf('140', plain,
% 0.91/1.10      ((~ (l1_pre_topc @ sk_A)
% 0.91/1.10        | (v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.91/1.10        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.91/1.10            != (k2_struct_0 @ sk_A)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['138', '139'])).
% 0.91/1.10  thf('141', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('142', plain,
% 0.91/1.10      (((v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.91/1.10        | ((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.91/1.10            != (k2_struct_0 @ sk_A)))),
% 0.91/1.10      inference('demod', [status(thm)], ['140', '141'])).
% 0.91/1.10  thf('143', plain,
% 0.91/1.10      (((k2_pre_topc @ sk_A @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1))
% 0.91/1.10         = (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B_1)))),
% 0.91/1.10      inference('sup+', [status(thm)], ['97', '98'])).
% 0.91/1.10  thf('144', plain,
% 0.91/1.10      (((v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)
% 0.91/1.10        | ((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B_1))
% 0.91/1.10            != (k2_struct_0 @ sk_A)))),
% 0.91/1.10      inference('demod', [status(thm)], ['142', '143'])).
% 0.91/1.10  thf('145', plain,
% 0.91/1.10      (((((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ k1_xboole_0)
% 0.91/1.10           != (k2_struct_0 @ sk_A))
% 0.91/1.10         | (v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)))
% 0.91/1.10         <= ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('sup-', [status(thm)], ['137', '144'])).
% 0.91/1.10  thf('146', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.91/1.10      inference('demod', [status(thm)], ['20', '34'])).
% 0.91/1.10  thf('147', plain,
% 0.91/1.10      (((((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.91/1.10         | (v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)))
% 0.91/1.10         <= ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('demod', [status(thm)], ['145', '146'])).
% 0.91/1.10  thf('148', plain,
% 0.91/1.10      ((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))
% 0.91/1.10         <= ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('demod', [status(thm)], ['127', '128'])).
% 0.91/1.10  thf('149', plain,
% 0.91/1.10      ((((u1_struct_0 @ sk_A) = (k2_struct_0 @ sk_A)))
% 0.91/1.10         <= ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('demod', [status(thm)], ['127', '128'])).
% 0.91/1.10  thf('150', plain,
% 0.91/1.10      (((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.91/1.10         | (v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A)))
% 0.91/1.10         <= ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('demod', [status(thm)], ['147', '148', '149'])).
% 0.91/1.10  thf('151', plain,
% 0.91/1.10      (((v1_tops_1 @ (k4_xboole_0 @ (k2_struct_0 @ sk_A) @ sk_B_1) @ sk_A))
% 0.91/1.10         <= ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('simplify', [status(thm)], ['150'])).
% 0.91/1.10  thf('152', plain,
% 0.91/1.10      (((v2_tops_1 @ sk_B_1 @ sk_A))
% 0.91/1.10         <= ((((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('demod', [status(thm)], ['136', '151'])).
% 0.91/1.10  thf('153', plain,
% 0.91/1.10      ((~ (v2_tops_1 @ sk_B_1 @ sk_A)) <= (~ ((v2_tops_1 @ sk_B_1 @ sk_A)))),
% 0.91/1.10      inference('split', [status(esa)], ['110'])).
% 0.91/1.10  thf('154', plain,
% 0.91/1.10      (((v2_tops_1 @ sk_B_1 @ sk_A)) | 
% 0.91/1.10       ~ (((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.91/1.10      inference('sup-', [status(thm)], ['152', '153'])).
% 0.91/1.10  thf('155', plain,
% 0.91/1.10      (((v2_tops_1 @ sk_B_1 @ sk_A)) | 
% 0.91/1.10       (((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.91/1.10      inference('split', [status(esa)], ['101'])).
% 0.91/1.10  thf('156', plain, (((v2_tops_1 @ sk_B_1 @ sk_A))),
% 0.91/1.10      inference('sat_resolution*', [status(thm)], ['111', '154', '155'])).
% 0.91/1.10  thf('157', plain,
% 0.91/1.10      ((v1_tops_1 @ (k4_xboole_0 @ (u1_struct_0 @ sk_A) @ sk_B_1) @ sk_A)),
% 0.91/1.10      inference('simpl_trail', [status(thm)], ['109', '156'])).
% 0.91/1.10  thf('158', plain,
% 0.91/1.10      (((k4_xboole_0 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B_1))
% 0.91/1.10         = (k2_struct_0 @ sk_A))),
% 0.91/1.10      inference('demod', [status(thm)], ['100', '157'])).
% 0.91/1.10  thf('159', plain,
% 0.91/1.10      (((k3_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.91/1.10         = (k1_tops_1 @ sk_A @ sk_B_1))),
% 0.91/1.10      inference('demod', [status(thm)], ['72', '158'])).
% 0.91/1.10  thf('160', plain,
% 0.91/1.10      ((((k3_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))
% 0.91/1.10          = (k1_tops_1 @ sk_A @ sk_B_1))
% 0.91/1.10        | ~ (l1_pre_topc @ sk_A))),
% 0.91/1.10      inference('sup+', [status(thm)], ['61', '159'])).
% 0.91/1.10  thf('161', plain,
% 0.91/1.10      (![X0 : $i]:
% 0.91/1.10         ((k3_subset_1 @ X0 @ (k4_xboole_0 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.91/1.10      inference('demod', [status(thm)], ['24', '25'])).
% 0.91/1.10  thf('162', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.91/1.10      inference('demod', [status(thm)], ['20', '34'])).
% 0.91/1.10  thf('163', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.91/1.10      inference('demod', [status(thm)], ['161', '162'])).
% 0.91/1.10  thf('164', plain, ((l1_pre_topc @ sk_A)),
% 0.91/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.10  thf('165', plain, (((k1_xboole_0) = (k1_tops_1 @ sk_A @ sk_B_1))),
% 0.91/1.10      inference('demod', [status(thm)], ['160', '163', '164'])).
% 0.91/1.10  thf('166', plain,
% 0.91/1.10      ((((k1_tops_1 @ sk_A @ sk_B_1) != (k1_xboole_0)))
% 0.91/1.10         <= (~ (((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0))))),
% 0.91/1.10      inference('split', [status(esa)], ['110'])).
% 0.91/1.10  thf('167', plain, (~ (((k1_tops_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.91/1.10      inference('sat_resolution*', [status(thm)], ['111', '154'])).
% 0.91/1.10  thf('168', plain, (((k1_tops_1 @ sk_A @ sk_B_1) != (k1_xboole_0))),
% 0.91/1.10      inference('simpl_trail', [status(thm)], ['166', '167'])).
% 0.91/1.10  thf('169', plain, ($false),
% 0.91/1.10      inference('simplify_reflect-', [status(thm)], ['165', '168'])).
% 0.91/1.10  
% 0.91/1.10  % SZS output end Refutation
% 0.91/1.10  
% 0.91/1.10  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
