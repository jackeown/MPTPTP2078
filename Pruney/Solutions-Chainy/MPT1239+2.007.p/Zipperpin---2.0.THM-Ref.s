%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UsbymTfZ4H

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:03:01 EST 2020

% Result     : Theorem 8.38s
% Output     : Refutation 8.38s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 117 expanded)
%              Number of leaves         :   27 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  680 (1551 expanded)
%              Number of equality atoms :   11 (  17 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_subset_1_type,type,(
    k7_subset_1: $i > $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(t50_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( r1_tarski @ ( k1_tops_1 @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
               => ( r1_tarski @ ( k1_tops_1 @ A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_tops_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ sk_C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k7_subset_1 @ A @ B @ C )
        = ( k4_xboole_0 @ B @ C ) ) ) )).

thf('2',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( ( k7_subset_1 @ X26 @ X25 @ X27 )
        = ( k4_xboole_0 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('6',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( l1_pre_topc @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) )
      | ( m1_subset_1 @ ( k1_tops_1 @ X30 @ X31 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tops_1])).

thf('7',plain,
    ( ( m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( ( k7_subset_1 @ X26 @ X25 @ X27 )
        = ( k4_xboole_0 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 )
      = ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['4','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('15',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ X23 ) )
      | ( m1_subset_1 @ ( k7_subset_1 @ X23 @ X22 @ X24 ) @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( k7_subset_1 @ ( u1_struct_0 @ sk_A ) @ sk_B @ X0 )
      = ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t48_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
             => ( ( r1_tarski @ B @ C )
               => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( r1_tarski @ X34 @ X36 )
      | ( r1_tarski @ ( k1_tops_1 @ X35 @ X34 ) @ ( k1_tops_1 @ X35 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X35 ) ) )
      | ~ ( l1_pre_topc @ X35 ) ) ),
    inference(cnf,[status(esa)],[t48_tops_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ X1 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ sk_B @ X0 ) @ sk_B )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['13','22'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['24'])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('26',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r1_tarski @ X5 @ X6 )
      | ( r1_tarski @ ( k4_xboole_0 @ X5 @ X7 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k1_tops_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['23','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t44_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) )).

thf('30',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X33 @ X32 ) @ X32 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('31',plain,
    ( ~ ( l1_pre_topc @ sk_A )
    | ( r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C ),
    inference(demod,[status(thm)],['31','32'])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('34',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_xboole_0 @ X9 @ X8 )
        = X8 )
      | ~ ( r1_tarski @ X9 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('35',plain,
    ( ( k2_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_C ) @ sk_C )
    = sk_C ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('36',plain,(
    ! [X17: $i,X18: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X17 @ X18 ) @ X18 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t70_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( ~ ( ( r1_xboole_0 @ A @ B )
              & ( r1_xboole_0 @ A @ C ) )
          & ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) )
          & ( r1_xboole_0 @ A @ B )
          & ( r1_xboole_0 @ A @ C ) ) ) )).

thf('37',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ( r1_xboole_0 @ X13 @ X14 )
      | ~ ( r1_xboole_0 @ X13 @ ( k2_xboole_0 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t70_xboole_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) @ X1 ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup+',[status(thm)],['35','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('41',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X33 ) ) )
      | ( r1_tarski @ ( k1_tops_1 @ X33 @ X32 ) @ X32 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[t44_tops_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ sk_A )
      | ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ ( k4_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('45',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ~ ( r1_xboole_0 @ X11 @ X12 )
      | ( r1_xboole_0 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ X0 ) ) @ X1 )
      | ~ ( r1_xboole_0 @ ( k4_xboole_0 @ sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r1_xboole_0 @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k1_tops_1 @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['39','46'])).

thf(t86_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ) )).

thf('48',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ X19 @ X20 )
      | ~ ( r1_xboole_0 @ X19 @ X21 )
      | ( r1_tarski @ X19 @ ( k4_xboole_0 @ X20 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t86_xboole_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ X0 @ ( k1_tops_1 @ sk_A @ sk_C ) ) )
      | ~ ( r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    r1_tarski @ ( k1_tops_1 @ sk_A @ ( k4_xboole_0 @ sk_B @ sk_C ) ) @ ( k4_xboole_0 @ ( k1_tops_1 @ sk_A @ sk_B ) @ ( k1_tops_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['12','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UsbymTfZ4H
% 0.13/0.37  % Computer   : n001.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 10:36:44 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 8.38/8.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.38/8.59  % Solved by: fo/fo7.sh
% 8.38/8.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.38/8.59  % done 8683 iterations in 8.106s
% 8.38/8.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.38/8.59  % SZS output start Refutation
% 8.38/8.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 8.38/8.59  thf(sk_A_type, type, sk_A: $i).
% 8.38/8.59  thf(k7_subset_1_type, type, k7_subset_1: $i > $i > $i > $i).
% 8.38/8.59  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 8.38/8.59  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 8.38/8.59  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 8.38/8.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.38/8.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 8.38/8.59  thf(sk_B_type, type, sk_B: $i).
% 8.38/8.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.38/8.59  thf(sk_C_type, type, sk_C: $i).
% 8.38/8.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.38/8.59  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 8.38/8.59  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 8.38/8.59  thf(t50_tops_1, conjecture,
% 8.38/8.59    (![A:$i]:
% 8.38/8.59     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.38/8.59       ( ![B:$i]:
% 8.38/8.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.38/8.59           ( ![C:$i]:
% 8.38/8.59             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.38/8.59               ( r1_tarski @
% 8.38/8.59                 ( k1_tops_1 @
% 8.38/8.59                   A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 8.38/8.59                 ( k7_subset_1 @
% 8.38/8.59                   ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 8.38/8.59                   ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 8.38/8.59  thf(zf_stmt_0, negated_conjecture,
% 8.38/8.59    (~( ![A:$i]:
% 8.38/8.59        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 8.38/8.59          ( ![B:$i]:
% 8.38/8.59            ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.38/8.59              ( ![C:$i]:
% 8.38/8.59                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.38/8.59                  ( r1_tarski @
% 8.38/8.59                    ( k1_tops_1 @
% 8.38/8.59                      A @ ( k7_subset_1 @ ( u1_struct_0 @ A ) @ B @ C ) ) @ 
% 8.38/8.59                    ( k7_subset_1 @
% 8.38/8.59                      ( u1_struct_0 @ A ) @ ( k1_tops_1 @ A @ B ) @ 
% 8.38/8.59                      ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 8.38/8.59    inference('cnf.neg', [status(esa)], [t50_tops_1])).
% 8.38/8.59  thf('0', plain,
% 8.38/8.59      (~ (r1_tarski @ 
% 8.38/8.59          (k1_tops_1 @ sk_A @ 
% 8.38/8.59           (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ sk_C)) @ 
% 8.38/8.59          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 8.38/8.59           (k1_tops_1 @ sk_A @ sk_C)))),
% 8.38/8.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.38/8.59  thf('1', plain,
% 8.38/8.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.38/8.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.38/8.59  thf(redefinition_k7_subset_1, axiom,
% 8.38/8.59    (![A:$i,B:$i,C:$i]:
% 8.38/8.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.38/8.59       ( ( k7_subset_1 @ A @ B @ C ) = ( k4_xboole_0 @ B @ C ) ) ))).
% 8.38/8.59  thf('2', plain,
% 8.38/8.59      (![X25 : $i, X26 : $i, X27 : $i]:
% 8.38/8.59         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 8.38/8.59          | ((k7_subset_1 @ X26 @ X25 @ X27) = (k4_xboole_0 @ X25 @ X27)))),
% 8.38/8.59      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 8.38/8.59  thf('3', plain,
% 8.38/8.59      (![X0 : $i]:
% 8.38/8.59         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 8.38/8.59           = (k4_xboole_0 @ sk_B @ X0))),
% 8.38/8.59      inference('sup-', [status(thm)], ['1', '2'])).
% 8.38/8.59  thf('4', plain,
% 8.38/8.59      (~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 8.38/8.59          (k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 8.38/8.59           (k1_tops_1 @ sk_A @ sk_C)))),
% 8.38/8.59      inference('demod', [status(thm)], ['0', '3'])).
% 8.38/8.59  thf('5', plain,
% 8.38/8.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.38/8.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.38/8.59  thf(dt_k1_tops_1, axiom,
% 8.38/8.59    (![A:$i,B:$i]:
% 8.38/8.59     ( ( ( l1_pre_topc @ A ) & 
% 8.38/8.59         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 8.38/8.59       ( m1_subset_1 @
% 8.38/8.59         ( k1_tops_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 8.38/8.59  thf('6', plain,
% 8.38/8.59      (![X30 : $i, X31 : $i]:
% 8.38/8.59         (~ (l1_pre_topc @ X30)
% 8.38/8.59          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X30)))
% 8.38/8.59          | (m1_subset_1 @ (k1_tops_1 @ X30 @ X31) @ 
% 8.38/8.59             (k1_zfmisc_1 @ (u1_struct_0 @ X30))))),
% 8.38/8.59      inference('cnf', [status(esa)], [dt_k1_tops_1])).
% 8.38/8.59  thf('7', plain,
% 8.38/8.59      (((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 8.38/8.59         (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.38/8.59        | ~ (l1_pre_topc @ sk_A))),
% 8.38/8.59      inference('sup-', [status(thm)], ['5', '6'])).
% 8.38/8.59  thf('8', plain, ((l1_pre_topc @ sk_A)),
% 8.38/8.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.38/8.59  thf('9', plain,
% 8.38/8.59      ((m1_subset_1 @ (k1_tops_1 @ sk_A @ sk_B) @ 
% 8.38/8.59        (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.38/8.59      inference('demod', [status(thm)], ['7', '8'])).
% 8.38/8.59  thf('10', plain,
% 8.38/8.59      (![X25 : $i, X26 : $i, X27 : $i]:
% 8.38/8.59         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 8.38/8.59          | ((k7_subset_1 @ X26 @ X25 @ X27) = (k4_xboole_0 @ X25 @ X27)))),
% 8.38/8.59      inference('cnf', [status(esa)], [redefinition_k7_subset_1])).
% 8.38/8.59  thf('11', plain,
% 8.38/8.59      (![X0 : $i]:
% 8.38/8.59         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ (k1_tops_1 @ sk_A @ sk_B) @ X0)
% 8.38/8.59           = (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ X0))),
% 8.38/8.59      inference('sup-', [status(thm)], ['9', '10'])).
% 8.38/8.59  thf('12', plain,
% 8.38/8.59      (~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 8.38/8.59          (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 8.38/8.59      inference('demod', [status(thm)], ['4', '11'])).
% 8.38/8.59  thf('13', plain,
% 8.38/8.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.38/8.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.38/8.59  thf('14', plain,
% 8.38/8.59      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.38/8.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.38/8.59  thf(dt_k7_subset_1, axiom,
% 8.38/8.59    (![A:$i,B:$i,C:$i]:
% 8.38/8.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 8.38/8.59       ( m1_subset_1 @ ( k7_subset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 8.38/8.59  thf('15', plain,
% 8.38/8.59      (![X22 : $i, X23 : $i, X24 : $i]:
% 8.38/8.59         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ X23))
% 8.38/8.59          | (m1_subset_1 @ (k7_subset_1 @ X23 @ X22 @ X24) @ 
% 8.38/8.59             (k1_zfmisc_1 @ X23)))),
% 8.38/8.59      inference('cnf', [status(esa)], [dt_k7_subset_1])).
% 8.38/8.59  thf('16', plain,
% 8.38/8.59      (![X0 : $i]:
% 8.38/8.59         (m1_subset_1 @ (k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0) @ 
% 8.38/8.59          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.38/8.59      inference('sup-', [status(thm)], ['14', '15'])).
% 8.38/8.59  thf('17', plain,
% 8.38/8.59      (![X0 : $i]:
% 8.38/8.59         ((k7_subset_1 @ (u1_struct_0 @ sk_A) @ sk_B @ X0)
% 8.38/8.59           = (k4_xboole_0 @ sk_B @ X0))),
% 8.38/8.59      inference('sup-', [status(thm)], ['1', '2'])).
% 8.38/8.59  thf('18', plain,
% 8.38/8.59      (![X0 : $i]:
% 8.38/8.59         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 8.38/8.59          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.38/8.59      inference('demod', [status(thm)], ['16', '17'])).
% 8.38/8.59  thf(t48_tops_1, axiom,
% 8.38/8.59    (![A:$i]:
% 8.38/8.59     ( ( l1_pre_topc @ A ) =>
% 8.38/8.59       ( ![B:$i]:
% 8.38/8.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.38/8.59           ( ![C:$i]:
% 8.38/8.59             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.38/8.59               ( ( r1_tarski @ B @ C ) =>
% 8.38/8.59                 ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ ( k1_tops_1 @ A @ C ) ) ) ) ) ) ) ))).
% 8.38/8.59  thf('19', plain,
% 8.38/8.59      (![X34 : $i, X35 : $i, X36 : $i]:
% 8.38/8.59         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 8.38/8.59          | ~ (r1_tarski @ X34 @ X36)
% 8.38/8.59          | (r1_tarski @ (k1_tops_1 @ X35 @ X34) @ (k1_tops_1 @ X35 @ X36))
% 8.38/8.59          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X35)))
% 8.38/8.59          | ~ (l1_pre_topc @ X35))),
% 8.38/8.59      inference('cnf', [status(esa)], [t48_tops_1])).
% 8.38/8.59  thf('20', plain,
% 8.38/8.59      (![X0 : $i, X1 : $i]:
% 8.38/8.59         (~ (l1_pre_topc @ sk_A)
% 8.38/8.59          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.38/8.59          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 8.38/8.59             (k1_tops_1 @ sk_A @ X1))
% 8.38/8.59          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 8.38/8.59      inference('sup-', [status(thm)], ['18', '19'])).
% 8.38/8.59  thf('21', plain, ((l1_pre_topc @ sk_A)),
% 8.38/8.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.38/8.59  thf('22', plain,
% 8.38/8.59      (![X0 : $i, X1 : $i]:
% 8.38/8.59         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))
% 8.38/8.59          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 8.38/8.59             (k1_tops_1 @ sk_A @ X1))
% 8.38/8.59          | ~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 8.38/8.59      inference('demod', [status(thm)], ['20', '21'])).
% 8.38/8.59  thf('23', plain,
% 8.38/8.59      (![X0 : $i]:
% 8.38/8.59         (~ (r1_tarski @ (k4_xboole_0 @ sk_B @ X0) @ sk_B)
% 8.38/8.59          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 8.38/8.59             (k1_tops_1 @ sk_A @ sk_B)))),
% 8.38/8.59      inference('sup-', [status(thm)], ['13', '22'])).
% 8.38/8.59  thf(d10_xboole_0, axiom,
% 8.38/8.59    (![A:$i,B:$i]:
% 8.38/8.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 8.38/8.59  thf('24', plain,
% 8.38/8.59      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 8.38/8.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 8.38/8.59  thf('25', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 8.38/8.59      inference('simplify', [status(thm)], ['24'])).
% 8.38/8.59  thf(t109_xboole_1, axiom,
% 8.38/8.59    (![A:$i,B:$i,C:$i]:
% 8.38/8.59     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 8.38/8.59  thf('26', plain,
% 8.38/8.59      (![X5 : $i, X6 : $i, X7 : $i]:
% 8.38/8.59         (~ (r1_tarski @ X5 @ X6) | (r1_tarski @ (k4_xboole_0 @ X5 @ X7) @ X6))),
% 8.38/8.59      inference('cnf', [status(esa)], [t109_xboole_1])).
% 8.38/8.59  thf('27', plain,
% 8.38/8.59      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X0)),
% 8.38/8.59      inference('sup-', [status(thm)], ['25', '26'])).
% 8.38/8.59  thf('28', plain,
% 8.38/8.59      (![X0 : $i]:
% 8.38/8.59         (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 8.38/8.59          (k1_tops_1 @ sk_A @ sk_B))),
% 8.38/8.59      inference('demod', [status(thm)], ['23', '27'])).
% 8.38/8.59  thf('29', plain,
% 8.38/8.59      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.38/8.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.38/8.59  thf(t44_tops_1, axiom,
% 8.38/8.59    (![A:$i]:
% 8.38/8.59     ( ( l1_pre_topc @ A ) =>
% 8.38/8.59       ( ![B:$i]:
% 8.38/8.59         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 8.38/8.59           ( r1_tarski @ ( k1_tops_1 @ A @ B ) @ B ) ) ) ))).
% 8.38/8.59  thf('30', plain,
% 8.38/8.59      (![X32 : $i, X33 : $i]:
% 8.38/8.59         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 8.38/8.59          | (r1_tarski @ (k1_tops_1 @ X33 @ X32) @ X32)
% 8.38/8.59          | ~ (l1_pre_topc @ X33))),
% 8.38/8.59      inference('cnf', [status(esa)], [t44_tops_1])).
% 8.38/8.59  thf('31', plain,
% 8.38/8.59      ((~ (l1_pre_topc @ sk_A) | (r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C))),
% 8.38/8.59      inference('sup-', [status(thm)], ['29', '30'])).
% 8.38/8.59  thf('32', plain, ((l1_pre_topc @ sk_A)),
% 8.38/8.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.38/8.59  thf('33', plain, ((r1_tarski @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C)),
% 8.38/8.59      inference('demod', [status(thm)], ['31', '32'])).
% 8.38/8.59  thf(t12_xboole_1, axiom,
% 8.38/8.59    (![A:$i,B:$i]:
% 8.38/8.59     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 8.38/8.59  thf('34', plain,
% 8.38/8.59      (![X8 : $i, X9 : $i]:
% 8.38/8.59         (((k2_xboole_0 @ X9 @ X8) = (X8)) | ~ (r1_tarski @ X9 @ X8))),
% 8.38/8.59      inference('cnf', [status(esa)], [t12_xboole_1])).
% 8.38/8.59  thf('35', plain,
% 8.38/8.59      (((k2_xboole_0 @ (k1_tops_1 @ sk_A @ sk_C) @ sk_C) = (sk_C))),
% 8.38/8.59      inference('sup-', [status(thm)], ['33', '34'])).
% 8.38/8.59  thf(t79_xboole_1, axiom,
% 8.38/8.59    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 8.38/8.59  thf('36', plain,
% 8.38/8.59      (![X17 : $i, X18 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X17 @ X18) @ X18)),
% 8.38/8.59      inference('cnf', [status(esa)], [t79_xboole_1])).
% 8.38/8.59  thf(t70_xboole_1, axiom,
% 8.38/8.59    (![A:$i,B:$i,C:$i]:
% 8.38/8.59     ( ( ~( ( ~( ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) & 
% 8.38/8.59            ( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) ) & 
% 8.38/8.59       ( ~( ( ~( r1_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) & 
% 8.38/8.59            ( r1_xboole_0 @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) ) ))).
% 8.38/8.59  thf('37', plain,
% 8.38/8.59      (![X13 : $i, X14 : $i, X16 : $i]:
% 8.38/8.59         ((r1_xboole_0 @ X13 @ X14)
% 8.38/8.59          | ~ (r1_xboole_0 @ X13 @ (k2_xboole_0 @ X14 @ X16)))),
% 8.38/8.59      inference('cnf', [status(esa)], [t70_xboole_1])).
% 8.38/8.59  thf('38', plain,
% 8.38/8.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.38/8.59         (r1_xboole_0 @ (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)) @ X1)),
% 8.38/8.59      inference('sup-', [status(thm)], ['36', '37'])).
% 8.38/8.59  thf('39', plain,
% 8.38/8.59      (![X0 : $i]:
% 8.38/8.59         (r1_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C) @ (k1_tops_1 @ sk_A @ sk_C))),
% 8.38/8.59      inference('sup+', [status(thm)], ['35', '38'])).
% 8.38/8.59  thf('40', plain,
% 8.38/8.59      (![X0 : $i]:
% 8.38/8.59         (m1_subset_1 @ (k4_xboole_0 @ sk_B @ X0) @ 
% 8.38/8.59          (k1_zfmisc_1 @ (u1_struct_0 @ sk_A)))),
% 8.38/8.59      inference('demod', [status(thm)], ['16', '17'])).
% 8.38/8.59  thf('41', plain,
% 8.38/8.59      (![X32 : $i, X33 : $i]:
% 8.38/8.59         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (u1_struct_0 @ X33)))
% 8.38/8.59          | (r1_tarski @ (k1_tops_1 @ X33 @ X32) @ X32)
% 8.38/8.59          | ~ (l1_pre_topc @ X33))),
% 8.38/8.59      inference('cnf', [status(esa)], [t44_tops_1])).
% 8.38/8.59  thf('42', plain,
% 8.38/8.59      (![X0 : $i]:
% 8.38/8.59         (~ (l1_pre_topc @ sk_A)
% 8.38/8.59          | (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 8.38/8.59             (k4_xboole_0 @ sk_B @ X0)))),
% 8.38/8.59      inference('sup-', [status(thm)], ['40', '41'])).
% 8.38/8.59  thf('43', plain, ((l1_pre_topc @ sk_A)),
% 8.38/8.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.38/8.59  thf('44', plain,
% 8.38/8.59      (![X0 : $i]:
% 8.38/8.59         (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ 
% 8.38/8.59          (k4_xboole_0 @ sk_B @ X0))),
% 8.38/8.59      inference('demod', [status(thm)], ['42', '43'])).
% 8.38/8.59  thf(t63_xboole_1, axiom,
% 8.38/8.59    (![A:$i,B:$i,C:$i]:
% 8.38/8.59     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 8.38/8.59       ( r1_xboole_0 @ A @ C ) ))).
% 8.38/8.59  thf('45', plain,
% 8.38/8.59      (![X10 : $i, X11 : $i, X12 : $i]:
% 8.38/8.59         (~ (r1_tarski @ X10 @ X11)
% 8.38/8.59          | ~ (r1_xboole_0 @ X11 @ X12)
% 8.38/8.59          | (r1_xboole_0 @ X10 @ X12))),
% 8.38/8.59      inference('cnf', [status(esa)], [t63_xboole_1])).
% 8.38/8.59  thf('46', plain,
% 8.38/8.59      (![X0 : $i, X1 : $i]:
% 8.38/8.59         ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ X0)) @ X1)
% 8.38/8.59          | ~ (r1_xboole_0 @ (k4_xboole_0 @ sk_B @ X0) @ X1))),
% 8.38/8.59      inference('sup-', [status(thm)], ['44', '45'])).
% 8.38/8.59  thf('47', plain,
% 8.38/8.59      ((r1_xboole_0 @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 8.38/8.59        (k1_tops_1 @ sk_A @ sk_C))),
% 8.38/8.59      inference('sup-', [status(thm)], ['39', '46'])).
% 8.38/8.59  thf(t86_xboole_1, axiom,
% 8.38/8.59    (![A:$i,B:$i,C:$i]:
% 8.38/8.59     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ A @ C ) ) =>
% 8.38/8.59       ( r1_tarski @ A @ ( k4_xboole_0 @ B @ C ) ) ))).
% 8.38/8.59  thf('48', plain,
% 8.38/8.59      (![X19 : $i, X20 : $i, X21 : $i]:
% 8.38/8.59         (~ (r1_tarski @ X19 @ X20)
% 8.38/8.59          | ~ (r1_xboole_0 @ X19 @ X21)
% 8.38/8.59          | (r1_tarski @ X19 @ (k4_xboole_0 @ X20 @ X21)))),
% 8.38/8.59      inference('cnf', [status(esa)], [t86_xboole_1])).
% 8.38/8.59  thf('49', plain,
% 8.38/8.59      (![X0 : $i]:
% 8.38/8.59         ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 8.38/8.59           (k4_xboole_0 @ X0 @ (k1_tops_1 @ sk_A @ sk_C)))
% 8.38/8.59          | ~ (r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 8.38/8.59               X0))),
% 8.38/8.59      inference('sup-', [status(thm)], ['47', '48'])).
% 8.38/8.59  thf('50', plain,
% 8.38/8.59      ((r1_tarski @ (k1_tops_1 @ sk_A @ (k4_xboole_0 @ sk_B @ sk_C)) @ 
% 8.38/8.59        (k4_xboole_0 @ (k1_tops_1 @ sk_A @ sk_B) @ (k1_tops_1 @ sk_A @ sk_C)))),
% 8.38/8.59      inference('sup-', [status(thm)], ['28', '49'])).
% 8.38/8.59  thf('51', plain, ($false), inference('demod', [status(thm)], ['12', '50'])).
% 8.38/8.59  
% 8.38/8.59  % SZS output end Refutation
% 8.38/8.59  
% 8.38/8.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
