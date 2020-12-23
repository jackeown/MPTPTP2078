%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3qLa5gxaol

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:41 EST 2020

% Result     : Theorem 0.51s
% Output     : Refutation 0.51s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 218 expanded)
%              Number of leaves         :   29 (  80 expanded)
%              Depth                    :   19
%              Number of atoms          :  712 (1625 expanded)
%              Number of equality atoms :   22 (  47 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(t27_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_struct_0 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X23 ) @ ( k1_struct_0 @ X23 ) ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t27_pre_topc])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X8 ) @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('3',plain,(
    ! [X7: $i] :
      ( ( k2_subset_1 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('4',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ~ ( v1_xboole_0 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(t35_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( r1_tarski @ X9 @ ( k3_subset_1 @ X10 @ X11 ) )
      | ~ ( r1_tarski @ X11 @ ( k3_subset_1 @ X10 @ X9 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t35_subset_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k3_subset_1 @ X0 @ X0 ) )
      | ( r1_tarski @ X0 @ ( k3_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( r1_tarski @ X0 @ ( k3_subset_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X1 @ ( k3_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k3_subset_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(clc,[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_struct_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','15'])).

thf(fc3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ) )).

thf('17',plain,(
    ! [X22: $i] :
      ( ( v1_xboole_0 @ ( k1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc3_struct_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('20',plain,(
    ! [X20: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('21',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( r1_tarski @ X24 @ ( k2_pre_topc @ X25 @ X24 ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('23',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ X1 @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_struct_0 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k2_struct_0 @ X0 ) ) @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','26'])).

thf('28',plain,(
    ! [X20: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('29',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r2_hidden @ X1 @ ( u1_struct_0 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k2_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ ( k2_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( r1_tarski @ ( k2_struct_0 @ X0 ) @ X1 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('42',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','43'])).

thf('45',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('48',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('49',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( r1_tarski @ X24 @ ( k2_pre_topc @ X25 @ X24 ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('54',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['52','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['47','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf(t27_tops_1,conjecture,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( l1_pre_topc @ A )
       => ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) )
          = ( k2_struct_0 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t27_tops_1])).

thf('61',plain,(
    ( k2_pre_topc @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ( u1_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['46','64'])).

thf('66',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ( k2_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    $false ),
    inference(simplify,[status(thm)],['67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3qLa5gxaol
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:39:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.51/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.51/0.70  % Solved by: fo/fo7.sh
% 0.51/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.51/0.70  % done 312 iterations in 0.236s
% 0.51/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.51/0.70  % SZS output start Refutation
% 0.51/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.51/0.70  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.51/0.70  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.51/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.51/0.70  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.51/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.51/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.51/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.51/0.70  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.51/0.70  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.51/0.70  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.51/0.70  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.51/0.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.51/0.70  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.51/0.70  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.51/0.70  thf(t27_pre_topc, axiom,
% 0.51/0.70    (![A:$i]:
% 0.51/0.70     ( ( l1_struct_0 @ A ) =>
% 0.51/0.70       ( ( k2_struct_0 @ A ) =
% 0.51/0.70         ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_struct_0 @ A ) ) ) ))).
% 0.51/0.70  thf('0', plain,
% 0.51/0.70      (![X23 : $i]:
% 0.51/0.70         (((k2_struct_0 @ X23)
% 0.51/0.70            = (k3_subset_1 @ (u1_struct_0 @ X23) @ (k1_struct_0 @ X23)))
% 0.51/0.70          | ~ (l1_struct_0 @ X23))),
% 0.51/0.70      inference('cnf', [status(esa)], [t27_pre_topc])).
% 0.51/0.70  thf(d3_tarski, axiom,
% 0.51/0.70    (![A:$i,B:$i]:
% 0.51/0.70     ( ( r1_tarski @ A @ B ) <=>
% 0.51/0.70       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.51/0.70  thf('1', plain,
% 0.51/0.70      (![X1 : $i, X3 : $i]:
% 0.51/0.70         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.51/0.70      inference('cnf', [status(esa)], [d3_tarski])).
% 0.51/0.70  thf(dt_k2_subset_1, axiom,
% 0.51/0.70    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.51/0.70  thf('2', plain,
% 0.51/0.70      (![X8 : $i]: (m1_subset_1 @ (k2_subset_1 @ X8) @ (k1_zfmisc_1 @ X8))),
% 0.51/0.70      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.51/0.70  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.51/0.70  thf('3', plain, (![X7 : $i]: ((k2_subset_1 @ X7) = (X7))),
% 0.51/0.70      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.51/0.70  thf('4', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.51/0.70      inference('demod', [status(thm)], ['2', '3'])).
% 0.51/0.70  thf(t5_subset, axiom,
% 0.51/0.70    (![A:$i,B:$i,C:$i]:
% 0.51/0.70     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.51/0.70          ( v1_xboole_0 @ C ) ) ))).
% 0.51/0.70  thf('5', plain,
% 0.51/0.70      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.51/0.70         (~ (r2_hidden @ X15 @ X16)
% 0.51/0.70          | ~ (v1_xboole_0 @ X17)
% 0.51/0.70          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 0.51/0.70      inference('cnf', [status(esa)], [t5_subset])).
% 0.51/0.70  thf('6', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.51/0.70      inference('sup-', [status(thm)], ['4', '5'])).
% 0.51/0.70  thf('7', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.51/0.70      inference('sup-', [status(thm)], ['1', '6'])).
% 0.51/0.70  thf(t3_subset, axiom,
% 0.51/0.70    (![A:$i,B:$i]:
% 0.51/0.70     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.51/0.70  thf('8', plain,
% 0.51/0.70      (![X12 : $i, X14 : $i]:
% 0.51/0.70         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.51/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.51/0.70  thf('9', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]:
% 0.51/0.70         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['7', '8'])).
% 0.51/0.70  thf('10', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.51/0.70      inference('demod', [status(thm)], ['2', '3'])).
% 0.51/0.70  thf(t35_subset_1, axiom,
% 0.51/0.70    (![A:$i,B:$i]:
% 0.51/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.51/0.70       ( ![C:$i]:
% 0.51/0.70         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.51/0.70           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.51/0.70             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.51/0.70  thf('11', plain,
% 0.51/0.70      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.51/0.70         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.51/0.70          | (r1_tarski @ X9 @ (k3_subset_1 @ X10 @ X11))
% 0.51/0.70          | ~ (r1_tarski @ X11 @ (k3_subset_1 @ X10 @ X9))
% 0.51/0.70          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.51/0.70      inference('cnf', [status(esa)], [t35_subset_1])).
% 0.51/0.70  thf('12', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]:
% 0.51/0.70         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.51/0.70          | ~ (r1_tarski @ X1 @ (k3_subset_1 @ X0 @ X0))
% 0.51/0.70          | (r1_tarski @ X0 @ (k3_subset_1 @ X0 @ X1)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['10', '11'])).
% 0.51/0.70  thf('13', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]:
% 0.51/0.70         (~ (v1_xboole_0 @ X1)
% 0.51/0.70          | (r1_tarski @ X0 @ (k3_subset_1 @ X0 @ X1))
% 0.51/0.70          | ~ (r1_tarski @ X1 @ (k3_subset_1 @ X0 @ X0)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['9', '12'])).
% 0.51/0.70  thf('14', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.51/0.70      inference('sup-', [status(thm)], ['1', '6'])).
% 0.51/0.70  thf('15', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]:
% 0.51/0.70         ((r1_tarski @ X0 @ (k3_subset_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X1))),
% 0.51/0.70      inference('clc', [status(thm)], ['13', '14'])).
% 0.51/0.70  thf('16', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         ((r1_tarski @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 0.51/0.70          | ~ (l1_struct_0 @ X0)
% 0.51/0.70          | ~ (v1_xboole_0 @ (k1_struct_0 @ X0)))),
% 0.51/0.70      inference('sup+', [status(thm)], ['0', '15'])).
% 0.51/0.70  thf(fc3_struct_0, axiom,
% 0.51/0.70    (![A:$i]: ( ( l1_struct_0 @ A ) => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ))).
% 0.51/0.70  thf('17', plain,
% 0.51/0.70      (![X22 : $i]:
% 0.51/0.70         ((v1_xboole_0 @ (k1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.51/0.70      inference('cnf', [status(esa)], [fc3_struct_0])).
% 0.51/0.70  thf('18', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (l1_struct_0 @ X0)
% 0.51/0.70          | (r1_tarski @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0)))),
% 0.51/0.70      inference('clc', [status(thm)], ['16', '17'])).
% 0.51/0.70  thf('19', plain,
% 0.51/0.70      (![X1 : $i, X3 : $i]:
% 0.51/0.70         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.51/0.70      inference('cnf', [status(esa)], [d3_tarski])).
% 0.51/0.70  thf(dt_k2_struct_0, axiom,
% 0.51/0.70    (![A:$i]:
% 0.51/0.70     ( ( l1_struct_0 @ A ) =>
% 0.51/0.70       ( m1_subset_1 @
% 0.51/0.70         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.51/0.70  thf('20', plain,
% 0.51/0.70      (![X20 : $i]:
% 0.51/0.70         ((m1_subset_1 @ (k2_struct_0 @ X20) @ 
% 0.51/0.70           (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.51/0.70          | ~ (l1_struct_0 @ X20))),
% 0.51/0.70      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.51/0.70  thf(t48_pre_topc, axiom,
% 0.51/0.70    (![A:$i]:
% 0.51/0.70     ( ( l1_pre_topc @ A ) =>
% 0.51/0.70       ( ![B:$i]:
% 0.51/0.70         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.51/0.70           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.51/0.70  thf('21', plain,
% 0.51/0.70      (![X24 : $i, X25 : $i]:
% 0.51/0.70         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.51/0.70          | (r1_tarski @ X24 @ (k2_pre_topc @ X25 @ X24))
% 0.51/0.70          | ~ (l1_pre_topc @ X25))),
% 0.51/0.70      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.51/0.70  thf('22', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (l1_struct_0 @ X0)
% 0.51/0.70          | ~ (l1_pre_topc @ X0)
% 0.51/0.70          | (r1_tarski @ (k2_struct_0 @ X0) @ 
% 0.51/0.70             (k2_pre_topc @ X0 @ (k2_struct_0 @ X0))))),
% 0.51/0.70      inference('sup-', [status(thm)], ['20', '21'])).
% 0.51/0.70  thf(dt_l1_pre_topc, axiom,
% 0.51/0.70    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.51/0.70  thf('23', plain,
% 0.51/0.70      (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.51/0.70      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.51/0.70  thf('24', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         ((r1_tarski @ (k2_struct_0 @ X0) @ 
% 0.51/0.70           (k2_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 0.51/0.70          | ~ (l1_pre_topc @ X0))),
% 0.51/0.70      inference('clc', [status(thm)], ['22', '23'])).
% 0.51/0.70  thf('25', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.70         (~ (r2_hidden @ X0 @ X1)
% 0.51/0.70          | (r2_hidden @ X0 @ X2)
% 0.51/0.70          | ~ (r1_tarski @ X1 @ X2))),
% 0.51/0.70      inference('cnf', [status(esa)], [d3_tarski])).
% 0.51/0.70  thf('26', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]:
% 0.51/0.70         (~ (l1_pre_topc @ X0)
% 0.51/0.70          | (r2_hidden @ X1 @ (k2_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 0.51/0.70          | ~ (r2_hidden @ X1 @ (k2_struct_0 @ X0)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['24', '25'])).
% 0.51/0.70  thf('27', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]:
% 0.51/0.70         ((r1_tarski @ (k2_struct_0 @ X0) @ X1)
% 0.51/0.70          | (r2_hidden @ (sk_C @ X1 @ (k2_struct_0 @ X0)) @ 
% 0.51/0.70             (k2_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 0.51/0.70          | ~ (l1_pre_topc @ X0))),
% 0.51/0.70      inference('sup-', [status(thm)], ['19', '26'])).
% 0.51/0.70  thf('28', plain,
% 0.51/0.70      (![X20 : $i]:
% 0.51/0.70         ((m1_subset_1 @ (k2_struct_0 @ X20) @ 
% 0.51/0.70           (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.51/0.70          | ~ (l1_struct_0 @ X20))),
% 0.51/0.70      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.51/0.70  thf(dt_k2_pre_topc, axiom,
% 0.51/0.70    (![A:$i,B:$i]:
% 0.51/0.70     ( ( ( l1_pre_topc @ A ) & 
% 0.51/0.70         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.51/0.70       ( m1_subset_1 @
% 0.51/0.70         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.51/0.70  thf('29', plain,
% 0.51/0.70      (![X18 : $i, X19 : $i]:
% 0.51/0.70         (~ (l1_pre_topc @ X18)
% 0.51/0.70          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.51/0.70          | (m1_subset_1 @ (k2_pre_topc @ X18 @ X19) @ 
% 0.51/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ X18))))),
% 0.51/0.70      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.51/0.70  thf('30', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (l1_struct_0 @ X0)
% 0.51/0.70          | (m1_subset_1 @ (k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ 
% 0.51/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.51/0.70          | ~ (l1_pre_topc @ X0))),
% 0.51/0.70      inference('sup-', [status(thm)], ['28', '29'])).
% 0.51/0.70  thf('31', plain,
% 0.51/0.70      (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.51/0.70      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.51/0.70  thf('32', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (l1_pre_topc @ X0)
% 0.51/0.70          | (m1_subset_1 @ (k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ 
% 0.51/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.51/0.70      inference('clc', [status(thm)], ['30', '31'])).
% 0.51/0.70  thf('33', plain,
% 0.51/0.70      (![X12 : $i, X13 : $i]:
% 0.51/0.70         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.51/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.51/0.70  thf('34', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (l1_pre_topc @ X0)
% 0.51/0.70          | (r1_tarski @ (k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ 
% 0.51/0.70             (u1_struct_0 @ X0)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['32', '33'])).
% 0.51/0.70  thf('35', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.51/0.70         (~ (r2_hidden @ X0 @ X1)
% 0.51/0.70          | (r2_hidden @ X0 @ X2)
% 0.51/0.70          | ~ (r1_tarski @ X1 @ X2))),
% 0.51/0.70      inference('cnf', [status(esa)], [d3_tarski])).
% 0.51/0.70  thf('36', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]:
% 0.51/0.70         (~ (l1_pre_topc @ X0)
% 0.51/0.70          | (r2_hidden @ X1 @ (u1_struct_0 @ X0))
% 0.51/0.70          | ~ (r2_hidden @ X1 @ (k2_pre_topc @ X0 @ (k2_struct_0 @ X0))))),
% 0.51/0.70      inference('sup-', [status(thm)], ['34', '35'])).
% 0.51/0.70  thf('37', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]:
% 0.51/0.70         (~ (l1_pre_topc @ X0)
% 0.51/0.70          | (r1_tarski @ (k2_struct_0 @ X0) @ X1)
% 0.51/0.70          | (r2_hidden @ (sk_C @ X1 @ (k2_struct_0 @ X0)) @ (u1_struct_0 @ X0))
% 0.51/0.70          | ~ (l1_pre_topc @ X0))),
% 0.51/0.70      inference('sup-', [status(thm)], ['27', '36'])).
% 0.51/0.70  thf('38', plain,
% 0.51/0.70      (![X0 : $i, X1 : $i]:
% 0.51/0.70         ((r2_hidden @ (sk_C @ X1 @ (k2_struct_0 @ X0)) @ (u1_struct_0 @ X0))
% 0.51/0.70          | (r1_tarski @ (k2_struct_0 @ X0) @ X1)
% 0.51/0.70          | ~ (l1_pre_topc @ X0))),
% 0.51/0.70      inference('simplify', [status(thm)], ['37'])).
% 0.51/0.70  thf('39', plain,
% 0.51/0.70      (![X1 : $i, X3 : $i]:
% 0.51/0.70         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.51/0.70      inference('cnf', [status(esa)], [d3_tarski])).
% 0.51/0.70  thf('40', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (l1_pre_topc @ X0)
% 0.51/0.70          | (r1_tarski @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X0))
% 0.51/0.70          | (r1_tarski @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X0)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['38', '39'])).
% 0.51/0.70  thf('41', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         ((r1_tarski @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X0))
% 0.51/0.70          | ~ (l1_pre_topc @ X0))),
% 0.51/0.70      inference('simplify', [status(thm)], ['40'])).
% 0.51/0.70  thf(d10_xboole_0, axiom,
% 0.51/0.70    (![A:$i,B:$i]:
% 0.51/0.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.51/0.70  thf('42', plain,
% 0.51/0.70      (![X4 : $i, X6 : $i]:
% 0.51/0.70         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.51/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.51/0.70  thf('43', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (l1_pre_topc @ X0)
% 0.51/0.70          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 0.51/0.70          | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['41', '42'])).
% 0.51/0.70  thf('44', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (l1_struct_0 @ X0)
% 0.51/0.70          | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0))
% 0.51/0.70          | ~ (l1_pre_topc @ X0))),
% 0.51/0.70      inference('sup-', [status(thm)], ['18', '43'])).
% 0.51/0.70  thf('45', plain,
% 0.51/0.70      (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.51/0.70      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.51/0.70  thf('46', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (l1_pre_topc @ X0) | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 0.51/0.70      inference('clc', [status(thm)], ['44', '45'])).
% 0.51/0.70  thf('47', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (l1_pre_topc @ X0) | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 0.51/0.70      inference('clc', [status(thm)], ['44', '45'])).
% 0.51/0.70  thf('48', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.51/0.70      inference('demod', [status(thm)], ['2', '3'])).
% 0.51/0.70  thf('49', plain,
% 0.51/0.70      (![X24 : $i, X25 : $i]:
% 0.51/0.70         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.51/0.70          | (r1_tarski @ X24 @ (k2_pre_topc @ X25 @ X24))
% 0.51/0.70          | ~ (l1_pre_topc @ X25))),
% 0.51/0.70      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.51/0.70  thf('50', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (l1_pre_topc @ X0)
% 0.51/0.70          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.51/0.70             (k2_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 0.51/0.70      inference('sup-', [status(thm)], ['48', '49'])).
% 0.51/0.70  thf('51', plain,
% 0.51/0.70      (![X4 : $i, X6 : $i]:
% 0.51/0.70         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.51/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.51/0.70  thf('52', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (l1_pre_topc @ X0)
% 0.51/0.70          | ~ (r1_tarski @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 0.51/0.70               (u1_struct_0 @ X0))
% 0.51/0.70          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['50', '51'])).
% 0.51/0.70  thf('53', plain, (![X8 : $i]: (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X8))),
% 0.51/0.70      inference('demod', [status(thm)], ['2', '3'])).
% 0.51/0.70  thf('54', plain,
% 0.51/0.70      (![X18 : $i, X19 : $i]:
% 0.51/0.70         (~ (l1_pre_topc @ X18)
% 0.51/0.70          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.51/0.70          | (m1_subset_1 @ (k2_pre_topc @ X18 @ X19) @ 
% 0.51/0.70             (k1_zfmisc_1 @ (u1_struct_0 @ X18))))),
% 0.51/0.70      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.51/0.70  thf('55', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         ((m1_subset_1 @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 0.51/0.70           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.51/0.70          | ~ (l1_pre_topc @ X0))),
% 0.51/0.70      inference('sup-', [status(thm)], ['53', '54'])).
% 0.51/0.70  thf('56', plain,
% 0.51/0.70      (![X12 : $i, X13 : $i]:
% 0.51/0.70         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.51/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.51/0.70  thf('57', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (l1_pre_topc @ X0)
% 0.51/0.70          | (r1_tarski @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 0.51/0.70             (u1_struct_0 @ X0)))),
% 0.51/0.70      inference('sup-', [status(thm)], ['55', '56'])).
% 0.51/0.70  thf('58', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.51/0.70          | ~ (l1_pre_topc @ X0))),
% 0.51/0.70      inference('clc', [status(thm)], ['52', '57'])).
% 0.51/0.70  thf('59', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.51/0.70          | ~ (l1_pre_topc @ X0)
% 0.51/0.70          | ~ (l1_pre_topc @ X0))),
% 0.51/0.70      inference('sup+', [status(thm)], ['47', '58'])).
% 0.51/0.70  thf('60', plain,
% 0.51/0.70      (![X0 : $i]:
% 0.51/0.70         (~ (l1_pre_topc @ X0)
% 0.51/0.70          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0)))),
% 0.51/0.70      inference('simplify', [status(thm)], ['59'])).
% 0.51/0.70  thf(t27_tops_1, conjecture,
% 0.51/0.70    (![A:$i]:
% 0.51/0.70     ( ( l1_pre_topc @ A ) =>
% 0.51/0.70       ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.51/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.51/0.70    (~( ![A:$i]:
% 0.51/0.70        ( ( l1_pre_topc @ A ) =>
% 0.51/0.70          ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ) )),
% 0.51/0.70    inference('cnf.neg', [status(esa)], [t27_tops_1])).
% 0.51/0.70  thf('61', plain,
% 0.51/0.70      (((k2_pre_topc @ sk_A @ (k2_struct_0 @ sk_A)) != (k2_struct_0 @ sk_A))),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('62', plain,
% 0.51/0.70      ((((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)) | ~ (l1_pre_topc @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['60', '61'])).
% 0.51/0.70  thf('63', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('64', plain, (((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.51/0.70      inference('demod', [status(thm)], ['62', '63'])).
% 0.51/0.70  thf('65', plain,
% 0.51/0.70      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)) | ~ (l1_pre_topc @ sk_A))),
% 0.51/0.70      inference('sup-', [status(thm)], ['46', '64'])).
% 0.51/0.70  thf('66', plain, ((l1_pre_topc @ sk_A)),
% 0.51/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.51/0.70  thf('67', plain, (((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.51/0.70      inference('demod', [status(thm)], ['65', '66'])).
% 0.51/0.70  thf('68', plain, ($false), inference('simplify', [status(thm)], ['67'])).
% 0.51/0.70  
% 0.51/0.70  % SZS output end Refutation
% 0.51/0.70  
% 0.51/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
