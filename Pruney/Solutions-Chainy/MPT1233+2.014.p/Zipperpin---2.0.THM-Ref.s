%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.loGMzn6lTt

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:51 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 161 expanded)
%              Number of leaves         :   45 (  66 expanded)
%              Depth                    :   25
%              Number of atoms          :  807 (1099 expanded)
%              Number of equality atoms :   61 (  84 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X45: $i] :
      ( ( ( k2_struct_0 @ X45 )
        = ( u1_struct_0 @ X45 ) )
      | ~ ( l1_struct_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X45: $i] :
      ( ( ( k2_struct_0 @ X45 )
        = ( u1_struct_0 @ X45 ) )
      | ~ ( l1_struct_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('3',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X44 ) ) )
      | ( v4_pre_topc @ X43 @ X44 )
      | ~ ( v1_xboole_0 @ X43 )
      | ~ ( l1_pre_topc @ X44 )
      | ~ ( v2_pre_topc @ X44 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('5',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

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

thf('8',plain,(
    ! [X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X49 ) ) )
      | ~ ( v4_pre_topc @ X48 @ X49 )
      | ( ( k2_pre_topc @ X49 @ X48 )
        = X48 )
      | ~ ( l1_pre_topc @ X49 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('12',plain,(
    ! [X17: $i] :
      ( r1_xboole_0 @ X17 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('13',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k4_xboole_0 @ X14 @ ( k4_xboole_0 @ X14 @ X15 ) )
      = ( k3_xboole_0 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('15',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X16 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('17',plain,(
    ! [X8: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k3_xboole_0 @ X8 @ X11 ) )
      | ~ ( r1_xboole_0 @ X8 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf(t88_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B )
        = A ) ) )).

thf('21',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X22 @ X23 ) @ X23 )
        = X22 )
      | ~ ( r1_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X17: $i] :
      ( r1_xboole_0 @ X17 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('24',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf(t72_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( ( k2_xboole_0 @ A @ B )
          = ( k2_xboole_0 @ C @ D ) )
        & ( r1_xboole_0 @ C @ A )
        & ( r1_xboole_0 @ D @ B ) )
     => ( C = B ) ) )).

thf('25',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X19 = X18 )
      | ~ ( r1_xboole_0 @ X19 @ X20 )
      | ( ( k2_xboole_0 @ X20 @ X18 )
       != ( k2_xboole_0 @ X19 @ X21 ) )
      | ~ ( r1_xboole_0 @ X21 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t72_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_xboole_0 @ X2 @ X1 )
       != X0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_xboole_0 @ X2 @ X1 )
       != X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ( X0 = X1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_xboole_0 @ X2 @ X1 )
        = X1 )
      | ~ ( r1_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['23','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','30'])).

thf(t68_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B )
        = k1_xboole_0 )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('32',plain,(
    ! [X24: $i,X25: $i] :
      ( ( r2_hidden @ X24 @ X25 )
      | ( ( k4_xboole_0 @ ( k1_tarski @ X24 ) @ X25 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t68_zfmisc_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf(t80_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('35',plain,(
    ! [X27: $i] :
      ( r1_tarski @ ( k1_tarski @ X27 ) @ ( k1_zfmisc_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t80_zfmisc_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('39',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ( m1_subset_1 @ X28 @ X29 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('41',plain,(
    ! [X33: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('43',plain,(
    ! [X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X51 ) ) )
      | ( ( k1_tops_1 @ X51 @ X50 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X51 ) @ ( k2_pre_topc @ X51 @ ( k3_subset_1 @ ( u1_struct_0 @ X51 ) @ X50 ) ) ) )
      | ~ ( l1_pre_topc @ X51 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('46',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k3_subset_1 @ X35 @ ( k3_subset_1 @ X35 @ X34 ) )
        = X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X39: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('49',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k3_subset_1 @ X31 @ X32 )
        = ( k4_xboole_0 @ X31 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X17: $i] :
      ( r1_xboole_0 @ X17 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('52',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k4_xboole_0 @ ( k2_xboole_0 @ X22 @ X23 ) @ X23 )
        = X22 )
      | ~ ( r1_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t88_xboole_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X12: $i] :
      ( ( k2_xboole_0 @ X12 @ k1_xboole_0 )
      = X12 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['50','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['44','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['11','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['50','55'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k1_tops_1 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k1_tops_1 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_struct_0 @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf(t43_tops_1,conjecture,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) )
        = ( k2_struct_0 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v2_pre_topc @ A )
          & ( l1_pre_topc @ A ) )
       => ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) )
          = ( k2_struct_0 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t43_tops_1])).

thf('66',plain,(
    ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('69',plain,(
    ! [X46: $i] :
      ( ( l1_struct_0 @ X46 )
      | ~ ( l1_pre_topc @ X46 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('70',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ( k2_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','70','71','72'])).

thf('74',plain,(
    $false ),
    inference(simplify,[status(thm)],['73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.loGMzn6lTt
% 0.12/0.33  % Computer   : n016.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:10:04 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.45/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.68  % Solved by: fo/fo7.sh
% 0.45/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.68  % done 1022 iterations in 0.241s
% 0.45/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.68  % SZS output start Refutation
% 0.45/0.68  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.45/0.68  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.45/0.68  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.45/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.68  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.45/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.68  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.45/0.68  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.68  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.68  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.68  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.45/0.68  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.45/0.68  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.45/0.68  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.45/0.68  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.45/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.68  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.45/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.68  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.45/0.68  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.45/0.68  thf(d3_struct_0, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.45/0.68  thf('0', plain,
% 0.45/0.68      (![X45 : $i]:
% 0.45/0.68         (((k2_struct_0 @ X45) = (u1_struct_0 @ X45)) | ~ (l1_struct_0 @ X45))),
% 0.45/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.68  thf('1', plain,
% 0.45/0.68      (![X45 : $i]:
% 0.45/0.68         (((k2_struct_0 @ X45) = (u1_struct_0 @ X45)) | ~ (l1_struct_0 @ X45))),
% 0.45/0.68      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.45/0.68  thf(t4_subset_1, axiom,
% 0.45/0.68    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.45/0.68  thf('2', plain,
% 0.45/0.68      (![X39 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X39))),
% 0.45/0.68      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.45/0.68  thf(cc2_pre_topc, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.68           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.45/0.68  thf('3', plain,
% 0.45/0.68      (![X43 : $i, X44 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (u1_struct_0 @ X44)))
% 0.45/0.68          | (v4_pre_topc @ X43 @ X44)
% 0.45/0.68          | ~ (v1_xboole_0 @ X43)
% 0.45/0.68          | ~ (l1_pre_topc @ X44)
% 0.45/0.68          | ~ (v2_pre_topc @ X44))),
% 0.45/0.68      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.45/0.68  thf('4', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (v2_pre_topc @ X0)
% 0.45/0.68          | ~ (l1_pre_topc @ X0)
% 0.45/0.68          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.45/0.68          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.45/0.68      inference('sup-', [status(thm)], ['2', '3'])).
% 0.45/0.68  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.45/0.68  thf('5', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.68      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.45/0.68  thf('6', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (v2_pre_topc @ X0)
% 0.45/0.68          | ~ (l1_pre_topc @ X0)
% 0.45/0.68          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.45/0.68      inference('demod', [status(thm)], ['4', '5'])).
% 0.45/0.68  thf('7', plain,
% 0.45/0.68      (![X39 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X39))),
% 0.45/0.68      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.45/0.68  thf(t52_pre_topc, axiom,
% 0.45/0.68    (![A:$i]:
% 0.45/0.68     ( ( l1_pre_topc @ A ) =>
% 0.45/0.68       ( ![B:$i]:
% 0.45/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.68           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.45/0.68             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.45/0.68               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.45/0.68  thf('8', plain,
% 0.45/0.68      (![X48 : $i, X49 : $i]:
% 0.45/0.68         (~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (u1_struct_0 @ X49)))
% 0.45/0.68          | ~ (v4_pre_topc @ X48 @ X49)
% 0.45/0.68          | ((k2_pre_topc @ X49 @ X48) = (X48))
% 0.45/0.68          | ~ (l1_pre_topc @ X49))),
% 0.45/0.68      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.45/0.68  thf('9', plain,
% 0.45/0.68      (![X0 : $i]:
% 0.45/0.68         (~ (l1_pre_topc @ X0)
% 0.45/0.68          | ((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.45/0.69          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['7', '8'])).
% 0.45/0.69  thf('10', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (~ (l1_pre_topc @ X0)
% 0.45/0.69          | ~ (v2_pre_topc @ X0)
% 0.45/0.69          | ((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.45/0.69          | ~ (l1_pre_topc @ X0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['6', '9'])).
% 0.45/0.69  thf('11', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.45/0.69          | ~ (v2_pre_topc @ X0)
% 0.45/0.69          | ~ (l1_pre_topc @ X0))),
% 0.45/0.69      inference('simplify', [status(thm)], ['10'])).
% 0.45/0.69  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.45/0.69  thf('12', plain, (![X17 : $i]: (r1_xboole_0 @ X17 @ k1_xboole_0)),
% 0.45/0.69      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.45/0.69  thf(t3_xboole_0, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.45/0.69            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.69       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.45/0.69            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.45/0.69  thf('13', plain,
% 0.45/0.69      (![X4 : $i, X5 : $i]:
% 0.45/0.69         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X4))),
% 0.45/0.69      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.45/0.69  thf(t48_xboole_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.45/0.69  thf('14', plain,
% 0.45/0.69      (![X14 : $i, X15 : $i]:
% 0.45/0.69         ((k4_xboole_0 @ X14 @ (k4_xboole_0 @ X14 @ X15))
% 0.45/0.69           = (k3_xboole_0 @ X14 @ X15))),
% 0.45/0.69      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.45/0.69  thf(t4_boole, axiom,
% 0.45/0.69    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.45/0.69  thf('15', plain,
% 0.45/0.69      (![X16 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X16) = (k1_xboole_0))),
% 0.45/0.69      inference('cnf', [status(esa)], [t4_boole])).
% 0.45/0.69  thf('16', plain,
% 0.45/0.69      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.45/0.69      inference('sup+', [status(thm)], ['14', '15'])).
% 0.45/0.69  thf(t4_xboole_0, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.69            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.45/0.69       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.45/0.69            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.45/0.69  thf('17', plain,
% 0.45/0.69      (![X8 : $i, X10 : $i, X11 : $i]:
% 0.45/0.69         (~ (r2_hidden @ X10 @ (k3_xboole_0 @ X8 @ X11))
% 0.45/0.69          | ~ (r1_xboole_0 @ X8 @ X11))),
% 0.45/0.69      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.45/0.69  thf('18', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['16', '17'])).
% 0.45/0.69  thf('19', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((r1_xboole_0 @ k1_xboole_0 @ X0) | ~ (r1_xboole_0 @ k1_xboole_0 @ X1))),
% 0.45/0.69      inference('sup-', [status(thm)], ['13', '18'])).
% 0.45/0.69  thf('20', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.45/0.69      inference('sup-', [status(thm)], ['12', '19'])).
% 0.45/0.69  thf(t88_xboole_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( r1_xboole_0 @ A @ B ) =>
% 0.45/0.69       ( ( k4_xboole_0 @ ( k2_xboole_0 @ A @ B ) @ B ) = ( A ) ) ))).
% 0.45/0.69  thf('21', plain,
% 0.45/0.69      (![X22 : $i, X23 : $i]:
% 0.45/0.69         (((k4_xboole_0 @ (k2_xboole_0 @ X22 @ X23) @ X23) = (X22))
% 0.45/0.69          | ~ (r1_xboole_0 @ X22 @ X23))),
% 0.45/0.69      inference('cnf', [status(esa)], [t88_xboole_1])).
% 0.45/0.69  thf('22', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((k4_xboole_0 @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X0) = (k1_xboole_0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['20', '21'])).
% 0.45/0.69  thf('23', plain, (![X17 : $i]: (r1_xboole_0 @ X17 @ k1_xboole_0)),
% 0.45/0.69      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.45/0.69  thf(t1_boole, axiom,
% 0.45/0.69    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.45/0.69  thf('24', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.45/0.69      inference('cnf', [status(esa)], [t1_boole])).
% 0.45/0.69  thf(t72_xboole_1, axiom,
% 0.45/0.69    (![A:$i,B:$i,C:$i,D:$i]:
% 0.45/0.69     ( ( ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ C @ D ) ) & 
% 0.45/0.69         ( r1_xboole_0 @ C @ A ) & ( r1_xboole_0 @ D @ B ) ) =>
% 0.45/0.69       ( ( C ) = ( B ) ) ))).
% 0.45/0.69  thf('25', plain,
% 0.45/0.69      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.45/0.69         (((X19) = (X18))
% 0.45/0.69          | ~ (r1_xboole_0 @ X19 @ X20)
% 0.45/0.69          | ((k2_xboole_0 @ X20 @ X18) != (k2_xboole_0 @ X19 @ X21))
% 0.45/0.69          | ~ (r1_xboole_0 @ X21 @ X18))),
% 0.45/0.69      inference('cnf', [status(esa)], [t72_xboole_1])).
% 0.45/0.69  thf('26', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         (((k2_xboole_0 @ X2 @ X1) != (X0))
% 0.45/0.69          | ~ (r1_xboole_0 @ k1_xboole_0 @ X1)
% 0.45/0.69          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.45/0.69          | ((X0) = (X1)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.69  thf('27', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.45/0.69      inference('sup-', [status(thm)], ['12', '19'])).
% 0.45/0.69  thf('28', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         (((k2_xboole_0 @ X2 @ X1) != (X0))
% 0.45/0.69          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.45/0.69          | ((X0) = (X1)))),
% 0.45/0.69      inference('demod', [status(thm)], ['26', '27'])).
% 0.45/0.69  thf('29', plain,
% 0.45/0.69      (![X1 : $i, X2 : $i]:
% 0.45/0.69         (((k2_xboole_0 @ X2 @ X1) = (X1))
% 0.45/0.69          | ~ (r1_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X2))),
% 0.45/0.69      inference('simplify', [status(thm)], ['28'])).
% 0.45/0.69  thf('30', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['23', '29'])).
% 0.45/0.69  thf('31', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.69      inference('demod', [status(thm)], ['22', '30'])).
% 0.45/0.69  thf(t68_zfmisc_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( ( k4_xboole_0 @ ( k1_tarski @ A ) @ B ) = ( k1_xboole_0 ) ) <=>
% 0.45/0.69       ( r2_hidden @ A @ B ) ))).
% 0.45/0.69  thf('32', plain,
% 0.45/0.69      (![X24 : $i, X25 : $i]:
% 0.45/0.69         ((r2_hidden @ X24 @ X25)
% 0.45/0.69          | ((k4_xboole_0 @ (k1_tarski @ X24) @ X25) != (k1_xboole_0)))),
% 0.45/0.69      inference('cnf', [status(esa)], [t68_zfmisc_1])).
% 0.45/0.69  thf('33', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (((k1_xboole_0) != (k1_xboole_0))
% 0.45/0.69          | (r2_hidden @ X0 @ (k1_tarski @ X0)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['31', '32'])).
% 0.45/0.69  thf('34', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.45/0.69      inference('simplify', [status(thm)], ['33'])).
% 0.45/0.69  thf(t80_zfmisc_1, axiom,
% 0.45/0.69    (![A:$i]: ( r1_tarski @ ( k1_tarski @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.45/0.69  thf('35', plain,
% 0.45/0.69      (![X27 : $i]: (r1_tarski @ (k1_tarski @ X27) @ (k1_zfmisc_1 @ X27))),
% 0.45/0.69      inference('cnf', [status(esa)], [t80_zfmisc_1])).
% 0.45/0.69  thf(d3_tarski, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( r1_tarski @ A @ B ) <=>
% 0.45/0.69       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.45/0.69  thf('36', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.69         (~ (r2_hidden @ X0 @ X1)
% 0.45/0.69          | (r2_hidden @ X0 @ X2)
% 0.45/0.69          | ~ (r1_tarski @ X1 @ X2))),
% 0.45/0.69      inference('cnf', [status(esa)], [d3_tarski])).
% 0.45/0.69  thf('37', plain,
% 0.45/0.69      (![X0 : $i, X1 : $i]:
% 0.45/0.69         ((r2_hidden @ X1 @ (k1_zfmisc_1 @ X0))
% 0.45/0.69          | ~ (r2_hidden @ X1 @ (k1_tarski @ X0)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['35', '36'])).
% 0.45/0.69  thf('38', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['34', '37'])).
% 0.45/0.69  thf(d2_subset_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( ( v1_xboole_0 @ A ) =>
% 0.45/0.69         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.45/0.69       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.45/0.69         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.45/0.69  thf('39', plain,
% 0.45/0.69      (![X28 : $i, X29 : $i]:
% 0.45/0.69         (~ (r2_hidden @ X28 @ X29)
% 0.45/0.69          | (m1_subset_1 @ X28 @ X29)
% 0.45/0.69          | (v1_xboole_0 @ X29))),
% 0.45/0.69      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.45/0.69  thf('40', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 0.45/0.69          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 0.45/0.69      inference('sup-', [status(thm)], ['38', '39'])).
% 0.45/0.69  thf(fc1_subset_1, axiom,
% 0.45/0.69    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.45/0.69  thf('41', plain, (![X33 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X33))),
% 0.45/0.69      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.45/0.69  thf('42', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.45/0.69      inference('clc', [status(thm)], ['40', '41'])).
% 0.45/0.69  thf(d1_tops_1, axiom,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( l1_pre_topc @ A ) =>
% 0.45/0.69       ( ![B:$i]:
% 0.45/0.69         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.45/0.69           ( ( k1_tops_1 @ A @ B ) =
% 0.45/0.69             ( k3_subset_1 @
% 0.45/0.69               ( u1_struct_0 @ A ) @ 
% 0.45/0.69               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.45/0.69  thf('43', plain,
% 0.45/0.69      (![X50 : $i, X51 : $i]:
% 0.45/0.69         (~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (u1_struct_0 @ X51)))
% 0.45/0.69          | ((k1_tops_1 @ X51 @ X50)
% 0.45/0.69              = (k3_subset_1 @ (u1_struct_0 @ X51) @ 
% 0.45/0.69                 (k2_pre_topc @ X51 @ (k3_subset_1 @ (u1_struct_0 @ X51) @ X50))))
% 0.45/0.69          | ~ (l1_pre_topc @ X51))),
% 0.45/0.69      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.45/0.69  thf('44', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (~ (l1_pre_topc @ X0)
% 0.45/0.69          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.45/0.69              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.45/0.69                 (k2_pre_topc @ X0 @ 
% 0.45/0.69                  (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))))))),
% 0.45/0.69      inference('sup-', [status(thm)], ['42', '43'])).
% 0.45/0.69  thf('45', plain,
% 0.45/0.69      (![X39 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X39))),
% 0.45/0.69      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.45/0.69  thf(involutiveness_k3_subset_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.69       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.45/0.69  thf('46', plain,
% 0.45/0.69      (![X34 : $i, X35 : $i]:
% 0.45/0.69         (((k3_subset_1 @ X35 @ (k3_subset_1 @ X35 @ X34)) = (X34))
% 0.45/0.69          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35)))),
% 0.45/0.69      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.45/0.69  thf('47', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['45', '46'])).
% 0.45/0.69  thf('48', plain,
% 0.45/0.69      (![X39 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X39))),
% 0.45/0.69      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.45/0.69  thf(d5_subset_1, axiom,
% 0.45/0.69    (![A:$i,B:$i]:
% 0.45/0.69     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.45/0.69       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 0.45/0.69  thf('49', plain,
% 0.45/0.69      (![X31 : $i, X32 : $i]:
% 0.45/0.69         (((k3_subset_1 @ X31 @ X32) = (k4_xboole_0 @ X31 @ X32))
% 0.45/0.69          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X31)))),
% 0.45/0.69      inference('cnf', [status(esa)], [d5_subset_1])).
% 0.45/0.69  thf('50', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['48', '49'])).
% 0.45/0.69  thf('51', plain, (![X17 : $i]: (r1_xboole_0 @ X17 @ k1_xboole_0)),
% 0.45/0.69      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.45/0.69  thf('52', plain,
% 0.45/0.69      (![X22 : $i, X23 : $i]:
% 0.45/0.69         (((k4_xboole_0 @ (k2_xboole_0 @ X22 @ X23) @ X23) = (X22))
% 0.45/0.69          | ~ (r1_xboole_0 @ X22 @ X23))),
% 0.45/0.69      inference('cnf', [status(esa)], [t88_xboole_1])).
% 0.45/0.69  thf('53', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ k1_xboole_0) @ k1_xboole_0) = (X0))),
% 0.45/0.69      inference('sup-', [status(thm)], ['51', '52'])).
% 0.45/0.69  thf('54', plain, (![X12 : $i]: ((k2_xboole_0 @ X12 @ k1_xboole_0) = (X12))),
% 0.45/0.69      inference('cnf', [status(esa)], [t1_boole])).
% 0.45/0.69  thf('55', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.45/0.69      inference('demod', [status(thm)], ['53', '54'])).
% 0.45/0.69  thf('56', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.45/0.69      inference('demod', [status(thm)], ['50', '55'])).
% 0.45/0.69  thf('57', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.45/0.69      inference('demod', [status(thm)], ['47', '56'])).
% 0.45/0.69  thf('58', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (~ (l1_pre_topc @ X0)
% 0.45/0.69          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.45/0.69              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.45/0.69                 (k2_pre_topc @ X0 @ k1_xboole_0))))),
% 0.45/0.69      inference('demod', [status(thm)], ['44', '57'])).
% 0.45/0.69  thf('59', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.45/0.69            = (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0))
% 0.45/0.69          | ~ (l1_pre_topc @ X0)
% 0.45/0.69          | ~ (v2_pre_topc @ X0)
% 0.45/0.69          | ~ (l1_pre_topc @ X0))),
% 0.45/0.69      inference('sup+', [status(thm)], ['11', '58'])).
% 0.45/0.69  thf('60', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 0.45/0.69      inference('demod', [status(thm)], ['50', '55'])).
% 0.45/0.69  thf('61', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (((k1_tops_1 @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.45/0.69          | ~ (l1_pre_topc @ X0)
% 0.45/0.69          | ~ (v2_pre_topc @ X0)
% 0.45/0.69          | ~ (l1_pre_topc @ X0))),
% 0.45/0.69      inference('demod', [status(thm)], ['59', '60'])).
% 0.45/0.69  thf('62', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (~ (v2_pre_topc @ X0)
% 0.45/0.69          | ~ (l1_pre_topc @ X0)
% 0.45/0.69          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0)))),
% 0.45/0.69      inference('simplify', [status(thm)], ['61'])).
% 0.45/0.69  thf('63', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (((k1_tops_1 @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.45/0.69          | ~ (l1_struct_0 @ X0)
% 0.45/0.69          | ~ (l1_pre_topc @ X0)
% 0.45/0.69          | ~ (v2_pre_topc @ X0))),
% 0.45/0.69      inference('sup+', [status(thm)], ['1', '62'])).
% 0.45/0.69  thf('64', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (((k1_tops_1 @ X0 @ (k2_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.45/0.69          | ~ (l1_struct_0 @ X0)
% 0.45/0.69          | ~ (v2_pre_topc @ X0)
% 0.45/0.69          | ~ (l1_pre_topc @ X0)
% 0.45/0.69          | ~ (l1_struct_0 @ X0))),
% 0.45/0.69      inference('sup+', [status(thm)], ['0', '63'])).
% 0.45/0.69  thf('65', plain,
% 0.45/0.69      (![X0 : $i]:
% 0.45/0.69         (~ (l1_pre_topc @ X0)
% 0.45/0.69          | ~ (v2_pre_topc @ X0)
% 0.45/0.69          | ~ (l1_struct_0 @ X0)
% 0.45/0.69          | ((k1_tops_1 @ X0 @ (k2_struct_0 @ X0)) = (k2_struct_0 @ X0)))),
% 0.45/0.69      inference('simplify', [status(thm)], ['64'])).
% 0.45/0.69  thf(t43_tops_1, conjecture,
% 0.45/0.69    (![A:$i]:
% 0.45/0.69     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.69       ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.45/0.69  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.69    (~( ![A:$i]:
% 0.45/0.69        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.45/0.69          ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ) )),
% 0.45/0.69    inference('cnf.neg', [status(esa)], [t43_tops_1])).
% 0.45/0.69  thf('66', plain,
% 0.45/0.69      (((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) != (k2_struct_0 @ sk_A))),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('67', plain,
% 0.45/0.69      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.45/0.69        | ~ (l1_struct_0 @ sk_A)
% 0.45/0.69        | ~ (v2_pre_topc @ sk_A)
% 0.45/0.69        | ~ (l1_pre_topc @ sk_A))),
% 0.45/0.69      inference('sup-', [status(thm)], ['65', '66'])).
% 0.45/0.69  thf('68', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf(dt_l1_pre_topc, axiom,
% 0.45/0.69    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.45/0.69  thf('69', plain,
% 0.45/0.69      (![X46 : $i]: ((l1_struct_0 @ X46) | ~ (l1_pre_topc @ X46))),
% 0.45/0.69      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.45/0.69  thf('70', plain, ((l1_struct_0 @ sk_A)),
% 0.45/0.69      inference('sup-', [status(thm)], ['68', '69'])).
% 0.45/0.69  thf('71', plain, ((v2_pre_topc @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('72', plain, ((l1_pre_topc @ sk_A)),
% 0.45/0.69      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.69  thf('73', plain, (((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.45/0.69      inference('demod', [status(thm)], ['67', '70', '71', '72'])).
% 0.45/0.69  thf('74', plain, ($false), inference('simplify', [status(thm)], ['73'])).
% 0.45/0.69  
% 0.45/0.69  % SZS output end Refutation
% 0.45/0.69  
% 0.45/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
