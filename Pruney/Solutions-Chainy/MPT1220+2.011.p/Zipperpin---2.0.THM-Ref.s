%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ht9q8509Qy

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:41 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 201 expanded)
%              Number of leaves         :   33 (  76 expanded)
%              Depth                    :   21
%              Number of atoms          :  639 (1436 expanded)
%              Number of equality atoms :   21 (  44 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t27_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_struct_0 @ A ) ) ) ) )).

thf('0',plain,(
    ! [X30: $i] :
      ( ( ( k2_struct_0 @ X30 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X30 ) @ ( k1_struct_0 @ X30 ) ) )
      | ~ ( l1_struct_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t27_pre_topc])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('1',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X15 ) @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('2',plain,(
    ! [X14: $i] :
      ( ( k2_subset_1 @ X14 )
      = X14 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('3',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('4',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('5',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','7'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('9',plain,(
    ! [X19: $i,X21: $i] :
      ( ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t43_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ C )
          <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_xboole_0 @ X18 @ X16 )
      | ( r1_tarski @ X18 @ ( k3_subset_1 @ X17 @ X16 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t43_subset_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ X2 @ ( k3_subset_1 @ X0 @ X1 ) )
      | ~ ( r1_xboole_0 @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ( r1_tarski @ X0 @ ( k3_subset_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','12'])).

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

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ( r2_hidden @ ( sk_C_1 @ X5 @ X4 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( r1_tarski @ X0 @ ( k3_subset_1 @ X0 @ X1 ) ) ) ),
    inference(clc,[status(thm)],['13','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_struct_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','17'])).

thf(fc3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ) )).

thf('19',plain,(
    ! [X29: $i] :
      ( ( v1_xboole_0 @ ( k1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc3_struct_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['18','19'])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('21',plain,(
    ! [X27: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('22',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( l1_pre_topc @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X25 @ X26 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('24',plain,(
    ! [X28: $i] :
      ( ( l1_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X27: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X27 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ~ ( l1_struct_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('29',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( r1_tarski @ X31 @ ( k2_pre_topc @ X32 @ X31 ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X28: $i] :
      ( ( l1_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('33',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X13 )
      | ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ X0 ) @ X1 )
      | ~ ( r1_tarski @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('37',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','38'])).

thf('40',plain,(
    ! [X28: $i] :
      ( ( l1_struct_0 @ X28 )
      | ~ ( l1_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('43',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('44',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ( r1_tarski @ X31 @ ( k2_pre_topc @ X32 @ X31 ) )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('49',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

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

thf('53',plain,(
    ( k2_pre_topc @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ( u1_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['41','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ( k2_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    $false ),
    inference(simplify,[status(thm)],['59'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ht9q8509Qy
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:28:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.68/0.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.68/0.88  % Solved by: fo/fo7.sh
% 0.68/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.88  % done 541 iterations in 0.410s
% 0.68/0.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.68/0.88  % SZS output start Refutation
% 0.68/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.68/0.88  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.68/0.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.68/0.88  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.68/0.88  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.68/0.88  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.68/0.88  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.68/0.88  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.68/0.88  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.68/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.88  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.68/0.88  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.68/0.88  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.68/0.88  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.68/0.88  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.68/0.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.68/0.88  thf(t27_pre_topc, axiom,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( l1_struct_0 @ A ) =>
% 0.68/0.88       ( ( k2_struct_0 @ A ) =
% 0.68/0.88         ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_struct_0 @ A ) ) ) ))).
% 0.68/0.88  thf('0', plain,
% 0.68/0.88      (![X30 : $i]:
% 0.68/0.88         (((k2_struct_0 @ X30)
% 0.68/0.88            = (k3_subset_1 @ (u1_struct_0 @ X30) @ (k1_struct_0 @ X30)))
% 0.68/0.88          | ~ (l1_struct_0 @ X30))),
% 0.68/0.88      inference('cnf', [status(esa)], [t27_pre_topc])).
% 0.68/0.88  thf(dt_k2_subset_1, axiom,
% 0.68/0.88    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.68/0.88  thf('1', plain,
% 0.68/0.88      (![X15 : $i]: (m1_subset_1 @ (k2_subset_1 @ X15) @ (k1_zfmisc_1 @ X15))),
% 0.68/0.88      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.68/0.88  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.68/0.88  thf('2', plain, (![X14 : $i]: ((k2_subset_1 @ X14) = (X14))),
% 0.68/0.88      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.68/0.88  thf('3', plain, (![X15 : $i]: (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X15))),
% 0.68/0.88      inference('demod', [status(thm)], ['1', '2'])).
% 0.68/0.88  thf(d3_tarski, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( r1_tarski @ A @ B ) <=>
% 0.68/0.88       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.68/0.88  thf('4', plain,
% 0.68/0.88      (![X1 : $i, X3 : $i]:
% 0.68/0.88         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.68/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.68/0.88  thf('5', plain, (![X15 : $i]: (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X15))),
% 0.68/0.88      inference('demod', [status(thm)], ['1', '2'])).
% 0.68/0.88  thf(t5_subset, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.68/0.88          ( v1_xboole_0 @ C ) ) ))).
% 0.68/0.88  thf('6', plain,
% 0.68/0.88      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.68/0.88         (~ (r2_hidden @ X22 @ X23)
% 0.68/0.88          | ~ (v1_xboole_0 @ X24)
% 0.68/0.88          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.68/0.88      inference('cnf', [status(esa)], [t5_subset])).
% 0.68/0.88  thf('7', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['5', '6'])).
% 0.68/0.88  thf('8', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['4', '7'])).
% 0.68/0.88  thf(t3_subset, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.68/0.88  thf('9', plain,
% 0.68/0.88      (![X19 : $i, X21 : $i]:
% 0.68/0.88         ((m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X21)) | ~ (r1_tarski @ X19 @ X21))),
% 0.68/0.88      inference('cnf', [status(esa)], [t3_subset])).
% 0.68/0.88  thf('10', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['8', '9'])).
% 0.68/0.88  thf(t43_subset_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.88       ( ![C:$i]:
% 0.68/0.88         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.68/0.88           ( ( r1_xboole_0 @ B @ C ) <=>
% 0.68/0.88             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.68/0.88  thf('11', plain,
% 0.68/0.88      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 0.68/0.88          | ~ (r1_xboole_0 @ X18 @ X16)
% 0.68/0.88          | (r1_tarski @ X18 @ (k3_subset_1 @ X17 @ X16))
% 0.68/0.88          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X17)))),
% 0.68/0.88      inference('cnf', [status(esa)], [t43_subset_1])).
% 0.68/0.88  thf('12', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (~ (v1_xboole_0 @ X1)
% 0.68/0.88          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X0))
% 0.68/0.88          | (r1_tarski @ X2 @ (k3_subset_1 @ X0 @ X1))
% 0.68/0.88          | ~ (r1_xboole_0 @ X2 @ X1))),
% 0.68/0.88      inference('sup-', [status(thm)], ['10', '11'])).
% 0.68/0.88  thf('13', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         (~ (r1_xboole_0 @ X0 @ X1)
% 0.68/0.88          | (r1_tarski @ X0 @ (k3_subset_1 @ X0 @ X1))
% 0.68/0.88          | ~ (v1_xboole_0 @ X1))),
% 0.68/0.88      inference('sup-', [status(thm)], ['3', '12'])).
% 0.68/0.88  thf(t3_xboole_0, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.68/0.88            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.68/0.88       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.68/0.88            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.68/0.88  thf('14', plain,
% 0.68/0.88      (![X4 : $i, X5 : $i]:
% 0.68/0.88         ((r1_xboole_0 @ X4 @ X5) | (r2_hidden @ (sk_C_1 @ X5 @ X4) @ X5))),
% 0.68/0.88      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.68/0.88  thf('15', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['5', '6'])).
% 0.68/0.88  thf('16', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['14', '15'])).
% 0.68/0.88  thf('17', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         (~ (v1_xboole_0 @ X1) | (r1_tarski @ X0 @ (k3_subset_1 @ X0 @ X1)))),
% 0.68/0.88      inference('clc', [status(thm)], ['13', '16'])).
% 0.68/0.88  thf('18', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((r1_tarski @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 0.68/0.88          | ~ (l1_struct_0 @ X0)
% 0.68/0.88          | ~ (v1_xboole_0 @ (k1_struct_0 @ X0)))),
% 0.68/0.88      inference('sup+', [status(thm)], ['0', '17'])).
% 0.68/0.88  thf(fc3_struct_0, axiom,
% 0.68/0.88    (![A:$i]: ( ( l1_struct_0 @ A ) => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ))).
% 0.68/0.88  thf('19', plain,
% 0.68/0.88      (![X29 : $i]:
% 0.68/0.88         ((v1_xboole_0 @ (k1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.68/0.88      inference('cnf', [status(esa)], [fc3_struct_0])).
% 0.68/0.88  thf('20', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (~ (l1_struct_0 @ X0)
% 0.68/0.88          | (r1_tarski @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0)))),
% 0.68/0.88      inference('clc', [status(thm)], ['18', '19'])).
% 0.68/0.88  thf(dt_k2_struct_0, axiom,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( l1_struct_0 @ A ) =>
% 0.68/0.88       ( m1_subset_1 @
% 0.68/0.88         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.68/0.88  thf('21', plain,
% 0.68/0.88      (![X27 : $i]:
% 0.68/0.88         ((m1_subset_1 @ (k2_struct_0 @ X27) @ 
% 0.68/0.88           (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.68/0.88          | ~ (l1_struct_0 @ X27))),
% 0.68/0.88      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.68/0.88  thf(dt_k2_pre_topc, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( ( l1_pre_topc @ A ) & 
% 0.68/0.88         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.68/0.88       ( m1_subset_1 @
% 0.68/0.88         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.68/0.88  thf('22', plain,
% 0.68/0.88      (![X25 : $i, X26 : $i]:
% 0.68/0.88         (~ (l1_pre_topc @ X25)
% 0.68/0.88          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.68/0.88          | (m1_subset_1 @ (k2_pre_topc @ X25 @ X26) @ 
% 0.68/0.88             (k1_zfmisc_1 @ (u1_struct_0 @ X25))))),
% 0.68/0.88      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.68/0.88  thf('23', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (~ (l1_struct_0 @ X0)
% 0.68/0.88          | (m1_subset_1 @ (k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ 
% 0.68/0.88             (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.68/0.88          | ~ (l1_pre_topc @ X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['21', '22'])).
% 0.68/0.88  thf(dt_l1_pre_topc, axiom,
% 0.68/0.88    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.68/0.88  thf('24', plain,
% 0.68/0.88      (![X28 : $i]: ((l1_struct_0 @ X28) | ~ (l1_pre_topc @ X28))),
% 0.68/0.88      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.68/0.88  thf('25', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (~ (l1_pre_topc @ X0)
% 0.68/0.88          | (m1_subset_1 @ (k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ 
% 0.68/0.88             (k1_zfmisc_1 @ (u1_struct_0 @ X0))))),
% 0.68/0.88      inference('clc', [status(thm)], ['23', '24'])).
% 0.68/0.88  thf('26', plain,
% 0.68/0.88      (![X19 : $i, X20 : $i]:
% 0.68/0.88         ((r1_tarski @ X19 @ X20) | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.68/0.88      inference('cnf', [status(esa)], [t3_subset])).
% 0.68/0.88  thf('27', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (~ (l1_pre_topc @ X0)
% 0.68/0.88          | (r1_tarski @ (k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ 
% 0.68/0.88             (u1_struct_0 @ X0)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['25', '26'])).
% 0.68/0.88  thf('28', plain,
% 0.68/0.88      (![X27 : $i]:
% 0.68/0.88         ((m1_subset_1 @ (k2_struct_0 @ X27) @ 
% 0.68/0.88           (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.68/0.88          | ~ (l1_struct_0 @ X27))),
% 0.68/0.88      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.68/0.88  thf(t48_pre_topc, axiom,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( l1_pre_topc @ A ) =>
% 0.68/0.88       ( ![B:$i]:
% 0.68/0.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.68/0.88           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.68/0.88  thf('29', plain,
% 0.68/0.88      (![X31 : $i, X32 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.68/0.88          | (r1_tarski @ X31 @ (k2_pre_topc @ X32 @ X31))
% 0.68/0.88          | ~ (l1_pre_topc @ X32))),
% 0.68/0.88      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.68/0.88  thf('30', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (~ (l1_struct_0 @ X0)
% 0.68/0.88          | ~ (l1_pre_topc @ X0)
% 0.68/0.88          | (r1_tarski @ (k2_struct_0 @ X0) @ 
% 0.68/0.88             (k2_pre_topc @ X0 @ (k2_struct_0 @ X0))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['28', '29'])).
% 0.68/0.88  thf('31', plain,
% 0.68/0.88      (![X28 : $i]: ((l1_struct_0 @ X28) | ~ (l1_pre_topc @ X28))),
% 0.68/0.88      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.68/0.88  thf('32', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((r1_tarski @ (k2_struct_0 @ X0) @ 
% 0.68/0.88           (k2_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 0.68/0.88          | ~ (l1_pre_topc @ X0))),
% 0.68/0.88      inference('clc', [status(thm)], ['30', '31'])).
% 0.68/0.88  thf(t1_xboole_1, axiom,
% 0.68/0.88    (![A:$i,B:$i,C:$i]:
% 0.68/0.88     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.68/0.88       ( r1_tarski @ A @ C ) ))).
% 0.68/0.88  thf('33', plain,
% 0.68/0.88      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.68/0.88         (~ (r1_tarski @ X11 @ X12)
% 0.68/0.88          | ~ (r1_tarski @ X12 @ X13)
% 0.68/0.88          | (r1_tarski @ X11 @ X13))),
% 0.68/0.88      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.68/0.88  thf('34', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         (~ (l1_pre_topc @ X0)
% 0.68/0.88          | (r1_tarski @ (k2_struct_0 @ X0) @ X1)
% 0.68/0.88          | ~ (r1_tarski @ (k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ X1))),
% 0.68/0.88      inference('sup-', [status(thm)], ['32', '33'])).
% 0.68/0.88  thf('35', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (~ (l1_pre_topc @ X0)
% 0.68/0.88          | (r1_tarski @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X0))
% 0.68/0.88          | ~ (l1_pre_topc @ X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['27', '34'])).
% 0.68/0.88  thf('36', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((r1_tarski @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X0))
% 0.68/0.88          | ~ (l1_pre_topc @ X0))),
% 0.68/0.88      inference('simplify', [status(thm)], ['35'])).
% 0.68/0.88  thf(d10_xboole_0, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.68/0.88  thf('37', plain,
% 0.68/0.88      (![X8 : $i, X10 : $i]:
% 0.68/0.88         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.68/0.88      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.68/0.88  thf('38', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (~ (l1_pre_topc @ X0)
% 0.68/0.88          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 0.68/0.88          | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['36', '37'])).
% 0.68/0.88  thf('39', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (~ (l1_struct_0 @ X0)
% 0.68/0.88          | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0))
% 0.68/0.88          | ~ (l1_pre_topc @ X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['20', '38'])).
% 0.68/0.88  thf('40', plain,
% 0.68/0.88      (![X28 : $i]: ((l1_struct_0 @ X28) | ~ (l1_pre_topc @ X28))),
% 0.68/0.88      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.68/0.88  thf('41', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (~ (l1_pre_topc @ X0) | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 0.68/0.88      inference('clc', [status(thm)], ['39', '40'])).
% 0.68/0.88  thf('42', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (~ (l1_pre_topc @ X0) | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 0.68/0.88      inference('clc', [status(thm)], ['39', '40'])).
% 0.68/0.88  thf('43', plain, (![X15 : $i]: (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X15))),
% 0.68/0.88      inference('demod', [status(thm)], ['1', '2'])).
% 0.68/0.88  thf('44', plain,
% 0.68/0.88      (![X31 : $i, X32 : $i]:
% 0.68/0.88         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.68/0.88          | (r1_tarski @ X31 @ (k2_pre_topc @ X32 @ X31))
% 0.68/0.88          | ~ (l1_pre_topc @ X32))),
% 0.68/0.88      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.68/0.88  thf('45', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (~ (l1_pre_topc @ X0)
% 0.68/0.88          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.68/0.88             (k2_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['43', '44'])).
% 0.68/0.88  thf('46', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.68/0.88           (k2_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 0.68/0.88          | ~ (l1_pre_topc @ X0)
% 0.68/0.88          | ~ (l1_pre_topc @ X0))),
% 0.68/0.88      inference('sup+', [status(thm)], ['42', '45'])).
% 0.68/0.88  thf('47', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (~ (l1_pre_topc @ X0)
% 0.68/0.88          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.68/0.88             (k2_pre_topc @ X0 @ (k2_struct_0 @ X0))))),
% 0.68/0.88      inference('simplify', [status(thm)], ['46'])).
% 0.68/0.88  thf('48', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (~ (l1_pre_topc @ X0)
% 0.68/0.88          | (r1_tarski @ (k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) @ 
% 0.68/0.88             (u1_struct_0 @ X0)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['25', '26'])).
% 0.68/0.88  thf('49', plain,
% 0.68/0.88      (![X8 : $i, X10 : $i]:
% 0.68/0.88         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 0.68/0.88      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.68/0.88  thf('50', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (~ (l1_pre_topc @ X0)
% 0.68/0.88          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.68/0.88               (k2_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 0.68/0.88          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (k2_struct_0 @ X0))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['48', '49'])).
% 0.68/0.88  thf('51', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (~ (l1_pre_topc @ X0)
% 0.68/0.88          | ((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 0.68/0.88          | ~ (l1_pre_topc @ X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['47', '50'])).
% 0.68/0.88  thf('52', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         (((u1_struct_0 @ X0) = (k2_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 0.68/0.88          | ~ (l1_pre_topc @ X0))),
% 0.68/0.88      inference('simplify', [status(thm)], ['51'])).
% 0.68/0.88  thf(t27_tops_1, conjecture,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( l1_pre_topc @ A ) =>
% 0.68/0.88       ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.68/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.88    (~( ![A:$i]:
% 0.68/0.88        ( ( l1_pre_topc @ A ) =>
% 0.68/0.88          ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ) )),
% 0.68/0.88    inference('cnf.neg', [status(esa)], [t27_tops_1])).
% 0.68/0.88  thf('53', plain,
% 0.68/0.88      (((k2_pre_topc @ sk_A @ (k2_struct_0 @ sk_A)) != (k2_struct_0 @ sk_A))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('54', plain,
% 0.68/0.88      ((((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)) | ~ (l1_pre_topc @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['52', '53'])).
% 0.68/0.88  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('56', plain, (((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.68/0.88      inference('demod', [status(thm)], ['54', '55'])).
% 0.68/0.88  thf('57', plain,
% 0.68/0.88      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)) | ~ (l1_pre_topc @ sk_A))),
% 0.68/0.88      inference('sup-', [status(thm)], ['41', '56'])).
% 0.68/0.88  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('59', plain, (((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.68/0.88      inference('demod', [status(thm)], ['57', '58'])).
% 0.68/0.88  thf('60', plain, ($false), inference('simplify', [status(thm)], ['59'])).
% 0.68/0.88  
% 0.68/0.88  % SZS output end Refutation
% 0.68/0.88  
% 0.68/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
