%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vF7DKkw0Fm

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:39 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 207 expanded)
%              Number of leaves         :   29 (  77 expanded)
%              Depth                    :   19
%              Number of atoms          :  599 (1478 expanded)
%              Number of equality atoms :   26 (  58 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

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
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('4',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('6',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X11 ) @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('7',plain,(
    ! [X10: $i] :
      ( ( k2_subset_1 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('8',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t35_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) )
           => ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( r1_tarski @ X12 @ ( k3_subset_1 @ X13 @ X14 ) )
      | ~ ( r1_tarski @ X14 @ ( k3_subset_1 @ X13 @ X12 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t35_subset_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k3_subset_1 @ X0 @ X0 ) )
      | ( r1_tarski @ X0 @ ( k3_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( r1_tarski @ X0 @ ( k3_subset_1 @ X0 @ X1 ) )
      | ~ ( r1_tarski @ X1 @ ( k3_subset_1 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k3_subset_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_struct_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['0','13'])).

thf(fc3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ) )).

thf('15',plain,(
    ! [X22: $i] :
      ( ( v1_xboole_0 @ ( k1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc3_struct_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['14','15'])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('18',plain,(
    ! [X20: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('19',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('26',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( r1_tarski @ X24 @ ( k2_pre_topc @ X25 @ X24 ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('31',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( l1_pre_topc @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X18 @ X19 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['24','35'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('37',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X20: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X20 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ~ ( l1_struct_0 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('40',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ( r1_tarski @ X24 @ ( k2_pre_topc @ X25 @ X24 ) )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(clc,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','47'])).

thf('49',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['36','37'])).

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

thf('52',plain,(
    ( k2_pre_topc @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ( u1_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ( k2_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    $false ),
    inference(simplify,[status(thm)],['58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vF7DKkw0Fm
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:08:03 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.37/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.37/0.62  % Solved by: fo/fo7.sh
% 0.37/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.62  % done 284 iterations in 0.179s
% 0.37/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.37/0.62  % SZS output start Refutation
% 0.37/0.62  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.37/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.62  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.37/0.62  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.37/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.37/0.62  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.37/0.62  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.37/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.62  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.37/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.37/0.62  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.37/0.62  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.37/0.62  thf(t27_pre_topc, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( l1_struct_0 @ A ) =>
% 0.37/0.62       ( ( k2_struct_0 @ A ) =
% 0.37/0.62         ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_struct_0 @ A ) ) ) ))).
% 0.37/0.62  thf('0', plain,
% 0.37/0.62      (![X23 : $i]:
% 0.37/0.62         (((k2_struct_0 @ X23)
% 0.37/0.62            = (k3_subset_1 @ (u1_struct_0 @ X23) @ (k1_struct_0 @ X23)))
% 0.37/0.62          | ~ (l1_struct_0 @ X23))),
% 0.37/0.62      inference('cnf', [status(esa)], [t27_pre_topc])).
% 0.37/0.62  thf(d3_tarski, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( r1_tarski @ A @ B ) <=>
% 0.37/0.62       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.37/0.62  thf('1', plain,
% 0.37/0.62      (![X4 : $i, X6 : $i]:
% 0.37/0.62         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.37/0.62      inference('cnf', [status(esa)], [d3_tarski])).
% 0.37/0.62  thf(d1_xboole_0, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.37/0.62  thf('2', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.37/0.62      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.37/0.62  thf('3', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.62  thf(t3_subset, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.37/0.62  thf('4', plain,
% 0.37/0.62      (![X15 : $i, X17 : $i]:
% 0.37/0.62         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 0.37/0.62      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.62  thf('5', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]:
% 0.37/0.62         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['3', '4'])).
% 0.37/0.62  thf(dt_k2_subset_1, axiom,
% 0.37/0.62    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.37/0.62  thf('6', plain,
% 0.37/0.62      (![X11 : $i]: (m1_subset_1 @ (k2_subset_1 @ X11) @ (k1_zfmisc_1 @ X11))),
% 0.37/0.62      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.37/0.62  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.37/0.62  thf('7', plain, (![X10 : $i]: ((k2_subset_1 @ X10) = (X10))),
% 0.37/0.62      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.37/0.62  thf('8', plain, (![X11 : $i]: (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X11))),
% 0.37/0.63      inference('demod', [status(thm)], ['6', '7'])).
% 0.37/0.63  thf(t35_subset_1, axiom,
% 0.37/0.63    (![A:$i,B:$i]:
% 0.37/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.63       ( ![C:$i]:
% 0.37/0.63         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.37/0.63           ( ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) =>
% 0.37/0.63             ( r1_tarski @ C @ ( k3_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.37/0.63  thf('9', plain,
% 0.37/0.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.37/0.63         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.37/0.63          | (r1_tarski @ X12 @ (k3_subset_1 @ X13 @ X14))
% 0.37/0.63          | ~ (r1_tarski @ X14 @ (k3_subset_1 @ X13 @ X12))
% 0.37/0.63          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.37/0.63      inference('cnf', [status(esa)], [t35_subset_1])).
% 0.37/0.63  thf('10', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.37/0.63          | ~ (r1_tarski @ X1 @ (k3_subset_1 @ X0 @ X0))
% 0.37/0.63          | (r1_tarski @ X0 @ (k3_subset_1 @ X0 @ X1)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['8', '9'])).
% 0.37/0.63  thf('11', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         (~ (v1_xboole_0 @ X1)
% 0.37/0.63          | (r1_tarski @ X0 @ (k3_subset_1 @ X0 @ X1))
% 0.37/0.63          | ~ (r1_tarski @ X1 @ (k3_subset_1 @ X0 @ X0)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['5', '10'])).
% 0.37/0.63  thf('12', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.37/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.37/0.63  thf('13', plain,
% 0.37/0.63      (![X0 : $i, X1 : $i]:
% 0.37/0.63         ((r1_tarski @ X0 @ (k3_subset_1 @ X0 @ X1)) | ~ (v1_xboole_0 @ X1))),
% 0.37/0.63      inference('clc', [status(thm)], ['11', '12'])).
% 0.37/0.63  thf('14', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         ((r1_tarski @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 0.37/0.63          | ~ (l1_struct_0 @ X0)
% 0.37/0.63          | ~ (v1_xboole_0 @ (k1_struct_0 @ X0)))),
% 0.37/0.63      inference('sup+', [status(thm)], ['0', '13'])).
% 0.37/0.63  thf(fc3_struct_0, axiom,
% 0.37/0.63    (![A:$i]: ( ( l1_struct_0 @ A ) => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ))).
% 0.37/0.63  thf('15', plain,
% 0.37/0.63      (![X22 : $i]:
% 0.37/0.63         ((v1_xboole_0 @ (k1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.37/0.63      inference('cnf', [status(esa)], [fc3_struct_0])).
% 0.37/0.63  thf('16', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         (~ (l1_struct_0 @ X0)
% 0.37/0.63          | (r1_tarski @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0)))),
% 0.37/0.63      inference('clc', [status(thm)], ['14', '15'])).
% 0.37/0.63  thf('17', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         (~ (l1_struct_0 @ X0)
% 0.37/0.63          | (r1_tarski @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0)))),
% 0.37/0.63      inference('clc', [status(thm)], ['14', '15'])).
% 0.37/0.63  thf(dt_k2_struct_0, axiom,
% 0.37/0.63    (![A:$i]:
% 0.37/0.63     ( ( l1_struct_0 @ A ) =>
% 0.37/0.63       ( m1_subset_1 @
% 0.37/0.63         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.37/0.63  thf('18', plain,
% 0.37/0.63      (![X20 : $i]:
% 0.37/0.63         ((m1_subset_1 @ (k2_struct_0 @ X20) @ 
% 0.37/0.63           (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.37/0.63          | ~ (l1_struct_0 @ X20))),
% 0.37/0.63      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.37/0.63  thf('19', plain,
% 0.37/0.63      (![X15 : $i, X16 : $i]:
% 0.37/0.63         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.37/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.63  thf('20', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         (~ (l1_struct_0 @ X0)
% 0.37/0.63          | (r1_tarski @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X0)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['18', '19'])).
% 0.37/0.63  thf(d10_xboole_0, axiom,
% 0.37/0.63    (![A:$i,B:$i]:
% 0.37/0.63     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.63  thf('21', plain,
% 0.37/0.63      (![X7 : $i, X9 : $i]:
% 0.37/0.63         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.37/0.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.63  thf('22', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         (~ (l1_struct_0 @ X0)
% 0.37/0.63          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 0.37/0.63          | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['20', '21'])).
% 0.37/0.63  thf('23', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         (~ (l1_struct_0 @ X0)
% 0.37/0.63          | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0))
% 0.37/0.63          | ~ (l1_struct_0 @ X0))),
% 0.37/0.63      inference('sup-', [status(thm)], ['17', '22'])).
% 0.37/0.63  thf('24', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         (((u1_struct_0 @ X0) = (k2_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.37/0.63      inference('simplify', [status(thm)], ['23'])).
% 0.37/0.63  thf('25', plain, (![X11 : $i]: (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X11))),
% 0.37/0.63      inference('demod', [status(thm)], ['6', '7'])).
% 0.37/0.63  thf(t48_pre_topc, axiom,
% 0.37/0.63    (![A:$i]:
% 0.37/0.63     ( ( l1_pre_topc @ A ) =>
% 0.37/0.63       ( ![B:$i]:
% 0.37/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.37/0.63           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.37/0.63  thf('26', plain,
% 0.37/0.63      (![X24 : $i, X25 : $i]:
% 0.37/0.63         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.37/0.63          | (r1_tarski @ X24 @ (k2_pre_topc @ X25 @ X24))
% 0.37/0.63          | ~ (l1_pre_topc @ X25))),
% 0.37/0.63      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.37/0.63  thf('27', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         (~ (l1_pre_topc @ X0)
% 0.37/0.63          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.37/0.63             (k2_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 0.37/0.63      inference('sup-', [status(thm)], ['25', '26'])).
% 0.37/0.63  thf('28', plain,
% 0.37/0.63      (![X7 : $i, X9 : $i]:
% 0.37/0.63         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.37/0.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.63  thf('29', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         (~ (l1_pre_topc @ X0)
% 0.37/0.63          | ~ (r1_tarski @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 0.37/0.63               (u1_struct_0 @ X0))
% 0.37/0.63          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['27', '28'])).
% 0.37/0.63  thf('30', plain, (![X11 : $i]: (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X11))),
% 0.37/0.63      inference('demod', [status(thm)], ['6', '7'])).
% 0.37/0.63  thf(dt_k2_pre_topc, axiom,
% 0.37/0.63    (![A:$i,B:$i]:
% 0.37/0.63     ( ( ( l1_pre_topc @ A ) & 
% 0.37/0.63         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.37/0.63       ( m1_subset_1 @
% 0.37/0.63         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.37/0.63  thf('31', plain,
% 0.37/0.63      (![X18 : $i, X19 : $i]:
% 0.37/0.63         (~ (l1_pre_topc @ X18)
% 0.37/0.63          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X18)))
% 0.37/0.63          | (m1_subset_1 @ (k2_pre_topc @ X18 @ X19) @ 
% 0.37/0.63             (k1_zfmisc_1 @ (u1_struct_0 @ X18))))),
% 0.37/0.63      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.37/0.63  thf('32', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         ((m1_subset_1 @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 0.37/0.63           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.37/0.63          | ~ (l1_pre_topc @ X0))),
% 0.37/0.63      inference('sup-', [status(thm)], ['30', '31'])).
% 0.37/0.63  thf('33', plain,
% 0.37/0.63      (![X15 : $i, X16 : $i]:
% 0.37/0.63         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.37/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.37/0.63  thf('34', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         (~ (l1_pre_topc @ X0)
% 0.37/0.63          | (r1_tarski @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 0.37/0.63             (u1_struct_0 @ X0)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['32', '33'])).
% 0.37/0.63  thf('35', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         (((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.37/0.63          | ~ (l1_pre_topc @ X0))),
% 0.37/0.63      inference('clc', [status(thm)], ['29', '34'])).
% 0.37/0.63  thf('36', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         (((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.37/0.63          | ~ (l1_struct_0 @ X0)
% 0.37/0.63          | ~ (l1_pre_topc @ X0))),
% 0.37/0.63      inference('sup+', [status(thm)], ['24', '35'])).
% 0.37/0.63  thf(dt_l1_pre_topc, axiom,
% 0.37/0.63    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.37/0.63  thf('37', plain,
% 0.37/0.63      (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.37/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.63  thf('38', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         (~ (l1_pre_topc @ X0)
% 0.37/0.63          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0)))),
% 0.37/0.63      inference('clc', [status(thm)], ['36', '37'])).
% 0.37/0.63  thf('39', plain,
% 0.37/0.63      (![X20 : $i]:
% 0.37/0.63         ((m1_subset_1 @ (k2_struct_0 @ X20) @ 
% 0.37/0.63           (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.37/0.63          | ~ (l1_struct_0 @ X20))),
% 0.37/0.63      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.37/0.63  thf('40', plain,
% 0.37/0.63      (![X24 : $i, X25 : $i]:
% 0.37/0.63         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.37/0.63          | (r1_tarski @ X24 @ (k2_pre_topc @ X25 @ X24))
% 0.37/0.63          | ~ (l1_pre_topc @ X25))),
% 0.37/0.63      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.37/0.63  thf('41', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         (~ (l1_struct_0 @ X0)
% 0.37/0.63          | ~ (l1_pre_topc @ X0)
% 0.37/0.63          | (r1_tarski @ (k2_struct_0 @ X0) @ 
% 0.37/0.63             (k2_pre_topc @ X0 @ (k2_struct_0 @ X0))))),
% 0.37/0.63      inference('sup-', [status(thm)], ['39', '40'])).
% 0.37/0.63  thf('42', plain,
% 0.37/0.63      (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.37/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.63  thf('43', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         ((r1_tarski @ (k2_struct_0 @ X0) @ 
% 0.37/0.63           (k2_pre_topc @ X0 @ (k2_struct_0 @ X0)))
% 0.37/0.63          | ~ (l1_pre_topc @ X0))),
% 0.37/0.63      inference('clc', [status(thm)], ['41', '42'])).
% 0.37/0.63  thf('44', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         ((r1_tarski @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X0))
% 0.37/0.63          | ~ (l1_pre_topc @ X0)
% 0.37/0.63          | ~ (l1_pre_topc @ X0))),
% 0.37/0.63      inference('sup+', [status(thm)], ['38', '43'])).
% 0.37/0.63  thf('45', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         (~ (l1_pre_topc @ X0)
% 0.37/0.63          | (r1_tarski @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X0)))),
% 0.37/0.63      inference('simplify', [status(thm)], ['44'])).
% 0.37/0.63  thf('46', plain,
% 0.37/0.63      (![X7 : $i, X9 : $i]:
% 0.37/0.63         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 0.37/0.63      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.63  thf('47', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         (~ (l1_pre_topc @ X0)
% 0.37/0.63          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 0.37/0.63          | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 0.37/0.63      inference('sup-', [status(thm)], ['45', '46'])).
% 0.37/0.63  thf('48', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         (~ (l1_struct_0 @ X0)
% 0.37/0.63          | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0))
% 0.37/0.63          | ~ (l1_pre_topc @ X0))),
% 0.37/0.63      inference('sup-', [status(thm)], ['16', '47'])).
% 0.37/0.63  thf('49', plain,
% 0.37/0.63      (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.37/0.63      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.37/0.63  thf('50', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         (~ (l1_pre_topc @ X0) | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 0.37/0.63      inference('clc', [status(thm)], ['48', '49'])).
% 0.37/0.63  thf('51', plain,
% 0.37/0.63      (![X0 : $i]:
% 0.37/0.63         (~ (l1_pre_topc @ X0)
% 0.37/0.63          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0)))),
% 0.37/0.63      inference('clc', [status(thm)], ['36', '37'])).
% 0.37/0.63  thf(t27_tops_1, conjecture,
% 0.37/0.63    (![A:$i]:
% 0.37/0.63     ( ( l1_pre_topc @ A ) =>
% 0.37/0.63       ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.37/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.63    (~( ![A:$i]:
% 0.37/0.63        ( ( l1_pre_topc @ A ) =>
% 0.37/0.63          ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ) )),
% 0.37/0.63    inference('cnf.neg', [status(esa)], [t27_tops_1])).
% 0.37/0.63  thf('52', plain,
% 0.37/0.63      (((k2_pre_topc @ sk_A @ (k2_struct_0 @ sk_A)) != (k2_struct_0 @ sk_A))),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('53', plain,
% 0.37/0.63      ((((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)) | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.63      inference('sup-', [status(thm)], ['51', '52'])).
% 0.37/0.63  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('55', plain, (((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.37/0.63      inference('demod', [status(thm)], ['53', '54'])).
% 0.37/0.63  thf('56', plain,
% 0.37/0.63      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)) | ~ (l1_pre_topc @ sk_A))),
% 0.37/0.63      inference('sup-', [status(thm)], ['50', '55'])).
% 0.37/0.63  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.37/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.63  thf('58', plain, (((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.37/0.63      inference('demod', [status(thm)], ['56', '57'])).
% 0.37/0.63  thf('59', plain, ($false), inference('simplify', [status(thm)], ['58'])).
% 0.37/0.63  
% 0.37/0.63  % SZS output end Refutation
% 0.37/0.63  
% 0.50/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
