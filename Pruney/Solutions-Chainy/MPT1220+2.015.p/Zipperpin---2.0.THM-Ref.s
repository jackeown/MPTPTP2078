%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.13LhErYqVN

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:41 EST 2020

% Result     : Theorem 0.55s
% Output     : Refutation 0.55s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 200 expanded)
%              Number of leaves         :   34 (  75 expanded)
%              Depth                    :   18
%              Number of atoms          :  588 (1318 expanded)
%              Number of equality atoms :   28 (  63 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(fc3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X24: $i] :
      ( ( v1_xboole_0 @ ( k1_struct_0 @ X24 ) )
      | ~ ( l1_struct_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc3_struct_0])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('1',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_xboole_0 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ( X8 = X9 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( k1_xboole_0
        = ( k1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(t27_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_struct_0 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X25: $i] :
      ( ( ( k2_struct_0 @ X25 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X25 ) @ ( k1_struct_0 @ X25 ) ) )
      | ~ ( l1_struct_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t27_pre_topc])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('8',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X11 ) @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('9',plain,(
    ! [X10: $i] :
      ( ( k2_subset_1 @ X10 )
      = X10 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('10',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('11',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('12',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('13',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t43_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_xboole_0 @ B @ C )
          <=> ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_xboole_0 @ X14 @ X12 )
      | ( r1_tarski @ X14 @ ( k3_subset_1 @ X13 @ X12 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t43_subset_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ X1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

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

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( r1_tarski @ X19 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_C @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( r1_tarski @ X1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['15','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','22'])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('24',plain,(
    ! [X22: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X22 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X22 ) ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf('25',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ~ ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('32',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(dt_k2_pre_topc,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( m1_subset_1 @ ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('33',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( l1_pre_topc @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( m1_subset_1 @ ( k2_pre_topc @ X20 @ X21 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_pre_topc])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r1_tarski @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['31','36'])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('38',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( u1_struct_0 @ X0 )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('41',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t48_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) )).

thf('42',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( r1_tarski @ X26 @ ( k2_pre_topc @ X27 @ X26 ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[t48_pre_topc])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( r1_tarski @ ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) ) @ ( k2_struct_0 @ X0 ) )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','50'])).

thf('52',plain,(
    ! [X23: $i] :
      ( ( l1_struct_0 @ X23 )
      | ~ ( l1_pre_topc @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( k2_struct_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['51','52'])).

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

thf('54',plain,(
    ( k2_pre_topc @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ( k2_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    $false ),
    inference(simplify,[status(thm)],['57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.13LhErYqVN
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:53:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.20/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.55/0.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.55/0.74  % Solved by: fo/fo7.sh
% 0.55/0.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.55/0.74  % done 587 iterations in 0.305s
% 0.55/0.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.55/0.74  % SZS output start Refutation
% 0.55/0.74  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.55/0.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.55/0.74  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.55/0.74  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.55/0.74  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.55/0.74  thf(sk_A_type, type, sk_A: $i).
% 0.55/0.74  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.55/0.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.55/0.74  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.55/0.74  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.55/0.74  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.55/0.74  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.55/0.74  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.55/0.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.55/0.74  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.55/0.74  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.55/0.74  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.55/0.74  thf(fc3_struct_0, axiom,
% 0.55/0.74    (![A:$i]: ( ( l1_struct_0 @ A ) => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ))).
% 0.55/0.74  thf('0', plain,
% 0.55/0.74      (![X24 : $i]:
% 0.55/0.74         ((v1_xboole_0 @ (k1_struct_0 @ X24)) | ~ (l1_struct_0 @ X24))),
% 0.55/0.74      inference('cnf', [status(esa)], [fc3_struct_0])).
% 0.55/0.74  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.55/0.74  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.55/0.74      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.55/0.74  thf(t8_boole, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.55/0.74  thf('2', plain,
% 0.55/0.74      (![X8 : $i, X9 : $i]:
% 0.55/0.74         (~ (v1_xboole_0 @ X8) | ~ (v1_xboole_0 @ X9) | ((X8) = (X9)))),
% 0.55/0.74      inference('cnf', [status(esa)], [t8_boole])).
% 0.55/0.74  thf('3', plain,
% 0.55/0.74      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['1', '2'])).
% 0.55/0.74  thf('4', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (l1_struct_0 @ X0) | ((k1_xboole_0) = (k1_struct_0 @ X0)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['0', '3'])).
% 0.55/0.74  thf(t27_pre_topc, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( l1_struct_0 @ A ) =>
% 0.55/0.74       ( ( k2_struct_0 @ A ) =
% 0.55/0.74         ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_struct_0 @ A ) ) ) ))).
% 0.55/0.74  thf('5', plain,
% 0.55/0.74      (![X25 : $i]:
% 0.55/0.74         (((k2_struct_0 @ X25)
% 0.55/0.74            = (k3_subset_1 @ (u1_struct_0 @ X25) @ (k1_struct_0 @ X25)))
% 0.55/0.74          | ~ (l1_struct_0 @ X25))),
% 0.55/0.74      inference('cnf', [status(esa)], [t27_pre_topc])).
% 0.55/0.74  thf('6', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (((k2_struct_0 @ X0)
% 0.55/0.74            = (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0))
% 0.55/0.74          | ~ (l1_struct_0 @ X0)
% 0.55/0.74          | ~ (l1_struct_0 @ X0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['4', '5'])).
% 0.55/0.74  thf('7', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (l1_struct_0 @ X0)
% 0.55/0.74          | ((k2_struct_0 @ X0)
% 0.55/0.74              = (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0)))),
% 0.55/0.74      inference('simplify', [status(thm)], ['6'])).
% 0.55/0.74  thf(dt_k2_subset_1, axiom,
% 0.55/0.74    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.55/0.74  thf('8', plain,
% 0.55/0.74      (![X11 : $i]: (m1_subset_1 @ (k2_subset_1 @ X11) @ (k1_zfmisc_1 @ X11))),
% 0.55/0.74      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.55/0.74  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.55/0.74  thf('9', plain, (![X10 : $i]: ((k2_subset_1 @ X10) = (X10))),
% 0.55/0.74      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.55/0.74  thf('10', plain, (![X11 : $i]: (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X11))),
% 0.55/0.74      inference('demod', [status(thm)], ['8', '9'])).
% 0.55/0.74  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.55/0.74  thf('11', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.55/0.74      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.55/0.74  thf(t3_subset, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.55/0.74  thf('12', plain,
% 0.55/0.74      (![X15 : $i, X17 : $i]:
% 0.55/0.74         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 0.55/0.74      inference('cnf', [status(esa)], [t3_subset])).
% 0.55/0.74  thf('13', plain,
% 0.55/0.74      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['11', '12'])).
% 0.55/0.74  thf(t43_subset_1, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.55/0.74       ( ![C:$i]:
% 0.55/0.74         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.55/0.74           ( ( r1_xboole_0 @ B @ C ) <=>
% 0.55/0.74             ( r1_tarski @ B @ ( k3_subset_1 @ A @ C ) ) ) ) ) ))).
% 0.55/0.74  thf('14', plain,
% 0.55/0.74      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.55/0.74          | ~ (r1_xboole_0 @ X14 @ X12)
% 0.55/0.74          | (r1_tarski @ X14 @ (k3_subset_1 @ X13 @ X12))
% 0.55/0.74          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X13)))),
% 0.55/0.74      inference('cnf', [status(esa)], [t43_subset_1])).
% 0.55/0.74  thf('15', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.55/0.74          | (r1_tarski @ X1 @ (k3_subset_1 @ X0 @ k1_xboole_0))
% 0.55/0.74          | ~ (r1_xboole_0 @ X1 @ k1_xboole_0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['13', '14'])).
% 0.55/0.74  thf('16', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.55/0.74      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.55/0.74  thf(t3_xboole_0, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.55/0.74            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.55/0.74       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.55/0.74            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.55/0.74  thf('17', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.55/0.74      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.55/0.74  thf(t7_ordinal1, axiom,
% 0.55/0.74    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.55/0.74  thf('18', plain,
% 0.55/0.74      (![X18 : $i, X19 : $i]:
% 0.55/0.74         (~ (r2_hidden @ X18 @ X19) | ~ (r1_tarski @ X19 @ X18))),
% 0.55/0.74      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.55/0.74  thf('19', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         ((r1_xboole_0 @ X1 @ X0) | ~ (r1_tarski @ X0 @ (sk_C @ X0 @ X1)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['17', '18'])).
% 0.55/0.74  thf('20', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.55/0.74      inference('sup-', [status(thm)], ['16', '19'])).
% 0.55/0.74  thf('21', plain,
% 0.55/0.74      (![X0 : $i, X1 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.55/0.74          | (r1_tarski @ X1 @ (k3_subset_1 @ X0 @ k1_xboole_0)))),
% 0.55/0.74      inference('demod', [status(thm)], ['15', '20'])).
% 0.55/0.74  thf('22', plain,
% 0.55/0.74      (![X0 : $i]: (r1_tarski @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['10', '21'])).
% 0.55/0.74  thf('23', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((r1_tarski @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 0.55/0.74          | ~ (l1_struct_0 @ X0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['7', '22'])).
% 0.55/0.74  thf(dt_k2_struct_0, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( l1_struct_0 @ A ) =>
% 0.55/0.74       ( m1_subset_1 @
% 0.55/0.74         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.55/0.74  thf('24', plain,
% 0.55/0.74      (![X22 : $i]:
% 0.55/0.74         ((m1_subset_1 @ (k2_struct_0 @ X22) @ 
% 0.55/0.74           (k1_zfmisc_1 @ (u1_struct_0 @ X22)))
% 0.55/0.74          | ~ (l1_struct_0 @ X22))),
% 0.55/0.74      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 0.55/0.74  thf('25', plain,
% 0.55/0.74      (![X15 : $i, X16 : $i]:
% 0.55/0.74         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.55/0.74      inference('cnf', [status(esa)], [t3_subset])).
% 0.55/0.74  thf('26', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (l1_struct_0 @ X0)
% 0.55/0.74          | (r1_tarski @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X0)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['24', '25'])).
% 0.55/0.74  thf(d10_xboole_0, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.55/0.74  thf('27', plain,
% 0.55/0.74      (![X4 : $i, X6 : $i]:
% 0.55/0.74         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.55/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.55/0.74  thf('28', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (l1_struct_0 @ X0)
% 0.55/0.74          | ~ (r1_tarski @ (u1_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 0.55/0.74          | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['26', '27'])).
% 0.55/0.74  thf('29', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (l1_struct_0 @ X0)
% 0.55/0.74          | ((u1_struct_0 @ X0) = (k2_struct_0 @ X0))
% 0.55/0.74          | ~ (l1_struct_0 @ X0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['23', '28'])).
% 0.55/0.74  thf('30', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (((u1_struct_0 @ X0) = (k2_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.55/0.74      inference('simplify', [status(thm)], ['29'])).
% 0.55/0.74  thf('31', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (((u1_struct_0 @ X0) = (k2_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.55/0.74      inference('simplify', [status(thm)], ['29'])).
% 0.55/0.74  thf('32', plain, (![X11 : $i]: (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X11))),
% 0.55/0.74      inference('demod', [status(thm)], ['8', '9'])).
% 0.55/0.74  thf(dt_k2_pre_topc, axiom,
% 0.55/0.74    (![A:$i,B:$i]:
% 0.55/0.74     ( ( ( l1_pre_topc @ A ) & 
% 0.55/0.74         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.55/0.74       ( m1_subset_1 @
% 0.55/0.74         ( k2_pre_topc @ A @ B ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 0.55/0.74  thf('33', plain,
% 0.55/0.74      (![X20 : $i, X21 : $i]:
% 0.55/0.74         (~ (l1_pre_topc @ X20)
% 0.55/0.74          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.55/0.74          | (m1_subset_1 @ (k2_pre_topc @ X20 @ X21) @ 
% 0.55/0.74             (k1_zfmisc_1 @ (u1_struct_0 @ X20))))),
% 0.55/0.74      inference('cnf', [status(esa)], [dt_k2_pre_topc])).
% 0.55/0.74  thf('34', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((m1_subset_1 @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 0.55/0.74           (k1_zfmisc_1 @ (u1_struct_0 @ X0)))
% 0.55/0.74          | ~ (l1_pre_topc @ X0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['32', '33'])).
% 0.55/0.74  thf('35', plain,
% 0.55/0.74      (![X15 : $i, X16 : $i]:
% 0.55/0.74         ((r1_tarski @ X15 @ X16) | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 0.55/0.74      inference('cnf', [status(esa)], [t3_subset])).
% 0.55/0.74  thf('36', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (l1_pre_topc @ X0)
% 0.55/0.74          | (r1_tarski @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 0.55/0.74             (u1_struct_0 @ X0)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['34', '35'])).
% 0.55/0.74  thf('37', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((r1_tarski @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 0.55/0.74           (k2_struct_0 @ X0))
% 0.55/0.74          | ~ (l1_struct_0 @ X0)
% 0.55/0.74          | ~ (l1_pre_topc @ X0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['31', '36'])).
% 0.55/0.74  thf(dt_l1_pre_topc, axiom,
% 0.55/0.74    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.55/0.74  thf('38', plain,
% 0.55/0.74      (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.55/0.74      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.55/0.74  thf('39', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (l1_pre_topc @ X0)
% 0.55/0.74          | (r1_tarski @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 0.55/0.74             (k2_struct_0 @ X0)))),
% 0.55/0.74      inference('clc', [status(thm)], ['37', '38'])).
% 0.55/0.74  thf('40', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (((u1_struct_0 @ X0) = (k2_struct_0 @ X0)) | ~ (l1_struct_0 @ X0))),
% 0.55/0.74      inference('simplify', [status(thm)], ['29'])).
% 0.55/0.74  thf('41', plain, (![X11 : $i]: (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X11))),
% 0.55/0.74      inference('demod', [status(thm)], ['8', '9'])).
% 0.55/0.74  thf(t48_pre_topc, axiom,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( l1_pre_topc @ A ) =>
% 0.55/0.74       ( ![B:$i]:
% 0.55/0.74         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.55/0.74           ( r1_tarski @ B @ ( k2_pre_topc @ A @ B ) ) ) ) ))).
% 0.55/0.74  thf('42', plain,
% 0.55/0.74      (![X26 : $i, X27 : $i]:
% 0.55/0.74         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.55/0.74          | (r1_tarski @ X26 @ (k2_pre_topc @ X27 @ X26))
% 0.55/0.74          | ~ (l1_pre_topc @ X27))),
% 0.55/0.74      inference('cnf', [status(esa)], [t48_pre_topc])).
% 0.55/0.74  thf('43', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (l1_pre_topc @ X0)
% 0.55/0.74          | (r1_tarski @ (u1_struct_0 @ X0) @ 
% 0.55/0.74             (k2_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 0.55/0.74      inference('sup-', [status(thm)], ['41', '42'])).
% 0.55/0.74  thf('44', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         ((r1_tarski @ (k2_struct_0 @ X0) @ 
% 0.55/0.74           (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)))
% 0.55/0.74          | ~ (l1_struct_0 @ X0)
% 0.55/0.74          | ~ (l1_pre_topc @ X0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['40', '43'])).
% 0.55/0.74  thf('45', plain,
% 0.55/0.74      (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.55/0.74      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.55/0.74  thf('46', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (l1_pre_topc @ X0)
% 0.55/0.74          | (r1_tarski @ (k2_struct_0 @ X0) @ 
% 0.55/0.74             (k2_pre_topc @ X0 @ (u1_struct_0 @ X0))))),
% 0.55/0.74      inference('clc', [status(thm)], ['44', '45'])).
% 0.55/0.74  thf('47', plain,
% 0.55/0.74      (![X4 : $i, X6 : $i]:
% 0.55/0.74         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.55/0.74      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.55/0.74  thf('48', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (l1_pre_topc @ X0)
% 0.55/0.74          | ~ (r1_tarski @ (k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) @ 
% 0.55/0.74               (k2_struct_0 @ X0))
% 0.55/0.74          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0)))),
% 0.55/0.74      inference('sup-', [status(thm)], ['46', '47'])).
% 0.55/0.74  thf('49', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (l1_pre_topc @ X0)
% 0.55/0.74          | ((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.55/0.74          | ~ (l1_pre_topc @ X0))),
% 0.55/0.74      inference('sup-', [status(thm)], ['39', '48'])).
% 0.55/0.74  thf('50', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (((k2_pre_topc @ X0 @ (u1_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.55/0.74          | ~ (l1_pre_topc @ X0))),
% 0.55/0.74      inference('simplify', [status(thm)], ['49'])).
% 0.55/0.74  thf('51', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (k2_struct_0 @ X0))
% 0.55/0.74          | ~ (l1_struct_0 @ X0)
% 0.55/0.74          | ~ (l1_pre_topc @ X0))),
% 0.55/0.74      inference('sup+', [status(thm)], ['30', '50'])).
% 0.55/0.74  thf('52', plain,
% 0.55/0.74      (![X23 : $i]: ((l1_struct_0 @ X23) | ~ (l1_pre_topc @ X23))),
% 0.55/0.74      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.55/0.74  thf('53', plain,
% 0.55/0.74      (![X0 : $i]:
% 0.55/0.74         (~ (l1_pre_topc @ X0)
% 0.55/0.74          | ((k2_pre_topc @ X0 @ (k2_struct_0 @ X0)) = (k2_struct_0 @ X0)))),
% 0.55/0.74      inference('clc', [status(thm)], ['51', '52'])).
% 0.55/0.74  thf(t27_tops_1, conjecture,
% 0.55/0.74    (![A:$i]:
% 0.55/0.74     ( ( l1_pre_topc @ A ) =>
% 0.55/0.74       ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.55/0.74  thf(zf_stmt_0, negated_conjecture,
% 0.55/0.74    (~( ![A:$i]:
% 0.55/0.74        ( ( l1_pre_topc @ A ) =>
% 0.55/0.74          ( ( k2_pre_topc @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ) )),
% 0.55/0.74    inference('cnf.neg', [status(esa)], [t27_tops_1])).
% 0.55/0.74  thf('54', plain,
% 0.55/0.74      (((k2_pre_topc @ sk_A @ (k2_struct_0 @ sk_A)) != (k2_struct_0 @ sk_A))),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('55', plain,
% 0.55/0.74      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)) | ~ (l1_pre_topc @ sk_A))),
% 0.55/0.74      inference('sup-', [status(thm)], ['53', '54'])).
% 0.55/0.74  thf('56', plain, ((l1_pre_topc @ sk_A)),
% 0.55/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.55/0.74  thf('57', plain, (((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.55/0.74      inference('demod', [status(thm)], ['55', '56'])).
% 0.55/0.74  thf('58', plain, ($false), inference('simplify', [status(thm)], ['57'])).
% 0.55/0.74  
% 0.55/0.74  % SZS output end Refutation
% 0.55/0.74  
% 0.55/0.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
