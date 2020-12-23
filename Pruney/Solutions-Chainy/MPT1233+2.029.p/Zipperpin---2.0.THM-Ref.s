%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8H4bzs9P2q

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:53 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 161 expanded)
%              Number of leaves         :   36 (  64 expanded)
%              Depth                    :   18
%              Number of atoms          :  582 ( 952 expanded)
%              Number of equality atoms :   48 (  93 expanded)
%              Maximal formula depth    :   11 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(fc3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X21: $i] :
      ( ( v1_xboole_0 @ ( k1_struct_0 @ X21 ) )
      | ~ ( l1_struct_0 @ X21 ) ) ),
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
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ( X4 = X5 ) ) ),
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
    ! [X22: $i] :
      ( ( ( k2_struct_0 @ X22 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X22 ) @ ( k1_struct_0 @ X22 ) ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t27_pre_topc])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ k1_xboole_0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['4','5'])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('7',plain,(
    ! [X6: $i] :
      ( ( k1_subset_1 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X10: $i] :
      ( ( k2_subset_1 @ X10 )
      = ( k3_subset_1 @ X10 @ ( k1_subset_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('9',plain,(
    ! [X7: $i] :
      ( ( k2_subset_1 @ X7 )
      = X7 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('10',plain,(
    ! [X10: $i] :
      ( X10
      = ( k3_subset_1 @ X10 @ ( k1_subset_1 @ X10 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

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

thf('14',plain,(
    ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('16',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X6: $i] :
      ( ( k1_subset_1 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('18',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k1_subset_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X4 )
      | ~ ( v1_xboole_0 @ X5 )
      | ( X4 = X5 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_subset_1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X6: $i] :
      ( ( k1_subset_1 @ X6 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('23',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('26',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X19 ) ) )
      | ( v4_pre_topc @ X18 @ X19 )
      | ~ ( v1_xboole_0 @ X18 )
      | ~ ( l1_pre_topc @ X19 )
      | ~ ( v2_pre_topc @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( v4_pre_topc @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ X1 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v2_pre_topc @ sk_A )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','28'])).

thf('30',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
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

thf('33',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X24 ) ) )
      | ~ ( v4_pre_topc @ X23 @ X24 )
      | ( ( k2_pre_topc @ X24 @ X23 )
        = X23 )
      | ~ ( l1_pre_topc @ X24 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('37',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['35','36','37'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('39',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('40',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('43',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('45',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X26 ) ) )
      | ( ( k1_tops_1 @ X26 @ X25 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X26 ) @ ( k2_pre_topc @ X26 @ ( k3_subset_1 @ ( u1_struct_0 @ X26 ) @ X25 ) ) ) )
      | ~ ( l1_pre_topc @ X26 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X11: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('48',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k3_subset_1 @ X9 @ ( k3_subset_1 @ X9 @ X8 ) )
        = X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['46','51'])).

thf('53',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['38','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('55',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k1_tops_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['15','56'])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('59',plain,(
    ! [X20: $i] :
      ( ( l1_struct_0 @ X20 )
      | ~ ( l1_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('60',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','60'])).

thf('62',plain,(
    ( u1_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','61'])).

thf('63',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','62'])).

thf('64',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['58','59'])).

thf('65',plain,(
    ( k2_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    $false ),
    inference(simplify,[status(thm)],['65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8H4bzs9P2q
% 0.15/0.37  % Computer   : n006.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 11:31:53 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 0.40/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.61  % Solved by: fo/fo7.sh
% 0.40/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.61  % done 326 iterations in 0.120s
% 0.40/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.61  % SZS output start Refutation
% 0.40/0.61  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.40/0.61  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.40/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.61  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.40/0.61  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.40/0.61  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.40/0.61  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.40/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.61  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.40/0.61  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.40/0.61  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.40/0.61  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.40/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.61  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.40/0.61  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.40/0.61  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.40/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.61  thf(fc3_struct_0, axiom,
% 0.40/0.61    (![A:$i]: ( ( l1_struct_0 @ A ) => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ))).
% 0.40/0.61  thf('0', plain,
% 0.40/0.61      (![X21 : $i]:
% 0.40/0.61         ((v1_xboole_0 @ (k1_struct_0 @ X21)) | ~ (l1_struct_0 @ X21))),
% 0.40/0.61      inference('cnf', [status(esa)], [fc3_struct_0])).
% 0.40/0.61  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.40/0.61  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.40/0.61  thf(t8_boole, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.40/0.61  thf('2', plain,
% 0.40/0.61      (![X4 : $i, X5 : $i]:
% 0.40/0.61         (~ (v1_xboole_0 @ X4) | ~ (v1_xboole_0 @ X5) | ((X4) = (X5)))),
% 0.40/0.61      inference('cnf', [status(esa)], [t8_boole])).
% 0.40/0.61  thf('3', plain,
% 0.40/0.61      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.61  thf('4', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (l1_struct_0 @ X0) | ((k1_xboole_0) = (k1_struct_0 @ X0)))),
% 0.40/0.61      inference('sup-', [status(thm)], ['0', '3'])).
% 0.40/0.61  thf(t27_pre_topc, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( l1_struct_0 @ A ) =>
% 0.40/0.61       ( ( k2_struct_0 @ A ) =
% 0.40/0.61         ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_struct_0 @ A ) ) ) ))).
% 0.40/0.61  thf('5', plain,
% 0.40/0.61      (![X22 : $i]:
% 0.40/0.61         (((k2_struct_0 @ X22)
% 0.40/0.61            = (k3_subset_1 @ (u1_struct_0 @ X22) @ (k1_struct_0 @ X22)))
% 0.40/0.61          | ~ (l1_struct_0 @ X22))),
% 0.40/0.61      inference('cnf', [status(esa)], [t27_pre_topc])).
% 0.40/0.61  thf('6', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (((k2_struct_0 @ X0)
% 0.40/0.61            = (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0))
% 0.40/0.61          | ~ (l1_struct_0 @ X0)
% 0.40/0.61          | ~ (l1_struct_0 @ X0))),
% 0.40/0.61      inference('sup+', [status(thm)], ['4', '5'])).
% 0.40/0.61  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.40/0.61  thf('7', plain, (![X6 : $i]: ((k1_subset_1 @ X6) = (k1_xboole_0))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.40/0.61  thf(t22_subset_1, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.40/0.61  thf('8', plain,
% 0.40/0.61      (![X10 : $i]:
% 0.40/0.61         ((k2_subset_1 @ X10) = (k3_subset_1 @ X10 @ (k1_subset_1 @ X10)))),
% 0.40/0.61      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.40/0.61  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.40/0.61  thf('9', plain, (![X7 : $i]: ((k2_subset_1 @ X7) = (X7))),
% 0.40/0.61      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.40/0.61  thf('10', plain,
% 0.40/0.61      (![X10 : $i]: ((X10) = (k3_subset_1 @ X10 @ (k1_subset_1 @ X10)))),
% 0.40/0.61      inference('demod', [status(thm)], ['8', '9'])).
% 0.40/0.61  thf('11', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.40/0.61      inference('sup+', [status(thm)], ['7', '10'])).
% 0.40/0.61  thf('12', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0))
% 0.40/0.61          | ~ (l1_struct_0 @ X0)
% 0.40/0.61          | ~ (l1_struct_0 @ X0))),
% 0.40/0.61      inference('demod', [status(thm)], ['6', '11'])).
% 0.40/0.61  thf('13', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (l1_struct_0 @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 0.40/0.61      inference('simplify', [status(thm)], ['12'])).
% 0.40/0.61  thf(t43_tops_1, conjecture,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.61       ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.40/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.61    (~( ![A:$i]:
% 0.40/0.61        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.61          ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ) )),
% 0.40/0.61    inference('cnf.neg', [status(esa)], [t43_tops_1])).
% 0.40/0.61  thf('14', plain,
% 0.40/0.61      (((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) != (k2_struct_0 @ sk_A))),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('15', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (l1_struct_0 @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 0.40/0.61      inference('simplify', [status(thm)], ['12'])).
% 0.40/0.61  thf('16', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('17', plain, (![X6 : $i]: ((k1_subset_1 @ X6) = (k1_xboole_0))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.40/0.61  thf('18', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.40/0.61  thf('19', plain, (![X0 : $i]: (v1_xboole_0 @ (k1_subset_1 @ X0))),
% 0.40/0.61      inference('sup+', [status(thm)], ['17', '18'])).
% 0.40/0.61  thf('20', plain,
% 0.40/0.61      (![X4 : $i, X5 : $i]:
% 0.40/0.61         (~ (v1_xboole_0 @ X4) | ~ (v1_xboole_0 @ X5) | ((X4) = (X5)))),
% 0.40/0.61      inference('cnf', [status(esa)], [t8_boole])).
% 0.40/0.61  thf('21', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (((k1_subset_1 @ X0) = (X1)) | ~ (v1_xboole_0 @ X1))),
% 0.40/0.61      inference('sup-', [status(thm)], ['19', '20'])).
% 0.40/0.61  thf('22', plain, (![X6 : $i]: ((k1_subset_1 @ X6) = (k1_xboole_0))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.40/0.61  thf(t4_subset_1, axiom,
% 0.40/0.61    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.40/0.61  thf('23', plain,
% 0.40/0.61      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.40/0.61      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.40/0.61  thf('24', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (m1_subset_1 @ (k1_subset_1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 0.40/0.61      inference('sup+', [status(thm)], ['22', '23'])).
% 0.40/0.61  thf('25', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | ~ (v1_xboole_0 @ X0))),
% 0.40/0.61      inference('sup+', [status(thm)], ['21', '24'])).
% 0.40/0.61  thf(cc2_pre_topc, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.40/0.61       ( ![B:$i]:
% 0.40/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.61           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.40/0.61  thf('26', plain,
% 0.40/0.61      (![X18 : $i, X19 : $i]:
% 0.40/0.61         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (u1_struct_0 @ X19)))
% 0.40/0.61          | (v4_pre_topc @ X18 @ X19)
% 0.40/0.61          | ~ (v1_xboole_0 @ X18)
% 0.40/0.61          | ~ (l1_pre_topc @ X19)
% 0.40/0.61          | ~ (v2_pre_topc @ X19))),
% 0.40/0.61      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.40/0.61  thf('27', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         (~ (v1_xboole_0 @ X1)
% 0.40/0.61          | ~ (v2_pre_topc @ X0)
% 0.40/0.61          | ~ (l1_pre_topc @ X0)
% 0.40/0.61          | ~ (v1_xboole_0 @ X1)
% 0.40/0.61          | (v4_pre_topc @ X1 @ X0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['25', '26'])).
% 0.40/0.61  thf('28', plain,
% 0.40/0.61      (![X0 : $i, X1 : $i]:
% 0.40/0.61         ((v4_pre_topc @ X1 @ X0)
% 0.40/0.61          | ~ (l1_pre_topc @ X0)
% 0.40/0.61          | ~ (v2_pre_topc @ X0)
% 0.40/0.61          | ~ (v1_xboole_0 @ X1))),
% 0.40/0.61      inference('simplify', [status(thm)], ['27'])).
% 0.40/0.61  thf('29', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (v1_xboole_0 @ X0)
% 0.40/0.61          | ~ (v2_pre_topc @ sk_A)
% 0.40/0.61          | (v4_pre_topc @ X0 @ sk_A))),
% 0.40/0.61      inference('sup-', [status(thm)], ['16', '28'])).
% 0.40/0.61  thf('30', plain, ((v2_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('31', plain,
% 0.40/0.61      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v4_pre_topc @ X0 @ sk_A))),
% 0.40/0.61      inference('demod', [status(thm)], ['29', '30'])).
% 0.40/0.61  thf('32', plain,
% 0.40/0.61      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.40/0.61      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.40/0.61  thf(t52_pre_topc, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( l1_pre_topc @ A ) =>
% 0.40/0.61       ( ![B:$i]:
% 0.40/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.61           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.40/0.61             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.40/0.61               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.40/0.61  thf('33', plain,
% 0.40/0.61      (![X23 : $i, X24 : $i]:
% 0.40/0.61         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (u1_struct_0 @ X24)))
% 0.40/0.61          | ~ (v4_pre_topc @ X23 @ X24)
% 0.40/0.61          | ((k2_pre_topc @ X24 @ X23) = (X23))
% 0.40/0.61          | ~ (l1_pre_topc @ X24))),
% 0.40/0.61      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.40/0.61  thf('34', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (l1_pre_topc @ X0)
% 0.40/0.61          | ((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.40/0.61          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['32', '33'])).
% 0.40/0.61  thf('35', plain,
% 0.40/0.61      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.40/0.61        | ((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))
% 0.40/0.61        | ~ (l1_pre_topc @ sk_A))),
% 0.40/0.61      inference('sup-', [status(thm)], ['31', '34'])).
% 0.40/0.61  thf('36', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.40/0.61  thf('37', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('38', plain, (((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 0.40/0.61      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.40/0.61  thf(d3_tarski, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( r1_tarski @ A @ B ) <=>
% 0.40/0.61       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.40/0.61  thf('39', plain,
% 0.40/0.61      (![X1 : $i, X3 : $i]:
% 0.40/0.61         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.61  thf('40', plain,
% 0.40/0.61      (![X1 : $i, X3 : $i]:
% 0.40/0.61         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.40/0.61      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.61  thf('41', plain,
% 0.40/0.61      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['39', '40'])).
% 0.40/0.61  thf('42', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.40/0.61      inference('simplify', [status(thm)], ['41'])).
% 0.40/0.61  thf(t3_subset, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.40/0.61  thf('43', plain,
% 0.40/0.61      (![X12 : $i, X14 : $i]:
% 0.40/0.61         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.40/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.61  thf('44', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['42', '43'])).
% 0.40/0.61  thf(d1_tops_1, axiom,
% 0.40/0.61    (![A:$i]:
% 0.40/0.61     ( ( l1_pre_topc @ A ) =>
% 0.40/0.61       ( ![B:$i]:
% 0.40/0.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.40/0.61           ( ( k1_tops_1 @ A @ B ) =
% 0.40/0.61             ( k3_subset_1 @
% 0.40/0.61               ( u1_struct_0 @ A ) @ 
% 0.40/0.61               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.40/0.61  thf('45', plain,
% 0.40/0.61      (![X25 : $i, X26 : $i]:
% 0.40/0.61         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (u1_struct_0 @ X26)))
% 0.40/0.61          | ((k1_tops_1 @ X26 @ X25)
% 0.40/0.61              = (k3_subset_1 @ (u1_struct_0 @ X26) @ 
% 0.40/0.61                 (k2_pre_topc @ X26 @ (k3_subset_1 @ (u1_struct_0 @ X26) @ X25))))
% 0.40/0.61          | ~ (l1_pre_topc @ X26))),
% 0.40/0.61      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.40/0.61  thf('46', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (l1_pre_topc @ X0)
% 0.40/0.61          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.40/0.61              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.40/0.61                 (k2_pre_topc @ X0 @ 
% 0.40/0.61                  (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))))))),
% 0.40/0.61      inference('sup-', [status(thm)], ['44', '45'])).
% 0.40/0.61  thf('47', plain,
% 0.40/0.61      (![X11 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X11))),
% 0.40/0.61      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.40/0.61  thf(involutiveness_k3_subset_1, axiom,
% 0.40/0.61    (![A:$i,B:$i]:
% 0.40/0.61     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.40/0.61       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.40/0.61  thf('48', plain,
% 0.40/0.61      (![X8 : $i, X9 : $i]:
% 0.40/0.61         (((k3_subset_1 @ X9 @ (k3_subset_1 @ X9 @ X8)) = (X8))
% 0.40/0.61          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.40/0.61      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.40/0.61  thf('49', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.40/0.61      inference('sup-', [status(thm)], ['47', '48'])).
% 0.40/0.61  thf('50', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.40/0.61      inference('sup+', [status(thm)], ['7', '10'])).
% 0.40/0.61  thf('51', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.40/0.61      inference('demod', [status(thm)], ['49', '50'])).
% 0.40/0.61  thf('52', plain,
% 0.40/0.61      (![X0 : $i]:
% 0.40/0.61         (~ (l1_pre_topc @ X0)
% 0.40/0.61          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.40/0.61              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.40/0.61                 (k2_pre_topc @ X0 @ k1_xboole_0))))),
% 0.40/0.61      inference('demod', [status(thm)], ['46', '51'])).
% 0.40/0.61  thf('53', plain,
% 0.40/0.61      ((((k1_tops_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 0.40/0.61          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0))
% 0.40/0.61        | ~ (l1_pre_topc @ sk_A))),
% 0.40/0.61      inference('sup+', [status(thm)], ['38', '52'])).
% 0.40/0.61  thf('54', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.40/0.61      inference('sup+', [status(thm)], ['7', '10'])).
% 0.40/0.61  thf('55', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf('56', plain,
% 0.40/0.61      (((k1_tops_1 @ sk_A @ (u1_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))),
% 0.40/0.61      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.40/0.61  thf('57', plain,
% 0.40/0.61      ((((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))
% 0.40/0.61        | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.61      inference('sup+', [status(thm)], ['15', '56'])).
% 0.40/0.61  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.40/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.61  thf(dt_l1_pre_topc, axiom,
% 0.40/0.61    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.40/0.61  thf('59', plain,
% 0.40/0.61      (![X20 : $i]: ((l1_struct_0 @ X20) | ~ (l1_pre_topc @ X20))),
% 0.40/0.61      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.40/0.61  thf('60', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.61      inference('sup-', [status(thm)], ['58', '59'])).
% 0.40/0.61  thf('61', plain,
% 0.40/0.61      (((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))),
% 0.40/0.61      inference('demod', [status(thm)], ['57', '60'])).
% 0.40/0.61  thf('62', plain, (((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.40/0.61      inference('demod', [status(thm)], ['14', '61'])).
% 0.40/0.61  thf('63', plain,
% 0.40/0.61      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.40/0.61      inference('sup-', [status(thm)], ['13', '62'])).
% 0.40/0.61  thf('64', plain, ((l1_struct_0 @ sk_A)),
% 0.40/0.61      inference('sup-', [status(thm)], ['58', '59'])).
% 0.40/0.61  thf('65', plain, (((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.40/0.61      inference('demod', [status(thm)], ['63', '64'])).
% 0.40/0.61  thf('66', plain, ($false), inference('simplify', [status(thm)], ['65'])).
% 0.40/0.61  
% 0.40/0.61  % SZS output end Refutation
% 0.40/0.61  
% 0.40/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
