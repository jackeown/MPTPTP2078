%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2XxAswKdrU

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:50 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 242 expanded)
%              Number of leaves         :   34 (  90 expanded)
%              Depth                    :   18
%              Number of atoms          :  721 (1657 expanded)
%              Number of equality atoms :   43 ( 104 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(fc3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X22: $i] :
      ( ( v1_xboole_0 @ ( k1_struct_0 @ X22 ) )
      | ~ ( l1_struct_0 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc3_struct_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k1_struct_0 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t27_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_struct_0 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X23: $i] :
      ( ( ( k2_struct_0 @ X23 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X23 ) @ ( k1_struct_0 @ X23 ) ) )
      | ~ ( l1_struct_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t27_pre_topc])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_struct_0 @ X1 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X1 ) @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_struct_0 @ X1 )
      | ~ ( l1_struct_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_struct_0 @ X1 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_struct_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_struct_0 @ X1 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X1 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('7',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('8',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

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

thf('10',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('12',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X20 ) ) )
      | ( v4_pre_topc @ X19 @ X20 )
      | ~ ( v1_xboole_0 @ X19 )
      | ~ ( l1_pre_topc @ X20 )
      | ~ ( v2_pre_topc @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['10','17'])).

thf('19',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
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

thf('22',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X25 ) ) )
      | ~ ( v4_pre_topc @ X24 @ X25 )
      | ( ( k2_pre_topc @ X25 @ X24 )
        = X24 )
      | ~ ( l1_pre_topc @ X25 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('26',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( ( k2_pre_topc @ sk_A @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','27'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('29',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X6 ) @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('30',plain,(
    ! [X5: $i] :
      ( ( k2_subset_1 @ X5 )
      = X5 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('31',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('32',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X27 ) ) )
      | ( ( k1_tops_1 @ X27 @ X26 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X27 ) @ ( k2_pre_topc @ X27 @ ( k3_subset_1 @ ( u1_struct_0 @ X27 ) @ X26 ) ) ) )
      | ~ ( l1_pre_topc @ X27 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('35',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t36_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C )
           => ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) )).

thf('36',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( r1_tarski @ ( k3_subset_1 @ X10 @ X9 ) @ X11 )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X10 @ X11 ) @ X9 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t36_subset_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ k1_xboole_0 )
      | ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('40',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X7 @ X8 ) @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('42',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_subset_1 @ X0 @ X0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('46',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('47',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['33','50'])).

thf('52',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['28','51'])).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('54',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( k1_tops_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(projectivity_k1_tops_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( l1_pre_topc @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) )
     => ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) )
        = ( k1_tops_1 @ A @ B ) ) ) )).

thf('57',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( l1_pre_topc @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( ( k1_tops_1 @ X28 @ ( k1_tops_1 @ X28 @ X29 ) )
        = ( k1_tops_1 @ X28 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[projectivity_k1_tops_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k1_tops_1 @ X0 @ ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
        = ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) )
      = ( k1_tops_1 @ sk_A @ ( u1_struct_0 @ sk_A ) ) )
    | ~ ( l1_pre_topc @ sk_A ) ),
    inference('sup+',[status(thm)],['55','58'])).

thf('60',plain,
    ( ( k1_tops_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('61',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( k1_tops_1 @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['6','62'])).

thf('64',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('65',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('66',plain,(
    ! [X21: $i] :
      ( ( l1_struct_0 @ X21 )
      | ~ ( l1_pre_topc @ X21 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('67',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','64','67'])).

thf('69',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = ( k2_struct_0 @ sk_A ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['5','68'])).

thf('70',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('71',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['65','66'])).

thf('72',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['72','73'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2XxAswKdrU
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:43:47 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.76/0.93  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/0.93  % Solved by: fo/fo7.sh
% 0.76/0.93  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.93  % done 1183 iterations in 0.472s
% 0.76/0.93  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/0.93  % SZS output start Refutation
% 0.76/0.93  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.93  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.76/0.93  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.76/0.93  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/0.93  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.76/0.93  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.76/0.93  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.76/0.93  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.76/0.93  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.93  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 0.76/0.93  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.93  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.76/0.93  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.76/0.93  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.76/0.93  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.76/0.93  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.76/0.93  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.93  thf(fc3_struct_0, axiom,
% 0.76/0.93    (![A:$i]: ( ( l1_struct_0 @ A ) => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ))).
% 0.76/0.93  thf('0', plain,
% 0.76/0.93      (![X22 : $i]:
% 0.76/0.93         ((v1_xboole_0 @ (k1_struct_0 @ X22)) | ~ (l1_struct_0 @ X22))),
% 0.76/0.93      inference('cnf', [status(esa)], [fc3_struct_0])).
% 0.76/0.93  thf(t8_boole, axiom,
% 0.76/0.93    (![A:$i,B:$i]:
% 0.76/0.93     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.76/0.93  thf('1', plain,
% 0.76/0.93      (![X3 : $i, X4 : $i]:
% 0.76/0.93         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 0.76/0.93      inference('cnf', [status(esa)], [t8_boole])).
% 0.76/0.93  thf('2', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         (~ (l1_struct_0 @ X0)
% 0.76/0.93          | ((k1_struct_0 @ X0) = (X1))
% 0.76/0.93          | ~ (v1_xboole_0 @ X1))),
% 0.76/0.93      inference('sup-', [status(thm)], ['0', '1'])).
% 0.76/0.93  thf(t27_pre_topc, axiom,
% 0.76/0.93    (![A:$i]:
% 0.76/0.93     ( ( l1_struct_0 @ A ) =>
% 0.76/0.93       ( ( k2_struct_0 @ A ) =
% 0.76/0.93         ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_struct_0 @ A ) ) ) ))).
% 0.76/0.93  thf('3', plain,
% 0.76/0.93      (![X23 : $i]:
% 0.76/0.93         (((k2_struct_0 @ X23)
% 0.76/0.93            = (k3_subset_1 @ (u1_struct_0 @ X23) @ (k1_struct_0 @ X23)))
% 0.76/0.93          | ~ (l1_struct_0 @ X23))),
% 0.76/0.93      inference('cnf', [status(esa)], [t27_pre_topc])).
% 0.76/0.93  thf('4', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         (((k2_struct_0 @ X1) = (k3_subset_1 @ (u1_struct_0 @ X1) @ X0))
% 0.76/0.93          | ~ (v1_xboole_0 @ X0)
% 0.76/0.93          | ~ (l1_struct_0 @ X1)
% 0.76/0.93          | ~ (l1_struct_0 @ X1))),
% 0.76/0.93      inference('sup+', [status(thm)], ['2', '3'])).
% 0.76/0.93  thf('5', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         (~ (l1_struct_0 @ X1)
% 0.76/0.93          | ~ (v1_xboole_0 @ X0)
% 0.76/0.93          | ((k2_struct_0 @ X1) = (k3_subset_1 @ (u1_struct_0 @ X1) @ X0)))),
% 0.76/0.93      inference('simplify', [status(thm)], ['4'])).
% 0.76/0.93  thf('6', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         (~ (l1_struct_0 @ X1)
% 0.76/0.93          | ~ (v1_xboole_0 @ X0)
% 0.76/0.93          | ((k2_struct_0 @ X1) = (k3_subset_1 @ (u1_struct_0 @ X1) @ X0)))),
% 0.76/0.93      inference('simplify', [status(thm)], ['4'])).
% 0.76/0.93  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.76/0.93  thf('7', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/0.93      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/0.93  thf('8', plain,
% 0.76/0.93      (![X3 : $i, X4 : $i]:
% 0.76/0.93         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 0.76/0.93      inference('cnf', [status(esa)], [t8_boole])).
% 0.76/0.93  thf('9', plain,
% 0.76/0.93      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.76/0.93      inference('sup-', [status(thm)], ['7', '8'])).
% 0.76/0.93  thf(t43_tops_1, conjecture,
% 0.76/0.93    (![A:$i]:
% 0.76/0.93     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.93       ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.76/0.93  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.93    (~( ![A:$i]:
% 0.76/0.93        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.93          ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ) )),
% 0.76/0.93    inference('cnf.neg', [status(esa)], [t43_tops_1])).
% 0.76/0.93  thf('10', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.93  thf('11', plain,
% 0.76/0.93      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.76/0.93      inference('sup-', [status(thm)], ['7', '8'])).
% 0.76/0.93  thf(t4_subset_1, axiom,
% 0.76/0.93    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.76/0.93  thf('12', plain,
% 0.76/0.93      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.76/0.93      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.76/0.93  thf(cc2_pre_topc, axiom,
% 0.76/0.93    (![A:$i]:
% 0.76/0.93     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.76/0.93       ( ![B:$i]:
% 0.76/0.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.93           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.76/0.93  thf('13', plain,
% 0.76/0.93      (![X19 : $i, X20 : $i]:
% 0.76/0.93         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (u1_struct_0 @ X20)))
% 0.76/0.93          | (v4_pre_topc @ X19 @ X20)
% 0.76/0.93          | ~ (v1_xboole_0 @ X19)
% 0.76/0.93          | ~ (l1_pre_topc @ X20)
% 0.76/0.93          | ~ (v2_pre_topc @ X20))),
% 0.76/0.93      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.76/0.93  thf('14', plain,
% 0.76/0.93      (![X0 : $i]:
% 0.76/0.93         (~ (v2_pre_topc @ X0)
% 0.76/0.93          | ~ (l1_pre_topc @ X0)
% 0.76/0.93          | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.76/0.93          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.76/0.93      inference('sup-', [status(thm)], ['12', '13'])).
% 0.76/0.93  thf('15', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/0.93      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/0.93  thf('16', plain,
% 0.76/0.93      (![X0 : $i]:
% 0.76/0.93         (~ (v2_pre_topc @ X0)
% 0.76/0.93          | ~ (l1_pre_topc @ X0)
% 0.76/0.93          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.76/0.93      inference('demod', [status(thm)], ['14', '15'])).
% 0.76/0.93  thf('17', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         ((v4_pre_topc @ X0 @ X1)
% 0.76/0.93          | ~ (v1_xboole_0 @ X0)
% 0.76/0.93          | ~ (l1_pre_topc @ X1)
% 0.76/0.93          | ~ (v2_pre_topc @ X1))),
% 0.76/0.93      inference('sup+', [status(thm)], ['11', '16'])).
% 0.76/0.93  thf('18', plain,
% 0.76/0.93      (![X0 : $i]:
% 0.76/0.93         (~ (v2_pre_topc @ sk_A)
% 0.76/0.93          | ~ (v1_xboole_0 @ X0)
% 0.76/0.93          | (v4_pre_topc @ X0 @ sk_A))),
% 0.76/0.93      inference('sup-', [status(thm)], ['10', '17'])).
% 0.76/0.93  thf('19', plain, ((v2_pre_topc @ sk_A)),
% 0.76/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.93  thf('20', plain,
% 0.76/0.93      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v4_pre_topc @ X0 @ sk_A))),
% 0.76/0.93      inference('demod', [status(thm)], ['18', '19'])).
% 0.76/0.93  thf('21', plain,
% 0.76/0.93      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.76/0.93      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.76/0.93  thf(t52_pre_topc, axiom,
% 0.76/0.93    (![A:$i]:
% 0.76/0.93     ( ( l1_pre_topc @ A ) =>
% 0.76/0.93       ( ![B:$i]:
% 0.76/0.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.93           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.76/0.93             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.76/0.93               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.76/0.93  thf('22', plain,
% 0.76/0.93      (![X24 : $i, X25 : $i]:
% 0.76/0.93         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (u1_struct_0 @ X25)))
% 0.76/0.93          | ~ (v4_pre_topc @ X24 @ X25)
% 0.76/0.93          | ((k2_pre_topc @ X25 @ X24) = (X24))
% 0.76/0.93          | ~ (l1_pre_topc @ X25))),
% 0.76/0.93      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.76/0.93  thf('23', plain,
% 0.76/0.93      (![X0 : $i]:
% 0.76/0.93         (~ (l1_pre_topc @ X0)
% 0.76/0.93          | ((k2_pre_topc @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.76/0.93          | ~ (v4_pre_topc @ k1_xboole_0 @ X0))),
% 0.76/0.93      inference('sup-', [status(thm)], ['21', '22'])).
% 0.76/0.93  thf('24', plain,
% 0.76/0.93      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.76/0.93        | ((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))
% 0.76/0.93        | ~ (l1_pre_topc @ sk_A))),
% 0.76/0.93      inference('sup-', [status(thm)], ['20', '23'])).
% 0.76/0.93  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/0.93      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/0.93  thf('26', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.93      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.93  thf('27', plain, (((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 0.76/0.93      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.76/0.93  thf('28', plain,
% 0.76/0.93      (![X0 : $i]:
% 0.76/0.93         (((k2_pre_topc @ sk_A @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.76/0.93      inference('sup+', [status(thm)], ['9', '27'])).
% 0.76/0.93  thf(dt_k2_subset_1, axiom,
% 0.76/0.93    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.76/0.93  thf('29', plain,
% 0.76/0.93      (![X6 : $i]: (m1_subset_1 @ (k2_subset_1 @ X6) @ (k1_zfmisc_1 @ X6))),
% 0.76/0.93      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.76/0.93  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.76/0.93  thf('30', plain, (![X5 : $i]: ((k2_subset_1 @ X5) = (X5))),
% 0.76/0.93      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.76/0.93  thf('31', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 0.76/0.93      inference('demod', [status(thm)], ['29', '30'])).
% 0.76/0.93  thf(d1_tops_1, axiom,
% 0.76/0.93    (![A:$i]:
% 0.76/0.93     ( ( l1_pre_topc @ A ) =>
% 0.76/0.93       ( ![B:$i]:
% 0.76/0.93         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.76/0.93           ( ( k1_tops_1 @ A @ B ) =
% 0.76/0.93             ( k3_subset_1 @
% 0.76/0.93               ( u1_struct_0 @ A ) @ 
% 0.76/0.93               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.76/0.93  thf('32', plain,
% 0.76/0.93      (![X26 : $i, X27 : $i]:
% 0.76/0.93         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (u1_struct_0 @ X27)))
% 0.76/0.93          | ((k1_tops_1 @ X27 @ X26)
% 0.76/0.93              = (k3_subset_1 @ (u1_struct_0 @ X27) @ 
% 0.76/0.93                 (k2_pre_topc @ X27 @ (k3_subset_1 @ (u1_struct_0 @ X27) @ X26))))
% 0.76/0.93          | ~ (l1_pre_topc @ X27))),
% 0.76/0.93      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.76/0.93  thf('33', plain,
% 0.76/0.93      (![X0 : $i]:
% 0.76/0.93         (~ (l1_pre_topc @ X0)
% 0.76/0.93          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.76/0.93              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.76/0.93                 (k2_pre_topc @ X0 @ 
% 0.76/0.93                  (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))))))),
% 0.76/0.93      inference('sup-', [status(thm)], ['31', '32'])).
% 0.76/0.93  thf('34', plain,
% 0.76/0.93      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.76/0.93      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.76/0.93  thf('35', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 0.76/0.93      inference('demod', [status(thm)], ['29', '30'])).
% 0.76/0.93  thf(t36_subset_1, axiom,
% 0.76/0.93    (![A:$i,B:$i]:
% 0.76/0.93     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.93       ( ![C:$i]:
% 0.76/0.93         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.93           ( ( r1_tarski @ ( k3_subset_1 @ A @ B ) @ C ) =>
% 0.76/0.93             ( r1_tarski @ ( k3_subset_1 @ A @ C ) @ B ) ) ) ) ))).
% 0.76/0.93  thf('36', plain,
% 0.76/0.93      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.76/0.93         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.76/0.93          | (r1_tarski @ (k3_subset_1 @ X10 @ X9) @ X11)
% 0.76/0.93          | ~ (r1_tarski @ (k3_subset_1 @ X10 @ X11) @ X9)
% 0.76/0.93          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X10)))),
% 0.76/0.93      inference('cnf', [status(esa)], [t36_subset_1])).
% 0.76/0.93  thf('37', plain,
% 0.76/0.93      (![X0 : $i, X1 : $i]:
% 0.76/0.93         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.76/0.93          | ~ (r1_tarski @ (k3_subset_1 @ X0 @ X1) @ X0)
% 0.76/0.93          | (r1_tarski @ (k3_subset_1 @ X0 @ X0) @ X1))),
% 0.76/0.93      inference('sup-', [status(thm)], ['35', '36'])).
% 0.76/0.93  thf('38', plain,
% 0.76/0.93      (![X0 : $i]:
% 0.76/0.93         ((r1_tarski @ (k3_subset_1 @ X0 @ X0) @ k1_xboole_0)
% 0.76/0.93          | ~ (r1_tarski @ (k3_subset_1 @ X0 @ k1_xboole_0) @ X0))),
% 0.76/0.93      inference('sup-', [status(thm)], ['34', '37'])).
% 0.76/0.93  thf('39', plain,
% 0.76/0.93      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.76/0.93      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.76/0.93  thf(dt_k3_subset_1, axiom,
% 0.76/0.93    (![A:$i,B:$i]:
% 0.76/0.93     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.76/0.93       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.76/0.93  thf('40', plain,
% 0.76/0.93      (![X7 : $i, X8 : $i]:
% 0.76/0.93         ((m1_subset_1 @ (k3_subset_1 @ X7 @ X8) @ (k1_zfmisc_1 @ X7))
% 0.76/0.93          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X7)))),
% 0.76/0.93      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.76/0.93  thf('41', plain,
% 0.76/0.93      (![X0 : $i]:
% 0.76/0.93         (m1_subset_1 @ (k3_subset_1 @ X0 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.76/0.93      inference('sup-', [status(thm)], ['39', '40'])).
% 0.76/0.93  thf(t3_subset, axiom,
% 0.76/0.93    (![A:$i,B:$i]:
% 0.76/0.93     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.76/0.93  thf('42', plain,
% 0.76/0.93      (![X13 : $i, X14 : $i]:
% 0.76/0.93         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.76/0.93      inference('cnf', [status(esa)], [t3_subset])).
% 0.76/0.93  thf('43', plain,
% 0.76/0.93      (![X0 : $i]: (r1_tarski @ (k3_subset_1 @ X0 @ k1_xboole_0) @ X0)),
% 0.76/0.93      inference('sup-', [status(thm)], ['41', '42'])).
% 0.76/0.93  thf('44', plain,
% 0.76/0.93      (![X0 : $i]: (r1_tarski @ (k3_subset_1 @ X0 @ X0) @ k1_xboole_0)),
% 0.76/0.93      inference('demod', [status(thm)], ['38', '43'])).
% 0.76/0.93  thf('45', plain,
% 0.76/0.93      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.76/0.93      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.76/0.93  thf('46', plain,
% 0.76/0.93      (![X13 : $i, X14 : $i]:
% 0.76/0.93         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.76/0.93      inference('cnf', [status(esa)], [t3_subset])).
% 0.76/0.94  thf('47', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.76/0.94      inference('sup-', [status(thm)], ['45', '46'])).
% 0.76/0.94  thf(d10_xboole_0, axiom,
% 0.76/0.94    (![A:$i,B:$i]:
% 0.76/0.94     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.76/0.94  thf('48', plain,
% 0.76/0.94      (![X0 : $i, X2 : $i]:
% 0.76/0.94         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.76/0.94      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.76/0.94  thf('49', plain,
% 0.76/0.94      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.76/0.94      inference('sup-', [status(thm)], ['47', '48'])).
% 0.76/0.94  thf('50', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.76/0.94      inference('sup-', [status(thm)], ['44', '49'])).
% 0.76/0.94  thf('51', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (~ (l1_pre_topc @ X0)
% 0.76/0.94          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.76/0.94              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.76/0.94                 (k2_pre_topc @ X0 @ k1_xboole_0))))),
% 0.76/0.94      inference('demod', [status(thm)], ['33', '50'])).
% 0.76/0.94  thf('52', plain,
% 0.76/0.94      ((((k1_tops_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 0.76/0.94          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0))
% 0.76/0.94        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.76/0.94        | ~ (l1_pre_topc @ sk_A))),
% 0.76/0.94      inference('sup+', [status(thm)], ['28', '51'])).
% 0.76/0.94  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/0.94      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/0.94  thf('54', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('55', plain,
% 0.76/0.94      (((k1_tops_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 0.76/0.94         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.76/0.94      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.76/0.94  thf('56', plain, (![X6 : $i]: (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X6))),
% 0.76/0.94      inference('demod', [status(thm)], ['29', '30'])).
% 0.76/0.94  thf(projectivity_k1_tops_1, axiom,
% 0.76/0.94    (![A:$i,B:$i]:
% 0.76/0.94     ( ( ( l1_pre_topc @ A ) & 
% 0.76/0.94         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) =>
% 0.76/0.94       ( ( k1_tops_1 @ A @ ( k1_tops_1 @ A @ B ) ) = ( k1_tops_1 @ A @ B ) ) ))).
% 0.76/0.94  thf('57', plain,
% 0.76/0.94      (![X28 : $i, X29 : $i]:
% 0.76/0.94         (~ (l1_pre_topc @ X28)
% 0.76/0.94          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.76/0.94          | ((k1_tops_1 @ X28 @ (k1_tops_1 @ X28 @ X29))
% 0.76/0.94              = (k1_tops_1 @ X28 @ X29)))),
% 0.76/0.94      inference('cnf', [status(esa)], [projectivity_k1_tops_1])).
% 0.76/0.94  thf('58', plain,
% 0.76/0.94      (![X0 : $i]:
% 0.76/0.94         (((k1_tops_1 @ X0 @ (k1_tops_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.76/0.94            = (k1_tops_1 @ X0 @ (u1_struct_0 @ X0)))
% 0.76/0.94          | ~ (l1_pre_topc @ X0))),
% 0.76/0.94      inference('sup-', [status(thm)], ['56', '57'])).
% 0.76/0.94  thf('59', plain,
% 0.76/0.94      ((((k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0))
% 0.76/0.94          = (k1_tops_1 @ sk_A @ (u1_struct_0 @ sk_A)))
% 0.76/0.94        | ~ (l1_pre_topc @ sk_A))),
% 0.76/0.94      inference('sup+', [status(thm)], ['55', '58'])).
% 0.76/0.94  thf('60', plain,
% 0.76/0.94      (((k1_tops_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 0.76/0.94         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.76/0.94      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.76/0.94  thf('61', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('62', plain,
% 0.76/0.94      (((k1_tops_1 @ sk_A @ (k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0))
% 0.76/0.94         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.76/0.94      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.76/0.94  thf('63', plain,
% 0.76/0.94      ((((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A))
% 0.76/0.94          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0))
% 0.76/0.94        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.76/0.94        | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.94      inference('sup+', [status(thm)], ['6', '62'])).
% 0.76/0.94  thf('64', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/0.94      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/0.94  thf('65', plain, ((l1_pre_topc @ sk_A)),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf(dt_l1_pre_topc, axiom,
% 0.76/0.94    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.76/0.94  thf('66', plain,
% 0.76/0.94      (![X21 : $i]: ((l1_struct_0 @ X21) | ~ (l1_pre_topc @ X21))),
% 0.76/0.94      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.76/0.94  thf('67', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.94      inference('sup-', [status(thm)], ['65', '66'])).
% 0.76/0.94  thf('68', plain,
% 0.76/0.94      (((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A))
% 0.76/0.94         = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ k1_xboole_0))),
% 0.76/0.94      inference('demod', [status(thm)], ['63', '64', '67'])).
% 0.76/0.94  thf('69', plain,
% 0.76/0.94      ((((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) = (k2_struct_0 @ sk_A))
% 0.76/0.94        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.76/0.94        | ~ (l1_struct_0 @ sk_A))),
% 0.76/0.94      inference('sup+', [status(thm)], ['5', '68'])).
% 0.76/0.94  thf('70', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/0.94      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/0.94  thf('71', plain, ((l1_struct_0 @ sk_A)),
% 0.76/0.94      inference('sup-', [status(thm)], ['65', '66'])).
% 0.76/0.94  thf('72', plain,
% 0.76/0.94      (((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) = (k2_struct_0 @ sk_A))),
% 0.76/0.94      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.76/0.94  thf('73', plain,
% 0.76/0.94      (((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) != (k2_struct_0 @ sk_A))),
% 0.76/0.94      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.94  thf('74', plain, ($false),
% 0.76/0.94      inference('simplify_reflect-', [status(thm)], ['72', '73'])).
% 0.76/0.94  
% 0.76/0.94  % SZS output end Refutation
% 0.76/0.94  
% 0.76/0.94  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
