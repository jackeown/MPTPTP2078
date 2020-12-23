%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MIvHZdge9J

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:53 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :  155 ( 900 expanded)
%              Number of leaves         :   43 ( 297 expanded)
%              Depth                    :   37
%              Number of atoms          : 1016 (6022 expanded)
%              Number of equality atoms :   83 ( 572 expanded)
%              Maximal formula depth    :   16 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(k1_struct_0_type,type,(
    k1_struct_0: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(fc3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X34: $i] :
      ( ( v1_xboole_0 @ ( k1_struct_0 @ X34 ) )
      | ~ ( l1_struct_0 @ X34 ) ) ),
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
    ! [X35: $i] :
      ( ( ( k2_struct_0 @ X35 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X35 ) @ ( k1_struct_0 @ X35 ) ) )
      | ~ ( l1_struct_0 @ X35 ) ) ),
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
    ! [X11: $i] :
      ( ( k1_subset_1 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('8',plain,(
    ! [X19: $i] :
      ( ( k2_subset_1 @ X19 )
      = ( k3_subset_1 @ X19 @ ( k1_subset_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('9',plain,(
    ! [X12: $i] :
      ( ( k2_subset_1 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('10',plain,(
    ! [X19: $i] :
      ( X19
      = ( k3_subset_1 @ X19 @ ( k1_subset_1 @ X19 ) ) ) ),
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
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(dt_k2_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( m1_subset_1 @ ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ) )).

thf('17',plain,(
    ! [X32: $i] :
      ( ( m1_subset_1 @ ( k2_struct_0 @ X32 ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( l1_struct_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_struct_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r1_tarski @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_struct_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( r1_tarski @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('23',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('24',plain,(
    ! [X0: $i,X2: $i] :
      ( ( ( k6_subset_1 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k6_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k6_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('29',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('31',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t29_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) )).

thf('32',plain,(
    ! [X26: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X26 ) @ X26 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(dt_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('33',plain,(
    ! [X13: $i,X14: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('34',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ~ ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k6_subset_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_subset_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k4_xboole_0 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('39',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k6_subset_1 @ X17 @ X18 )
      = ( k4_xboole_0 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k6_subset_1 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('45',plain,(
    ! [X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X31 ) ) )
      | ( v4_pre_topc @ X30 @ X31 )
      | ~ ( v1_xboole_0 @ X30 )
      | ~ ( l1_pre_topc @ X31 )
      | ~ ( v2_pre_topc @ X31 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_pre_topc @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference('sup+',[status(thm)],['30','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','49'])).

thf('51',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v4_pre_topc @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X13: $i,X14: $i] :
      ( m1_subset_1 @ ( k6_subset_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_subset_1])).

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

thf('54',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X37 ) ) )
      | ~ ( v4_pre_topc @ X36 @ X37 )
      | ( ( k2_pre_topc @ X37 @ X36 )
        = X36 )
      | ~ ( l1_pre_topc @ X37 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k6_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) )
        = ( k6_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) )
      | ~ ( v4_pre_topc @ ( k6_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( ( k2_pre_topc @ sk_A @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
        = ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( l1_pre_topc @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
      | ( ( k2_pre_topc @ sk_A @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
        = ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k6_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 ) )
      | ~ ( l1_struct_0 @ sk_A )
      | ( ( k2_pre_topc @ sk_A @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
        = ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['28','58'])).

thf('60',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('61',plain,(
    ! [X33: $i] :
      ( ( l1_struct_0 @ X33 )
      | ~ ( l1_pre_topc @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('62',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k6_subset_1 @ ( k2_struct_0 @ sk_A ) @ X0 ) )
      | ( ( k2_pre_topc @ sk_A @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) )
        = ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A )
    | ( ( k2_pre_topc @ sk_A @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
      = ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['27','63'])).

thf('65',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('66',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['60','61'])).

thf('67',plain,
    ( ( k2_pre_topc @ sk_A @ ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
    = ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( ( ( k2_pre_topc @ sk_A @ ( k6_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
      = ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['26','67'])).

thf('69',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['60','61'])).

thf('70',plain,
    ( ( k2_pre_topc @ sk_A @ ( k6_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
    = ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
      = ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['25','70'])).

thf('72',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['60','61'])).

thf('73',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k6_subset_1 @ X0 @ X1 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('75',plain,
    ( ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k6_subset_1 @ ( k2_struct_0 @ X0 ) @ ( k2_struct_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','24'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('78',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = ( k6_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('79',plain,
    ( ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
      = ( k6_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['60','61'])).

thf('81',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = ( k6_subset_1 @ ( k2_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,
    ( ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['76','81'])).

thf('83',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['60','61'])).

thf('84',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['75','84'])).

thf('86',plain,(
    r1_tarski @ ( u1_struct_0 @ sk_A ) @ ( k2_struct_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X20: $i,X22: $i] :
      ( ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( r1_tarski @ X20 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('88',plain,(
    m1_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_struct_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( l1_struct_0 @ X0 )
      | ( ( k2_struct_0 @ X0 )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('90',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X39 ) ) )
      | ( ( k1_tops_1 @ X39 @ X38 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X39 ) @ ( k2_pre_topc @ X39 @ ( k3_subset_1 @ ( u1_struct_0 @ X39 ) @ X38 ) ) ) )
      | ~ ( l1_pre_topc @ X39 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_struct_0 @ X0 ) ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ X1 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ X1 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
      = ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( k2_pre_topc @ sk_A @ ( k3_subset_1 @ ( u1_struct_0 @ sk_A ) @ ( u1_struct_0 @ sk_A ) ) ) ) )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('94',plain,(
    ! [X15: $i,X16: $i] :
      ( ( ( k3_subset_1 @ X16 @ ( k3_subset_1 @ X16 @ X15 ) )
        = X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( k2_pre_topc @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['82','83'])).

thf('99',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['7','10'])).

thf('100',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['60','61'])).

thf('102',plain,
    ( ( k1_tops_1 @ sk_A @ ( u1_struct_0 @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['92','97','98','99','100','101'])).

thf('103',plain,
    ( ( ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
      = ( u1_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup+',[status(thm)],['15','102'])).

thf('104',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['60','61'])).

thf('105',plain,
    ( ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
    = ( u1_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['103','104'])).

thf('106',plain,(
    ( u1_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['14','105'])).

thf('107',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','106'])).

thf('108',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['60','61'])).

thf('109',plain,(
    ( k2_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    $false ),
    inference(simplify,[status(thm)],['109'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MIvHZdge9J
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:16:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.06/1.26  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.06/1.26  % Solved by: fo/fo7.sh
% 1.06/1.26  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.26  % done 1921 iterations in 0.793s
% 1.06/1.26  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.06/1.26  % SZS output start Refutation
% 1.06/1.26  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.06/1.26  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 1.06/1.26  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.06/1.26  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.06/1.26  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 1.06/1.26  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.06/1.26  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 1.06/1.26  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 1.06/1.26  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 1.06/1.26  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 1.06/1.26  thf(k1_struct_0_type, type, k1_struct_0: $i > $i).
% 1.06/1.26  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 1.06/1.26  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.06/1.26  thf(sk_B_type, type, sk_B: $i > $i).
% 1.06/1.26  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 1.06/1.26  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.06/1.26  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 1.06/1.26  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.06/1.26  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.06/1.26  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 1.06/1.26  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 1.06/1.26  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.26  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.06/1.26  thf(fc3_struct_0, axiom,
% 1.06/1.26    (![A:$i]: ( ( l1_struct_0 @ A ) => ( v1_xboole_0 @ ( k1_struct_0 @ A ) ) ))).
% 1.06/1.26  thf('0', plain,
% 1.06/1.26      (![X34 : $i]:
% 1.06/1.26         ((v1_xboole_0 @ (k1_struct_0 @ X34)) | ~ (l1_struct_0 @ X34))),
% 1.06/1.26      inference('cnf', [status(esa)], [fc3_struct_0])).
% 1.06/1.26  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.06/1.26  thf('1', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.06/1.26      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.06/1.26  thf(t8_boole, axiom,
% 1.06/1.26    (![A:$i,B:$i]:
% 1.06/1.26     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 1.06/1.26  thf('2', plain,
% 1.06/1.26      (![X8 : $i, X9 : $i]:
% 1.06/1.26         (~ (v1_xboole_0 @ X8) | ~ (v1_xboole_0 @ X9) | ((X8) = (X9)))),
% 1.06/1.26      inference('cnf', [status(esa)], [t8_boole])).
% 1.06/1.26  thf('3', plain,
% 1.06/1.26      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.06/1.26      inference('sup-', [status(thm)], ['1', '2'])).
% 1.06/1.26  thf('4', plain,
% 1.06/1.26      (![X0 : $i]:
% 1.06/1.26         (~ (l1_struct_0 @ X0) | ((k1_xboole_0) = (k1_struct_0 @ X0)))),
% 1.06/1.26      inference('sup-', [status(thm)], ['0', '3'])).
% 1.06/1.26  thf(t27_pre_topc, axiom,
% 1.06/1.26    (![A:$i]:
% 1.06/1.26     ( ( l1_struct_0 @ A ) =>
% 1.06/1.26       ( ( k2_struct_0 @ A ) =
% 1.06/1.26         ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k1_struct_0 @ A ) ) ) ))).
% 1.06/1.26  thf('5', plain,
% 1.06/1.26      (![X35 : $i]:
% 1.06/1.26         (((k2_struct_0 @ X35)
% 1.06/1.26            = (k3_subset_1 @ (u1_struct_0 @ X35) @ (k1_struct_0 @ X35)))
% 1.06/1.26          | ~ (l1_struct_0 @ X35))),
% 1.06/1.26      inference('cnf', [status(esa)], [t27_pre_topc])).
% 1.06/1.26  thf('6', plain,
% 1.06/1.26      (![X0 : $i]:
% 1.06/1.26         (((k2_struct_0 @ X0)
% 1.06/1.26            = (k3_subset_1 @ (u1_struct_0 @ X0) @ k1_xboole_0))
% 1.06/1.26          | ~ (l1_struct_0 @ X0)
% 1.06/1.26          | ~ (l1_struct_0 @ X0))),
% 1.06/1.26      inference('sup+', [status(thm)], ['4', '5'])).
% 1.06/1.26  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 1.06/1.26  thf('7', plain, (![X11 : $i]: ((k1_subset_1 @ X11) = (k1_xboole_0))),
% 1.06/1.26      inference('cnf', [status(esa)], [d3_subset_1])).
% 1.06/1.26  thf(t22_subset_1, axiom,
% 1.06/1.26    (![A:$i]:
% 1.06/1.26     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 1.06/1.26  thf('8', plain,
% 1.06/1.26      (![X19 : $i]:
% 1.06/1.26         ((k2_subset_1 @ X19) = (k3_subset_1 @ X19 @ (k1_subset_1 @ X19)))),
% 1.06/1.26      inference('cnf', [status(esa)], [t22_subset_1])).
% 1.06/1.26  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.06/1.26  thf('9', plain, (![X12 : $i]: ((k2_subset_1 @ X12) = (X12))),
% 1.06/1.26      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.06/1.26  thf('10', plain,
% 1.06/1.26      (![X19 : $i]: ((X19) = (k3_subset_1 @ X19 @ (k1_subset_1 @ X19)))),
% 1.06/1.26      inference('demod', [status(thm)], ['8', '9'])).
% 1.06/1.26  thf('11', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 1.06/1.26      inference('sup+', [status(thm)], ['7', '10'])).
% 1.06/1.26  thf('12', plain,
% 1.06/1.26      (![X0 : $i]:
% 1.06/1.26         (((k2_struct_0 @ X0) = (u1_struct_0 @ X0))
% 1.06/1.26          | ~ (l1_struct_0 @ X0)
% 1.06/1.26          | ~ (l1_struct_0 @ X0))),
% 1.06/1.26      inference('demod', [status(thm)], ['6', '11'])).
% 1.06/1.26  thf('13', plain,
% 1.06/1.26      (![X0 : $i]:
% 1.06/1.26         (~ (l1_struct_0 @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 1.06/1.26      inference('simplify', [status(thm)], ['12'])).
% 1.06/1.26  thf(t43_tops_1, conjecture,
% 1.06/1.26    (![A:$i]:
% 1.06/1.26     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.26       ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 1.06/1.26  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.26    (~( ![A:$i]:
% 1.06/1.26        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.26          ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ) )),
% 1.06/1.26    inference('cnf.neg', [status(esa)], [t43_tops_1])).
% 1.06/1.26  thf('14', plain,
% 1.06/1.26      (((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) != (k2_struct_0 @ sk_A))),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('15', plain,
% 1.06/1.26      (![X0 : $i]:
% 1.06/1.26         (~ (l1_struct_0 @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 1.06/1.26      inference('simplify', [status(thm)], ['12'])).
% 1.06/1.26  thf('16', plain,
% 1.06/1.26      (![X0 : $i]:
% 1.06/1.26         (~ (l1_struct_0 @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 1.06/1.26      inference('simplify', [status(thm)], ['12'])).
% 1.06/1.26  thf(dt_k2_struct_0, axiom,
% 1.06/1.26    (![A:$i]:
% 1.06/1.26     ( ( l1_struct_0 @ A ) =>
% 1.06/1.26       ( m1_subset_1 @
% 1.06/1.26         ( k2_struct_0 @ A ) @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) ))).
% 1.06/1.26  thf('17', plain,
% 1.06/1.26      (![X32 : $i]:
% 1.06/1.26         ((m1_subset_1 @ (k2_struct_0 @ X32) @ 
% 1.06/1.26           (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 1.06/1.26          | ~ (l1_struct_0 @ X32))),
% 1.06/1.26      inference('cnf', [status(esa)], [dt_k2_struct_0])).
% 1.06/1.26  thf(t3_subset, axiom,
% 1.06/1.26    (![A:$i,B:$i]:
% 1.06/1.26     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.06/1.26  thf('18', plain,
% 1.06/1.26      (![X20 : $i, X21 : $i]:
% 1.06/1.26         ((r1_tarski @ X20 @ X21) | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21)))),
% 1.06/1.26      inference('cnf', [status(esa)], [t3_subset])).
% 1.06/1.26  thf('19', plain,
% 1.06/1.26      (![X0 : $i]:
% 1.06/1.26         (~ (l1_struct_0 @ X0)
% 1.06/1.26          | (r1_tarski @ (k2_struct_0 @ X0) @ (u1_struct_0 @ X0)))),
% 1.06/1.26      inference('sup-', [status(thm)], ['17', '18'])).
% 1.06/1.26  thf('20', plain,
% 1.06/1.26      (![X0 : $i]:
% 1.06/1.26         ((r1_tarski @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 1.06/1.26          | ~ (l1_struct_0 @ X0)
% 1.06/1.26          | ~ (l1_struct_0 @ X0))),
% 1.06/1.26      inference('sup+', [status(thm)], ['16', '19'])).
% 1.06/1.26  thf('21', plain,
% 1.06/1.26      (![X0 : $i]:
% 1.06/1.26         (~ (l1_struct_0 @ X0)
% 1.06/1.26          | (r1_tarski @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0)))),
% 1.06/1.26      inference('simplify', [status(thm)], ['20'])).
% 1.06/1.26  thf(l32_xboole_1, axiom,
% 1.06/1.26    (![A:$i,B:$i]:
% 1.06/1.26     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.06/1.26  thf('22', plain,
% 1.06/1.26      (![X0 : $i, X2 : $i]:
% 1.06/1.26         (((k4_xboole_0 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 1.06/1.26      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.06/1.26  thf(redefinition_k6_subset_1, axiom,
% 1.06/1.26    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 1.06/1.26  thf('23', plain,
% 1.06/1.26      (![X17 : $i, X18 : $i]:
% 1.06/1.26         ((k6_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))),
% 1.06/1.26      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.06/1.26  thf('24', plain,
% 1.06/1.26      (![X0 : $i, X2 : $i]:
% 1.06/1.26         (((k6_subset_1 @ X0 @ X2) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ X2))),
% 1.06/1.26      inference('demod', [status(thm)], ['22', '23'])).
% 1.06/1.26  thf('25', plain,
% 1.06/1.26      (![X0 : $i]:
% 1.06/1.26         (~ (l1_struct_0 @ X0)
% 1.06/1.26          | ((k6_subset_1 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 1.06/1.26              = (k1_xboole_0)))),
% 1.06/1.26      inference('sup-', [status(thm)], ['21', '24'])).
% 1.06/1.26  thf('26', plain,
% 1.06/1.26      (![X0 : $i]:
% 1.06/1.26         (~ (l1_struct_0 @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 1.06/1.26      inference('simplify', [status(thm)], ['12'])).
% 1.06/1.26  thf('27', plain,
% 1.06/1.26      (![X0 : $i]:
% 1.06/1.26         (~ (l1_struct_0 @ X0)
% 1.06/1.26          | ((k6_subset_1 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 1.06/1.26              = (k1_xboole_0)))),
% 1.06/1.26      inference('sup-', [status(thm)], ['21', '24'])).
% 1.06/1.26  thf('28', plain,
% 1.06/1.26      (![X0 : $i]:
% 1.06/1.26         (~ (l1_struct_0 @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 1.06/1.26      inference('simplify', [status(thm)], ['12'])).
% 1.06/1.26  thf('29', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('30', plain,
% 1.06/1.26      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.06/1.26      inference('sup-', [status(thm)], ['1', '2'])).
% 1.06/1.26  thf('31', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.06/1.26      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.06/1.26  thf(t29_mcart_1, axiom,
% 1.06/1.26    (![A:$i]:
% 1.06/1.26     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 1.06/1.26          ( ![B:$i]:
% 1.06/1.26            ( ~( ( r2_hidden @ B @ A ) & 
% 1.06/1.26                 ( ![C:$i,D:$i,E:$i]:
% 1.06/1.26                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 1.06/1.26                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 1.06/1.26  thf('32', plain,
% 1.06/1.26      (![X26 : $i]:
% 1.06/1.26         (((X26) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X26) @ X26))),
% 1.06/1.26      inference('cnf', [status(esa)], [t29_mcart_1])).
% 1.06/1.26  thf(dt_k6_subset_1, axiom,
% 1.06/1.26    (![A:$i,B:$i]:
% 1.06/1.26     ( m1_subset_1 @ ( k6_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ))).
% 1.06/1.26  thf('33', plain,
% 1.06/1.26      (![X13 : $i, X14 : $i]:
% 1.06/1.26         (m1_subset_1 @ (k6_subset_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13))),
% 1.06/1.26      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 1.06/1.26  thf(t5_subset, axiom,
% 1.06/1.26    (![A:$i,B:$i,C:$i]:
% 1.06/1.26     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 1.06/1.26          ( v1_xboole_0 @ C ) ) ))).
% 1.06/1.26  thf('34', plain,
% 1.06/1.26      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.06/1.26         (~ (r2_hidden @ X23 @ X24)
% 1.06/1.26          | ~ (v1_xboole_0 @ X25)
% 1.06/1.26          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25)))),
% 1.06/1.26      inference('cnf', [status(esa)], [t5_subset])).
% 1.06/1.26  thf('35', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.06/1.26         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X2 @ (k6_subset_1 @ X0 @ X1)))),
% 1.06/1.26      inference('sup-', [status(thm)], ['33', '34'])).
% 1.06/1.26  thf('36', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]:
% 1.06/1.26         (((k6_subset_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X1))),
% 1.06/1.26      inference('sup-', [status(thm)], ['32', '35'])).
% 1.06/1.26  thf('37', plain,
% 1.06/1.26      (![X0 : $i]: ((k6_subset_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.06/1.26      inference('sup-', [status(thm)], ['31', '36'])).
% 1.06/1.26  thf('38', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]:
% 1.06/1.26         ((r1_tarski @ X0 @ X1) | ((k4_xboole_0 @ X0 @ X1) != (k1_xboole_0)))),
% 1.06/1.26      inference('cnf', [status(esa)], [l32_xboole_1])).
% 1.06/1.26  thf('39', plain,
% 1.06/1.26      (![X17 : $i, X18 : $i]:
% 1.06/1.26         ((k6_subset_1 @ X17 @ X18) = (k4_xboole_0 @ X17 @ X18))),
% 1.06/1.26      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 1.06/1.26  thf('40', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]:
% 1.06/1.26         ((r1_tarski @ X0 @ X1) | ((k6_subset_1 @ X0 @ X1) != (k1_xboole_0)))),
% 1.06/1.26      inference('demod', [status(thm)], ['38', '39'])).
% 1.06/1.26  thf('41', plain,
% 1.06/1.26      (![X0 : $i]:
% 1.06/1.26         (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ k1_xboole_0 @ X0))),
% 1.06/1.26      inference('sup-', [status(thm)], ['37', '40'])).
% 1.06/1.26  thf('42', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.06/1.26      inference('simplify', [status(thm)], ['41'])).
% 1.06/1.26  thf('43', plain,
% 1.06/1.26      (![X20 : $i, X22 : $i]:
% 1.06/1.26         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 1.06/1.26      inference('cnf', [status(esa)], [t3_subset])).
% 1.06/1.26  thf('44', plain,
% 1.06/1.26      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.06/1.26      inference('sup-', [status(thm)], ['42', '43'])).
% 1.06/1.26  thf(cc2_pre_topc, axiom,
% 1.06/1.26    (![A:$i]:
% 1.06/1.26     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 1.06/1.26       ( ![B:$i]:
% 1.06/1.26         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.26           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 1.06/1.26  thf('45', plain,
% 1.06/1.26      (![X30 : $i, X31 : $i]:
% 1.06/1.26         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (u1_struct_0 @ X31)))
% 1.06/1.26          | (v4_pre_topc @ X30 @ X31)
% 1.06/1.26          | ~ (v1_xboole_0 @ X30)
% 1.06/1.26          | ~ (l1_pre_topc @ X31)
% 1.06/1.26          | ~ (v2_pre_topc @ X31))),
% 1.06/1.26      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 1.06/1.26  thf('46', plain,
% 1.06/1.26      (![X0 : $i]:
% 1.06/1.26         (~ (v2_pre_topc @ X0)
% 1.06/1.26          | ~ (l1_pre_topc @ X0)
% 1.06/1.26          | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.06/1.26          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 1.06/1.26      inference('sup-', [status(thm)], ['44', '45'])).
% 1.06/1.26  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.06/1.26      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.06/1.26  thf('48', plain,
% 1.06/1.26      (![X0 : $i]:
% 1.06/1.26         (~ (v2_pre_topc @ X0)
% 1.06/1.26          | ~ (l1_pre_topc @ X0)
% 1.06/1.26          | (v4_pre_topc @ k1_xboole_0 @ X0))),
% 1.06/1.26      inference('demod', [status(thm)], ['46', '47'])).
% 1.06/1.26  thf('49', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]:
% 1.06/1.26         ((v4_pre_topc @ X0 @ X1)
% 1.06/1.26          | ~ (v1_xboole_0 @ X0)
% 1.06/1.26          | ~ (l1_pre_topc @ X1)
% 1.06/1.26          | ~ (v2_pre_topc @ X1))),
% 1.06/1.26      inference('sup+', [status(thm)], ['30', '48'])).
% 1.06/1.26  thf('50', plain,
% 1.06/1.26      (![X0 : $i]:
% 1.06/1.26         (~ (v2_pre_topc @ sk_A)
% 1.06/1.26          | ~ (v1_xboole_0 @ X0)
% 1.06/1.26          | (v4_pre_topc @ X0 @ sk_A))),
% 1.06/1.26      inference('sup-', [status(thm)], ['29', '49'])).
% 1.06/1.26  thf('51', plain, ((v2_pre_topc @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('52', plain,
% 1.06/1.26      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v4_pre_topc @ X0 @ sk_A))),
% 1.06/1.26      inference('demod', [status(thm)], ['50', '51'])).
% 1.06/1.26  thf('53', plain,
% 1.06/1.26      (![X13 : $i, X14 : $i]:
% 1.06/1.26         (m1_subset_1 @ (k6_subset_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13))),
% 1.06/1.26      inference('cnf', [status(esa)], [dt_k6_subset_1])).
% 1.06/1.26  thf(t52_pre_topc, axiom,
% 1.06/1.26    (![A:$i]:
% 1.06/1.26     ( ( l1_pre_topc @ A ) =>
% 1.06/1.26       ( ![B:$i]:
% 1.06/1.26         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.26           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 1.06/1.26             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 1.06/1.26               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 1.06/1.26  thf('54', plain,
% 1.06/1.26      (![X36 : $i, X37 : $i]:
% 1.06/1.26         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (u1_struct_0 @ X37)))
% 1.06/1.26          | ~ (v4_pre_topc @ X36 @ X37)
% 1.06/1.26          | ((k2_pre_topc @ X37 @ X36) = (X36))
% 1.06/1.26          | ~ (l1_pre_topc @ X37))),
% 1.06/1.26      inference('cnf', [status(esa)], [t52_pre_topc])).
% 1.06/1.26  thf('55', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]:
% 1.06/1.26         (~ (l1_pre_topc @ X0)
% 1.06/1.26          | ((k2_pre_topc @ X0 @ (k6_subset_1 @ (u1_struct_0 @ X0) @ X1))
% 1.06/1.26              = (k6_subset_1 @ (u1_struct_0 @ X0) @ X1))
% 1.06/1.26          | ~ (v4_pre_topc @ (k6_subset_1 @ (u1_struct_0 @ X0) @ X1) @ X0))),
% 1.06/1.26      inference('sup-', [status(thm)], ['53', '54'])).
% 1.06/1.26  thf('56', plain,
% 1.06/1.26      (![X0 : $i]:
% 1.06/1.26         (~ (v1_xboole_0 @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 1.06/1.26          | ((k2_pre_topc @ sk_A @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 1.06/1.26              = (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 1.06/1.26          | ~ (l1_pre_topc @ sk_A))),
% 1.06/1.26      inference('sup-', [status(thm)], ['52', '55'])).
% 1.06/1.26  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('58', plain,
% 1.06/1.26      (![X0 : $i]:
% 1.06/1.26         (~ (v1_xboole_0 @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 1.06/1.26          | ((k2_pre_topc @ sk_A @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 1.06/1.26              = (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))),
% 1.06/1.26      inference('demod', [status(thm)], ['56', '57'])).
% 1.06/1.26  thf('59', plain,
% 1.06/1.26      (![X0 : $i]:
% 1.06/1.26         (~ (v1_xboole_0 @ (k6_subset_1 @ (k2_struct_0 @ sk_A) @ X0))
% 1.06/1.26          | ~ (l1_struct_0 @ sk_A)
% 1.06/1.26          | ((k2_pre_topc @ sk_A @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 1.06/1.26              = (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))),
% 1.06/1.26      inference('sup-', [status(thm)], ['28', '58'])).
% 1.06/1.26  thf('60', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf(dt_l1_pre_topc, axiom,
% 1.06/1.26    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 1.06/1.26  thf('61', plain,
% 1.06/1.26      (![X33 : $i]: ((l1_struct_0 @ X33) | ~ (l1_pre_topc @ X33))),
% 1.06/1.26      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 1.06/1.26  thf('62', plain, ((l1_struct_0 @ sk_A)),
% 1.06/1.26      inference('sup-', [status(thm)], ['60', '61'])).
% 1.06/1.26  thf('63', plain,
% 1.06/1.26      (![X0 : $i]:
% 1.06/1.26         (~ (v1_xboole_0 @ (k6_subset_1 @ (k2_struct_0 @ sk_A) @ X0))
% 1.06/1.26          | ((k2_pre_topc @ sk_A @ (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0))
% 1.06/1.26              = (k6_subset_1 @ (u1_struct_0 @ sk_A) @ X0)))),
% 1.06/1.26      inference('demod', [status(thm)], ['59', '62'])).
% 1.06/1.26  thf('64', plain,
% 1.06/1.26      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.06/1.26        | ~ (l1_struct_0 @ sk_A)
% 1.06/1.26        | ((k2_pre_topc @ sk_A @ 
% 1.06/1.26            (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 1.06/1.26            = (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['27', '63'])).
% 1.06/1.26  thf('65', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.06/1.26      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.06/1.26  thf('66', plain, ((l1_struct_0 @ sk_A)),
% 1.06/1.26      inference('sup-', [status(thm)], ['60', '61'])).
% 1.06/1.26  thf('67', plain,
% 1.06/1.26      (((k2_pre_topc @ sk_A @ 
% 1.06/1.26         (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 1.06/1.26         = (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))),
% 1.06/1.26      inference('demod', [status(thm)], ['64', '65', '66'])).
% 1.06/1.26  thf('68', plain,
% 1.06/1.26      ((((k2_pre_topc @ sk_A @ 
% 1.06/1.26          (k6_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 1.06/1.26          = (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 1.06/1.26        | ~ (l1_struct_0 @ sk_A))),
% 1.06/1.26      inference('sup+', [status(thm)], ['26', '67'])).
% 1.06/1.26  thf('69', plain, ((l1_struct_0 @ sk_A)),
% 1.06/1.26      inference('sup-', [status(thm)], ['60', '61'])).
% 1.06/1.26  thf('70', plain,
% 1.06/1.26      (((k2_pre_topc @ sk_A @ 
% 1.06/1.26         (k6_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 1.06/1.26         = (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))),
% 1.06/1.26      inference('demod', [status(thm)], ['68', '69'])).
% 1.06/1.26  thf('71', plain,
% 1.06/1.26      ((((k2_pre_topc @ sk_A @ k1_xboole_0)
% 1.06/1.26          = (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 1.06/1.26        | ~ (l1_struct_0 @ sk_A))),
% 1.06/1.26      inference('sup+', [status(thm)], ['25', '70'])).
% 1.06/1.26  thf('72', plain, ((l1_struct_0 @ sk_A)),
% 1.06/1.26      inference('sup-', [status(thm)], ['60', '61'])).
% 1.06/1.26  thf('73', plain,
% 1.06/1.26      (((k2_pre_topc @ sk_A @ k1_xboole_0)
% 1.06/1.26         = (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))),
% 1.06/1.26      inference('demod', [status(thm)], ['71', '72'])).
% 1.06/1.26  thf('74', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]:
% 1.06/1.26         ((r1_tarski @ X0 @ X1) | ((k6_subset_1 @ X0 @ X1) != (k1_xboole_0)))),
% 1.06/1.26      inference('demod', [status(thm)], ['38', '39'])).
% 1.06/1.26  thf('75', plain,
% 1.06/1.26      ((((k2_pre_topc @ sk_A @ k1_xboole_0) != (k1_xboole_0))
% 1.06/1.26        | (r1_tarski @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))),
% 1.06/1.26      inference('sup-', [status(thm)], ['73', '74'])).
% 1.06/1.26  thf('76', plain,
% 1.06/1.26      (![X0 : $i]:
% 1.06/1.26         (~ (l1_struct_0 @ X0)
% 1.06/1.26          | ((k6_subset_1 @ (k2_struct_0 @ X0) @ (k2_struct_0 @ X0))
% 1.06/1.26              = (k1_xboole_0)))),
% 1.06/1.26      inference('sup-', [status(thm)], ['21', '24'])).
% 1.06/1.26  thf('77', plain,
% 1.06/1.26      (![X0 : $i]:
% 1.06/1.26         (~ (l1_struct_0 @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 1.06/1.26      inference('simplify', [status(thm)], ['12'])).
% 1.06/1.26  thf('78', plain,
% 1.06/1.26      (((k2_pre_topc @ sk_A @ k1_xboole_0)
% 1.06/1.26         = (k6_subset_1 @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))),
% 1.06/1.26      inference('demod', [status(thm)], ['71', '72'])).
% 1.06/1.26  thf('79', plain,
% 1.06/1.26      ((((k2_pre_topc @ sk_A @ k1_xboole_0)
% 1.06/1.26          = (k6_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))
% 1.06/1.26        | ~ (l1_struct_0 @ sk_A))),
% 1.06/1.26      inference('sup+', [status(thm)], ['77', '78'])).
% 1.06/1.26  thf('80', plain, ((l1_struct_0 @ sk_A)),
% 1.06/1.26      inference('sup-', [status(thm)], ['60', '61'])).
% 1.06/1.26  thf('81', plain,
% 1.06/1.26      (((k2_pre_topc @ sk_A @ k1_xboole_0)
% 1.06/1.26         = (k6_subset_1 @ (k2_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))),
% 1.06/1.26      inference('demod', [status(thm)], ['79', '80'])).
% 1.06/1.26  thf('82', plain,
% 1.06/1.26      ((((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))
% 1.06/1.26        | ~ (l1_struct_0 @ sk_A))),
% 1.06/1.26      inference('sup+', [status(thm)], ['76', '81'])).
% 1.06/1.26  thf('83', plain, ((l1_struct_0 @ sk_A)),
% 1.06/1.26      inference('sup-', [status(thm)], ['60', '61'])).
% 1.06/1.26  thf('84', plain, (((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 1.06/1.26      inference('demod', [status(thm)], ['82', '83'])).
% 1.06/1.26  thf('85', plain,
% 1.06/1.26      ((((k1_xboole_0) != (k1_xboole_0))
% 1.06/1.26        | (r1_tarski @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A)))),
% 1.06/1.26      inference('demod', [status(thm)], ['75', '84'])).
% 1.06/1.26  thf('86', plain, ((r1_tarski @ (u1_struct_0 @ sk_A) @ (k2_struct_0 @ sk_A))),
% 1.06/1.26      inference('simplify', [status(thm)], ['85'])).
% 1.06/1.26  thf('87', plain,
% 1.06/1.26      (![X20 : $i, X22 : $i]:
% 1.06/1.26         ((m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X22)) | ~ (r1_tarski @ X20 @ X22))),
% 1.06/1.26      inference('cnf', [status(esa)], [t3_subset])).
% 1.06/1.26  thf('88', plain,
% 1.06/1.26      ((m1_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.26        (k1_zfmisc_1 @ (k2_struct_0 @ sk_A)))),
% 1.06/1.26      inference('sup-', [status(thm)], ['86', '87'])).
% 1.06/1.26  thf('89', plain,
% 1.06/1.26      (![X0 : $i]:
% 1.06/1.26         (~ (l1_struct_0 @ X0) | ((k2_struct_0 @ X0) = (u1_struct_0 @ X0)))),
% 1.06/1.26      inference('simplify', [status(thm)], ['12'])).
% 1.06/1.26  thf(d1_tops_1, axiom,
% 1.06/1.26    (![A:$i]:
% 1.06/1.26     ( ( l1_pre_topc @ A ) =>
% 1.06/1.26       ( ![B:$i]:
% 1.06/1.26         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 1.06/1.26           ( ( k1_tops_1 @ A @ B ) =
% 1.06/1.26             ( k3_subset_1 @
% 1.06/1.26               ( u1_struct_0 @ A ) @ 
% 1.06/1.26               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 1.06/1.26  thf('90', plain,
% 1.06/1.26      (![X38 : $i, X39 : $i]:
% 1.06/1.26         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (u1_struct_0 @ X39)))
% 1.06/1.26          | ((k1_tops_1 @ X39 @ X38)
% 1.06/1.26              = (k3_subset_1 @ (u1_struct_0 @ X39) @ 
% 1.06/1.26                 (k2_pre_topc @ X39 @ (k3_subset_1 @ (u1_struct_0 @ X39) @ X38))))
% 1.06/1.26          | ~ (l1_pre_topc @ X39))),
% 1.06/1.26      inference('cnf', [status(esa)], [d1_tops_1])).
% 1.06/1.26  thf('91', plain,
% 1.06/1.26      (![X0 : $i, X1 : $i]:
% 1.06/1.26         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_struct_0 @ X0)))
% 1.06/1.26          | ~ (l1_struct_0 @ X0)
% 1.06/1.26          | ~ (l1_pre_topc @ X0)
% 1.06/1.26          | ((k1_tops_1 @ X0 @ X1)
% 1.06/1.26              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 1.06/1.26                 (k2_pre_topc @ X0 @ (k3_subset_1 @ (u1_struct_0 @ X0) @ X1)))))),
% 1.06/1.26      inference('sup-', [status(thm)], ['89', '90'])).
% 1.06/1.26  thf('92', plain,
% 1.06/1.26      ((((k1_tops_1 @ sk_A @ (u1_struct_0 @ sk_A))
% 1.06/1.26          = (k3_subset_1 @ (u1_struct_0 @ sk_A) @ 
% 1.06/1.26             (k2_pre_topc @ sk_A @ 
% 1.06/1.26              (k3_subset_1 @ (u1_struct_0 @ sk_A) @ (u1_struct_0 @ sk_A)))))
% 1.06/1.26        | ~ (l1_pre_topc @ sk_A)
% 1.06/1.26        | ~ (l1_struct_0 @ sk_A))),
% 1.06/1.26      inference('sup-', [status(thm)], ['88', '91'])).
% 1.06/1.26  thf('93', plain,
% 1.06/1.26      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.06/1.26      inference('sup-', [status(thm)], ['42', '43'])).
% 1.06/1.26  thf(involutiveness_k3_subset_1, axiom,
% 1.06/1.26    (![A:$i,B:$i]:
% 1.06/1.26     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.06/1.26       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 1.06/1.26  thf('94', plain,
% 1.06/1.26      (![X15 : $i, X16 : $i]:
% 1.06/1.26         (((k3_subset_1 @ X16 @ (k3_subset_1 @ X16 @ X15)) = (X15))
% 1.06/1.26          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16)))),
% 1.06/1.26      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 1.06/1.26  thf('95', plain,
% 1.06/1.26      (![X0 : $i]:
% 1.06/1.26         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 1.06/1.26      inference('sup-', [status(thm)], ['93', '94'])).
% 1.06/1.26  thf('96', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 1.06/1.26      inference('sup+', [status(thm)], ['7', '10'])).
% 1.06/1.26  thf('97', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 1.06/1.26      inference('demod', [status(thm)], ['95', '96'])).
% 1.06/1.26  thf('98', plain, (((k2_pre_topc @ sk_A @ k1_xboole_0) = (k1_xboole_0))),
% 1.06/1.26      inference('demod', [status(thm)], ['82', '83'])).
% 1.06/1.26  thf('99', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 1.06/1.26      inference('sup+', [status(thm)], ['7', '10'])).
% 1.06/1.26  thf('100', plain, ((l1_pre_topc @ sk_A)),
% 1.06/1.26      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.26  thf('101', plain, ((l1_struct_0 @ sk_A)),
% 1.06/1.26      inference('sup-', [status(thm)], ['60', '61'])).
% 1.06/1.26  thf('102', plain,
% 1.06/1.26      (((k1_tops_1 @ sk_A @ (u1_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))),
% 1.06/1.26      inference('demod', [status(thm)], ['92', '97', '98', '99', '100', '101'])).
% 1.06/1.26  thf('103', plain,
% 1.06/1.26      ((((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))
% 1.06/1.26        | ~ (l1_struct_0 @ sk_A))),
% 1.06/1.26      inference('sup+', [status(thm)], ['15', '102'])).
% 1.06/1.26  thf('104', plain, ((l1_struct_0 @ sk_A)),
% 1.06/1.26      inference('sup-', [status(thm)], ['60', '61'])).
% 1.06/1.26  thf('105', plain,
% 1.06/1.26      (((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) = (u1_struct_0 @ sk_A))),
% 1.06/1.26      inference('demod', [status(thm)], ['103', '104'])).
% 1.06/1.26  thf('106', plain, (((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 1.06/1.26      inference('demod', [status(thm)], ['14', '105'])).
% 1.06/1.26  thf('107', plain,
% 1.06/1.26      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 1.06/1.26      inference('sup-', [status(thm)], ['13', '106'])).
% 1.06/1.26  thf('108', plain, ((l1_struct_0 @ sk_A)),
% 1.06/1.26      inference('sup-', [status(thm)], ['60', '61'])).
% 1.06/1.26  thf('109', plain, (((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 1.06/1.26      inference('demod', [status(thm)], ['107', '108'])).
% 1.06/1.26  thf('110', plain, ($false), inference('simplify', [status(thm)], ['109'])).
% 1.06/1.26  
% 1.06/1.26  % SZS output end Refutation
% 1.06/1.26  
% 1.06/1.27  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
