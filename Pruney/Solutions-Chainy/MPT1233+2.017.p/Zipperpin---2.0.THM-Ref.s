%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aPs6QtOuCy

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:02:51 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 132 expanded)
%              Number of leaves         :   37 (  55 expanded)
%              Depth                    :   18
%              Number of atoms          :  654 ( 853 expanded)
%              Number of equality atoms :   60 (  83 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(l1_pre_topc_type,type,(
    l1_pre_topc: $i > $o )).

thf(v4_pre_topc_type,type,(
    v4_pre_topc: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(u1_struct_0_type,type,(
    u1_struct_0: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_tops_1_type,type,(
    k1_tops_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_pre_topc_type,type,(
    v2_pre_topc: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k2_struct_0_type,type,(
    k2_struct_0: $i > $i )).

thf(k1_subset_1_type,type,(
    k1_subset_1: $i > $i )).

thf(l1_struct_0_type,type,(
    l1_struct_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k2_pre_topc_type,type,(
    k2_pre_topc: $i > $i > $i )).

thf(d3_struct_0,axiom,(
    ! [A: $i] :
      ( ( l1_struct_0 @ A )
     => ( ( k2_struct_0 @ A )
        = ( u1_struct_0 @ A ) ) ) )).

thf('0',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf('1',plain,(
    ! [X29: $i] :
      ( ( ( k2_struct_0 @ X29 )
        = ( u1_struct_0 @ X29 ) )
      | ~ ( l1_struct_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d3_struct_0])).

thf(d3_subset_1,axiom,(
    ! [A: $i] :
      ( ( k1_subset_1 @ A )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X11: $i] :
      ( ( k1_subset_1 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('3',plain,(
    ! [X11: $i] :
      ( ( k1_subset_1 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

thf(cc2_pre_topc,axiom,(
    ! [A: $i] :
      ( ( ( v2_pre_topc @ A )
        & ( l1_pre_topc @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( v1_xboole_0 @ B )
           => ( v4_pre_topc @ B @ A ) ) ) ) )).

thf('6',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X28 ) ) )
      | ( v4_pre_topc @ X27 @ X28 )
      | ~ ( v1_xboole_0 @ X27 )
      | ~ ( l1_pre_topc @ X28 )
      | ~ ( v2_pre_topc @ X28 ) ) ),
    inference(cnf,[status(esa)],[cc2_pre_topc])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v1_xboole_0 @ ( k1_subset_1 @ X1 ) )
      | ( v4_pre_topc @ ( k1_subset_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X11: $i] :
      ( ( k1_subset_1 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('9',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('10',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k1_subset_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( v4_pre_topc @ ( k1_subset_1 @ X1 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k1_subset_1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['3','4'])).

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

thf('13',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X32 ) ) )
      | ~ ( v4_pre_topc @ X31 @ X32 )
      | ( ( k2_pre_topc @ X32 @ X31 )
        = X31 )
      | ~ ( l1_pre_topc @ X32 ) ) ),
    inference(cnf,[status(esa)],[t52_pre_topc])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k1_subset_1 @ X1 ) )
        = ( k1_subset_1 @ X1 ) )
      | ~ ( v4_pre_topc @ ( k1_subset_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ( ( k2_pre_topc @ X0 @ ( k1_subset_1 @ X1 ) )
        = ( k1_subset_1 @ X1 ) )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_pre_topc @ X0 @ ( k1_subset_1 @ X1 ) )
        = ( k1_subset_1 @ X1 ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_pre_topc @ X1 @ k1_xboole_0 )
        = ( k1_subset_1 @ X0 ) )
      | ~ ( l1_pre_topc @ X1 )
      | ~ ( v2_pre_topc @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','16'])).

thf('18',plain,(
    ! [X11: $i] :
      ( ( k1_subset_1 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('19',plain,(
    ! [X11: $i] :
      ( ( k1_subset_1 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_subset_1 @ X1 )
      = ( k1_subset_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t22_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ) )).

thf('21',plain,(
    ! [X15: $i] :
      ( ( k2_subset_1 @ X15 )
      = ( k3_subset_1 @ X15 @ ( k1_subset_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t22_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('22',plain,(
    ! [X12: $i] :
      ( ( k2_subset_1 @ X12 )
      = X12 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('23',plain,(
    ! [X15: $i] :
      ( X15
      = ( k3_subset_1 @ X15 @ ( k1_subset_1 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k3_subset_1 @ X1 @ ( k1_subset_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X2
        = ( k3_subset_1 @ X2 @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','24'])).

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

thf('26',plain,(
    ! [X23: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X23 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('27',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X1 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('28',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X1 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X23: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X23 ) @ X23 ) ) ),
    inference(cnf,[status(esa)],[t29_mcart_1])).

thf('31',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ~ ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('32',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k4_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ ( sk_B @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 )
      | ( ( k4_xboole_0 @ X0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ( ( k4_xboole_0 @ X6 @ X7 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['37'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('39',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(d1_tops_1,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) )
         => ( ( k1_tops_1 @ A @ B )
            = ( k3_subset_1 @ ( u1_struct_0 @ A ) @ ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) )).

thf('41',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( u1_struct_0 @ X34 ) ) )
      | ( ( k1_tops_1 @ X34 @ X33 )
        = ( k3_subset_1 @ ( u1_struct_0 @ X34 ) @ ( k2_pre_topc @ X34 @ ( k3_subset_1 @ ( u1_struct_0 @ X34 ) @ X33 ) ) ) )
      | ~ ( l1_pre_topc @ X34 ) ) ),
    inference(cnf,[status(esa)],[d1_tops_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( u1_struct_0 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X16: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('44',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k3_subset_1 @ X14 @ ( k3_subset_1 @ X14 @ X13 ) )
        = X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X11: $i] :
      ( ( k1_subset_1 @ X11 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[d3_subset_1])).

thf('47',plain,(
    ! [X15: $i] :
      ( X15
      = ( k3_subset_1 @ X15 @ ( k1_subset_1 @ X15 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('48',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( k3_subset_1 @ ( u1_struct_0 @ X0 ) @ ( k2_pre_topc @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(demod,[status(thm)],['42','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v2_pre_topc @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ( ( k1_tops_1 @ X0 @ ( u1_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k1_tops_1 @ X0 @ ( k2_struct_0 @ X0 ) )
        = ( u1_struct_0 @ X0 ) )
      | ~ ( l1_struct_0 @ X0 )
      | ~ ( l1_pre_topc @ X0 )
      | ~ ( v2_pre_topc @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','52'])).

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

thf('54',plain,(
    ( k1_tops_1 @ sk_A @ ( k2_struct_0 @ sk_A ) )
 != ( k2_struct_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( ( u1_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( v2_pre_topc @ sk_A )
    | ~ ( l1_pre_topc @ sk_A )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v2_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    l1_pre_topc @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_l1_pre_topc,axiom,(
    ! [A: $i] :
      ( ( l1_pre_topc @ A )
     => ( l1_struct_0 @ A ) ) )).

thf('59',plain,(
    ! [X30: $i] :
      ( ( l1_struct_0 @ X30 )
      | ~ ( l1_pre_topc @ X30 ) ) ),
    inference(cnf,[status(esa)],[dt_l1_pre_topc])).

thf('60',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ( u1_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56','57','60'])).

thf('62',plain,
    ( ( ( k2_struct_0 @ sk_A )
     != ( k2_struct_0 @ sk_A ) )
    | ~ ( l1_struct_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['0','61'])).

thf('63',plain,(
    l1_struct_0 @ sk_A ),
    inference('sup-',[status(thm)],['58','59'])).

thf('64',plain,(
    ( k2_struct_0 @ sk_A )
 != ( k2_struct_0 @ sk_A ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    $false ),
    inference(simplify,[status(thm)],['64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aPs6QtOuCy
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:53:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.67/0.88  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.67/0.88  % Solved by: fo/fo7.sh
% 0.67/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.88  % done 570 iterations in 0.457s
% 0.67/0.88  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.67/0.88  % SZS output start Refutation
% 0.67/0.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.67/0.88  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.67/0.88  thf(l1_pre_topc_type, type, l1_pre_topc: $i > $o).
% 0.67/0.88  thf(v4_pre_topc_type, type, v4_pre_topc: $i > $i > $o).
% 0.67/0.88  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.67/0.88  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.67/0.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.67/0.88  thf(u1_struct_0_type, type, u1_struct_0: $i > $i).
% 0.67/0.88  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.67/0.88  thf(k1_tops_1_type, type, k1_tops_1: $i > $i > $i).
% 0.67/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.88  thf(v2_pre_topc_type, type, v2_pre_topc: $i > $o).
% 0.67/0.88  thf(sk_B_type, type, sk_B: $i > $i).
% 0.67/0.88  thf(k2_struct_0_type, type, k2_struct_0: $i > $i).
% 0.67/0.88  thf(k1_subset_1_type, type, k1_subset_1: $i > $i).
% 0.67/0.88  thf(l1_struct_0_type, type, l1_struct_0: $i > $o).
% 0.67/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.67/0.88  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.67/0.88  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.67/0.88  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.67/0.88  thf(k2_pre_topc_type, type, k2_pre_topc: $i > $i > $i).
% 0.67/0.88  thf(d3_struct_0, axiom,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( l1_struct_0 @ A ) => ( ( k2_struct_0 @ A ) = ( u1_struct_0 @ A ) ) ))).
% 0.67/0.88  thf('0', plain,
% 0.67/0.88      (![X29 : $i]:
% 0.67/0.88         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.67/0.88      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.88  thf('1', plain,
% 0.67/0.88      (![X29 : $i]:
% 0.67/0.88         (((k2_struct_0 @ X29) = (u1_struct_0 @ X29)) | ~ (l1_struct_0 @ X29))),
% 0.67/0.88      inference('cnf', [status(esa)], [d3_struct_0])).
% 0.67/0.88  thf(d3_subset_1, axiom, (![A:$i]: ( ( k1_subset_1 @ A ) = ( k1_xboole_0 ) ))).
% 0.67/0.88  thf('2', plain, (![X11 : $i]: ((k1_subset_1 @ X11) = (k1_xboole_0))),
% 0.67/0.88      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.67/0.88  thf('3', plain, (![X11 : $i]: ((k1_subset_1 @ X11) = (k1_xboole_0))),
% 0.67/0.88      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.67/0.88  thf(t4_subset_1, axiom,
% 0.67/0.88    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.67/0.88  thf('4', plain,
% 0.67/0.88      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 0.67/0.88      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.67/0.88  thf('5', plain,
% 0.67/0.88      (![X0 : $i, X1 : $i]:
% 0.67/0.88         (m1_subset_1 @ (k1_subset_1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 0.67/0.88      inference('sup+', [status(thm)], ['3', '4'])).
% 0.67/0.88  thf(cc2_pre_topc, axiom,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.67/0.88       ( ![B:$i]:
% 0.67/0.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.88           ( ( v1_xboole_0 @ B ) => ( v4_pre_topc @ B @ A ) ) ) ) ))).
% 0.67/0.88  thf('6', plain,
% 0.67/0.88      (![X27 : $i, X28 : $i]:
% 0.67/0.88         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (u1_struct_0 @ X28)))
% 0.67/0.88          | (v4_pre_topc @ X27 @ X28)
% 0.67/0.88          | ~ (v1_xboole_0 @ X27)
% 0.67/0.88          | ~ (l1_pre_topc @ X28)
% 0.67/0.88          | ~ (v2_pre_topc @ X28))),
% 0.67/0.88      inference('cnf', [status(esa)], [cc2_pre_topc])).
% 0.67/0.88  thf('7', plain,
% 0.67/0.88      (![X0 : $i, X1 : $i]:
% 0.67/0.88         (~ (v2_pre_topc @ X0)
% 0.67/0.88          | ~ (l1_pre_topc @ X0)
% 0.67/0.88          | ~ (v1_xboole_0 @ (k1_subset_1 @ X1))
% 0.67/0.88          | (v4_pre_topc @ (k1_subset_1 @ X1) @ X0))),
% 0.67/0.88      inference('sup-', [status(thm)], ['5', '6'])).
% 0.67/0.88  thf('8', plain, (![X11 : $i]: ((k1_subset_1 @ X11) = (k1_xboole_0))),
% 0.67/0.88      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.67/0.88  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.67/0.88  thf('9', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.67/0.88      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.67/0.88  thf('10', plain, (![X0 : $i]: (v1_xboole_0 @ (k1_subset_1 @ X0))),
% 0.67/0.88      inference('sup+', [status(thm)], ['8', '9'])).
% 0.67/0.88  thf('11', plain,
% 0.67/0.88      (![X0 : $i, X1 : $i]:
% 0.67/0.88         (~ (v2_pre_topc @ X0)
% 0.67/0.88          | ~ (l1_pre_topc @ X0)
% 0.67/0.88          | (v4_pre_topc @ (k1_subset_1 @ X1) @ X0))),
% 0.67/0.88      inference('demod', [status(thm)], ['7', '10'])).
% 0.67/0.88  thf('12', plain,
% 0.67/0.88      (![X0 : $i, X1 : $i]:
% 0.67/0.88         (m1_subset_1 @ (k1_subset_1 @ X0) @ (k1_zfmisc_1 @ X1))),
% 0.67/0.88      inference('sup+', [status(thm)], ['3', '4'])).
% 0.67/0.88  thf(t52_pre_topc, axiom,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( l1_pre_topc @ A ) =>
% 0.67/0.88       ( ![B:$i]:
% 0.67/0.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.88           ( ( ( v4_pre_topc @ B @ A ) => ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) & 
% 0.67/0.88             ( ( ( v2_pre_topc @ A ) & ( ( k2_pre_topc @ A @ B ) = ( B ) ) ) =>
% 0.67/0.88               ( v4_pre_topc @ B @ A ) ) ) ) ) ))).
% 0.67/0.88  thf('13', plain,
% 0.67/0.88      (![X31 : $i, X32 : $i]:
% 0.67/0.88         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (u1_struct_0 @ X32)))
% 0.67/0.88          | ~ (v4_pre_topc @ X31 @ X32)
% 0.67/0.88          | ((k2_pre_topc @ X32 @ X31) = (X31))
% 0.67/0.88          | ~ (l1_pre_topc @ X32))),
% 0.67/0.88      inference('cnf', [status(esa)], [t52_pre_topc])).
% 0.67/0.88  thf('14', plain,
% 0.67/0.88      (![X0 : $i, X1 : $i]:
% 0.67/0.88         (~ (l1_pre_topc @ X0)
% 0.67/0.88          | ((k2_pre_topc @ X0 @ (k1_subset_1 @ X1)) = (k1_subset_1 @ X1))
% 0.67/0.88          | ~ (v4_pre_topc @ (k1_subset_1 @ X1) @ X0))),
% 0.67/0.88      inference('sup-', [status(thm)], ['12', '13'])).
% 0.67/0.88  thf('15', plain,
% 0.67/0.88      (![X0 : $i, X1 : $i]:
% 0.67/0.88         (~ (l1_pre_topc @ X0)
% 0.67/0.88          | ~ (v2_pre_topc @ X0)
% 0.67/0.88          | ((k2_pre_topc @ X0 @ (k1_subset_1 @ X1)) = (k1_subset_1 @ X1))
% 0.67/0.88          | ~ (l1_pre_topc @ X0))),
% 0.67/0.88      inference('sup-', [status(thm)], ['11', '14'])).
% 0.67/0.88  thf('16', plain,
% 0.67/0.88      (![X0 : $i, X1 : $i]:
% 0.67/0.88         (((k2_pre_topc @ X0 @ (k1_subset_1 @ X1)) = (k1_subset_1 @ X1))
% 0.67/0.88          | ~ (v2_pre_topc @ X0)
% 0.67/0.88          | ~ (l1_pre_topc @ X0))),
% 0.67/0.88      inference('simplify', [status(thm)], ['15'])).
% 0.67/0.88  thf('17', plain,
% 0.67/0.88      (![X0 : $i, X1 : $i]:
% 0.67/0.88         (((k2_pre_topc @ X1 @ k1_xboole_0) = (k1_subset_1 @ X0))
% 0.67/0.88          | ~ (l1_pre_topc @ X1)
% 0.67/0.88          | ~ (v2_pre_topc @ X1))),
% 0.67/0.88      inference('sup+', [status(thm)], ['2', '16'])).
% 0.67/0.88  thf('18', plain, (![X11 : $i]: ((k1_subset_1 @ X11) = (k1_xboole_0))),
% 0.67/0.88      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.67/0.88  thf('19', plain, (![X11 : $i]: ((k1_subset_1 @ X11) = (k1_xboole_0))),
% 0.67/0.88      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.67/0.88  thf('20', plain,
% 0.67/0.88      (![X0 : $i, X1 : $i]: ((k1_subset_1 @ X1) = (k1_subset_1 @ X0))),
% 0.67/0.88      inference('sup+', [status(thm)], ['18', '19'])).
% 0.67/0.88  thf(t22_subset_1, axiom,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( k2_subset_1 @ A ) = ( k3_subset_1 @ A @ ( k1_subset_1 @ A ) ) ))).
% 0.67/0.88  thf('21', plain,
% 0.67/0.88      (![X15 : $i]:
% 0.67/0.88         ((k2_subset_1 @ X15) = (k3_subset_1 @ X15 @ (k1_subset_1 @ X15)))),
% 0.67/0.88      inference('cnf', [status(esa)], [t22_subset_1])).
% 0.67/0.88  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.67/0.88  thf('22', plain, (![X12 : $i]: ((k2_subset_1 @ X12) = (X12))),
% 0.67/0.88      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.67/0.88  thf('23', plain,
% 0.67/0.88      (![X15 : $i]: ((X15) = (k3_subset_1 @ X15 @ (k1_subset_1 @ X15)))),
% 0.67/0.88      inference('demod', [status(thm)], ['21', '22'])).
% 0.67/0.88  thf('24', plain,
% 0.67/0.88      (![X0 : $i, X1 : $i]: ((X1) = (k3_subset_1 @ X1 @ (k1_subset_1 @ X0)))),
% 0.67/0.88      inference('sup+', [status(thm)], ['20', '23'])).
% 0.67/0.88  thf('25', plain,
% 0.67/0.88      (![X0 : $i, X2 : $i]:
% 0.67/0.88         (((X2) = (k3_subset_1 @ X2 @ (k2_pre_topc @ X0 @ k1_xboole_0)))
% 0.67/0.88          | ~ (v2_pre_topc @ X0)
% 0.67/0.88          | ~ (l1_pre_topc @ X0))),
% 0.67/0.88      inference('sup+', [status(thm)], ['17', '24'])).
% 0.67/0.88  thf(t29_mcart_1, axiom,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.67/0.88          ( ![B:$i]:
% 0.67/0.88            ( ~( ( r2_hidden @ B @ A ) & 
% 0.67/0.88                 ( ![C:$i,D:$i,E:$i]:
% 0.67/0.88                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.67/0.88                        ( ( B ) = ( k3_mcart_1 @ C @ D @ E ) ) ) ) ) ) ) ) ) ))).
% 0.67/0.88  thf('26', plain,
% 0.67/0.88      (![X23 : $i]:
% 0.67/0.88         (((X23) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X23) @ X23))),
% 0.67/0.88      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.67/0.88  thf(d5_xboole_0, axiom,
% 0.67/0.88    (![A:$i,B:$i,C:$i]:
% 0.67/0.88     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.67/0.88       ( ![D:$i]:
% 0.67/0.88         ( ( r2_hidden @ D @ C ) <=>
% 0.67/0.88           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.67/0.88  thf('27', plain,
% 0.67/0.88      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.67/0.88         (~ (r2_hidden @ X4 @ X3)
% 0.67/0.88          | (r2_hidden @ X4 @ X1)
% 0.67/0.88          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.67/0.88      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.67/0.88  thf('28', plain,
% 0.67/0.88      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.67/0.88         ((r2_hidden @ X4 @ X1) | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.67/0.88      inference('simplify', [status(thm)], ['27'])).
% 0.67/0.88  thf('29', plain,
% 0.67/0.88      (![X0 : $i, X1 : $i]:
% 0.67/0.88         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.67/0.88          | (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X1))),
% 0.67/0.88      inference('sup-', [status(thm)], ['26', '28'])).
% 0.67/0.88  thf('30', plain,
% 0.67/0.88      (![X23 : $i]:
% 0.67/0.88         (((X23) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X23) @ X23))),
% 0.67/0.88      inference('cnf', [status(esa)], [t29_mcart_1])).
% 0.67/0.88  thf('31', plain,
% 0.67/0.88      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.67/0.88         (~ (r2_hidden @ X4 @ X3)
% 0.67/0.88          | ~ (r2_hidden @ X4 @ X2)
% 0.67/0.88          | ((X3) != (k4_xboole_0 @ X1 @ X2)))),
% 0.67/0.88      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.67/0.88  thf('32', plain,
% 0.67/0.88      (![X1 : $i, X2 : $i, X4 : $i]:
% 0.67/0.88         (~ (r2_hidden @ X4 @ X2)
% 0.67/0.88          | ~ (r2_hidden @ X4 @ (k4_xboole_0 @ X1 @ X2)))),
% 0.67/0.88      inference('simplify', [status(thm)], ['31'])).
% 0.67/0.88  thf('33', plain,
% 0.67/0.88      (![X0 : $i, X1 : $i]:
% 0.67/0.88         (((k4_xboole_0 @ X1 @ X0) = (k1_xboole_0))
% 0.67/0.88          | ~ (r2_hidden @ (sk_B @ (k4_xboole_0 @ X1 @ X0)) @ X0))),
% 0.67/0.88      inference('sup-', [status(thm)], ['30', '32'])).
% 0.67/0.88  thf('34', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         (((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))
% 0.67/0.88          | ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0)))),
% 0.67/0.88      inference('sup-', [status(thm)], ['29', '33'])).
% 0.67/0.88  thf('35', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.67/0.88      inference('simplify', [status(thm)], ['34'])).
% 0.67/0.88  thf(l32_xboole_1, axiom,
% 0.67/0.88    (![A:$i,B:$i]:
% 0.67/0.88     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.67/0.88  thf('36', plain,
% 0.67/0.88      (![X6 : $i, X7 : $i]:
% 0.67/0.88         ((r1_tarski @ X6 @ X7) | ((k4_xboole_0 @ X6 @ X7) != (k1_xboole_0)))),
% 0.67/0.88      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.67/0.88  thf('37', plain,
% 0.67/0.88      (![X0 : $i]: (((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ X0 @ X0))),
% 0.67/0.88      inference('sup-', [status(thm)], ['35', '36'])).
% 0.67/0.88  thf('38', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.67/0.88      inference('simplify', [status(thm)], ['37'])).
% 0.67/0.88  thf(t3_subset, axiom,
% 0.67/0.88    (![A:$i,B:$i]:
% 0.67/0.88     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.67/0.88  thf('39', plain,
% 0.67/0.88      (![X17 : $i, X19 : $i]:
% 0.67/0.88         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 0.67/0.88      inference('cnf', [status(esa)], [t3_subset])).
% 0.67/0.88  thf('40', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.67/0.88      inference('sup-', [status(thm)], ['38', '39'])).
% 0.67/0.88  thf(d1_tops_1, axiom,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( l1_pre_topc @ A ) =>
% 0.67/0.88       ( ![B:$i]:
% 0.67/0.88         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( u1_struct_0 @ A ) ) ) =>
% 0.67/0.88           ( ( k1_tops_1 @ A @ B ) =
% 0.67/0.88             ( k3_subset_1 @
% 0.67/0.88               ( u1_struct_0 @ A ) @ 
% 0.67/0.88               ( k2_pre_topc @ A @ ( k3_subset_1 @ ( u1_struct_0 @ A ) @ B ) ) ) ) ) ) ))).
% 0.67/0.88  thf('41', plain,
% 0.67/0.88      (![X33 : $i, X34 : $i]:
% 0.67/0.88         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (u1_struct_0 @ X34)))
% 0.67/0.88          | ((k1_tops_1 @ X34 @ X33)
% 0.67/0.88              = (k3_subset_1 @ (u1_struct_0 @ X34) @ 
% 0.67/0.88                 (k2_pre_topc @ X34 @ (k3_subset_1 @ (u1_struct_0 @ X34) @ X33))))
% 0.67/0.88          | ~ (l1_pre_topc @ X34))),
% 0.67/0.88      inference('cnf', [status(esa)], [d1_tops_1])).
% 0.67/0.88  thf('42', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         (~ (l1_pre_topc @ X0)
% 0.67/0.88          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.67/0.88              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.67/0.88                 (k2_pre_topc @ X0 @ 
% 0.67/0.88                  (k3_subset_1 @ (u1_struct_0 @ X0) @ (u1_struct_0 @ X0))))))),
% 0.67/0.88      inference('sup-', [status(thm)], ['40', '41'])).
% 0.67/0.88  thf('43', plain,
% 0.67/0.88      (![X16 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 0.67/0.88      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.67/0.88  thf(involutiveness_k3_subset_1, axiom,
% 0.67/0.88    (![A:$i,B:$i]:
% 0.67/0.88     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.67/0.88       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.67/0.88  thf('44', plain,
% 0.67/0.88      (![X13 : $i, X14 : $i]:
% 0.67/0.88         (((k3_subset_1 @ X14 @ (k3_subset_1 @ X14 @ X13)) = (X13))
% 0.67/0.88          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.67/0.88      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.67/0.88  thf('45', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         ((k3_subset_1 @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.67/0.88      inference('sup-', [status(thm)], ['43', '44'])).
% 0.67/0.88  thf('46', plain, (![X11 : $i]: ((k1_subset_1 @ X11) = (k1_xboole_0))),
% 0.67/0.88      inference('cnf', [status(esa)], [d3_subset_1])).
% 0.67/0.88  thf('47', plain,
% 0.67/0.88      (![X15 : $i]: ((X15) = (k3_subset_1 @ X15 @ (k1_subset_1 @ X15)))),
% 0.67/0.88      inference('demod', [status(thm)], ['21', '22'])).
% 0.67/0.88  thf('48', plain, (![X0 : $i]: ((X0) = (k3_subset_1 @ X0 @ k1_xboole_0))),
% 0.67/0.88      inference('sup+', [status(thm)], ['46', '47'])).
% 0.67/0.88  thf('49', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.67/0.88      inference('demod', [status(thm)], ['45', '48'])).
% 0.67/0.88  thf('50', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         (~ (l1_pre_topc @ X0)
% 0.67/0.88          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0))
% 0.67/0.88              = (k3_subset_1 @ (u1_struct_0 @ X0) @ 
% 0.67/0.88                 (k2_pre_topc @ X0 @ k1_xboole_0))))),
% 0.67/0.88      inference('demod', [status(thm)], ['42', '49'])).
% 0.67/0.88  thf('51', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         (((k1_tops_1 @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.67/0.88          | ~ (l1_pre_topc @ X0)
% 0.67/0.88          | ~ (v2_pre_topc @ X0)
% 0.67/0.88          | ~ (l1_pre_topc @ X0))),
% 0.67/0.88      inference('sup+', [status(thm)], ['25', '50'])).
% 0.67/0.88  thf('52', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         (~ (v2_pre_topc @ X0)
% 0.67/0.88          | ~ (l1_pre_topc @ X0)
% 0.67/0.88          | ((k1_tops_1 @ X0 @ (u1_struct_0 @ X0)) = (u1_struct_0 @ X0)))),
% 0.67/0.88      inference('simplify', [status(thm)], ['51'])).
% 0.67/0.88  thf('53', plain,
% 0.67/0.88      (![X0 : $i]:
% 0.67/0.88         (((k1_tops_1 @ X0 @ (k2_struct_0 @ X0)) = (u1_struct_0 @ X0))
% 0.67/0.88          | ~ (l1_struct_0 @ X0)
% 0.67/0.88          | ~ (l1_pre_topc @ X0)
% 0.67/0.88          | ~ (v2_pre_topc @ X0))),
% 0.67/0.88      inference('sup+', [status(thm)], ['1', '52'])).
% 0.67/0.88  thf(t43_tops_1, conjecture,
% 0.67/0.88    (![A:$i]:
% 0.67/0.88     ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.67/0.88       ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ))).
% 0.67/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.88    (~( ![A:$i]:
% 0.67/0.88        ( ( ( v2_pre_topc @ A ) & ( l1_pre_topc @ A ) ) =>
% 0.67/0.88          ( ( k1_tops_1 @ A @ ( k2_struct_0 @ A ) ) = ( k2_struct_0 @ A ) ) ) )),
% 0.67/0.88    inference('cnf.neg', [status(esa)], [t43_tops_1])).
% 0.67/0.88  thf('54', plain,
% 0.67/0.88      (((k1_tops_1 @ sk_A @ (k2_struct_0 @ sk_A)) != (k2_struct_0 @ sk_A))),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('55', plain,
% 0.67/0.88      ((((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))
% 0.67/0.88        | ~ (v2_pre_topc @ sk_A)
% 0.67/0.88        | ~ (l1_pre_topc @ sk_A)
% 0.67/0.88        | ~ (l1_struct_0 @ sk_A))),
% 0.67/0.88      inference('sup-', [status(thm)], ['53', '54'])).
% 0.67/0.88  thf('56', plain, ((v2_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('57', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf('58', plain, ((l1_pre_topc @ sk_A)),
% 0.67/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.88  thf(dt_l1_pre_topc, axiom,
% 0.67/0.88    (![A:$i]: ( ( l1_pre_topc @ A ) => ( l1_struct_0 @ A ) ))).
% 0.67/0.88  thf('59', plain,
% 0.67/0.88      (![X30 : $i]: ((l1_struct_0 @ X30) | ~ (l1_pre_topc @ X30))),
% 0.67/0.88      inference('cnf', [status(esa)], [dt_l1_pre_topc])).
% 0.67/0.88  thf('60', plain, ((l1_struct_0 @ sk_A)),
% 0.67/0.88      inference('sup-', [status(thm)], ['58', '59'])).
% 0.67/0.88  thf('61', plain, (((u1_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['55', '56', '57', '60'])).
% 0.67/0.88  thf('62', plain,
% 0.67/0.88      ((((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A)) | ~ (l1_struct_0 @ sk_A))),
% 0.67/0.88      inference('sup-', [status(thm)], ['0', '61'])).
% 0.67/0.88  thf('63', plain, ((l1_struct_0 @ sk_A)),
% 0.67/0.88      inference('sup-', [status(thm)], ['58', '59'])).
% 0.67/0.88  thf('64', plain, (((k2_struct_0 @ sk_A) != (k2_struct_0 @ sk_A))),
% 0.67/0.88      inference('demod', [status(thm)], ['62', '63'])).
% 0.67/0.88  thf('65', plain, ($false), inference('simplify', [status(thm)], ['64'])).
% 0.67/0.88  
% 0.67/0.88  % SZS output end Refutation
% 0.67/0.88  
% 0.71/0.89  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
