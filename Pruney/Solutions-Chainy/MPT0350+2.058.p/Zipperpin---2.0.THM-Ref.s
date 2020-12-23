%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QtsT4s139R

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:36:53 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.15s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 245 expanded)
%              Number of leaves         :   33 (  91 expanded)
%              Depth                    :   20
%              Number of atoms          : 1008 (1843 expanded)
%              Number of equality atoms :  104 ( 192 expanded)
%              Maximal formula depth    :   10 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_xboole_0_type,type,(
    k5_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t25_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_subset_1])).

thf('0',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('1',plain,(
    ! [X36: $i] :
      ( ( k2_subset_1 @ X36 )
      = X36 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('2',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k3_subset_1 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X37: $i,X38: $i] :
      ( ( ( k3_subset_1 @ X37 @ X38 )
        = ( k4_xboole_0 @ X37 @ X38 ) )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('5',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ sk_B ) )
 != sk_A ),
    inference(demod,[status(thm)],['2','5'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('7',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('8',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ X26 @ X27 )
      | ( r2_hidden @ X26 @ X28 )
      | ( X28
       != ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('9',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r2_hidden @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( r1_tarski @ X26 @ X27 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('11',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X33 @ X34 )
      | ( m1_subset_1 @ X33 @ X34 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('13',plain,(
    ! [X41: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('16',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X43 ) )
      | ( ( k4_subset_1 @ X43 @ X42 @ X44 )
        = ( k2_xboole_0 @ X42 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k4_subset_1 @ sk_A @ sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) )
      = ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(commutativity_k5_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k5_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t92_xboole_1,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ A )
      = k1_xboole_0 ) )).

thf('21',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf(t91_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C )
      = ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ) )).

thf('22',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf(t5_boole,axiom,(
    ! [A: $i] :
      ( ( k5_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('25',plain,(
    ! [X14: $i] :
      ( ( k5_xboole_0 @ X14 @ k1_xboole_0 )
      = X14 ) ),
    inference(cnf,[status(esa)],[t5_boole])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ X34 )
      | ( r2_hidden @ X33 @ X34 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X41: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('33',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X29 @ X28 )
      | ( r1_tarski @ X29 @ X27 )
      | ( X28
       != ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('35',plain,(
    ! [X27: $i,X29: $i] :
      ( ( r1_tarski @ X29 @ X27 )
      | ~ ( r2_hidden @ X29 @ ( k1_zfmisc_1 @ X27 ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['33','35'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('37',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('38',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t112_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ) )).

thf('40',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X7 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X2 @ X1 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ sk_B @ ( k3_xboole_0 @ X0 @ sk_B ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t100_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('44',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = ( k3_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['42','45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ ( k5_xboole_0 @ X0 @ sk_A ) )
      = ( k3_xboole_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','47'])).

thf('49',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('50',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ sk_B @ X0 ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['48','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X0 @ X1 ) )
      = ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_B ) @ k1_xboole_0 )
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('62',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ X4 )
      = X4 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf('63',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k5_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X18: $i] :
      ( ( k5_xboole_0 @ X18 @ X18 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t92_xboole_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k3_xboole_0 @ X10 @ X11 )
        = X10 )
      | ~ ( r1_tarski @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k3_xboole_0 @ X0 @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['61','72'])).

thf('74',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('75',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k5_xboole_0 @ ( k3_xboole_0 @ X7 @ X9 ) @ ( k3_xboole_0 @ X8 @ X9 ) )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t112_xboole_1])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['76','77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k3_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['73','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['20','27'])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( X1
      = ( k5_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ sk_B )
      = ( k5_xboole_0 @ ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_B ) @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['80','85'])).

thf('87',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k5_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['24','25'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ sk_B )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf(t94_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('91',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ ( k5_xboole_0 @ X19 @ X20 ) @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t94_xboole_1])).

thf('92',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( k5_xboole_0 @ ( k5_xboole_0 @ X15 @ X16 ) @ X17 )
      = ( k5_xboole_0 @ X15 @ ( k5_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t91_xboole_1])).

thf('93',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k5_xboole_0 @ X1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['90','93'])).

thf('95',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k4_xboole_0 @ X5 @ X6 )
      = ( k5_xboole_0 @ X5 @ ( k3_xboole_0 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t100_xboole_1])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = ( k5_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['89','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X0 @ X1 )
      = ( k5_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ X0 @ sk_B ) )
      = ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['97','98'])).

thf('100',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_A )
    = sk_B ),
    inference('sup-',[status(thm)],['36','37'])).

thf('101',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k2_xboole_0 @ X19 @ X20 )
      = ( k5_xboole_0 @ X19 @ ( k5_xboole_0 @ X20 @ ( k3_xboole_0 @ X19 @ X20 ) ) ) ) ),
    inference(demod,[status(thm)],['91','92'])).

thf('102',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = ( k5_xboole_0 @ sk_B @ ( k5_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup+',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k5_xboole_0 @ X3 @ X2 )
      = ( k5_xboole_0 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k5_xboole_0])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k5_xboole_0 @ X1 @ ( k5_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('105',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['102','103','104'])).

thf('106',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['6','18','99','105'])).

thf('107',plain,(
    $false ),
    inference(simplify,[status(thm)],['106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QtsT4s139R
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:09:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 1.15/1.38  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.15/1.38  % Solved by: fo/fo7.sh
% 1.15/1.38  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.15/1.38  % done 1721 iterations in 0.924s
% 1.15/1.38  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.15/1.38  % SZS output start Refutation
% 1.15/1.38  thf(k5_xboole_0_type, type, k5_xboole_0: $i > $i > $i).
% 1.15/1.38  thf(sk_A_type, type, sk_A: $i).
% 1.15/1.38  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 1.15/1.38  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.15/1.38  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.15/1.38  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.15/1.38  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 1.15/1.38  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.15/1.38  thf(sk_B_type, type, sk_B: $i).
% 1.15/1.38  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.15/1.38  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 1.15/1.38  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.15/1.38  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.15/1.38  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.15/1.38  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.15/1.38  thf(t25_subset_1, conjecture,
% 1.15/1.38    (![A:$i,B:$i]:
% 1.15/1.38     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.15/1.38       ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 1.15/1.38         ( k2_subset_1 @ A ) ) ))).
% 1.15/1.38  thf(zf_stmt_0, negated_conjecture,
% 1.15/1.38    (~( ![A:$i,B:$i]:
% 1.15/1.38        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.15/1.38          ( ( k4_subset_1 @ A @ B @ ( k3_subset_1 @ A @ B ) ) =
% 1.15/1.38            ( k2_subset_1 @ A ) ) ) )),
% 1.15/1.38    inference('cnf.neg', [status(esa)], [t25_subset_1])).
% 1.15/1.38  thf('0', plain,
% 1.15/1.38      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B))
% 1.15/1.38         != (k2_subset_1 @ sk_A))),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 1.15/1.38  thf('1', plain, (![X36 : $i]: ((k2_subset_1 @ X36) = (X36))),
% 1.15/1.38      inference('cnf', [status(esa)], [d4_subset_1])).
% 1.15/1.38  thf('2', plain,
% 1.15/1.38      (((k4_subset_1 @ sk_A @ sk_B @ (k3_subset_1 @ sk_A @ sk_B)) != (sk_A))),
% 1.15/1.38      inference('demod', [status(thm)], ['0', '1'])).
% 1.15/1.38  thf('3', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf(d5_subset_1, axiom,
% 1.15/1.38    (![A:$i,B:$i]:
% 1.15/1.38     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 1.15/1.38       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 1.15/1.38  thf('4', plain,
% 1.15/1.38      (![X37 : $i, X38 : $i]:
% 1.15/1.38         (((k3_subset_1 @ X37 @ X38) = (k4_xboole_0 @ X37 @ X38))
% 1.15/1.38          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X37)))),
% 1.15/1.38      inference('cnf', [status(esa)], [d5_subset_1])).
% 1.15/1.38  thf('5', plain,
% 1.15/1.38      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 1.15/1.38      inference('sup-', [status(thm)], ['3', '4'])).
% 1.15/1.38  thf('6', plain,
% 1.15/1.38      (((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ sk_B)) != (sk_A))),
% 1.15/1.38      inference('demod', [status(thm)], ['2', '5'])).
% 1.15/1.38  thf(t36_xboole_1, axiom,
% 1.15/1.38    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 1.15/1.38  thf('7', plain,
% 1.15/1.38      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 1.15/1.38      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.15/1.38  thf(d1_zfmisc_1, axiom,
% 1.15/1.38    (![A:$i,B:$i]:
% 1.15/1.38     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 1.15/1.38       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 1.15/1.38  thf('8', plain,
% 1.15/1.38      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.15/1.38         (~ (r1_tarski @ X26 @ X27)
% 1.15/1.38          | (r2_hidden @ X26 @ X28)
% 1.15/1.38          | ((X28) != (k1_zfmisc_1 @ X27)))),
% 1.15/1.38      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.15/1.38  thf('9', plain,
% 1.15/1.38      (![X26 : $i, X27 : $i]:
% 1.15/1.38         ((r2_hidden @ X26 @ (k1_zfmisc_1 @ X27)) | ~ (r1_tarski @ X26 @ X27))),
% 1.15/1.38      inference('simplify', [status(thm)], ['8'])).
% 1.15/1.38  thf('10', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]:
% 1.15/1.38         (r2_hidden @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.15/1.38      inference('sup-', [status(thm)], ['7', '9'])).
% 1.15/1.38  thf(d2_subset_1, axiom,
% 1.15/1.38    (![A:$i,B:$i]:
% 1.15/1.38     ( ( ( v1_xboole_0 @ A ) =>
% 1.15/1.38         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 1.15/1.38       ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.15/1.38         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 1.15/1.38  thf('11', plain,
% 1.15/1.38      (![X33 : $i, X34 : $i]:
% 1.15/1.38         (~ (r2_hidden @ X33 @ X34)
% 1.15/1.38          | (m1_subset_1 @ X33 @ X34)
% 1.15/1.38          | (v1_xboole_0 @ X34))),
% 1.15/1.38      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.15/1.38  thf('12', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]:
% 1.15/1.38         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 1.15/1.38          | (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 1.15/1.38      inference('sup-', [status(thm)], ['10', '11'])).
% 1.15/1.38  thf(fc1_subset_1, axiom,
% 1.15/1.38    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 1.15/1.38  thf('13', plain, (![X41 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X41))),
% 1.15/1.38      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.15/1.38  thf('14', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]:
% 1.15/1.38         (m1_subset_1 @ (k4_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.15/1.38      inference('clc', [status(thm)], ['12', '13'])).
% 1.15/1.38  thf('15', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf(redefinition_k4_subset_1, axiom,
% 1.15/1.38    (![A:$i,B:$i,C:$i]:
% 1.15/1.38     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 1.15/1.38         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.15/1.38       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 1.15/1.38  thf('16', plain,
% 1.15/1.38      (![X42 : $i, X43 : $i, X44 : $i]:
% 1.15/1.38         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43))
% 1.15/1.38          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X43))
% 1.15/1.38          | ((k4_subset_1 @ X43 @ X42 @ X44) = (k2_xboole_0 @ X42 @ X44)))),
% 1.15/1.38      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 1.15/1.38  thf('17', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 1.15/1.38          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 1.15/1.38      inference('sup-', [status(thm)], ['15', '16'])).
% 1.15/1.38  thf('18', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         ((k4_subset_1 @ sk_A @ sk_B @ (k4_xboole_0 @ sk_A @ X0))
% 1.15/1.38           = (k2_xboole_0 @ sk_B @ (k4_xboole_0 @ sk_A @ X0)))),
% 1.15/1.38      inference('sup-', [status(thm)], ['14', '17'])).
% 1.15/1.38  thf(commutativity_k3_xboole_0, axiom,
% 1.15/1.38    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 1.15/1.38  thf('19', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.15/1.38      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.15/1.38  thf(commutativity_k5_xboole_0, axiom,
% 1.15/1.38    (![A:$i,B:$i]: ( ( k5_xboole_0 @ A @ B ) = ( k5_xboole_0 @ B @ A ) ))).
% 1.15/1.38  thf('20', plain,
% 1.15/1.38      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.15/1.38      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.15/1.38  thf(t92_xboole_1, axiom,
% 1.15/1.38    (![A:$i]: ( ( k5_xboole_0 @ A @ A ) = ( k1_xboole_0 ) ))).
% 1.15/1.38  thf('21', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 1.15/1.38      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.15/1.38  thf(t91_xboole_1, axiom,
% 1.15/1.38    (![A:$i,B:$i,C:$i]:
% 1.15/1.38     ( ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ C ) =
% 1.15/1.38       ( k5_xboole_0 @ A @ ( k5_xboole_0 @ B @ C ) ) ))).
% 1.15/1.38  thf('22', plain,
% 1.15/1.38      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.15/1.38         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 1.15/1.38           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 1.15/1.38      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.15/1.38  thf('23', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]:
% 1.15/1.38         ((k5_xboole_0 @ k1_xboole_0 @ X0)
% 1.15/1.38           = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.15/1.38      inference('sup+', [status(thm)], ['21', '22'])).
% 1.15/1.38  thf('24', plain,
% 1.15/1.38      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.15/1.38      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.15/1.38  thf(t5_boole, axiom,
% 1.15/1.38    (![A:$i]: ( ( k5_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 1.15/1.38  thf('25', plain, (![X14 : $i]: ((k5_xboole_0 @ X14 @ k1_xboole_0) = (X14))),
% 1.15/1.38      inference('cnf', [status(esa)], [t5_boole])).
% 1.15/1.38  thf('26', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.15/1.38      inference('sup+', [status(thm)], ['24', '25'])).
% 1.15/1.38  thf('27', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]:
% 1.15/1.38         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.15/1.38      inference('demod', [status(thm)], ['23', '26'])).
% 1.15/1.38  thf('28', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]:
% 1.15/1.38         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.15/1.38      inference('sup+', [status(thm)], ['20', '27'])).
% 1.15/1.38  thf('29', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.15/1.38      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.15/1.38  thf('30', plain,
% 1.15/1.38      (![X33 : $i, X34 : $i]:
% 1.15/1.38         (~ (m1_subset_1 @ X33 @ X34)
% 1.15/1.38          | (r2_hidden @ X33 @ X34)
% 1.15/1.38          | (v1_xboole_0 @ X34))),
% 1.15/1.38      inference('cnf', [status(esa)], [d2_subset_1])).
% 1.15/1.38  thf('31', plain,
% 1.15/1.38      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 1.15/1.38        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 1.15/1.38      inference('sup-', [status(thm)], ['29', '30'])).
% 1.15/1.38  thf('32', plain, (![X41 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X41))),
% 1.15/1.38      inference('cnf', [status(esa)], [fc1_subset_1])).
% 1.15/1.38  thf('33', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 1.15/1.38      inference('clc', [status(thm)], ['31', '32'])).
% 1.15/1.38  thf('34', plain,
% 1.15/1.38      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.15/1.38         (~ (r2_hidden @ X29 @ X28)
% 1.15/1.38          | (r1_tarski @ X29 @ X27)
% 1.15/1.38          | ((X28) != (k1_zfmisc_1 @ X27)))),
% 1.15/1.38      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 1.15/1.38  thf('35', plain,
% 1.15/1.38      (![X27 : $i, X29 : $i]:
% 1.15/1.38         ((r1_tarski @ X29 @ X27) | ~ (r2_hidden @ X29 @ (k1_zfmisc_1 @ X27)))),
% 1.15/1.38      inference('simplify', [status(thm)], ['34'])).
% 1.15/1.38  thf('36', plain, ((r1_tarski @ sk_B @ sk_A)),
% 1.15/1.38      inference('sup-', [status(thm)], ['33', '35'])).
% 1.15/1.38  thf(t28_xboole_1, axiom,
% 1.15/1.38    (![A:$i,B:$i]:
% 1.15/1.38     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.15/1.38  thf('37', plain,
% 1.15/1.38      (![X10 : $i, X11 : $i]:
% 1.15/1.38         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 1.15/1.38      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.15/1.38  thf('38', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 1.15/1.38      inference('sup-', [status(thm)], ['36', '37'])).
% 1.15/1.38  thf('39', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.15/1.38      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.15/1.38  thf(t112_xboole_1, axiom,
% 1.15/1.38    (![A:$i,B:$i,C:$i]:
% 1.15/1.38     ( ( k5_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ C @ B ) ) =
% 1.15/1.38       ( k3_xboole_0 @ ( k5_xboole_0 @ A @ C ) @ B ) ))).
% 1.15/1.38  thf('40', plain,
% 1.15/1.38      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.15/1.38         ((k5_xboole_0 @ (k3_xboole_0 @ X7 @ X9) @ (k3_xboole_0 @ X8 @ X9))
% 1.15/1.38           = (k3_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9))),
% 1.15/1.38      inference('cnf', [status(esa)], [t112_xboole_1])).
% 1.15/1.38  thf('41', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.15/1.38         ((k5_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X2 @ X1))
% 1.15/1.38           = (k3_xboole_0 @ (k5_xboole_0 @ X0 @ X2) @ X1))),
% 1.15/1.38      inference('sup+', [status(thm)], ['39', '40'])).
% 1.15/1.38  thf('42', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         ((k5_xboole_0 @ sk_B @ (k3_xboole_0 @ X0 @ sk_B))
% 1.15/1.38           = (k3_xboole_0 @ (k5_xboole_0 @ sk_A @ X0) @ sk_B))),
% 1.15/1.38      inference('sup+', [status(thm)], ['38', '41'])).
% 1.15/1.38  thf('43', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.15/1.38      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.15/1.38  thf(t100_xboole_1, axiom,
% 1.15/1.38    (![A:$i,B:$i]:
% 1.15/1.38     ( ( k4_xboole_0 @ A @ B ) = ( k5_xboole_0 @ A @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.15/1.38  thf('44', plain,
% 1.15/1.38      (![X5 : $i, X6 : $i]:
% 1.15/1.38         ((k4_xboole_0 @ X5 @ X6)
% 1.15/1.38           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.15/1.38      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.15/1.38  thf('45', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]:
% 1.15/1.38         ((k4_xboole_0 @ X0 @ X1)
% 1.15/1.38           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.15/1.38      inference('sup+', [status(thm)], ['43', '44'])).
% 1.15/1.38  thf('46', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.15/1.38      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.15/1.38  thf('47', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         ((k4_xboole_0 @ sk_B @ X0)
% 1.15/1.38           = (k3_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ X0)))),
% 1.15/1.38      inference('demod', [status(thm)], ['42', '45', '46'])).
% 1.15/1.38  thf('48', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         ((k4_xboole_0 @ sk_B @ (k5_xboole_0 @ X0 @ sk_A))
% 1.15/1.38           = (k3_xboole_0 @ sk_B @ X0))),
% 1.15/1.38      inference('sup+', [status(thm)], ['28', '47'])).
% 1.15/1.38  thf('49', plain,
% 1.15/1.38      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 1.15/1.38      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.15/1.38  thf('50', plain,
% 1.15/1.38      (![X10 : $i, X11 : $i]:
% 1.15/1.38         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 1.15/1.38      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.15/1.38  thf('51', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]:
% 1.15/1.38         ((k3_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0)
% 1.15/1.38           = (k4_xboole_0 @ X0 @ X1))),
% 1.15/1.38      inference('sup-', [status(thm)], ['49', '50'])).
% 1.15/1.38  thf('52', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.15/1.38      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.15/1.38  thf('53', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]:
% 1.15/1.38         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.15/1.38           = (k4_xboole_0 @ X0 @ X1))),
% 1.15/1.38      inference('demod', [status(thm)], ['51', '52'])).
% 1.15/1.38  thf('54', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]:
% 1.15/1.38         ((k4_xboole_0 @ X0 @ X1)
% 1.15/1.38           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.15/1.38      inference('sup+', [status(thm)], ['43', '44'])).
% 1.15/1.38  thf('55', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]:
% 1.15/1.38         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1)
% 1.15/1.38           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.15/1.38      inference('sup+', [status(thm)], ['53', '54'])).
% 1.15/1.38  thf('56', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 1.15/1.38      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.15/1.38  thf('57', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]:
% 1.15/1.38         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X1) = (k1_xboole_0))),
% 1.15/1.38      inference('demod', [status(thm)], ['55', '56'])).
% 1.15/1.38  thf('58', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         ((k4_xboole_0 @ (k3_xboole_0 @ sk_B @ X0) @ sk_B) = (k1_xboole_0))),
% 1.15/1.38      inference('sup+', [status(thm)], ['48', '57'])).
% 1.15/1.38  thf('59', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         ((k4_xboole_0 @ (k3_xboole_0 @ X0 @ sk_B) @ sk_B) = (k1_xboole_0))),
% 1.15/1.38      inference('sup+', [status(thm)], ['19', '58'])).
% 1.15/1.38  thf('60', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]:
% 1.15/1.38         ((k3_xboole_0 @ X0 @ (k4_xboole_0 @ X0 @ X1))
% 1.15/1.38           = (k4_xboole_0 @ X0 @ X1))),
% 1.15/1.38      inference('demod', [status(thm)], ['51', '52'])).
% 1.15/1.38  thf('61', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         ((k3_xboole_0 @ (k3_xboole_0 @ X0 @ sk_B) @ k1_xboole_0)
% 1.15/1.38           = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ sk_B) @ sk_B))),
% 1.15/1.38      inference('sup+', [status(thm)], ['59', '60'])).
% 1.15/1.38  thf(idempotence_k3_xboole_0, axiom,
% 1.15/1.38    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 1.15/1.38  thf('62', plain, (![X4 : $i]: ((k3_xboole_0 @ X4 @ X4) = (X4))),
% 1.15/1.38      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 1.15/1.38  thf('63', plain,
% 1.15/1.38      (![X5 : $i, X6 : $i]:
% 1.15/1.38         ((k4_xboole_0 @ X5 @ X6)
% 1.15/1.38           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.15/1.38      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.15/1.38  thf('64', plain,
% 1.15/1.38      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k5_xboole_0 @ X0 @ X0))),
% 1.15/1.38      inference('sup+', [status(thm)], ['62', '63'])).
% 1.15/1.38  thf('65', plain, (![X18 : $i]: ((k5_xboole_0 @ X18 @ X18) = (k1_xboole_0))),
% 1.15/1.38      inference('cnf', [status(esa)], [t92_xboole_1])).
% 1.15/1.38  thf('66', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.15/1.38      inference('sup+', [status(thm)], ['64', '65'])).
% 1.15/1.38  thf('67', plain,
% 1.15/1.38      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 1.15/1.38      inference('cnf', [status(esa)], [t36_xboole_1])).
% 1.15/1.38  thf('68', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.15/1.38      inference('sup+', [status(thm)], ['66', '67'])).
% 1.15/1.38  thf('69', plain,
% 1.15/1.38      (![X10 : $i, X11 : $i]:
% 1.15/1.38         (((k3_xboole_0 @ X10 @ X11) = (X10)) | ~ (r1_tarski @ X10 @ X11))),
% 1.15/1.38      inference('cnf', [status(esa)], [t28_xboole_1])).
% 1.15/1.38  thf('70', plain,
% 1.15/1.38      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 1.15/1.38      inference('sup-', [status(thm)], ['68', '69'])).
% 1.15/1.38  thf('71', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.15/1.38      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.15/1.38  thf('72', plain,
% 1.15/1.38      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 1.15/1.38      inference('sup+', [status(thm)], ['70', '71'])).
% 1.15/1.38  thf('73', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         ((k1_xboole_0) = (k4_xboole_0 @ (k3_xboole_0 @ X0 @ sk_B) @ sk_B))),
% 1.15/1.38      inference('demod', [status(thm)], ['61', '72'])).
% 1.15/1.38  thf('74', plain,
% 1.15/1.38      (![X5 : $i, X6 : $i]:
% 1.15/1.38         ((k4_xboole_0 @ X5 @ X6)
% 1.15/1.38           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.15/1.38      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.15/1.38  thf('75', plain,
% 1.15/1.38      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.15/1.38         ((k5_xboole_0 @ (k3_xboole_0 @ X7 @ X9) @ (k3_xboole_0 @ X8 @ X9))
% 1.15/1.38           = (k3_xboole_0 @ (k5_xboole_0 @ X7 @ X8) @ X9))),
% 1.15/1.38      inference('cnf', [status(esa)], [t112_xboole_1])).
% 1.15/1.38  thf('76', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]:
% 1.15/1.38         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 1.15/1.38           = (k3_xboole_0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0)) @ X0))),
% 1.15/1.38      inference('sup+', [status(thm)], ['74', '75'])).
% 1.15/1.38  thf('77', plain,
% 1.15/1.38      (![X5 : $i, X6 : $i]:
% 1.15/1.38         ((k4_xboole_0 @ X5 @ X6)
% 1.15/1.38           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.15/1.38      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.15/1.38  thf('78', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.15/1.38      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.15/1.38  thf('79', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]:
% 1.15/1.38         ((k4_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X0)
% 1.15/1.38           = (k3_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.15/1.38      inference('demod', [status(thm)], ['76', '77', '78'])).
% 1.15/1.38  thf('80', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         ((k1_xboole_0) = (k3_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_B)))),
% 1.15/1.38      inference('demod', [status(thm)], ['73', '79'])).
% 1.15/1.38  thf('81', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]:
% 1.15/1.38         ((k4_xboole_0 @ X0 @ X1)
% 1.15/1.38           = (k5_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.15/1.38      inference('sup+', [status(thm)], ['43', '44'])).
% 1.15/1.38  thf('82', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]:
% 1.15/1.38         ((X1) = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.15/1.38      inference('sup+', [status(thm)], ['20', '27'])).
% 1.15/1.38  thf('83', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]:
% 1.15/1.38         ((X1)
% 1.15/1.38           = (k5_xboole_0 @ (k3_xboole_0 @ X0 @ X1) @ (k4_xboole_0 @ X1 @ X0)))),
% 1.15/1.38      inference('sup+', [status(thm)], ['81', '82'])).
% 1.15/1.38  thf('84', plain,
% 1.15/1.38      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.15/1.38      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.15/1.38  thf('85', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]:
% 1.15/1.38         ((X1)
% 1.15/1.38           = (k5_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 1.15/1.38      inference('demod', [status(thm)], ['83', '84'])).
% 1.15/1.38  thf('86', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         ((k4_xboole_0 @ X0 @ sk_B)
% 1.15/1.38           = (k5_xboole_0 @ (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_B) @ 
% 1.15/1.38              k1_xboole_0))),
% 1.15/1.38      inference('sup+', [status(thm)], ['80', '85'])).
% 1.15/1.38  thf('87', plain,
% 1.15/1.38      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.15/1.38      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.15/1.38  thf('88', plain, (![X0 : $i]: ((k5_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 1.15/1.38      inference('sup+', [status(thm)], ['24', '25'])).
% 1.15/1.38  thf('89', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         ((k4_xboole_0 @ X0 @ sk_B)
% 1.15/1.38           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_B))),
% 1.15/1.38      inference('demod', [status(thm)], ['86', '87', '88'])).
% 1.15/1.38  thf('90', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 1.15/1.38      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 1.15/1.38  thf(t94_xboole_1, axiom,
% 1.15/1.38    (![A:$i,B:$i]:
% 1.15/1.38     ( ( k2_xboole_0 @ A @ B ) =
% 1.15/1.38       ( k5_xboole_0 @ ( k5_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ B ) ) ))).
% 1.15/1.38  thf('91', plain,
% 1.15/1.38      (![X19 : $i, X20 : $i]:
% 1.15/1.38         ((k2_xboole_0 @ X19 @ X20)
% 1.15/1.38           = (k5_xboole_0 @ (k5_xboole_0 @ X19 @ X20) @ 
% 1.15/1.38              (k3_xboole_0 @ X19 @ X20)))),
% 1.15/1.38      inference('cnf', [status(esa)], [t94_xboole_1])).
% 1.15/1.38  thf('92', plain,
% 1.15/1.38      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.15/1.38         ((k5_xboole_0 @ (k5_xboole_0 @ X15 @ X16) @ X17)
% 1.15/1.38           = (k5_xboole_0 @ X15 @ (k5_xboole_0 @ X16 @ X17)))),
% 1.15/1.38      inference('cnf', [status(esa)], [t91_xboole_1])).
% 1.15/1.38  thf('93', plain,
% 1.15/1.38      (![X19 : $i, X20 : $i]:
% 1.15/1.38         ((k2_xboole_0 @ X19 @ X20)
% 1.15/1.38           = (k5_xboole_0 @ X19 @ 
% 1.15/1.38              (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X19 @ X20))))),
% 1.15/1.38      inference('demod', [status(thm)], ['91', '92'])).
% 1.15/1.38  thf('94', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]:
% 1.15/1.38         ((k2_xboole_0 @ X0 @ X1)
% 1.15/1.38           = (k5_xboole_0 @ X0 @ (k5_xboole_0 @ X1 @ (k3_xboole_0 @ X1 @ X0))))),
% 1.15/1.38      inference('sup+', [status(thm)], ['90', '93'])).
% 1.15/1.38  thf('95', plain,
% 1.15/1.38      (![X5 : $i, X6 : $i]:
% 1.15/1.38         ((k4_xboole_0 @ X5 @ X6)
% 1.15/1.38           = (k5_xboole_0 @ X5 @ (k3_xboole_0 @ X5 @ X6)))),
% 1.15/1.38      inference('cnf', [status(esa)], [t100_xboole_1])).
% 1.15/1.38  thf('96', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]:
% 1.15/1.38         ((k2_xboole_0 @ X0 @ X1)
% 1.15/1.38           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.15/1.38      inference('demod', [status(thm)], ['94', '95'])).
% 1.15/1.38  thf('97', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         ((k2_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_B))
% 1.15/1.38           = (k5_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_B)))),
% 1.15/1.38      inference('sup+', [status(thm)], ['89', '96'])).
% 1.15/1.38  thf('98', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]:
% 1.15/1.38         ((k2_xboole_0 @ X0 @ X1)
% 1.15/1.38           = (k5_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 1.15/1.38      inference('demod', [status(thm)], ['94', '95'])).
% 1.15/1.38  thf('99', plain,
% 1.15/1.38      (![X0 : $i]:
% 1.15/1.38         ((k2_xboole_0 @ sk_B @ (k4_xboole_0 @ X0 @ sk_B))
% 1.15/1.38           = (k2_xboole_0 @ sk_B @ X0))),
% 1.15/1.38      inference('demod', [status(thm)], ['97', '98'])).
% 1.15/1.38  thf('100', plain, (((k3_xboole_0 @ sk_B @ sk_A) = (sk_B))),
% 1.15/1.38      inference('sup-', [status(thm)], ['36', '37'])).
% 1.15/1.38  thf('101', plain,
% 1.15/1.38      (![X19 : $i, X20 : $i]:
% 1.15/1.38         ((k2_xboole_0 @ X19 @ X20)
% 1.15/1.38           = (k5_xboole_0 @ X19 @ 
% 1.15/1.38              (k5_xboole_0 @ X20 @ (k3_xboole_0 @ X19 @ X20))))),
% 1.15/1.38      inference('demod', [status(thm)], ['91', '92'])).
% 1.15/1.38  thf('102', plain,
% 1.15/1.38      (((k2_xboole_0 @ sk_B @ sk_A)
% 1.15/1.38         = (k5_xboole_0 @ sk_B @ (k5_xboole_0 @ sk_A @ sk_B)))),
% 1.15/1.38      inference('sup+', [status(thm)], ['100', '101'])).
% 1.15/1.38  thf('103', plain,
% 1.15/1.38      (![X2 : $i, X3 : $i]: ((k5_xboole_0 @ X3 @ X2) = (k5_xboole_0 @ X2 @ X3))),
% 1.15/1.38      inference('cnf', [status(esa)], [commutativity_k5_xboole_0])).
% 1.15/1.38  thf('104', plain,
% 1.15/1.38      (![X0 : $i, X1 : $i]:
% 1.15/1.38         ((X0) = (k5_xboole_0 @ X1 @ (k5_xboole_0 @ X1 @ X0)))),
% 1.15/1.38      inference('demod', [status(thm)], ['23', '26'])).
% 1.15/1.38  thf('105', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 1.15/1.38      inference('demod', [status(thm)], ['102', '103', '104'])).
% 1.15/1.38  thf('106', plain, (((sk_A) != (sk_A))),
% 1.15/1.38      inference('demod', [status(thm)], ['6', '18', '99', '105'])).
% 1.15/1.38  thf('107', plain, ($false), inference('simplify', [status(thm)], ['106'])).
% 1.15/1.38  
% 1.15/1.38  % SZS output end Refutation
% 1.15/1.38  
% 1.15/1.39  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
