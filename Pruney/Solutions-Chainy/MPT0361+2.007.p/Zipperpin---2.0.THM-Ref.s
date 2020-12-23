%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EyFQRxYFSx

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:51 EST 2020

% Result     : Theorem 3.10s
% Output     : Refutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 208 expanded)
%              Number of leaves         :   29 (  74 expanded)
%              Depth                    :   19
%              Number of atoms          :  923 (1586 expanded)
%              Number of equality atoms :   64 (  99 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t41_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ! [C: $i] :
            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
           => ( r1_tarski @ ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ ( k3_subset_1 @ A @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t41_subset_1])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k4_subset_1 @ sk_A @ sk_B @ sk_C_1 ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('3',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X36 ) )
      | ( ( k4_subset_1 @ X36 @ X35 @ X37 )
        = ( k2_xboole_0 @ X35 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B @ X0 )
        = ( k2_xboole_0 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_xboole_0 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('7',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_xboole_0 @ sk_C_1 @ sk_B ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ~ ( r1_tarski @ ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) @ ( k3_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['0','7'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('9',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ( X2 != X3 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('10',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['9'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('11',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ X20 @ X21 )
      | ( r2_hidden @ X20 @ X22 )
      | ( X22
       != ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('12',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r2_hidden @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('14',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ( m1_subset_1 @ X25 @ X26 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('16',plain,(
    ! [X32: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['15','16'])).

thf(d5_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ B )
        = ( k4_xboole_0 @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t46_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) )
      = k1_xboole_0 ) )).

thf('20',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ X16 @ ( k2_xboole_0 @ X16 @ X17 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t46_xboole_1])).

thf(t41_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C )
      = ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('21',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('22',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X16 @ X16 ) @ X17 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('24',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k4_xboole_0 @ ( k3_subset_1 @ X16 @ X16 ) @ X17 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('25',plain,(
    ! [X38: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('26',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('30',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( r1_tarski @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('32',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('33',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ X1 )
      | ( r1_tarski @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','35'])).

thf('37',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('40',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k3_subset_1 @ X0 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['27','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k3_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ X0 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','44'])).

thf('46',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ X26 )
      | ( r2_hidden @ X25 @ X26 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('50',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X32: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('52',plain,(
    r2_hidden @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X23 @ X22 )
      | ( r1_tarski @ X23 @ X21 )
      | ( X22
       != ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('54',plain,(
    ! [X21: $i,X23: $i] :
      ( ( r1_tarski @ X23 @ X21 )
      | ~ ( r2_hidden @ X23 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('57',plain,
    ( ( k2_xboole_0 @ sk_B @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A )
      = ( k4_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ sk_A )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_B ) @ X0 ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['47','59'])).

thf('61',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('62',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('63',plain,(
    ! [X2: $i,X4: $i] :
      ( ( X2 = X4 )
      | ~ ( r1_tarski @ X4 @ X2 )
      | ~ ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ sk_B ) @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X25 @ X26 )
      | ( r2_hidden @ X25 @ X26 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('69',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X32: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('71',plain,(
    r2_hidden @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X21: $i,X23: $i] :
      ( ( r1_tarski @ X23 @ X21 )
      | ~ ( r2_hidden @ X23 @ ( k1_zfmisc_1 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('73',plain,(
    r1_tarski @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('75',plain,
    ( ( k2_xboole_0 @ sk_C_1 @ sk_A )
    = sk_A ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_C_1 ) @ sk_A )
      = ( k4_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['75','76'])).

thf('78',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ sk_A ) ),
    inference('sup+',[status(thm)],['66','77'])).

thf('79',plain,(
    ! [X3: $i] :
      ( r1_tarski @ X3 @ X3 ) ),
    inference(simplify,[status(thm)],['9'])).

thf('80',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r1_tarski @ X13 @ ( k2_xboole_0 @ X14 @ X15 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X15 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_xboole_0 @ X6 @ X5 )
        = X5 )
      | ~ ( r1_tarski @ X6 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      = ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('84',plain,(
    ! [X18: $i,X19: $i] :
      ( r1_tarski @ X18 @ ( k2_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('85',plain,(
    ! [X20: $i,X21: $i] :
      ( ( r2_hidden @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r1_tarski @ X20 @ X21 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ( m1_subset_1 @ X25 @ X26 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X32: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup+',[status(thm)],['83','90'])).

thf('92',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_xboole_0 @ sk_A @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['78','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['92','95'])).

thf('97',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('98',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = ( k4_xboole_0 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('100',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X10 @ X11 ) @ X12 )
      = ( k4_xboole_0 @ X10 @ ( k2_xboole_0 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t41_xboole_1])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X2 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['99','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k3_subset_1 @ X28 @ X29 )
        = ( k4_xboole_0 @ X28 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[d5_subset_1])).

thf('104',plain,
    ( ( k3_subset_1 @ sk_A @ sk_B )
    = ( k4_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,
    ( ( k3_subset_1 @ sk_A @ ( k2_xboole_0 @ sk_C_1 @ sk_B ) )
    = ( k4_xboole_0 @ ( k3_subset_1 @ sk_A @ sk_B ) @ sk_C_1 ) ),
    inference(demod,[status(thm)],['98','101','104'])).

thf('106',plain,(
    ! [X8: $i,X9: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X8 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('107',plain,(
    $false ),
    inference(demod,[status(thm)],['8','105','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EyFQRxYFSx
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:48:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.10/3.32  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.10/3.32  % Solved by: fo/fo7.sh
% 3.10/3.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.10/3.32  % done 5366 iterations in 2.870s
% 3.10/3.32  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.10/3.32  % SZS output start Refutation
% 3.10/3.32  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.10/3.32  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 3.10/3.32  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 3.10/3.32  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.10/3.32  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 3.10/3.32  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.10/3.32  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.10/3.32  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.10/3.32  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 3.10/3.32  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.10/3.32  thf(sk_A_type, type, sk_A: $i).
% 3.10/3.32  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.10/3.32  thf(sk_B_type, type, sk_B: $i).
% 3.10/3.32  thf(t41_subset_1, conjecture,
% 3.10/3.32    (![A:$i,B:$i]:
% 3.10/3.32     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.10/3.32       ( ![C:$i]:
% 3.10/3.32         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 3.10/3.32           ( r1_tarski @
% 3.10/3.32             ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 3.10/3.32             ( k3_subset_1 @ A @ B ) ) ) ) ))).
% 3.10/3.32  thf(zf_stmt_0, negated_conjecture,
% 3.10/3.32    (~( ![A:$i,B:$i]:
% 3.10/3.32        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.10/3.32          ( ![C:$i]:
% 3.10/3.32            ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 3.10/3.32              ( r1_tarski @
% 3.10/3.32                ( k3_subset_1 @ A @ ( k4_subset_1 @ A @ B @ C ) ) @ 
% 3.10/3.32                ( k3_subset_1 @ A @ B ) ) ) ) ) )),
% 3.10/3.32    inference('cnf.neg', [status(esa)], [t41_subset_1])).
% 3.10/3.32  thf('0', plain,
% 3.10/3.32      (~ (r1_tarski @ 
% 3.10/3.32          (k3_subset_1 @ sk_A @ (k4_subset_1 @ sk_A @ sk_B @ sk_C_1)) @ 
% 3.10/3.32          (k3_subset_1 @ sk_A @ sk_B))),
% 3.10/3.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.10/3.32  thf('1', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 3.10/3.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.10/3.32  thf('2', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 3.10/3.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.10/3.32  thf(redefinition_k4_subset_1, axiom,
% 3.10/3.32    (![A:$i,B:$i,C:$i]:
% 3.10/3.32     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 3.10/3.32         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 3.10/3.32       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 3.10/3.32  thf('3', plain,
% 3.10/3.32      (![X35 : $i, X36 : $i, X37 : $i]:
% 3.10/3.32         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 3.10/3.32          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ X36))
% 3.10/3.32          | ((k4_subset_1 @ X36 @ X35 @ X37) = (k2_xboole_0 @ X35 @ X37)))),
% 3.10/3.32      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 3.10/3.32  thf('4', plain,
% 3.10/3.32      (![X0 : $i]:
% 3.10/3.32         (((k4_subset_1 @ sk_A @ sk_B @ X0) = (k2_xboole_0 @ sk_B @ X0))
% 3.10/3.32          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 3.10/3.32      inference('sup-', [status(thm)], ['2', '3'])).
% 3.10/3.32  thf('5', plain,
% 3.10/3.32      (((k4_subset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_xboole_0 @ sk_B @ sk_C_1))),
% 3.10/3.32      inference('sup-', [status(thm)], ['1', '4'])).
% 3.10/3.32  thf(commutativity_k2_xboole_0, axiom,
% 3.10/3.32    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 3.10/3.32  thf('6', plain,
% 3.10/3.32      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.10/3.32      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.10/3.32  thf('7', plain,
% 3.10/3.32      (((k4_subset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_xboole_0 @ sk_C_1 @ sk_B))),
% 3.10/3.32      inference('demod', [status(thm)], ['5', '6'])).
% 3.10/3.32  thf('8', plain,
% 3.10/3.32      (~ (r1_tarski @ (k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)) @ 
% 3.10/3.32          (k3_subset_1 @ sk_A @ sk_B))),
% 3.10/3.32      inference('demod', [status(thm)], ['0', '7'])).
% 3.10/3.32  thf(d10_xboole_0, axiom,
% 3.10/3.32    (![A:$i,B:$i]:
% 3.10/3.32     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.10/3.32  thf('9', plain,
% 3.10/3.32      (![X2 : $i, X3 : $i]: ((r1_tarski @ X2 @ X3) | ((X2) != (X3)))),
% 3.10/3.32      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.10/3.32  thf('10', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 3.10/3.32      inference('simplify', [status(thm)], ['9'])).
% 3.10/3.32  thf(d1_zfmisc_1, axiom,
% 3.10/3.32    (![A:$i,B:$i]:
% 3.10/3.32     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 3.10/3.32       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 3.10/3.32  thf('11', plain,
% 3.10/3.32      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.10/3.32         (~ (r1_tarski @ X20 @ X21)
% 3.10/3.32          | (r2_hidden @ X20 @ X22)
% 3.10/3.32          | ((X22) != (k1_zfmisc_1 @ X21)))),
% 3.10/3.32      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 3.10/3.32  thf('12', plain,
% 3.10/3.32      (![X20 : $i, X21 : $i]:
% 3.10/3.32         ((r2_hidden @ X20 @ (k1_zfmisc_1 @ X21)) | ~ (r1_tarski @ X20 @ X21))),
% 3.10/3.32      inference('simplify', [status(thm)], ['11'])).
% 3.10/3.32  thf('13', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 3.10/3.32      inference('sup-', [status(thm)], ['10', '12'])).
% 3.10/3.32  thf(d2_subset_1, axiom,
% 3.10/3.32    (![A:$i,B:$i]:
% 3.10/3.32     ( ( ( v1_xboole_0 @ A ) =>
% 3.10/3.32         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 3.10/3.32       ( ( ~( v1_xboole_0 @ A ) ) =>
% 3.10/3.32         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 3.10/3.32  thf('14', plain,
% 3.10/3.32      (![X25 : $i, X26 : $i]:
% 3.10/3.32         (~ (r2_hidden @ X25 @ X26)
% 3.10/3.32          | (m1_subset_1 @ X25 @ X26)
% 3.10/3.32          | (v1_xboole_0 @ X26))),
% 3.10/3.32      inference('cnf', [status(esa)], [d2_subset_1])).
% 3.10/3.32  thf('15', plain,
% 3.10/3.32      (![X0 : $i]:
% 3.10/3.32         ((v1_xboole_0 @ (k1_zfmisc_1 @ X0))
% 3.10/3.32          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0)))),
% 3.10/3.32      inference('sup-', [status(thm)], ['13', '14'])).
% 3.10/3.32  thf(fc1_subset_1, axiom,
% 3.10/3.32    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 3.10/3.32  thf('16', plain, (![X32 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X32))),
% 3.10/3.32      inference('cnf', [status(esa)], [fc1_subset_1])).
% 3.10/3.32  thf('17', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 3.10/3.32      inference('clc', [status(thm)], ['15', '16'])).
% 3.10/3.32  thf(d5_subset_1, axiom,
% 3.10/3.32    (![A:$i,B:$i]:
% 3.10/3.32     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 3.10/3.32       ( ( k3_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ) ))).
% 3.10/3.32  thf('18', plain,
% 3.10/3.32      (![X28 : $i, X29 : $i]:
% 3.10/3.32         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 3.10/3.32          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 3.10/3.32      inference('cnf', [status(esa)], [d5_subset_1])).
% 3.10/3.32  thf('19', plain,
% 3.10/3.32      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 3.10/3.32      inference('sup-', [status(thm)], ['17', '18'])).
% 3.10/3.32  thf(t46_xboole_1, axiom,
% 3.10/3.32    (![A:$i,B:$i]:
% 3.10/3.32     ( ( k4_xboole_0 @ A @ ( k2_xboole_0 @ A @ B ) ) = ( k1_xboole_0 ) ))).
% 3.10/3.32  thf('20', plain,
% 3.10/3.32      (![X16 : $i, X17 : $i]:
% 3.10/3.32         ((k4_xboole_0 @ X16 @ (k2_xboole_0 @ X16 @ X17)) = (k1_xboole_0))),
% 3.10/3.32      inference('cnf', [status(esa)], [t46_xboole_1])).
% 3.10/3.32  thf(t41_xboole_1, axiom,
% 3.10/3.32    (![A:$i,B:$i,C:$i]:
% 3.10/3.32     ( ( k4_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ C ) =
% 3.10/3.32       ( k4_xboole_0 @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 3.10/3.32  thf('21', plain,
% 3.10/3.32      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.10/3.32         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 3.10/3.32           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 3.10/3.32      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.10/3.32  thf('22', plain,
% 3.10/3.32      (![X16 : $i, X17 : $i]:
% 3.10/3.32         ((k4_xboole_0 @ (k4_xboole_0 @ X16 @ X16) @ X17) = (k1_xboole_0))),
% 3.10/3.32      inference('demod', [status(thm)], ['20', '21'])).
% 3.10/3.32  thf('23', plain,
% 3.10/3.32      (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k4_xboole_0 @ X0 @ X0))),
% 3.10/3.32      inference('sup-', [status(thm)], ['17', '18'])).
% 3.10/3.32  thf('24', plain,
% 3.10/3.32      (![X16 : $i, X17 : $i]:
% 3.10/3.32         ((k4_xboole_0 @ (k3_subset_1 @ X16 @ X16) @ X17) = (k1_xboole_0))),
% 3.10/3.32      inference('demod', [status(thm)], ['22', '23'])).
% 3.10/3.32  thf(t4_subset_1, axiom,
% 3.10/3.32    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 3.10/3.32  thf('25', plain,
% 3.10/3.32      (![X38 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X38))),
% 3.10/3.32      inference('cnf', [status(esa)], [t4_subset_1])).
% 3.10/3.32  thf('26', plain,
% 3.10/3.32      (![X28 : $i, X29 : $i]:
% 3.10/3.32         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 3.10/3.32          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 3.10/3.32      inference('cnf', [status(esa)], [d5_subset_1])).
% 3.10/3.32  thf('27', plain,
% 3.10/3.32      (![X0 : $i]:
% 3.10/3.32         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 3.10/3.32      inference('sup-', [status(thm)], ['25', '26'])).
% 3.10/3.32  thf('28', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 3.10/3.32      inference('simplify', [status(thm)], ['9'])).
% 3.10/3.32  thf('29', plain,
% 3.10/3.32      (![X0 : $i]:
% 3.10/3.32         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 3.10/3.32      inference('sup-', [status(thm)], ['25', '26'])).
% 3.10/3.32  thf(t44_xboole_1, axiom,
% 3.10/3.32    (![A:$i,B:$i,C:$i]:
% 3.10/3.32     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 3.10/3.32       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 3.10/3.32  thf('30', plain,
% 3.10/3.32      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.10/3.32         ((r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15))
% 3.10/3.32          | ~ (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15))),
% 3.10/3.32      inference('cnf', [status(esa)], [t44_xboole_1])).
% 3.10/3.32  thf('31', plain,
% 3.10/3.32      (![X0 : $i, X1 : $i]:
% 3.10/3.32         (~ (r1_tarski @ (k3_subset_1 @ X0 @ k1_xboole_0) @ X1)
% 3.10/3.32          | (r1_tarski @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ X1)))),
% 3.10/3.32      inference('sup-', [status(thm)], ['29', '30'])).
% 3.10/3.32  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 3.10/3.32  thf('32', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 3.10/3.32      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.10/3.32  thf(t12_xboole_1, axiom,
% 3.10/3.32    (![A:$i,B:$i]:
% 3.10/3.32     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 3.10/3.32  thf('33', plain,
% 3.10/3.32      (![X5 : $i, X6 : $i]:
% 3.10/3.32         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 3.10/3.32      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.10/3.32  thf('34', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 3.10/3.32      inference('sup-', [status(thm)], ['32', '33'])).
% 3.10/3.32  thf('35', plain,
% 3.10/3.32      (![X0 : $i, X1 : $i]:
% 3.10/3.32         (~ (r1_tarski @ (k3_subset_1 @ X0 @ k1_xboole_0) @ X1)
% 3.10/3.32          | (r1_tarski @ X0 @ X1))),
% 3.10/3.32      inference('demod', [status(thm)], ['31', '34'])).
% 3.10/3.32  thf('36', plain,
% 3.10/3.32      (![X0 : $i]: (r1_tarski @ X0 @ (k3_subset_1 @ X0 @ k1_xboole_0))),
% 3.10/3.32      inference('sup-', [status(thm)], ['28', '35'])).
% 3.10/3.32  thf('37', plain,
% 3.10/3.32      (![X2 : $i, X4 : $i]:
% 3.10/3.32         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 3.10/3.32      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.10/3.32  thf('38', plain,
% 3.10/3.32      (![X0 : $i]:
% 3.10/3.32         (~ (r1_tarski @ (k3_subset_1 @ X0 @ k1_xboole_0) @ X0)
% 3.10/3.32          | ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0)))),
% 3.10/3.32      inference('sup-', [status(thm)], ['36', '37'])).
% 3.10/3.32  thf('39', plain,
% 3.10/3.32      (![X0 : $i]:
% 3.10/3.32         ((k3_subset_1 @ X0 @ k1_xboole_0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 3.10/3.32      inference('sup-', [status(thm)], ['25', '26'])).
% 3.10/3.32  thf(t36_xboole_1, axiom,
% 3.10/3.32    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 3.10/3.32  thf('40', plain,
% 3.10/3.32      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 3.10/3.32      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.10/3.32  thf('41', plain,
% 3.10/3.32      (![X0 : $i]: (r1_tarski @ (k3_subset_1 @ X0 @ k1_xboole_0) @ X0)),
% 3.10/3.32      inference('sup+', [status(thm)], ['39', '40'])).
% 3.10/3.32  thf('42', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ k1_xboole_0) = (X0))),
% 3.10/3.32      inference('demod', [status(thm)], ['38', '41'])).
% 3.10/3.32  thf('43', plain, (![X0 : $i]: ((X0) = (k4_xboole_0 @ X0 @ k1_xboole_0))),
% 3.10/3.32      inference('demod', [status(thm)], ['27', '42'])).
% 3.10/3.32  thf('44', plain, (![X0 : $i]: ((k3_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 3.10/3.32      inference('sup+', [status(thm)], ['24', '43'])).
% 3.10/3.32  thf('45', plain, (![X0 : $i]: ((k1_xboole_0) = (k4_xboole_0 @ X0 @ X0))),
% 3.10/3.32      inference('demod', [status(thm)], ['19', '44'])).
% 3.10/3.32  thf('46', plain,
% 3.10/3.32      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.10/3.32         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 3.10/3.32           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 3.10/3.32      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.10/3.32  thf('47', plain,
% 3.10/3.32      (![X0 : $i, X1 : $i]:
% 3.10/3.32         ((k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 3.10/3.32           = (k1_xboole_0))),
% 3.10/3.32      inference('sup+', [status(thm)], ['45', '46'])).
% 3.10/3.32  thf('48', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 3.10/3.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.10/3.32  thf('49', plain,
% 3.10/3.32      (![X25 : $i, X26 : $i]:
% 3.10/3.32         (~ (m1_subset_1 @ X25 @ X26)
% 3.10/3.32          | (r2_hidden @ X25 @ X26)
% 3.10/3.32          | (v1_xboole_0 @ X26))),
% 3.10/3.32      inference('cnf', [status(esa)], [d2_subset_1])).
% 3.10/3.32  thf('50', plain,
% 3.10/3.32      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 3.10/3.32        | (r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A)))),
% 3.10/3.32      inference('sup-', [status(thm)], ['48', '49'])).
% 3.10/3.32  thf('51', plain, (![X32 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X32))),
% 3.10/3.32      inference('cnf', [status(esa)], [fc1_subset_1])).
% 3.10/3.32  thf('52', plain, ((r2_hidden @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 3.10/3.32      inference('clc', [status(thm)], ['50', '51'])).
% 3.10/3.32  thf('53', plain,
% 3.10/3.32      (![X21 : $i, X22 : $i, X23 : $i]:
% 3.10/3.32         (~ (r2_hidden @ X23 @ X22)
% 3.10/3.32          | (r1_tarski @ X23 @ X21)
% 3.10/3.32          | ((X22) != (k1_zfmisc_1 @ X21)))),
% 3.10/3.32      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 3.10/3.32  thf('54', plain,
% 3.10/3.32      (![X21 : $i, X23 : $i]:
% 3.10/3.32         ((r1_tarski @ X23 @ X21) | ~ (r2_hidden @ X23 @ (k1_zfmisc_1 @ X21)))),
% 3.10/3.32      inference('simplify', [status(thm)], ['53'])).
% 3.10/3.32  thf('55', plain, ((r1_tarski @ sk_B @ sk_A)),
% 3.10/3.32      inference('sup-', [status(thm)], ['52', '54'])).
% 3.10/3.32  thf('56', plain,
% 3.10/3.32      (![X5 : $i, X6 : $i]:
% 3.10/3.32         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 3.10/3.32      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.10/3.32  thf('57', plain, (((k2_xboole_0 @ sk_B @ sk_A) = (sk_A))),
% 3.10/3.32      inference('sup-', [status(thm)], ['55', '56'])).
% 3.10/3.32  thf('58', plain,
% 3.10/3.32      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.10/3.32         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 3.10/3.32           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 3.10/3.32      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.10/3.32  thf('59', plain,
% 3.10/3.32      (![X0 : $i]:
% 3.10/3.32         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A)
% 3.10/3.32           = (k4_xboole_0 @ X0 @ sk_A))),
% 3.10/3.32      inference('sup+', [status(thm)], ['57', '58'])).
% 3.10/3.32  thf('60', plain,
% 3.10/3.32      (![X0 : $i]:
% 3.10/3.32         ((k4_xboole_0 @ k1_xboole_0 @ sk_A)
% 3.10/3.32           = (k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ sk_B) @ X0) @ 
% 3.10/3.32              sk_A))),
% 3.10/3.32      inference('sup+', [status(thm)], ['47', '59'])).
% 3.10/3.32  thf('61', plain,
% 3.10/3.32      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 3.10/3.32      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.10/3.32  thf('62', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 3.10/3.32      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.10/3.32  thf('63', plain,
% 3.10/3.32      (![X2 : $i, X4 : $i]:
% 3.10/3.32         (((X2) = (X4)) | ~ (r1_tarski @ X4 @ X2) | ~ (r1_tarski @ X2 @ X4))),
% 3.10/3.32      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.10/3.32  thf('64', plain,
% 3.10/3.32      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 3.10/3.32      inference('sup-', [status(thm)], ['62', '63'])).
% 3.10/3.32  thf('65', plain,
% 3.10/3.32      (![X0 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 3.10/3.32      inference('sup-', [status(thm)], ['61', '64'])).
% 3.10/3.32  thf('66', plain,
% 3.10/3.32      (![X0 : $i]:
% 3.10/3.32         ((k1_xboole_0)
% 3.10/3.32           = (k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ sk_B) @ X0) @ 
% 3.10/3.32              sk_A))),
% 3.10/3.32      inference('demod', [status(thm)], ['60', '65'])).
% 3.10/3.32  thf('67', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 3.10/3.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.10/3.32  thf('68', plain,
% 3.10/3.32      (![X25 : $i, X26 : $i]:
% 3.10/3.32         (~ (m1_subset_1 @ X25 @ X26)
% 3.10/3.32          | (r2_hidden @ X25 @ X26)
% 3.10/3.32          | (v1_xboole_0 @ X26))),
% 3.10/3.32      inference('cnf', [status(esa)], [d2_subset_1])).
% 3.10/3.32  thf('69', plain,
% 3.10/3.32      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 3.10/3.32        | (r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A)))),
% 3.10/3.32      inference('sup-', [status(thm)], ['67', '68'])).
% 3.10/3.32  thf('70', plain, (![X32 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X32))),
% 3.10/3.32      inference('cnf', [status(esa)], [fc1_subset_1])).
% 3.10/3.32  thf('71', plain, ((r2_hidden @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 3.10/3.32      inference('clc', [status(thm)], ['69', '70'])).
% 3.10/3.32  thf('72', plain,
% 3.10/3.32      (![X21 : $i, X23 : $i]:
% 3.10/3.32         ((r1_tarski @ X23 @ X21) | ~ (r2_hidden @ X23 @ (k1_zfmisc_1 @ X21)))),
% 3.10/3.32      inference('simplify', [status(thm)], ['53'])).
% 3.10/3.32  thf('73', plain, ((r1_tarski @ sk_C_1 @ sk_A)),
% 3.10/3.32      inference('sup-', [status(thm)], ['71', '72'])).
% 3.10/3.32  thf('74', plain,
% 3.10/3.32      (![X5 : $i, X6 : $i]:
% 3.10/3.32         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 3.10/3.32      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.10/3.32  thf('75', plain, (((k2_xboole_0 @ sk_C_1 @ sk_A) = (sk_A))),
% 3.10/3.32      inference('sup-', [status(thm)], ['73', '74'])).
% 3.10/3.32  thf('76', plain,
% 3.10/3.32      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.10/3.32         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 3.10/3.32           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 3.10/3.32      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.10/3.32  thf('77', plain,
% 3.10/3.32      (![X0 : $i]:
% 3.10/3.32         ((k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_C_1) @ sk_A)
% 3.10/3.32           = (k4_xboole_0 @ X0 @ sk_A))),
% 3.10/3.32      inference('sup+', [status(thm)], ['75', '76'])).
% 3.10/3.32  thf('78', plain,
% 3.10/3.32      (((k1_xboole_0) = (k4_xboole_0 @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ sk_A))),
% 3.10/3.32      inference('sup+', [status(thm)], ['66', '77'])).
% 3.10/3.32  thf('79', plain, (![X3 : $i]: (r1_tarski @ X3 @ X3)),
% 3.10/3.32      inference('simplify', [status(thm)], ['9'])).
% 3.10/3.32  thf('80', plain,
% 3.10/3.32      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.10/3.32         ((r1_tarski @ X13 @ (k2_xboole_0 @ X14 @ X15))
% 3.10/3.32          | ~ (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X15))),
% 3.10/3.32      inference('cnf', [status(esa)], [t44_xboole_1])).
% 3.10/3.32  thf('81', plain,
% 3.10/3.32      (![X0 : $i, X1 : $i]:
% 3.10/3.32         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.10/3.32      inference('sup-', [status(thm)], ['79', '80'])).
% 3.10/3.32  thf('82', plain,
% 3.10/3.32      (![X5 : $i, X6 : $i]:
% 3.10/3.32         (((k2_xboole_0 @ X6 @ X5) = (X5)) | ~ (r1_tarski @ X6 @ X5))),
% 3.10/3.32      inference('cnf', [status(esa)], [t12_xboole_1])).
% 3.10/3.32  thf('83', plain,
% 3.10/3.32      (![X0 : $i, X1 : $i]:
% 3.10/3.32         ((k2_xboole_0 @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 3.10/3.32           = (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 3.10/3.32      inference('sup-', [status(thm)], ['81', '82'])).
% 3.10/3.32  thf(t7_xboole_1, axiom,
% 3.10/3.32    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 3.10/3.32  thf('84', plain,
% 3.10/3.32      (![X18 : $i, X19 : $i]: (r1_tarski @ X18 @ (k2_xboole_0 @ X18 @ X19))),
% 3.10/3.32      inference('cnf', [status(esa)], [t7_xboole_1])).
% 3.10/3.32  thf('85', plain,
% 3.10/3.32      (![X20 : $i, X21 : $i]:
% 3.10/3.32         ((r2_hidden @ X20 @ (k1_zfmisc_1 @ X21)) | ~ (r1_tarski @ X20 @ X21))),
% 3.10/3.32      inference('simplify', [status(thm)], ['11'])).
% 3.10/3.32  thf('86', plain,
% 3.10/3.32      (![X0 : $i, X1 : $i]:
% 3.10/3.32         (r2_hidden @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.10/3.32      inference('sup-', [status(thm)], ['84', '85'])).
% 3.10/3.32  thf('87', plain,
% 3.10/3.32      (![X25 : $i, X26 : $i]:
% 3.10/3.32         (~ (r2_hidden @ X25 @ X26)
% 3.10/3.32          | (m1_subset_1 @ X25 @ X26)
% 3.10/3.32          | (v1_xboole_0 @ X26))),
% 3.10/3.32      inference('cnf', [status(esa)], [d2_subset_1])).
% 3.10/3.32  thf('88', plain,
% 3.10/3.32      (![X0 : $i, X1 : $i]:
% 3.10/3.32         ((v1_xboole_0 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))
% 3.10/3.32          | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0))))),
% 3.10/3.32      inference('sup-', [status(thm)], ['86', '87'])).
% 3.10/3.32  thf('89', plain, (![X32 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X32))),
% 3.10/3.32      inference('cnf', [status(esa)], [fc1_subset_1])).
% 3.10/3.32  thf('90', plain,
% 3.10/3.32      (![X0 : $i, X1 : $i]:
% 3.10/3.32         (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.10/3.32      inference('clc', [status(thm)], ['88', '89'])).
% 3.10/3.32  thf('91', plain,
% 3.10/3.32      (![X0 : $i, X1 : $i]:
% 3.10/3.32         (m1_subset_1 @ X1 @ 
% 3.10/3.32          (k1_zfmisc_1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 3.10/3.32      inference('sup+', [status(thm)], ['83', '90'])).
% 3.10/3.32  thf('92', plain,
% 3.10/3.32      ((m1_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ 
% 3.10/3.32        (k1_zfmisc_1 @ (k2_xboole_0 @ sk_A @ k1_xboole_0)))),
% 3.10/3.32      inference('sup+', [status(thm)], ['78', '91'])).
% 3.10/3.32  thf('93', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 3.10/3.32      inference('sup-', [status(thm)], ['32', '33'])).
% 3.10/3.32  thf('94', plain,
% 3.10/3.32      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.10/3.32      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.10/3.32  thf('95', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 3.10/3.32      inference('sup+', [status(thm)], ['93', '94'])).
% 3.10/3.32  thf('96', plain,
% 3.10/3.32      ((m1_subset_1 @ (k2_xboole_0 @ sk_C_1 @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 3.10/3.32      inference('demod', [status(thm)], ['92', '95'])).
% 3.10/3.32  thf('97', plain,
% 3.10/3.32      (![X28 : $i, X29 : $i]:
% 3.10/3.32         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 3.10/3.32          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 3.10/3.32      inference('cnf', [status(esa)], [d5_subset_1])).
% 3.10/3.32  thf('98', plain,
% 3.10/3.32      (((k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B))
% 3.10/3.32         = (k4_xboole_0 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B)))),
% 3.10/3.32      inference('sup-', [status(thm)], ['96', '97'])).
% 3.10/3.32  thf('99', plain,
% 3.10/3.32      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 3.10/3.32      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 3.10/3.32  thf('100', plain,
% 3.10/3.32      (![X10 : $i, X11 : $i, X12 : $i]:
% 3.10/3.32         ((k4_xboole_0 @ (k4_xboole_0 @ X10 @ X11) @ X12)
% 3.10/3.32           = (k4_xboole_0 @ X10 @ (k2_xboole_0 @ X11 @ X12)))),
% 3.10/3.32      inference('cnf', [status(esa)], [t41_xboole_1])).
% 3.10/3.32  thf('101', plain,
% 3.10/3.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.10/3.32         ((k4_xboole_0 @ (k4_xboole_0 @ X2 @ X0) @ X1)
% 3.10/3.32           = (k4_xboole_0 @ X2 @ (k2_xboole_0 @ X1 @ X0)))),
% 3.10/3.32      inference('sup+', [status(thm)], ['99', '100'])).
% 3.10/3.32  thf('102', plain, ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ sk_A))),
% 3.10/3.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.10/3.32  thf('103', plain,
% 3.10/3.32      (![X28 : $i, X29 : $i]:
% 3.10/3.32         (((k3_subset_1 @ X28 @ X29) = (k4_xboole_0 @ X28 @ X29))
% 3.10/3.32          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X28)))),
% 3.10/3.32      inference('cnf', [status(esa)], [d5_subset_1])).
% 3.10/3.32  thf('104', plain,
% 3.10/3.32      (((k3_subset_1 @ sk_A @ sk_B) = (k4_xboole_0 @ sk_A @ sk_B))),
% 3.10/3.32      inference('sup-', [status(thm)], ['102', '103'])).
% 3.10/3.32  thf('105', plain,
% 3.10/3.32      (((k3_subset_1 @ sk_A @ (k2_xboole_0 @ sk_C_1 @ sk_B))
% 3.10/3.32         = (k4_xboole_0 @ (k3_subset_1 @ sk_A @ sk_B) @ sk_C_1))),
% 3.10/3.32      inference('demod', [status(thm)], ['98', '101', '104'])).
% 3.10/3.32  thf('106', plain,
% 3.10/3.32      (![X8 : $i, X9 : $i]: (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X8)),
% 3.10/3.32      inference('cnf', [status(esa)], [t36_xboole_1])).
% 3.10/3.32  thf('107', plain, ($false),
% 3.10/3.32      inference('demod', [status(thm)], ['8', '105', '106'])).
% 3.10/3.32  
% 3.10/3.32  % SZS output end Refutation
% 3.10/3.32  
% 3.10/3.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
