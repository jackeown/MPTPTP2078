%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ylvvWn6y7a

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:40 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :  177 (5814 expanded)
%              Number of leaves         :   28 (1847 expanded)
%              Depth                    :   39
%              Number of atoms          : 1212 (40150 expanded)
%              Number of equality atoms :   80 (1787 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t62_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
          = k1_xboole_0 )
        & ( ( k5_relat_1 @ A @ k1_xboole_0 )
          = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ( ( ( k5_relat_1 @ k1_xboole_0 @ A )
            = k1_xboole_0 )
          & ( ( k5_relat_1 @ A @ k1_xboole_0 )
            = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_relat_1])).

thf('2',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('13',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('14',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X22 @ X21 ) ) @ ( k2_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('17',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X8: $i,X10: $i] :
      ( ( X8 = X10 )
      | ~ ( r1_tarski @ X10 @ X8 )
      | ~ ( r1_tarski @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('25',plain,(
    ! [X19: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['10','30'])).

thf('32',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','9'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('44',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_relat_1 @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( v1_relat_1 @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','47'])).

thf('49',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','50'])).

thf('52',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','35'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('60',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('61',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X1 @ k1_xboole_0 )
        = ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','63'])).

thf('65',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('66',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf(t54_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) )).

thf('67',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X24 @ X23 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X23 ) @ ( k4_relat_1 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('68',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['66','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['65','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['64','73'])).

thf('75',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','54'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['77'])).

thf('79',plain,
    ( ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['57','78'])).

thf('80',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('81',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','54'])).

thf('82',plain,(
    v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf(involutiveness_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) )
        = A ) ) )).

thf('83',plain,(
    ! [X20: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X20 ) )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('84',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X24 @ X23 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X23 ) @ ( k4_relat_1 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ X1 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','54'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['1','35'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('92',plain,
    ( ( ( k4_relat_1 @ k1_xboole_0 )
      = ( k5_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('94',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','54'])).

thf('95',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = ( k5_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['92','93','94'])).

thf('96',plain,
    ( ( ( k4_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['89','95'])).

thf('97',plain,(
    v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('98',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('99',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X0 ) @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['88','99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['37','100'])).

thf('102',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,(
    ! [X20: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X20 ) )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ( ( k4_relat_1 @ k1_xboole_0 )
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X20: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X20 ) )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('110',plain,(
    v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('111',plain,(
    ! [X20: $i] :
      ( ( ( k4_relat_1 @ ( k4_relat_1 @ X20 ) )
        = X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k4_relat_1])).

thf('112',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X24 @ X23 ) )
        = ( k5_relat_1 @ ( k4_relat_1 @ X23 ) @ ( k4_relat_1 @ X24 ) ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t54_relat_1])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_relat_1 @ ( k5_relat_1 @ X1 @ ( k4_relat_1 @ X0 ) ) )
        = ( k5_relat_1 @ X0 @ ( k4_relat_1 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ k1_xboole_0 ) ) )
        = ( k5_relat_1 @ k1_xboole_0 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['110','113'])).

thf('115',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['38','54'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k4_relat_1 @ ( k5_relat_1 @ X0 @ ( k4_relat_1 @ k1_xboole_0 ) ) )
        = ( k5_relat_1 @ k1_xboole_0 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['116','117'])).

thf('119',plain,(
    v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ ( k4_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ ( k4_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['109','121'])).

thf('123',plain,(
    ! [X16: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X16 ) )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['108','124'])).

thf('126',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('127',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['127'])).

thf('129',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['126','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('131',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('132',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['127'])).

thf('133',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,
    ( ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('136',plain,
    ( ~ ( v1_xboole_0 @ ( k5_relat_1 @ sk_A @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['134','135'])).

thf('137',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['130','136'])).

thf('138',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['137','138'])).

thf('140',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['127'])).

thf('141',plain,(
    ( k5_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ sk_A )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['129','141'])).

thf('143',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['125','142'])).

thf('144',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('146',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['143','144','145'])).

thf('147',plain,(
    $false ),
    inference(simplify,[status(thm)],['146'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ylvvWn6y7a
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:07:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.36/1.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.36/1.54  % Solved by: fo/fo7.sh
% 1.36/1.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.36/1.54  % done 1678 iterations in 1.085s
% 1.36/1.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.36/1.54  % SZS output start Refutation
% 1.36/1.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.36/1.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.36/1.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.36/1.54  thf(sk_A_type, type, sk_A: $i).
% 1.36/1.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.36/1.54  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.36/1.54  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 1.36/1.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.36/1.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.36/1.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.36/1.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.36/1.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.36/1.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.36/1.54  thf(dt_k4_relat_1, axiom,
% 1.36/1.54    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 1.36/1.54  thf('0', plain,
% 1.36/1.54      (![X16 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X16)) | ~ (v1_relat_1 @ X16))),
% 1.36/1.54      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.36/1.54  thf(l13_xboole_0, axiom,
% 1.36/1.54    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.36/1.54  thf('1', plain,
% 1.36/1.54      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 1.36/1.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.36/1.54  thf(t62_relat_1, conjecture,
% 1.36/1.54    (![A:$i]:
% 1.36/1.54     ( ( v1_relat_1 @ A ) =>
% 1.36/1.54       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 1.36/1.54         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 1.36/1.54  thf(zf_stmt_0, negated_conjecture,
% 1.36/1.54    (~( ![A:$i]:
% 1.36/1.54        ( ( v1_relat_1 @ A ) =>
% 1.36/1.54          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 1.36/1.54            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 1.36/1.54    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 1.36/1.54  thf('2', plain, ((v1_relat_1 @ sk_A)),
% 1.36/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.54  thf(d3_tarski, axiom,
% 1.36/1.54    (![A:$i,B:$i]:
% 1.36/1.54     ( ( r1_tarski @ A @ B ) <=>
% 1.36/1.54       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.36/1.54  thf('3', plain,
% 1.36/1.54      (![X4 : $i, X6 : $i]:
% 1.36/1.54         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 1.36/1.54      inference('cnf', [status(esa)], [d3_tarski])).
% 1.36/1.54  thf(d1_xboole_0, axiom,
% 1.36/1.54    (![A:$i]:
% 1.36/1.54     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 1.36/1.54  thf('4', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 1.36/1.54      inference('cnf', [status(esa)], [d1_xboole_0])).
% 1.36/1.54  thf('5', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.36/1.54      inference('sup-', [status(thm)], ['3', '4'])).
% 1.36/1.54  thf(t3_subset, axiom,
% 1.36/1.54    (![A:$i,B:$i]:
% 1.36/1.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.36/1.54  thf('6', plain,
% 1.36/1.54      (![X11 : $i, X13 : $i]:
% 1.36/1.54         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 1.36/1.54      inference('cnf', [status(esa)], [t3_subset])).
% 1.36/1.54  thf('7', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.36/1.54      inference('sup-', [status(thm)], ['5', '6'])).
% 1.36/1.54  thf(cc2_relat_1, axiom,
% 1.36/1.54    (![A:$i]:
% 1.36/1.54     ( ( v1_relat_1 @ A ) =>
% 1.36/1.54       ( ![B:$i]:
% 1.36/1.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.36/1.54  thf('8', plain,
% 1.36/1.54      (![X14 : $i, X15 : $i]:
% 1.36/1.54         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 1.36/1.54          | (v1_relat_1 @ X14)
% 1.36/1.54          | ~ (v1_relat_1 @ X15))),
% 1.36/1.54      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.36/1.54  thf('9', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         (~ (v1_xboole_0 @ X1) | ~ (v1_relat_1 @ X0) | (v1_relat_1 @ X1))),
% 1.36/1.54      inference('sup-', [status(thm)], ['7', '8'])).
% 1.36/1.54  thf('10', plain, (![X0 : $i]: ((v1_relat_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 1.36/1.54      inference('sup-', [status(thm)], ['2', '9'])).
% 1.36/1.54  thf(dt_k5_relat_1, axiom,
% 1.36/1.54    (![A:$i,B:$i]:
% 1.36/1.54     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 1.36/1.54       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 1.36/1.54  thf('11', plain,
% 1.36/1.54      (![X17 : $i, X18 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X17)
% 1.36/1.54          | ~ (v1_relat_1 @ X18)
% 1.36/1.54          | (v1_relat_1 @ (k5_relat_1 @ X17 @ X18)))),
% 1.36/1.54      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.36/1.54  thf('12', plain, (![X0 : $i]: ((v1_relat_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 1.36/1.54      inference('sup-', [status(thm)], ['2', '9'])).
% 1.36/1.54  thf(t60_relat_1, axiom,
% 1.36/1.54    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 1.36/1.54     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.36/1.54  thf('13', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.36/1.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.36/1.54  thf(t45_relat_1, axiom,
% 1.36/1.54    (![A:$i]:
% 1.36/1.54     ( ( v1_relat_1 @ A ) =>
% 1.36/1.54       ( ![B:$i]:
% 1.36/1.54         ( ( v1_relat_1 @ B ) =>
% 1.36/1.54           ( r1_tarski @
% 1.36/1.54             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 1.36/1.54  thf('14', plain,
% 1.36/1.54      (![X21 : $i, X22 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X21)
% 1.36/1.54          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X22 @ X21)) @ 
% 1.36/1.54             (k2_relat_1 @ X21))
% 1.36/1.54          | ~ (v1_relat_1 @ X22))),
% 1.36/1.54      inference('cnf', [status(esa)], [t45_relat_1])).
% 1.36/1.54  thf('15', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 1.36/1.54           k1_xboole_0)
% 1.36/1.54          | ~ (v1_relat_1 @ X0)
% 1.36/1.54          | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.36/1.54      inference('sup+', [status(thm)], ['13', '14'])).
% 1.36/1.54  thf('16', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.36/1.54          | ~ (v1_relat_1 @ X0)
% 1.36/1.54          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 1.36/1.54             k1_xboole_0))),
% 1.36/1.54      inference('sup-', [status(thm)], ['12', '15'])).
% 1.36/1.54  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.36/1.54  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.36/1.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.36/1.54  thf('18', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X0)
% 1.36/1.54          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 1.36/1.54             k1_xboole_0))),
% 1.36/1.54      inference('demod', [status(thm)], ['16', '17'])).
% 1.36/1.54  thf('19', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.36/1.54      inference('sup-', [status(thm)], ['3', '4'])).
% 1.36/1.54  thf(d10_xboole_0, axiom,
% 1.36/1.54    (![A:$i,B:$i]:
% 1.36/1.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.36/1.54  thf('20', plain,
% 1.36/1.54      (![X8 : $i, X10 : $i]:
% 1.36/1.54         (((X8) = (X10)) | ~ (r1_tarski @ X10 @ X8) | ~ (r1_tarski @ X8 @ X10))),
% 1.36/1.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.36/1.54  thf('21', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 1.36/1.54      inference('sup-', [status(thm)], ['19', '20'])).
% 1.36/1.54  thf('22', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X0)
% 1.36/1.54          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))
% 1.36/1.54          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.36/1.54      inference('sup-', [status(thm)], ['18', '21'])).
% 1.36/1.54  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.36/1.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.36/1.54  thf('24', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X0)
% 1.36/1.54          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 1.36/1.54      inference('demod', [status(thm)], ['22', '23'])).
% 1.36/1.54  thf(fc9_relat_1, axiom,
% 1.36/1.54    (![A:$i]:
% 1.36/1.54     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 1.36/1.54       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 1.36/1.54  thf('25', plain,
% 1.36/1.54      (![X19 : $i]:
% 1.36/1.54         (~ (v1_xboole_0 @ (k2_relat_1 @ X19))
% 1.36/1.54          | ~ (v1_relat_1 @ X19)
% 1.36/1.54          | (v1_xboole_0 @ X19))),
% 1.36/1.54      inference('cnf', [status(esa)], [fc9_relat_1])).
% 1.36/1.54  thf('26', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.36/1.54          | ~ (v1_relat_1 @ X0)
% 1.36/1.54          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.36/1.54          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 1.36/1.54      inference('sup-', [status(thm)], ['24', '25'])).
% 1.36/1.54  thf('27', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.36/1.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.36/1.54  thf('28', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X0)
% 1.36/1.54          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.36/1.54          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 1.36/1.54      inference('demod', [status(thm)], ['26', '27'])).
% 1.36/1.54  thf('29', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ k1_xboole_0)
% 1.36/1.54          | ~ (v1_relat_1 @ X0)
% 1.36/1.54          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.36/1.54          | ~ (v1_relat_1 @ X0))),
% 1.36/1.54      inference('sup-', [status(thm)], ['11', '28'])).
% 1.36/1.54  thf('30', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         ((v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.36/1.54          | ~ (v1_relat_1 @ X0)
% 1.36/1.54          | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.36/1.54      inference('simplify', [status(thm)], ['29'])).
% 1.36/1.54  thf('31', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.36/1.54          | ~ (v1_relat_1 @ X0)
% 1.36/1.54          | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 1.36/1.54      inference('sup-', [status(thm)], ['10', '30'])).
% 1.36/1.54  thf('32', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.36/1.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.36/1.54  thf('33', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 1.36/1.54      inference('demod', [status(thm)], ['31', '32'])).
% 1.36/1.54  thf('34', plain,
% 1.36/1.54      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 1.36/1.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.36/1.54  thf('35', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X0)
% 1.36/1.54          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 1.36/1.54      inference('sup-', [status(thm)], ['33', '34'])).
% 1.36/1.54  thf('36', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         (((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 1.36/1.54          | ~ (v1_xboole_0 @ X0)
% 1.36/1.54          | ~ (v1_relat_1 @ X1))),
% 1.36/1.54      inference('sup+', [status(thm)], ['1', '35'])).
% 1.36/1.54  thf('37', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X0)
% 1.36/1.54          | ~ (v1_xboole_0 @ X1)
% 1.36/1.54          | ((k5_relat_1 @ (k4_relat_1 @ X0) @ X1) = (k1_xboole_0)))),
% 1.36/1.54      inference('sup-', [status(thm)], ['0', '36'])).
% 1.36/1.54  thf('38', plain, ((v1_relat_1 @ sk_A)),
% 1.36/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.54  thf('39', plain,
% 1.36/1.54      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 1.36/1.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.36/1.54  thf('40', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X0)
% 1.36/1.54          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 1.36/1.54      inference('demod', [status(thm)], ['22', '23'])).
% 1.36/1.54  thf('41', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         (((k2_relat_1 @ (k5_relat_1 @ X1 @ X0)) = (k1_xboole_0))
% 1.36/1.54          | ~ (v1_xboole_0 @ X0)
% 1.36/1.54          | ~ (v1_relat_1 @ X1))),
% 1.36/1.54      inference('sup+', [status(thm)], ['39', '40'])).
% 1.36/1.54  thf('42', plain, (![X0 : $i]: ((v1_relat_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 1.36/1.54      inference('sup-', [status(thm)], ['2', '9'])).
% 1.36/1.54  thf('43', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X0)
% 1.36/1.54          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 1.36/1.54             k1_xboole_0))),
% 1.36/1.54      inference('demod', [status(thm)], ['16', '17'])).
% 1.36/1.54  thf('44', plain,
% 1.36/1.54      (![X11 : $i, X13 : $i]:
% 1.36/1.54         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 1.36/1.54      inference('cnf', [status(esa)], [t3_subset])).
% 1.36/1.54  thf('45', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X0)
% 1.36/1.54          | (m1_subset_1 @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 1.36/1.54             (k1_zfmisc_1 @ k1_xboole_0)))),
% 1.36/1.54      inference('sup-', [status(thm)], ['43', '44'])).
% 1.36/1.54  thf('46', plain,
% 1.36/1.54      (![X14 : $i, X15 : $i]:
% 1.36/1.54         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 1.36/1.54          | (v1_relat_1 @ X14)
% 1.36/1.54          | ~ (v1_relat_1 @ X15))),
% 1.36/1.54      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.36/1.54  thf('47', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X0)
% 1.36/1.54          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.36/1.54          | (v1_relat_1 @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))))),
% 1.36/1.54      inference('sup-', [status(thm)], ['45', '46'])).
% 1.36/1.54  thf('48', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (~ (v1_xboole_0 @ k1_xboole_0)
% 1.36/1.54          | (v1_relat_1 @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 1.36/1.54          | ~ (v1_relat_1 @ X0))),
% 1.36/1.54      inference('sup-', [status(thm)], ['42', '47'])).
% 1.36/1.54  thf('49', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.36/1.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.36/1.54  thf('50', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         ((v1_relat_1 @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 1.36/1.54          | ~ (v1_relat_1 @ X0))),
% 1.36/1.54      inference('demod', [status(thm)], ['48', '49'])).
% 1.36/1.54  thf('51', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         ((v1_relat_1 @ k1_xboole_0)
% 1.36/1.54          | ~ (v1_relat_1 @ X0)
% 1.36/1.54          | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.36/1.54          | ~ (v1_relat_1 @ X0))),
% 1.36/1.54      inference('sup+', [status(thm)], ['41', '50'])).
% 1.36/1.54  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.36/1.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.36/1.54  thf('53', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         ((v1_relat_1 @ k1_xboole_0)
% 1.36/1.54          | ~ (v1_relat_1 @ X0)
% 1.36/1.54          | ~ (v1_relat_1 @ X0))),
% 1.36/1.54      inference('demod', [status(thm)], ['51', '52'])).
% 1.36/1.54  thf('54', plain,
% 1.36/1.54      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 1.36/1.54      inference('simplify', [status(thm)], ['53'])).
% 1.36/1.54  thf('55', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.36/1.54      inference('sup-', [status(thm)], ['38', '54'])).
% 1.36/1.54  thf('56', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         (((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 1.36/1.54          | ~ (v1_xboole_0 @ X0)
% 1.36/1.54          | ~ (v1_relat_1 @ X1))),
% 1.36/1.54      inference('sup+', [status(thm)], ['1', '35'])).
% 1.36/1.54  thf('57', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (~ (v1_xboole_0 @ X0)
% 1.36/1.54          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 1.36/1.54      inference('sup-', [status(thm)], ['55', '56'])).
% 1.36/1.54  thf('58', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 1.36/1.54      inference('demod', [status(thm)], ['31', '32'])).
% 1.36/1.54  thf('59', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 1.36/1.54      inference('demod', [status(thm)], ['31', '32'])).
% 1.36/1.54  thf('60', plain,
% 1.36/1.54      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 1.36/1.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.36/1.54  thf('61', plain,
% 1.36/1.54      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 1.36/1.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.36/1.54  thf('62', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 1.36/1.54      inference('sup+', [status(thm)], ['60', '61'])).
% 1.36/1.54  thf('63', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X0)
% 1.36/1.54          | ~ (v1_xboole_0 @ X1)
% 1.36/1.54          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (X1)))),
% 1.36/1.54      inference('sup-', [status(thm)], ['59', '62'])).
% 1.36/1.54  thf('64', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X0)
% 1.36/1.54          | ((k5_relat_1 @ X1 @ k1_xboole_0) = (k5_relat_1 @ X0 @ k1_xboole_0))
% 1.36/1.54          | ~ (v1_relat_1 @ X1))),
% 1.36/1.54      inference('sup-', [status(thm)], ['58', '63'])).
% 1.36/1.54  thf('65', plain,
% 1.36/1.54      (![X16 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X16)) | ~ (v1_relat_1 @ X16))),
% 1.36/1.54      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.36/1.54  thf('66', plain,
% 1.36/1.54      (![X16 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X16)) | ~ (v1_relat_1 @ X16))),
% 1.36/1.54      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.36/1.54  thf(t54_relat_1, axiom,
% 1.36/1.54    (![A:$i]:
% 1.36/1.54     ( ( v1_relat_1 @ A ) =>
% 1.36/1.54       ( ![B:$i]:
% 1.36/1.54         ( ( v1_relat_1 @ B ) =>
% 1.36/1.54           ( ( k4_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 1.36/1.54             ( k5_relat_1 @ ( k4_relat_1 @ B ) @ ( k4_relat_1 @ A ) ) ) ) ) ))).
% 1.36/1.54  thf('67', plain,
% 1.36/1.54      (![X23 : $i, X24 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X23)
% 1.36/1.54          | ((k4_relat_1 @ (k5_relat_1 @ X24 @ X23))
% 1.36/1.54              = (k5_relat_1 @ (k4_relat_1 @ X23) @ (k4_relat_1 @ X24)))
% 1.36/1.54          | ~ (v1_relat_1 @ X24))),
% 1.36/1.54      inference('cnf', [status(esa)], [t54_relat_1])).
% 1.36/1.54  thf('68', plain,
% 1.36/1.54      (![X17 : $i, X18 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X17)
% 1.36/1.54          | ~ (v1_relat_1 @ X18)
% 1.36/1.54          | (v1_relat_1 @ (k5_relat_1 @ X17 @ X18)))),
% 1.36/1.54      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 1.36/1.54  thf('69', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         ((v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 1.36/1.54          | ~ (v1_relat_1 @ X1)
% 1.36/1.54          | ~ (v1_relat_1 @ X0)
% 1.36/1.54          | ~ (v1_relat_1 @ (k4_relat_1 @ X1))
% 1.36/1.54          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 1.36/1.54      inference('sup+', [status(thm)], ['67', '68'])).
% 1.36/1.54  thf('70', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X0)
% 1.36/1.54          | ~ (v1_relat_1 @ (k4_relat_1 @ X1))
% 1.36/1.54          | ~ (v1_relat_1 @ X1)
% 1.36/1.54          | ~ (v1_relat_1 @ X0)
% 1.36/1.54          | (v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X0 @ X1))))),
% 1.36/1.54      inference('sup-', [status(thm)], ['66', '69'])).
% 1.36/1.54  thf('71', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         ((v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X0 @ X1)))
% 1.36/1.54          | ~ (v1_relat_1 @ X1)
% 1.36/1.54          | ~ (v1_relat_1 @ (k4_relat_1 @ X1))
% 1.36/1.54          | ~ (v1_relat_1 @ X0))),
% 1.36/1.54      inference('simplify', [status(thm)], ['70'])).
% 1.36/1.54  thf('72', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X0)
% 1.36/1.54          | ~ (v1_relat_1 @ X1)
% 1.36/1.54          | ~ (v1_relat_1 @ X0)
% 1.36/1.54          | (v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X1 @ X0))))),
% 1.36/1.54      inference('sup-', [status(thm)], ['65', '71'])).
% 1.36/1.54  thf('73', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         ((v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 1.36/1.54          | ~ (v1_relat_1 @ X1)
% 1.36/1.54          | ~ (v1_relat_1 @ X0))),
% 1.36/1.54      inference('simplify', [status(thm)], ['72'])).
% 1.36/1.54  thf('74', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         ((v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 1.36/1.54          | ~ (v1_relat_1 @ X0)
% 1.36/1.54          | ~ (v1_relat_1 @ X1)
% 1.36/1.54          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.36/1.54          | ~ (v1_relat_1 @ X1))),
% 1.36/1.54      inference('sup+', [status(thm)], ['64', '73'])).
% 1.36/1.54  thf('75', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.36/1.54      inference('sup-', [status(thm)], ['38', '54'])).
% 1.36/1.54  thf('76', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         ((v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 1.36/1.54          | ~ (v1_relat_1 @ X0)
% 1.36/1.54          | ~ (v1_relat_1 @ X1)
% 1.36/1.54          | ~ (v1_relat_1 @ X1))),
% 1.36/1.54      inference('demod', [status(thm)], ['74', '75'])).
% 1.36/1.54  thf('77', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X1)
% 1.36/1.54          | ~ (v1_relat_1 @ X0)
% 1.36/1.54          | (v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))))),
% 1.36/1.54      inference('simplify', [status(thm)], ['76'])).
% 1.36/1.54  thf('78', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         ((v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)))
% 1.36/1.54          | ~ (v1_relat_1 @ X0))),
% 1.36/1.54      inference('condensation', [status(thm)], ['77'])).
% 1.36/1.54  thf('79', plain,
% 1.36/1.54      (((v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))
% 1.36/1.54        | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.36/1.54        | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.36/1.54      inference('sup+', [status(thm)], ['57', '78'])).
% 1.36/1.54  thf('80', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.36/1.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.36/1.54  thf('81', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.36/1.54      inference('sup-', [status(thm)], ['38', '54'])).
% 1.36/1.54  thf('82', plain, ((v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))),
% 1.36/1.54      inference('demod', [status(thm)], ['79', '80', '81'])).
% 1.36/1.54  thf(involutiveness_k4_relat_1, axiom,
% 1.36/1.54    (![A:$i]:
% 1.36/1.54     ( ( v1_relat_1 @ A ) => ( ( k4_relat_1 @ ( k4_relat_1 @ A ) ) = ( A ) ) ))).
% 1.36/1.54  thf('83', plain,
% 1.36/1.54      (![X20 : $i]:
% 1.36/1.54         (((k4_relat_1 @ (k4_relat_1 @ X20)) = (X20)) | ~ (v1_relat_1 @ X20))),
% 1.36/1.54      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 1.36/1.54  thf('84', plain,
% 1.36/1.54      (![X23 : $i, X24 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X23)
% 1.36/1.54          | ((k4_relat_1 @ (k5_relat_1 @ X24 @ X23))
% 1.36/1.54              = (k5_relat_1 @ (k4_relat_1 @ X23) @ (k4_relat_1 @ X24)))
% 1.36/1.54          | ~ (v1_relat_1 @ X24))),
% 1.36/1.54      inference('cnf', [status(esa)], [t54_relat_1])).
% 1.36/1.54  thf('85', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         (((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ X0) @ X1))
% 1.36/1.54            = (k5_relat_1 @ (k4_relat_1 @ X1) @ X0))
% 1.36/1.54          | ~ (v1_relat_1 @ X0)
% 1.36/1.54          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 1.36/1.54          | ~ (v1_relat_1 @ X1))),
% 1.36/1.54      inference('sup+', [status(thm)], ['83', '84'])).
% 1.36/1.54  thf('86', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X0)
% 1.36/1.54          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.36/1.54          | ((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ k1_xboole_0) @ X0))
% 1.36/1.54              = (k5_relat_1 @ (k4_relat_1 @ X0) @ k1_xboole_0)))),
% 1.36/1.54      inference('sup-', [status(thm)], ['82', '85'])).
% 1.36/1.54  thf('87', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.36/1.54      inference('sup-', [status(thm)], ['38', '54'])).
% 1.36/1.54  thf('88', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X0)
% 1.36/1.54          | ((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ k1_xboole_0) @ X0))
% 1.36/1.54              = (k5_relat_1 @ (k4_relat_1 @ X0) @ k1_xboole_0)))),
% 1.36/1.54      inference('demod', [status(thm)], ['86', '87'])).
% 1.36/1.54  thf('89', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         (((k5_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 1.36/1.54          | ~ (v1_xboole_0 @ X0)
% 1.36/1.54          | ~ (v1_relat_1 @ X1))),
% 1.36/1.54      inference('sup+', [status(thm)], ['1', '35'])).
% 1.36/1.54  thf('90', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X0)
% 1.36/1.54          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 1.36/1.54      inference('sup-', [status(thm)], ['33', '34'])).
% 1.36/1.54  thf('91', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X0)
% 1.36/1.54          | ((k4_relat_1 @ (k5_relat_1 @ (k4_relat_1 @ k1_xboole_0) @ X0))
% 1.36/1.54              = (k5_relat_1 @ (k4_relat_1 @ X0) @ k1_xboole_0)))),
% 1.36/1.54      inference('demod', [status(thm)], ['86', '87'])).
% 1.36/1.54  thf('92', plain,
% 1.36/1.54      ((((k4_relat_1 @ k1_xboole_0)
% 1.36/1.54          = (k5_relat_1 @ (k4_relat_1 @ k1_xboole_0) @ k1_xboole_0))
% 1.36/1.54        | ~ (v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))
% 1.36/1.54        | ~ (v1_relat_1 @ k1_xboole_0))),
% 1.36/1.54      inference('sup+', [status(thm)], ['90', '91'])).
% 1.36/1.54  thf('93', plain, ((v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))),
% 1.36/1.54      inference('demod', [status(thm)], ['79', '80', '81'])).
% 1.36/1.54  thf('94', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.36/1.54      inference('sup-', [status(thm)], ['38', '54'])).
% 1.36/1.54  thf('95', plain,
% 1.36/1.54      (((k4_relat_1 @ k1_xboole_0)
% 1.36/1.54         = (k5_relat_1 @ (k4_relat_1 @ k1_xboole_0) @ k1_xboole_0))),
% 1.36/1.54      inference('demod', [status(thm)], ['92', '93', '94'])).
% 1.36/1.54  thf('96', plain,
% 1.36/1.54      ((((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 1.36/1.54        | ~ (v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))
% 1.36/1.54        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.36/1.54      inference('sup+', [status(thm)], ['89', '95'])).
% 1.36/1.54  thf('97', plain, ((v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))),
% 1.36/1.54      inference('demod', [status(thm)], ['79', '80', '81'])).
% 1.36/1.54  thf('98', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.36/1.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.36/1.54  thf('99', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.36/1.54      inference('demod', [status(thm)], ['96', '97', '98'])).
% 1.36/1.54  thf('100', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X0)
% 1.36/1.54          | ((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.36/1.54              = (k5_relat_1 @ (k4_relat_1 @ X0) @ k1_xboole_0)))),
% 1.36/1.54      inference('demod', [status(thm)], ['88', '99'])).
% 1.36/1.54  thf('101', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 1.36/1.54          | ~ (v1_xboole_0 @ k1_xboole_0)
% 1.36/1.54          | ~ (v1_relat_1 @ X0)
% 1.36/1.54          | ~ (v1_relat_1 @ X0))),
% 1.36/1.54      inference('sup+', [status(thm)], ['37', '100'])).
% 1.36/1.54  thf('102', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.36/1.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.36/1.54  thf('103', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))
% 1.36/1.54          | ~ (v1_relat_1 @ X0)
% 1.36/1.54          | ~ (v1_relat_1 @ X0))),
% 1.36/1.54      inference('demod', [status(thm)], ['101', '102'])).
% 1.36/1.54  thf('104', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X0)
% 1.36/1.54          | ((k4_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 1.36/1.54      inference('simplify', [status(thm)], ['103'])).
% 1.36/1.54  thf('105', plain,
% 1.36/1.54      (![X20 : $i]:
% 1.36/1.54         (((k4_relat_1 @ (k4_relat_1 @ X20)) = (X20)) | ~ (v1_relat_1 @ X20))),
% 1.36/1.54      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 1.36/1.54  thf('106', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (((k4_relat_1 @ k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.36/1.54          | ~ (v1_relat_1 @ X0)
% 1.36/1.54          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.36/1.54      inference('sup+', [status(thm)], ['104', '105'])).
% 1.36/1.54  thf('107', plain, (((k4_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.36/1.54      inference('demod', [status(thm)], ['96', '97', '98'])).
% 1.36/1.54  thf('108', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.36/1.54          | ~ (v1_relat_1 @ X0)
% 1.36/1.54          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.36/1.54      inference('demod', [status(thm)], ['106', '107'])).
% 1.36/1.54  thf('109', plain,
% 1.36/1.54      (![X20 : $i]:
% 1.36/1.54         (((k4_relat_1 @ (k4_relat_1 @ X20)) = (X20)) | ~ (v1_relat_1 @ X20))),
% 1.36/1.54      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 1.36/1.54  thf('110', plain, ((v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))),
% 1.36/1.54      inference('demod', [status(thm)], ['79', '80', '81'])).
% 1.36/1.54  thf('111', plain,
% 1.36/1.54      (![X20 : $i]:
% 1.36/1.54         (((k4_relat_1 @ (k4_relat_1 @ X20)) = (X20)) | ~ (v1_relat_1 @ X20))),
% 1.36/1.54      inference('cnf', [status(esa)], [involutiveness_k4_relat_1])).
% 1.36/1.54  thf('112', plain,
% 1.36/1.54      (![X23 : $i, X24 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X23)
% 1.36/1.54          | ((k4_relat_1 @ (k5_relat_1 @ X24 @ X23))
% 1.36/1.54              = (k5_relat_1 @ (k4_relat_1 @ X23) @ (k4_relat_1 @ X24)))
% 1.36/1.54          | ~ (v1_relat_1 @ X24))),
% 1.36/1.54      inference('cnf', [status(esa)], [t54_relat_1])).
% 1.36/1.54  thf('113', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         (((k4_relat_1 @ (k5_relat_1 @ X1 @ (k4_relat_1 @ X0)))
% 1.36/1.54            = (k5_relat_1 @ X0 @ (k4_relat_1 @ X1)))
% 1.36/1.54          | ~ (v1_relat_1 @ X0)
% 1.36/1.54          | ~ (v1_relat_1 @ X1)
% 1.36/1.54          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 1.36/1.54      inference('sup+', [status(thm)], ['111', '112'])).
% 1.36/1.54  thf('114', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X0)
% 1.36/1.54          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.36/1.54          | ((k4_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ k1_xboole_0)))
% 1.36/1.54              = (k5_relat_1 @ k1_xboole_0 @ (k4_relat_1 @ X0))))),
% 1.36/1.54      inference('sup-', [status(thm)], ['110', '113'])).
% 1.36/1.54  thf('115', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.36/1.54      inference('sup-', [status(thm)], ['38', '54'])).
% 1.36/1.54  thf('116', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X0)
% 1.36/1.54          | ((k4_relat_1 @ (k5_relat_1 @ X0 @ (k4_relat_1 @ k1_xboole_0)))
% 1.36/1.54              = (k5_relat_1 @ k1_xboole_0 @ (k4_relat_1 @ X0))))),
% 1.36/1.54      inference('demod', [status(thm)], ['114', '115'])).
% 1.36/1.54  thf('117', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         ((v1_relat_1 @ (k4_relat_1 @ (k5_relat_1 @ X1 @ X0)))
% 1.36/1.54          | ~ (v1_relat_1 @ X1)
% 1.36/1.54          | ~ (v1_relat_1 @ X0))),
% 1.36/1.54      inference('simplify', [status(thm)], ['72'])).
% 1.36/1.54  thf('118', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         ((v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ (k4_relat_1 @ X0)))
% 1.36/1.54          | ~ (v1_relat_1 @ X0)
% 1.36/1.54          | ~ (v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))
% 1.36/1.54          | ~ (v1_relat_1 @ X0))),
% 1.36/1.54      inference('sup+', [status(thm)], ['116', '117'])).
% 1.36/1.54  thf('119', plain, ((v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))),
% 1.36/1.54      inference('demod', [status(thm)], ['79', '80', '81'])).
% 1.36/1.54  thf('120', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         ((v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ (k4_relat_1 @ X0)))
% 1.36/1.54          | ~ (v1_relat_1 @ X0)
% 1.36/1.54          | ~ (v1_relat_1 @ X0))),
% 1.36/1.54      inference('demod', [status(thm)], ['118', '119'])).
% 1.36/1.54  thf('121', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X0)
% 1.36/1.54          | (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ (k4_relat_1 @ X0))))),
% 1.36/1.54      inference('simplify', [status(thm)], ['120'])).
% 1.36/1.54  thf('122', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         ((v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 1.36/1.54          | ~ (v1_relat_1 @ X0)
% 1.36/1.54          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 1.36/1.54      inference('sup+', [status(thm)], ['109', '121'])).
% 1.36/1.54  thf('123', plain,
% 1.36/1.54      (![X16 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X16)) | ~ (v1_relat_1 @ X16))),
% 1.36/1.54      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 1.36/1.54  thf('124', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.36/1.54      inference('clc', [status(thm)], ['122', '123'])).
% 1.36/1.54  thf('125', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X0)
% 1.36/1.54          | ((k1_xboole_0) = (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 1.36/1.54      inference('clc', [status(thm)], ['108', '124'])).
% 1.36/1.54  thf('126', plain,
% 1.36/1.54      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X7))),
% 1.36/1.54      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.36/1.54  thf('127', plain,
% 1.36/1.54      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 1.36/1.54        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 1.36/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.54  thf('128', plain,
% 1.36/1.54      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 1.36/1.54         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.36/1.54      inference('split', [status(esa)], ['127'])).
% 1.36/1.54  thf('129', plain,
% 1.36/1.54      ((![X0 : $i]:
% 1.36/1.54          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 1.36/1.54         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 1.36/1.54      inference('sup-', [status(thm)], ['126', '128'])).
% 1.36/1.54  thf('130', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ X0 @ k1_xboole_0)))),
% 1.36/1.54      inference('demod', [status(thm)], ['31', '32'])).
% 1.36/1.54  thf('131', plain,
% 1.36/1.54      (![X0 : $i, X1 : $i]:
% 1.36/1.54         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 1.36/1.54      inference('sup+', [status(thm)], ['60', '61'])).
% 1.36/1.54  thf('132', plain,
% 1.36/1.54      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 1.36/1.54         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.36/1.54      inference('split', [status(esa)], ['127'])).
% 1.36/1.54  thf('133', plain,
% 1.36/1.54      ((![X0 : $i]:
% 1.36/1.54          (((X0) != (k1_xboole_0))
% 1.36/1.54           | ~ (v1_xboole_0 @ X0)
% 1.36/1.54           | ~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))))
% 1.36/1.54         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.36/1.54      inference('sup-', [status(thm)], ['131', '132'])).
% 1.36/1.54  thf('134', plain,
% 1.36/1.54      (((~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0))
% 1.36/1.54         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 1.36/1.54         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.36/1.54      inference('simplify', [status(thm)], ['133'])).
% 1.36/1.54  thf('135', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.36/1.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.36/1.54  thf('136', plain,
% 1.36/1.54      ((~ (v1_xboole_0 @ (k5_relat_1 @ sk_A @ k1_xboole_0)))
% 1.36/1.54         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.36/1.54      inference('simplify_reflect+', [status(thm)], ['134', '135'])).
% 1.36/1.54  thf('137', plain,
% 1.36/1.54      ((~ (v1_relat_1 @ sk_A))
% 1.36/1.54         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 1.36/1.54      inference('sup-', [status(thm)], ['130', '136'])).
% 1.36/1.54  thf('138', plain, ((v1_relat_1 @ sk_A)),
% 1.36/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.54  thf('139', plain, ((((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 1.36/1.54      inference('demod', [status(thm)], ['137', '138'])).
% 1.36/1.54  thf('140', plain,
% 1.36/1.54      (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))) | 
% 1.36/1.54       ~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 1.36/1.54      inference('split', [status(esa)], ['127'])).
% 1.36/1.54  thf('141', plain, (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 1.36/1.54      inference('sat_resolution*', [status(thm)], ['139', '140'])).
% 1.36/1.54  thf('142', plain,
% 1.36/1.54      (![X0 : $i]:
% 1.36/1.54         (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.36/1.54      inference('simpl_trail', [status(thm)], ['129', '141'])).
% 1.36/1.54  thf('143', plain,
% 1.36/1.54      ((((k1_xboole_0) != (k1_xboole_0))
% 1.36/1.54        | ~ (v1_relat_1 @ sk_A)
% 1.36/1.54        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.36/1.54      inference('sup-', [status(thm)], ['125', '142'])).
% 1.36/1.54  thf('144', plain, ((v1_relat_1 @ sk_A)),
% 1.36/1.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.36/1.54  thf('145', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.36/1.54      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.36/1.54  thf('146', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 1.36/1.54      inference('demod', [status(thm)], ['143', '144', '145'])).
% 1.36/1.54  thf('147', plain, ($false), inference('simplify', [status(thm)], ['146'])).
% 1.36/1.54  
% 1.36/1.54  % SZS output end Refutation
% 1.36/1.54  
% 1.36/1.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
