%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fysmi7jJWq

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:37:00 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 149 expanded)
%              Number of leaves         :   33 (  59 expanded)
%              Depth                    :   15
%              Number of atoms          :  590 ( 981 expanded)
%              Number of equality atoms :   50 (  96 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('0',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X41 ) @ ( k1_zfmisc_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('1',plain,(
    ! [X40: $i] :
      ( ( k2_subset_1 @ X40 )
      = X40 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('2',plain,(
    ! [X41: $i] :
      ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X41 ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(t28_subset_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
        = ( k2_subset_1 @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
       => ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) )
          = ( k2_subset_1 @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_subset_1])).

thf('3',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k4_subset_1 @ A @ B @ C )
        = ( k2_xboole_0 @ B @ C ) ) ) )).

thf('4',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X43 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ X43 ) )
      | ( ( k4_subset_1 @ X43 @ X42 @ X44 )
        = ( k2_xboole_0 @ X42 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( ( k4_subset_1 @ sk_A @ sk_B_1 @ X0 )
        = ( k2_xboole_0 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B_1 @ sk_A )
    = ( k2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('7',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('8',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('9',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X37 @ X38 )
      | ( r2_hidden @ X37 @ X38 )
      | ( v1_xboole_0 @ X38 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_zfmisc_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( r1_tarski @ C @ A ) ) ) )).

thf('11',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( r2_hidden @ X33 @ X32 )
      | ( r1_tarski @ X33 @ X31 )
      | ( X32
       != ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('12',plain,(
    ! [X31: $i,X33: $i] :
      ( ( r1_tarski @ X33 @ X31 )
      | ~ ( r2_hidden @ X33 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( r1_tarski @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf(t28_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k3_xboole_0 @ A @ B )
        = A ) ) )).

thf('14',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k3_xboole_0 @ X14 @ X15 )
        = X14 )
      | ~ ( r1_tarski @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t28_xboole_1])).

thf('15',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
      = sk_B_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('16',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('17',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ~ ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r1_tarski @ X30 @ X31 )
      | ( r2_hidden @ X30 @ X32 )
      | ( X32
       != ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[d1_zfmisc_1])).

thf('21',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r2_hidden @ X30 @ ( k1_zfmisc_1 @ X31 ) )
      | ~ ( r1_tarski @ X30 @ X31 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('24',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( k3_xboole_0 @ sk_B_1 @ sk_A )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['15','24'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('26',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k4_xboole_0 @ X18 @ ( k4_xboole_0 @ X18 @ X19 ) )
      = ( k3_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('27',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ~ ( r2_hidden @ X11 @ X9 )
      | ( X10
       != ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('28',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['25','29'])).

thf('31',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X10 )
      | ( r2_hidden @ X11 @ X8 )
      | ( X10
       != ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('32',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ( r2_hidden @ X11 @ X8 )
      | ~ ( r2_hidden @ X11 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k4_xboole_0 @ sk_B_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['30','32'])).

thf('34',plain,(
    v1_xboole_0 @ ( k4_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['7','33'])).

thf('35',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(commutativity_k2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_tarski @ A @ B )
      = ( k2_tarski @ B @ A ) ) )).

thf('36',plain,(
    ! [X23: $i,X24: $i] :
      ( ( k2_tarski @ X24 @ X23 )
      = ( k2_tarski @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_tarski])).

thf(l51_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_tarski @ ( k2_tarski @ A @ B ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('37',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X35 @ X36 ) )
      = ( k2_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X1 @ X0 ) )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X35: $i,X36: $i] :
      ( ( k3_tarski @ ( k2_tarski @ X35 @ X36 ) )
      = ( k2_xboole_0 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[l51_zfmisc_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('41',plain,(
    ! [X13: $i] :
      ( ( k2_xboole_0 @ X13 @ k1_xboole_0 )
      = X13 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('43',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k2_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X8: $i,X9: $i,X11: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ ( k4_xboole_0 @ X8 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['48'])).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','49'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('51',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_xboole_0 @ X21 )
      | ~ ( v1_xboole_0 @ X22 )
      | ( X21 = X22 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( k1_xboole_0
    = ( k4_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['34','52'])).

thf('54',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k2_xboole_0 @ X16 @ ( k4_xboole_0 @ X17 @ X16 ) )
      = ( k2_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('55',plain,
    ( ( k2_xboole_0 @ sk_A @ k1_xboole_0 )
    = ( k2_xboole_0 @ sk_A @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('59',plain,
    ( sk_A
    = ( k2_xboole_0 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['55','56','57','58'])).

thf('60',plain,
    ( ( k4_subset_1 @ sk_A @ sk_B_1 @ sk_A )
    = sk_A ),
    inference(demod,[status(thm)],['6','59'])).

thf('61',plain,(
    ( k4_subset_1 @ sk_A @ sk_B_1 @ ( k2_subset_1 @ sk_A ) )
 != ( k2_subset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X40: $i] :
      ( ( k2_subset_1 @ X40 )
      = X40 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('63',plain,(
    ! [X40: $i] :
      ( ( k2_subset_1 @ X40 )
      = X40 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('64',plain,(
    ( k4_subset_1 @ sk_A @ sk_B_1 @ sk_A )
 != sk_A ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['60','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.fysmi7jJWq
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:45:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.41/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.60  % Solved by: fo/fo7.sh
% 0.41/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.60  % done 266 iterations in 0.150s
% 0.41/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.60  % SZS output start Refutation
% 0.41/0.60  thf(sk_B_type, type, sk_B: $i > $i).
% 0.41/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.41/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.60  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.41/0.60  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.41/0.60  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.41/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.60  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.41/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.41/0.60  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.41/0.60  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.41/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.60  thf(dt_k2_subset_1, axiom,
% 0.41/0.60    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.41/0.60  thf('0', plain,
% 0.41/0.60      (![X41 : $i]: (m1_subset_1 @ (k2_subset_1 @ X41) @ (k1_zfmisc_1 @ X41))),
% 0.41/0.60      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.41/0.60  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.41/0.60  thf('1', plain, (![X40 : $i]: ((k2_subset_1 @ X40) = (X40))),
% 0.41/0.60      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.41/0.60  thf('2', plain, (![X41 : $i]: (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X41))),
% 0.41/0.60      inference('demod', [status(thm)], ['0', '1'])).
% 0.41/0.60  thf(t28_subset_1, conjecture,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.60       ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ))).
% 0.41/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.60    (~( ![A:$i,B:$i]:
% 0.41/0.60        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.60          ( ( k4_subset_1 @ A @ B @ ( k2_subset_1 @ A ) ) = ( k2_subset_1 @ A ) ) ) )),
% 0.41/0.60    inference('cnf.neg', [status(esa)], [t28_subset_1])).
% 0.41/0.60  thf('3', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(redefinition_k4_subset_1, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) & 
% 0.41/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.60       ( ( k4_subset_1 @ A @ B @ C ) = ( k2_xboole_0 @ B @ C ) ) ))).
% 0.41/0.60  thf('4', plain,
% 0.41/0.60      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X43))
% 0.41/0.60          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ X43))
% 0.41/0.60          | ((k4_subset_1 @ X43 @ X42 @ X44) = (k2_xboole_0 @ X42 @ X44)))),
% 0.41/0.60      inference('cnf', [status(esa)], [redefinition_k4_subset_1])).
% 0.41/0.60  thf('5', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (((k4_subset_1 @ sk_A @ sk_B_1 @ X0) = (k2_xboole_0 @ sk_B_1 @ X0))
% 0.41/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.41/0.60  thf('6', plain,
% 0.41/0.60      (((k4_subset_1 @ sk_A @ sk_B_1 @ sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['2', '5'])).
% 0.41/0.60  thf(d1_xboole_0, axiom,
% 0.41/0.60    (![A:$i]:
% 0.41/0.60     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.41/0.60  thf('7', plain,
% 0.41/0.60      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.60  thf('8', plain, ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf(d2_subset_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( v1_xboole_0 @ A ) =>
% 0.41/0.60         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.41/0.60       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.41/0.60         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.41/0.60  thf('9', plain,
% 0.41/0.60      (![X37 : $i, X38 : $i]:
% 0.41/0.60         (~ (m1_subset_1 @ X37 @ X38)
% 0.41/0.60          | (r2_hidden @ X37 @ X38)
% 0.41/0.60          | (v1_xboole_0 @ X38))),
% 0.41/0.60      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.41/0.60  thf('10', plain,
% 0.41/0.60      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.41/0.60        | (r2_hidden @ sk_B_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['8', '9'])).
% 0.41/0.60  thf(d1_zfmisc_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( ( B ) = ( k1_zfmisc_1 @ A ) ) <=>
% 0.41/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( r1_tarski @ C @ A ) ) ) ))).
% 0.41/0.60  thf('11', plain,
% 0.41/0.60      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X33 @ X32)
% 0.41/0.60          | (r1_tarski @ X33 @ X31)
% 0.41/0.60          | ((X32) != (k1_zfmisc_1 @ X31)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.41/0.60  thf('12', plain,
% 0.41/0.60      (![X31 : $i, X33 : $i]:
% 0.41/0.60         ((r1_tarski @ X33 @ X31) | ~ (r2_hidden @ X33 @ (k1_zfmisc_1 @ X31)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['11'])).
% 0.41/0.60  thf('13', plain,
% 0.41/0.60      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)) | (r1_tarski @ sk_B_1 @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['10', '12'])).
% 0.41/0.60  thf(t28_xboole_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( r1_tarski @ A @ B ) => ( ( k3_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.41/0.60  thf('14', plain,
% 0.41/0.60      (![X14 : $i, X15 : $i]:
% 0.41/0.60         (((k3_xboole_0 @ X14 @ X15) = (X14)) | ~ (r1_tarski @ X14 @ X15))),
% 0.41/0.60      inference('cnf', [status(esa)], [t28_xboole_1])).
% 0.41/0.60  thf('15', plain,
% 0.41/0.60      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.41/0.60        | ((k3_xboole_0 @ sk_B_1 @ sk_A) = (sk_B_1)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['13', '14'])).
% 0.41/0.60  thf(d3_tarski, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( r1_tarski @ A @ B ) <=>
% 0.41/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.41/0.60  thf('16', plain,
% 0.41/0.60      (![X4 : $i, X6 : $i]:
% 0.41/0.60         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.60  thf('17', plain,
% 0.41/0.60      (![X4 : $i, X6 : $i]:
% 0.41/0.60         ((r1_tarski @ X4 @ X6) | ~ (r2_hidden @ (sk_C @ X6 @ X4) @ X6))),
% 0.41/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.41/0.60  thf('18', plain,
% 0.41/0.60      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['16', '17'])).
% 0.41/0.60  thf('19', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.41/0.60      inference('simplify', [status(thm)], ['18'])).
% 0.41/0.60  thf('20', plain,
% 0.41/0.60      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.41/0.60         (~ (r1_tarski @ X30 @ X31)
% 0.41/0.60          | (r2_hidden @ X30 @ X32)
% 0.41/0.60          | ((X32) != (k1_zfmisc_1 @ X31)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_zfmisc_1])).
% 0.41/0.60  thf('21', plain,
% 0.41/0.60      (![X30 : $i, X31 : $i]:
% 0.41/0.60         ((r2_hidden @ X30 @ (k1_zfmisc_1 @ X31)) | ~ (r1_tarski @ X30 @ X31))),
% 0.41/0.60      inference('simplify', [status(thm)], ['20'])).
% 0.41/0.60  thf('22', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['19', '21'])).
% 0.41/0.60  thf('23', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.60  thf('24', plain, (![X0 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['22', '23'])).
% 0.41/0.60  thf('25', plain, (((k3_xboole_0 @ sk_B_1 @ sk_A) = (sk_B_1))),
% 0.41/0.60      inference('sup-', [status(thm)], ['15', '24'])).
% 0.41/0.60  thf(t48_xboole_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 0.41/0.60  thf('26', plain,
% 0.41/0.60      (![X18 : $i, X19 : $i]:
% 0.41/0.60         ((k4_xboole_0 @ X18 @ (k4_xboole_0 @ X18 @ X19))
% 0.41/0.60           = (k3_xboole_0 @ X18 @ X19))),
% 0.41/0.60      inference('cnf', [status(esa)], [t48_xboole_1])).
% 0.41/0.60  thf(d5_xboole_0, axiom,
% 0.41/0.60    (![A:$i,B:$i,C:$i]:
% 0.41/0.60     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 0.41/0.60       ( ![D:$i]:
% 0.41/0.60         ( ( r2_hidden @ D @ C ) <=>
% 0.41/0.60           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 0.41/0.60  thf('27', plain,
% 0.41/0.60      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X11 @ X10)
% 0.41/0.60          | ~ (r2_hidden @ X11 @ X9)
% 0.41/0.60          | ((X10) != (k4_xboole_0 @ X8 @ X9)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.41/0.60  thf('28', plain,
% 0.41/0.60      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X11 @ X9)
% 0.41/0.60          | ~ (r2_hidden @ X11 @ (k4_xboole_0 @ X8 @ X9)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['27'])).
% 0.41/0.60  thf('29', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X1 @ X0))
% 0.41/0.60          | ~ (r2_hidden @ X2 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['26', '28'])).
% 0.41/0.60  thf('30', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X0 @ sk_B_1)
% 0.41/0.60          | ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_B_1 @ sk_A)))),
% 0.41/0.60      inference('sup-', [status(thm)], ['25', '29'])).
% 0.41/0.60  thf('31', plain,
% 0.41/0.60      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X11 @ X10)
% 0.41/0.60          | (r2_hidden @ X11 @ X8)
% 0.41/0.60          | ((X10) != (k4_xboole_0 @ X8 @ X9)))),
% 0.41/0.60      inference('cnf', [status(esa)], [d5_xboole_0])).
% 0.41/0.60  thf('32', plain,
% 0.41/0.60      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.41/0.60         ((r2_hidden @ X11 @ X8)
% 0.41/0.60          | ~ (r2_hidden @ X11 @ (k4_xboole_0 @ X8 @ X9)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['31'])).
% 0.41/0.60  thf('33', plain,
% 0.41/0.60      (![X0 : $i]: ~ (r2_hidden @ X0 @ (k4_xboole_0 @ sk_B_1 @ sk_A))),
% 0.41/0.60      inference('clc', [status(thm)], ['30', '32'])).
% 0.41/0.60  thf('34', plain, ((v1_xboole_0 @ (k4_xboole_0 @ sk_B_1 @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['7', '33'])).
% 0.41/0.60  thf('35', plain,
% 0.41/0.60      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.41/0.60      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.60  thf(commutativity_k2_tarski, axiom,
% 0.41/0.60    (![A:$i,B:$i]: ( ( k2_tarski @ A @ B ) = ( k2_tarski @ B @ A ) ))).
% 0.41/0.60  thf('36', plain,
% 0.41/0.60      (![X23 : $i, X24 : $i]:
% 0.41/0.60         ((k2_tarski @ X24 @ X23) = (k2_tarski @ X23 @ X24))),
% 0.41/0.60      inference('cnf', [status(esa)], [commutativity_k2_tarski])).
% 0.41/0.60  thf(l51_zfmisc_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( k3_tarski @ ( k2_tarski @ A @ B ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.41/0.60  thf('37', plain,
% 0.41/0.60      (![X35 : $i, X36 : $i]:
% 0.41/0.60         ((k3_tarski @ (k2_tarski @ X35 @ X36)) = (k2_xboole_0 @ X35 @ X36))),
% 0.41/0.60      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.41/0.60  thf('38', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         ((k3_tarski @ (k2_tarski @ X1 @ X0)) = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.60      inference('sup+', [status(thm)], ['36', '37'])).
% 0.41/0.60  thf('39', plain,
% 0.41/0.60      (![X35 : $i, X36 : $i]:
% 0.41/0.60         ((k3_tarski @ (k2_tarski @ X35 @ X36)) = (k2_xboole_0 @ X35 @ X36))),
% 0.41/0.60      inference('cnf', [status(esa)], [l51_zfmisc_1])).
% 0.41/0.60  thf('40', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.60      inference('sup+', [status(thm)], ['38', '39'])).
% 0.41/0.60  thf(t1_boole, axiom,
% 0.41/0.60    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.41/0.60  thf('41', plain, (![X13 : $i]: ((k2_xboole_0 @ X13 @ k1_xboole_0) = (X13))),
% 0.41/0.60      inference('cnf', [status(esa)], [t1_boole])).
% 0.41/0.60  thf('42', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['40', '41'])).
% 0.41/0.60  thf(t39_xboole_1, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.41/0.60  thf('43', plain,
% 0.41/0.60      (![X16 : $i, X17 : $i]:
% 0.41/0.60         ((k2_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16))
% 0.41/0.60           = (k2_xboole_0 @ X16 @ X17))),
% 0.41/0.60      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.41/0.60  thf('44', plain,
% 0.41/0.60      (![X0 : $i]:
% 0.41/0.60         ((k4_xboole_0 @ X0 @ k1_xboole_0) = (k2_xboole_0 @ k1_xboole_0 @ X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['42', '43'])).
% 0.41/0.60  thf('45', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['40', '41'])).
% 0.41/0.60  thf('46', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 0.41/0.60      inference('demod', [status(thm)], ['44', '45'])).
% 0.41/0.60  thf('47', plain,
% 0.41/0.60      (![X8 : $i, X9 : $i, X11 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X11 @ X9)
% 0.41/0.60          | ~ (r2_hidden @ X11 @ (k4_xboole_0 @ X8 @ X9)))),
% 0.41/0.60      inference('simplify', [status(thm)], ['27'])).
% 0.41/0.60  thf('48', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]:
% 0.41/0.60         (~ (r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['46', '47'])).
% 0.41/0.60  thf('49', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.41/0.60      inference('condensation', [status(thm)], ['48'])).
% 0.41/0.60  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.60      inference('sup-', [status(thm)], ['35', '49'])).
% 0.41/0.60  thf(t8_boole, axiom,
% 0.41/0.60    (![A:$i,B:$i]:
% 0.41/0.60     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.41/0.60  thf('51', plain,
% 0.41/0.60      (![X21 : $i, X22 : $i]:
% 0.41/0.60         (~ (v1_xboole_0 @ X21) | ~ (v1_xboole_0 @ X22) | ((X21) = (X22)))),
% 0.41/0.60      inference('cnf', [status(esa)], [t8_boole])).
% 0.41/0.60  thf('52', plain,
% 0.41/0.60      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.60      inference('sup-', [status(thm)], ['50', '51'])).
% 0.41/0.60  thf('53', plain, (((k1_xboole_0) = (k4_xboole_0 @ sk_B_1 @ sk_A))),
% 0.41/0.60      inference('sup-', [status(thm)], ['34', '52'])).
% 0.41/0.60  thf('54', plain,
% 0.41/0.60      (![X16 : $i, X17 : $i]:
% 0.41/0.60         ((k2_xboole_0 @ X16 @ (k4_xboole_0 @ X17 @ X16))
% 0.41/0.60           = (k2_xboole_0 @ X16 @ X17))),
% 0.41/0.60      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.41/0.60  thf('55', plain,
% 0.41/0.60      (((k2_xboole_0 @ sk_A @ k1_xboole_0) = (k2_xboole_0 @ sk_A @ sk_B_1))),
% 0.41/0.60      inference('sup+', [status(thm)], ['53', '54'])).
% 0.41/0.60  thf('56', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.60      inference('sup+', [status(thm)], ['38', '39'])).
% 0.41/0.60  thf('57', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.41/0.60      inference('sup+', [status(thm)], ['40', '41'])).
% 0.41/0.60  thf('58', plain,
% 0.41/0.60      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.41/0.60      inference('sup+', [status(thm)], ['38', '39'])).
% 0.41/0.60  thf('59', plain, (((sk_A) = (k2_xboole_0 @ sk_B_1 @ sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['55', '56', '57', '58'])).
% 0.41/0.60  thf('60', plain, (((k4_subset_1 @ sk_A @ sk_B_1 @ sk_A) = (sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['6', '59'])).
% 0.41/0.60  thf('61', plain,
% 0.41/0.60      (((k4_subset_1 @ sk_A @ sk_B_1 @ (k2_subset_1 @ sk_A))
% 0.41/0.60         != (k2_subset_1 @ sk_A))),
% 0.41/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.60  thf('62', plain, (![X40 : $i]: ((k2_subset_1 @ X40) = (X40))),
% 0.41/0.60      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.41/0.60  thf('63', plain, (![X40 : $i]: ((k2_subset_1 @ X40) = (X40))),
% 0.41/0.60      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.41/0.60  thf('64', plain, (((k4_subset_1 @ sk_A @ sk_B_1 @ sk_A) != (sk_A))),
% 0.41/0.60      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.41/0.60  thf('65', plain, ($false),
% 0.41/0.60      inference('simplify_reflect-', [status(thm)], ['60', '64'])).
% 0.41/0.60  
% 0.41/0.60  % SZS output end Refutation
% 0.41/0.60  
% 0.41/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
