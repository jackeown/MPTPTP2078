%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9Rlg4Noi3P

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:47:14 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 280 expanded)
%              Number of leaves         :   30 (  93 expanded)
%              Depth                    :   21
%              Number of atoms          :  788 (2439 expanded)
%              Number of equality atoms :   38 ( 100 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X23 @ X24 ) )
        = ( k9_relat_1 @ X23 @ X24 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(t167_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t167_funct_1])).

thf('1',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X14 ) @ X15 )
      | ( r2_hidden @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(t207_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_xboole_0 @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = k1_xboole_0 ) ) ) )).

thf('8',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_xboole_0 @ X27 @ X28 )
      | ~ ( v1_relat_1 @ X29 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X29 @ X27 ) @ X28 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t207_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ ( k1_tarski @ X1 ) ) @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ ( k1_tarski @ X1 ) ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','13'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('16',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t97_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k7_relat_1 @ B @ A )
          = B ) ) ) )).

thf('17',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X32 ) @ X33 )
      | ( ( k7_relat_1 @ X32 @ X33 )
        = X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('19',plain,(
    ! [X30: $i,X31: $i] :
      ( ( ( k7_relat_1 @ X30 @ X31 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X30 ) @ X31 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('23',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X25 ) @ X26 )
      | ( ( k9_relat_1 @ X25 @ X26 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( ( k9_relat_1 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','13'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ k1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 ) ) ),
    inference(clc,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('28',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X23 @ X24 ) )
        = ( k9_relat_1 @ X23 @ X24 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['26','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','13'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ ( k1_tarski @ X1 ) ) @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('35',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['15'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('36',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ( v4_relat_1 @ X16 @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(fc23_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v4_relat_1 @ C @ B ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) )
        & ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ A )
        & ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ) )).

thf('38',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ ( k7_relat_1 @ X20 @ X21 ) @ X22 )
      | ~ ( v4_relat_1 @ X20 @ X22 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc23_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v4_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X32: $i,X33: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X32 ) @ X33 )
      | ( ( k7_relat_1 @ X32 @ X33 )
        = X32 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t97_relat_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_relat_1 @ X0 ) )
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k7_relat_1 @ X1 @ ( k1_tarski @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['34','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ X1 @ ( k1_tarski @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
    | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) )
      | ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['33','54'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('56',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(condensation,[status(thm)],['57'])).

thf('59',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(condensation,[status(thm)],['57'])).

thf(t118_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) )
       => ( ( k9_relat_1 @ C @ ( k2_tarski @ A @ B ) )
          = ( k2_tarski @ ( k1_funct_1 @ C @ A ) @ ( k1_funct_1 @ C @ B ) ) ) ) ) )).

thf('60',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( r2_hidden @ X34 @ ( k1_relat_1 @ X35 ) )
      | ~ ( r2_hidden @ X36 @ ( k1_relat_1 @ X35 ) )
      | ( ( k9_relat_1 @ X35 @ ( k2_tarski @ X34 @ X36 ) )
        = ( k2_tarski @ ( k1_funct_1 @ X35 @ X34 ) @ ( k1_funct_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t118_funct_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( ( k9_relat_1 @ sk_B @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_B @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ( k9_relat_1 @ sk_B @ ( k2_tarski @ sk_A @ sk_A ) )
    = ( k2_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['58','64'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('66',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('67',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('68',plain,
    ( ( k9_relat_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    = ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['15'])).

thf('70',plain,(
    $false ),
    inference(demod,[status(thm)],['4','68','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9Rlg4Noi3P
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:32:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.91/1.12  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.91/1.12  % Solved by: fo/fo7.sh
% 0.91/1.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.12  % done 1032 iterations in 0.664s
% 0.91/1.12  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.91/1.12  % SZS output start Refutation
% 0.91/1.12  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.12  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.91/1.12  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.91/1.12  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.91/1.12  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.91/1.12  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.91/1.12  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.12  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.12  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.91/1.12  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.91/1.12  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.91/1.12  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.12  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.91/1.12  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.12  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.91/1.12  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.91/1.12  thf(t148_relat_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( v1_relat_1 @ B ) =>
% 0.91/1.12       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.91/1.12  thf('0', plain,
% 0.91/1.12      (![X23 : $i, X24 : $i]:
% 0.91/1.12         (((k2_relat_1 @ (k7_relat_1 @ X23 @ X24)) = (k9_relat_1 @ X23 @ X24))
% 0.91/1.12          | ~ (v1_relat_1 @ X23))),
% 0.91/1.12      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.91/1.12  thf(t167_funct_1, conjecture,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.91/1.12       ( r1_tarski @
% 0.91/1.12         ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ 
% 0.91/1.12         ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ))).
% 0.91/1.12  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.12    (~( ![A:$i,B:$i]:
% 0.91/1.12        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.91/1.12          ( r1_tarski @
% 0.91/1.12            ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ 
% 0.91/1.12            ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) )),
% 0.91/1.12    inference('cnf.neg', [status(esa)], [t167_funct_1])).
% 0.91/1.12  thf('1', plain,
% 0.91/1.12      (~ (r1_tarski @ 
% 0.91/1.12          (k2_relat_1 @ (k7_relat_1 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.91/1.12          (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('2', plain,
% 0.91/1.12      ((~ (r1_tarski @ (k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.91/1.12           (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.91/1.12        | ~ (v1_relat_1 @ sk_B))),
% 0.91/1.12      inference('sup-', [status(thm)], ['0', '1'])).
% 0.91/1.12  thf('3', plain, ((v1_relat_1 @ sk_B)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('4', plain,
% 0.91/1.12      (~ (r1_tarski @ (k9_relat_1 @ sk_B @ (k1_tarski @ sk_A)) @ 
% 0.91/1.12          (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.91/1.12      inference('demod', [status(thm)], ['2', '3'])).
% 0.91/1.12  thf('5', plain, ((v1_relat_1 @ sk_B)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf(dt_k7_relat_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.91/1.12  thf('6', plain,
% 0.91/1.12      (![X18 : $i, X19 : $i]:
% 0.91/1.12         (~ (v1_relat_1 @ X18) | (v1_relat_1 @ (k7_relat_1 @ X18 @ X19)))),
% 0.91/1.12      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.91/1.12  thf(l27_zfmisc_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.91/1.12  thf('7', plain,
% 0.91/1.12      (![X14 : $i, X15 : $i]:
% 0.91/1.12         ((r1_xboole_0 @ (k1_tarski @ X14) @ X15) | (r2_hidden @ X14 @ X15))),
% 0.91/1.12      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.91/1.12  thf(t207_relat_1, axiom,
% 0.91/1.12    (![A:$i,B:$i,C:$i]:
% 0.91/1.12     ( ( v1_relat_1 @ C ) =>
% 0.91/1.12       ( ( r1_xboole_0 @ A @ B ) =>
% 0.91/1.12         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.91/1.12  thf('8', plain,
% 0.91/1.12      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.91/1.12         (~ (r1_xboole_0 @ X27 @ X28)
% 0.91/1.12          | ~ (v1_relat_1 @ X29)
% 0.91/1.12          | ((k7_relat_1 @ (k7_relat_1 @ X29 @ X27) @ X28) = (k1_xboole_0)))),
% 0.91/1.12      inference('cnf', [status(esa)], [t207_relat_1])).
% 0.91/1.12  thf('9', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.12         ((r2_hidden @ X1 @ X0)
% 0.91/1.12          | ((k7_relat_1 @ (k7_relat_1 @ X2 @ (k1_tarski @ X1)) @ X0)
% 0.91/1.12              = (k1_xboole_0))
% 0.91/1.12          | ~ (v1_relat_1 @ X2))),
% 0.91/1.12      inference('sup-', [status(thm)], ['7', '8'])).
% 0.91/1.12  thf('10', plain,
% 0.91/1.12      (![X18 : $i, X19 : $i]:
% 0.91/1.12         (~ (v1_relat_1 @ X18) | (v1_relat_1 @ (k7_relat_1 @ X18 @ X19)))),
% 0.91/1.12      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.91/1.12  thf('11', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.12         ((v1_relat_1 @ k1_xboole_0)
% 0.91/1.12          | ~ (v1_relat_1 @ X2)
% 0.91/1.12          | (r2_hidden @ X1 @ X0)
% 0.91/1.12          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ (k1_tarski @ X1))))),
% 0.91/1.12      inference('sup+', [status(thm)], ['9', '10'])).
% 0.91/1.12  thf('12', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.12         (~ (v1_relat_1 @ X1)
% 0.91/1.12          | (r2_hidden @ X0 @ X2)
% 0.91/1.12          | ~ (v1_relat_1 @ X1)
% 0.91/1.12          | (v1_relat_1 @ k1_xboole_0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['6', '11'])).
% 0.91/1.12  thf('13', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.12         ((v1_relat_1 @ k1_xboole_0)
% 0.91/1.12          | (r2_hidden @ X0 @ X2)
% 0.91/1.12          | ~ (v1_relat_1 @ X1))),
% 0.91/1.12      inference('simplify', [status(thm)], ['12'])).
% 0.91/1.12  thf('14', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         ((r2_hidden @ X1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['5', '13'])).
% 0.91/1.12  thf(d10_xboole_0, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.91/1.12  thf('15', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.91/1.12      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.91/1.12  thf('16', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.91/1.12      inference('simplify', [status(thm)], ['15'])).
% 0.91/1.12  thf(t97_relat_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( v1_relat_1 @ B ) =>
% 0.91/1.12       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.91/1.12         ( ( k7_relat_1 @ B @ A ) = ( B ) ) ) ))).
% 0.91/1.12  thf('17', plain,
% 0.91/1.12      (![X32 : $i, X33 : $i]:
% 0.91/1.12         (~ (r1_tarski @ (k1_relat_1 @ X32) @ X33)
% 0.91/1.12          | ((k7_relat_1 @ X32 @ X33) = (X32))
% 0.91/1.12          | ~ (v1_relat_1 @ X32))),
% 0.91/1.12      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.91/1.12  thf('18', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['16', '17'])).
% 0.91/1.12  thf(t95_relat_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( v1_relat_1 @ B ) =>
% 0.91/1.12       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.91/1.12         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.91/1.12  thf('19', plain,
% 0.91/1.12      (![X30 : $i, X31 : $i]:
% 0.91/1.12         (((k7_relat_1 @ X30 @ X31) != (k1_xboole_0))
% 0.91/1.12          | (r1_xboole_0 @ (k1_relat_1 @ X30) @ X31)
% 0.91/1.12          | ~ (v1_relat_1 @ X30))),
% 0.91/1.12      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.91/1.12  thf('20', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         (((X0) != (k1_xboole_0))
% 0.91/1.12          | ~ (v1_relat_1 @ X0)
% 0.91/1.12          | ~ (v1_relat_1 @ X0)
% 0.91/1.12          | (r1_xboole_0 @ (k1_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['18', '19'])).
% 0.91/1.12  thf('21', plain,
% 0.91/1.12      (((r1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ (k1_relat_1 @ k1_xboole_0))
% 0.91/1.12        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.91/1.12      inference('simplify', [status(thm)], ['20'])).
% 0.91/1.12  thf('22', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         ((r2_hidden @ X1 @ X0)
% 0.91/1.12          | (r1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ 
% 0.91/1.12             (k1_relat_1 @ k1_xboole_0)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['14', '21'])).
% 0.91/1.12  thf(t151_relat_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( v1_relat_1 @ B ) =>
% 0.91/1.12       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.91/1.12         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.91/1.12  thf('23', plain,
% 0.91/1.12      (![X25 : $i, X26 : $i]:
% 0.91/1.12         (~ (r1_xboole_0 @ (k1_relat_1 @ X25) @ X26)
% 0.91/1.12          | ((k9_relat_1 @ X25 @ X26) = (k1_xboole_0))
% 0.91/1.12          | ~ (v1_relat_1 @ X25))),
% 0.91/1.12      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.91/1.12  thf('24', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         ((r2_hidden @ X1 @ X0)
% 0.91/1.12          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.91/1.12          | ((k9_relat_1 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))
% 0.91/1.12              = (k1_xboole_0)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['22', '23'])).
% 0.91/1.12  thf('25', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         ((r2_hidden @ X1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['5', '13'])).
% 0.91/1.12  thf('26', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         (((k9_relat_1 @ k1_xboole_0 @ (k1_relat_1 @ k1_xboole_0))
% 0.91/1.12            = (k1_xboole_0))
% 0.91/1.12          | (r2_hidden @ X1 @ X0))),
% 0.91/1.12      inference('clc', [status(thm)], ['24', '25'])).
% 0.91/1.12  thf('27', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         (~ (v1_relat_1 @ X0) | ((k7_relat_1 @ X0 @ (k1_relat_1 @ X0)) = (X0)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['16', '17'])).
% 0.91/1.12  thf('28', plain,
% 0.91/1.12      (![X23 : $i, X24 : $i]:
% 0.91/1.12         (((k2_relat_1 @ (k7_relat_1 @ X23 @ X24)) = (k9_relat_1 @ X23 @ X24))
% 0.91/1.12          | ~ (v1_relat_1 @ X23))),
% 0.91/1.12      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.91/1.12  thf('29', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         (((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.91/1.12          | ~ (v1_relat_1 @ X0)
% 0.91/1.12          | ~ (v1_relat_1 @ X0))),
% 0.91/1.12      inference('sup+', [status(thm)], ['27', '28'])).
% 0.91/1.12  thf('30', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         (~ (v1_relat_1 @ X0)
% 0.91/1.12          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.91/1.12      inference('simplify', [status(thm)], ['29'])).
% 0.91/1.12  thf('31', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))
% 0.91/1.12          | (r2_hidden @ X1 @ X0)
% 0.91/1.12          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.91/1.12      inference('sup+', [status(thm)], ['26', '30'])).
% 0.91/1.12  thf('32', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         ((r2_hidden @ X1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.91/1.12      inference('sup-', [status(thm)], ['5', '13'])).
% 0.91/1.12  thf('33', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         ((r2_hidden @ X1 @ X0) | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.91/1.12      inference('clc', [status(thm)], ['31', '32'])).
% 0.91/1.12  thf('34', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.91/1.12         ((r2_hidden @ X1 @ X0)
% 0.91/1.12          | ((k7_relat_1 @ (k7_relat_1 @ X2 @ (k1_tarski @ X1)) @ X0)
% 0.91/1.12              = (k1_xboole_0))
% 0.91/1.12          | ~ (v1_relat_1 @ X2))),
% 0.91/1.12      inference('sup-', [status(thm)], ['7', '8'])).
% 0.91/1.12  thf('35', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.91/1.12      inference('simplify', [status(thm)], ['15'])).
% 0.91/1.12  thf(d18_relat_1, axiom,
% 0.91/1.12    (![A:$i,B:$i]:
% 0.91/1.12     ( ( v1_relat_1 @ B ) =>
% 0.91/1.12       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.91/1.12  thf('36', plain,
% 0.91/1.12      (![X16 : $i, X17 : $i]:
% 0.91/1.12         (~ (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 0.91/1.12          | (v4_relat_1 @ X16 @ X17)
% 0.91/1.12          | ~ (v1_relat_1 @ X16))),
% 0.91/1.12      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.91/1.12  thf('37', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['35', '36'])).
% 0.91/1.12  thf(fc23_relat_1, axiom,
% 0.91/1.12    (![A:$i,B:$i,C:$i]:
% 0.91/1.12     ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ B ) ) =>
% 0.91/1.12       ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) ) & 
% 0.91/1.12         ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ A ) & 
% 0.91/1.12         ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ))).
% 0.91/1.12  thf('38', plain,
% 0.91/1.12      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.91/1.12         ((v4_relat_1 @ (k7_relat_1 @ X20 @ X21) @ X22)
% 0.91/1.12          | ~ (v4_relat_1 @ X20 @ X22)
% 0.91/1.12          | ~ (v1_relat_1 @ X20))),
% 0.91/1.12      inference('cnf', [status(esa)], [fc23_relat_1])).
% 0.91/1.12  thf('39', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         (~ (v1_relat_1 @ X0)
% 0.91/1.12          | ~ (v1_relat_1 @ X0)
% 0.91/1.12          | (v4_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['37', '38'])).
% 0.91/1.12  thf('40', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         ((v4_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.91/1.12          | ~ (v1_relat_1 @ X0))),
% 0.91/1.12      inference('simplify', [status(thm)], ['39'])).
% 0.91/1.12  thf('41', plain,
% 0.91/1.12      (![X16 : $i, X17 : $i]:
% 0.91/1.12         (~ (v4_relat_1 @ X16 @ X17)
% 0.91/1.12          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 0.91/1.12          | ~ (v1_relat_1 @ X16))),
% 0.91/1.12      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.91/1.12  thf('42', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         (~ (v1_relat_1 @ X0)
% 0.91/1.12          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.91/1.12          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 0.91/1.12             (k1_relat_1 @ X0)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['40', '41'])).
% 0.91/1.12  thf('43', plain,
% 0.91/1.12      (![X18 : $i, X19 : $i]:
% 0.91/1.12         (~ (v1_relat_1 @ X18) | (v1_relat_1 @ (k7_relat_1 @ X18 @ X19)))),
% 0.91/1.12      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.91/1.12  thf('44', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X0 @ X1)) @ 
% 0.91/1.12           (k1_relat_1 @ X0))
% 0.91/1.12          | ~ (v1_relat_1 @ X0))),
% 0.91/1.12      inference('clc', [status(thm)], ['42', '43'])).
% 0.91/1.12  thf('45', plain,
% 0.91/1.12      (![X32 : $i, X33 : $i]:
% 0.91/1.12         (~ (r1_tarski @ (k1_relat_1 @ X32) @ X33)
% 0.91/1.12          | ((k7_relat_1 @ X32 @ X33) = (X32))
% 0.91/1.12          | ~ (v1_relat_1 @ X32))),
% 0.91/1.12      inference('cnf', [status(esa)], [t97_relat_1])).
% 0.91/1.12  thf('46', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         (~ (v1_relat_1 @ X0)
% 0.91/1.12          | ~ (v1_relat_1 @ (k7_relat_1 @ X0 @ X1))
% 0.91/1.12          | ((k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.91/1.12              = (k7_relat_1 @ X0 @ X1)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['44', '45'])).
% 0.91/1.12  thf('47', plain,
% 0.91/1.12      (![X18 : $i, X19 : $i]:
% 0.91/1.12         (~ (v1_relat_1 @ X18) | (v1_relat_1 @ (k7_relat_1 @ X18 @ X19)))),
% 0.91/1.12      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.91/1.12  thf('48', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         (((k7_relat_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_relat_1 @ X0))
% 0.91/1.12            = (k7_relat_1 @ X0 @ X1))
% 0.91/1.12          | ~ (v1_relat_1 @ X0))),
% 0.91/1.12      inference('clc', [status(thm)], ['46', '47'])).
% 0.91/1.12  thf('49', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         (((k1_xboole_0) = (k7_relat_1 @ X1 @ (k1_tarski @ X0)))
% 0.91/1.12          | ~ (v1_relat_1 @ X1)
% 0.91/1.12          | (r2_hidden @ X0 @ (k1_relat_1 @ X1))
% 0.91/1.12          | ~ (v1_relat_1 @ X1))),
% 0.91/1.12      inference('sup+', [status(thm)], ['34', '48'])).
% 0.91/1.12  thf('50', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         ((r2_hidden @ X0 @ (k1_relat_1 @ X1))
% 0.91/1.12          | ~ (v1_relat_1 @ X1)
% 0.91/1.12          | ((k1_xboole_0) = (k7_relat_1 @ X1 @ (k1_tarski @ X0))))),
% 0.91/1.12      inference('simplify', [status(thm)], ['49'])).
% 0.91/1.12  thf('51', plain,
% 0.91/1.12      (~ (r1_tarski @ 
% 0.91/1.12          (k2_relat_1 @ (k7_relat_1 @ sk_B @ (k1_tarski @ sk_A))) @ 
% 0.91/1.12          (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('52', plain,
% 0.91/1.12      ((~ (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ 
% 0.91/1.12           (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.91/1.12        | ~ (v1_relat_1 @ sk_B)
% 0.91/1.12        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['50', '51'])).
% 0.91/1.12  thf('53', plain, ((v1_relat_1 @ sk_B)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('54', plain,
% 0.91/1.12      ((~ (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ 
% 0.91/1.12           (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.91/1.12        | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.91/1.12      inference('demod', [status(thm)], ['52', '53'])).
% 0.91/1.12  thf('55', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         (~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))
% 0.91/1.12          | (r2_hidden @ X1 @ X0)
% 0.91/1.12          | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['33', '54'])).
% 0.91/1.12  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.91/1.12  thf('56', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.91/1.12      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.91/1.12  thf('57', plain,
% 0.91/1.12      (![X0 : $i, X1 : $i]:
% 0.91/1.12         ((r2_hidden @ X1 @ X0) | (r2_hidden @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.91/1.12      inference('demod', [status(thm)], ['55', '56'])).
% 0.91/1.12  thf('58', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.91/1.12      inference('condensation', [status(thm)], ['57'])).
% 0.91/1.12  thf('59', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.91/1.12      inference('condensation', [status(thm)], ['57'])).
% 0.91/1.12  thf(t118_funct_1, axiom,
% 0.91/1.12    (![A:$i,B:$i,C:$i]:
% 0.91/1.12     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.91/1.12       ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.91/1.12           ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) ) =>
% 0.91/1.12         ( ( k9_relat_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 0.91/1.12           ( k2_tarski @ ( k1_funct_1 @ C @ A ) @ ( k1_funct_1 @ C @ B ) ) ) ) ))).
% 0.91/1.12  thf('60', plain,
% 0.91/1.12      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.91/1.12         (~ (r2_hidden @ X34 @ (k1_relat_1 @ X35))
% 0.91/1.12          | ~ (r2_hidden @ X36 @ (k1_relat_1 @ X35))
% 0.91/1.12          | ((k9_relat_1 @ X35 @ (k2_tarski @ X34 @ X36))
% 0.91/1.12              = (k2_tarski @ (k1_funct_1 @ X35 @ X34) @ 
% 0.91/1.12                 (k1_funct_1 @ X35 @ X36)))
% 0.91/1.12          | ~ (v1_funct_1 @ X35)
% 0.91/1.12          | ~ (v1_relat_1 @ X35))),
% 0.91/1.12      inference('cnf', [status(esa)], [t118_funct_1])).
% 0.91/1.12  thf('61', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         (~ (v1_relat_1 @ sk_B)
% 0.91/1.12          | ~ (v1_funct_1 @ sk_B)
% 0.91/1.12          | ((k9_relat_1 @ sk_B @ (k2_tarski @ sk_A @ X0))
% 0.91/1.12              = (k2_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 0.91/1.12                 (k1_funct_1 @ sk_B @ X0)))
% 0.91/1.12          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['59', '60'])).
% 0.91/1.12  thf('62', plain, ((v1_relat_1 @ sk_B)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('63', plain, ((v1_funct_1 @ sk_B)),
% 0.91/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.12  thf('64', plain,
% 0.91/1.12      (![X0 : $i]:
% 0.91/1.12         (((k9_relat_1 @ sk_B @ (k2_tarski @ sk_A @ X0))
% 0.91/1.12            = (k2_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ 
% 0.91/1.12               (k1_funct_1 @ sk_B @ X0)))
% 0.91/1.12          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B)))),
% 0.91/1.12      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.91/1.12  thf('65', plain,
% 0.91/1.12      (((k9_relat_1 @ sk_B @ (k2_tarski @ sk_A @ sk_A))
% 0.91/1.12         = (k2_tarski @ (k1_funct_1 @ sk_B @ sk_A) @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.91/1.12      inference('sup-', [status(thm)], ['58', '64'])).
% 0.91/1.12  thf(t69_enumset1, axiom,
% 0.91/1.12    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.91/1.12  thf('66', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.91/1.12      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.91/1.12  thf('67', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.91/1.12      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.91/1.12  thf('68', plain,
% 0.91/1.12      (((k9_relat_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.91/1.12         = (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 0.91/1.12      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.91/1.12  thf('69', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.91/1.12      inference('simplify', [status(thm)], ['15'])).
% 0.91/1.12  thf('70', plain, ($false),
% 0.91/1.12      inference('demod', [status(thm)], ['4', '68', '69'])).
% 0.91/1.12  
% 0.91/1.12  % SZS output end Refutation
% 0.91/1.12  
% 0.91/1.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
