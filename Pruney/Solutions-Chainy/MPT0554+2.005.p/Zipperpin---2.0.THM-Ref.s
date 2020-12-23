%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eRfbvItLvP

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:30 EST 2020

% Result     : Theorem 19.25s
% Output     : Refutation 19.25s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 261 expanded)
%              Number of leaves         :   22 (  84 expanded)
%              Depth                    :   16
%              Number of atoms          :  687 (2385 expanded)
%              Number of equality atoms :   48 ( 171 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d5_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k4_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ~ ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X7 )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf(t156_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t156_relat_1])).

thf('2',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k4_xboole_0 @ sk_A @ X0 ) )
      | ( r2_hidden @ ( sk_D @ sk_A @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('7',plain,(
    ! [X7: $i,X8: $i,X11: $i] :
      ( ( X11
        = ( k4_xboole_0 @ X7 @ X8 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X8 )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X7 )
      | ~ ( r2_hidden @ ( sk_D @ X11 @ X8 @ X7 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( X9
       != ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[d5_xboole_0])).

thf('13',plain,(
    ! [X7: $i,X8: $i,X10: $i] :
      ( ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X10 @ ( k4_xboole_0 @ X7 @ X8 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) )
      | ( sk_A
        = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['5','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( sk_A
      = ( k4_xboole_0 @ sk_A @ ( k4_xboole_0 @ X0 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X0 )
      | ( X0
        = ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k4_xboole_0 @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( r2_hidden @ ( sk_D @ X2 @ ( k4_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ( X0
        = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( X0
      = ( k4_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ sk_B )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ sk_B ) @ sk_A ) ) ),
    inference('sup+',[status(thm)],['16','20'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('23',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ( X12 != X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('24',plain,(
    ! [X13: $i] :
      ( r1_tarski @ X13 @ X13 ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('25',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      | ~ ( r1_tarski @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('27',plain,(
    ! [X16: $i] :
      ( ( k4_xboole_0 @ X16 @ k1_xboole_0 )
      = X16 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('31',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ X23 @ ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X17 @ X18 ) @ X19 )
      | ~ ( r1_tarski @ X17 @ ( k2_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','39'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('41',plain,(
    ! [X15: $i] :
      ( r1_tarski @ k1_xboole_0 @ X15 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('42',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 ) @ X1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','44'])).

thf('46',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['21','45'])).

thf('47',plain,(
    ! [X13: $i] :
      ( r1_tarski @ X13 @ X13 ) ),
    inference(simplify,[status(thm)],['23'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('48',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( r1_tarski @ X20 @ ( k2_xboole_0 @ X21 @ X22 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X20 @ X21 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) @ X1 )
      | ( ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( r1_tarski @ ( k2_xboole_0 @ sk_B @ k1_xboole_0 ) @ ( k2_xboole_0 @ sk_A @ sk_B ) )
    | ( ( k2_xboole_0 @ sk_B @ ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_B ) )
      = ( k2_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('55',plain,
    ( ( k4_xboole_0 @ ( k2_xboole_0 @ sk_A @ sk_B ) @ sk_B )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['21','45'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup+',[status(thm)],['35','36'])).

thf('57',plain,
    ( sk_B
    = ( k2_xboole_0 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['52','53','54','55','56'])).

thf(t153_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k9_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('58',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k9_relat_1 @ X25 @ ( k2_xboole_0 @ X26 @ X27 ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ X25 @ X26 ) @ ( k9_relat_1 @ X25 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t153_relat_1])).

thf('59',plain,(
    ! [X23: $i,X24: $i] :
      ( r1_tarski @ X23 @ ( k2_xboole_0 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['57','60'])).

thf('62',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ ( k9_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['63','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.eRfbvItLvP
% 0.15/0.34  % Computer   : n001.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 16:38:00 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 19.25/19.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 19.25/19.48  % Solved by: fo/fo7.sh
% 19.25/19.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 19.25/19.48  % done 15162 iterations in 19.018s
% 19.25/19.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 19.25/19.48  % SZS output start Refutation
% 19.25/19.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 19.25/19.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 19.25/19.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 19.25/19.48  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 19.25/19.48  thf(sk_B_type, type, sk_B: $i).
% 19.25/19.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 19.25/19.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 19.25/19.48  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 19.25/19.48  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 19.25/19.48  thf(sk_A_type, type, sk_A: $i).
% 19.25/19.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 19.25/19.48  thf(d5_xboole_0, axiom,
% 19.25/19.48    (![A:$i,B:$i,C:$i]:
% 19.25/19.48     ( ( ( C ) = ( k4_xboole_0 @ A @ B ) ) <=>
% 19.25/19.48       ( ![D:$i]:
% 19.25/19.48         ( ( r2_hidden @ D @ C ) <=>
% 19.25/19.48           ( ( r2_hidden @ D @ A ) & ( ~( r2_hidden @ D @ B ) ) ) ) ) ))).
% 19.25/19.48  thf('0', plain,
% 19.25/19.48      (![X7 : $i, X8 : $i, X11 : $i]:
% 19.25/19.48         (((X11) = (k4_xboole_0 @ X7 @ X8))
% 19.25/19.48          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X7)
% 19.25/19.48          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 19.25/19.48      inference('cnf', [status(esa)], [d5_xboole_0])).
% 19.25/19.48  thf('1', plain,
% 19.25/19.48      (![X0 : $i, X1 : $i]:
% 19.25/19.48         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 19.25/19.48          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 19.25/19.48      inference('eq_fact', [status(thm)], ['0'])).
% 19.25/19.48  thf(t156_relat_1, conjecture,
% 19.25/19.48    (![A:$i,B:$i,C:$i]:
% 19.25/19.48     ( ( v1_relat_1 @ C ) =>
% 19.25/19.48       ( ( r1_tarski @ A @ B ) =>
% 19.25/19.48         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 19.25/19.48  thf(zf_stmt_0, negated_conjecture,
% 19.25/19.48    (~( ![A:$i,B:$i,C:$i]:
% 19.25/19.48        ( ( v1_relat_1 @ C ) =>
% 19.25/19.48          ( ( r1_tarski @ A @ B ) =>
% 19.25/19.48            ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 19.25/19.48    inference('cnf.neg', [status(esa)], [t156_relat_1])).
% 19.25/19.48  thf('2', plain, ((r1_tarski @ sk_A @ sk_B)),
% 19.25/19.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.25/19.48  thf(d3_tarski, axiom,
% 19.25/19.48    (![A:$i,B:$i]:
% 19.25/19.48     ( ( r1_tarski @ A @ B ) <=>
% 19.25/19.48       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 19.25/19.48  thf('3', plain,
% 19.25/19.48      (![X2 : $i, X3 : $i, X4 : $i]:
% 19.25/19.48         (~ (r2_hidden @ X2 @ X3)
% 19.25/19.48          | (r2_hidden @ X2 @ X4)
% 19.25/19.48          | ~ (r1_tarski @ X3 @ X4))),
% 19.25/19.48      inference('cnf', [status(esa)], [d3_tarski])).
% 19.25/19.48  thf('4', plain,
% 19.25/19.48      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 19.25/19.48      inference('sup-', [status(thm)], ['2', '3'])).
% 19.25/19.48  thf('5', plain,
% 19.25/19.48      (![X0 : $i]:
% 19.25/19.48         (((sk_A) = (k4_xboole_0 @ sk_A @ X0))
% 19.25/19.48          | (r2_hidden @ (sk_D @ sk_A @ X0 @ sk_A) @ sk_B))),
% 19.25/19.48      inference('sup-', [status(thm)], ['1', '4'])).
% 19.25/19.48  thf('6', plain,
% 19.25/19.48      (![X0 : $i, X1 : $i]:
% 19.25/19.48         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 19.25/19.48          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 19.25/19.48      inference('eq_fact', [status(thm)], ['0'])).
% 19.25/19.48  thf('7', plain,
% 19.25/19.48      (![X7 : $i, X8 : $i, X11 : $i]:
% 19.25/19.48         (((X11) = (k4_xboole_0 @ X7 @ X8))
% 19.25/19.48          | (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X8)
% 19.25/19.48          | ~ (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X7)
% 19.25/19.48          | ~ (r2_hidden @ (sk_D @ X11 @ X8 @ X7) @ X11))),
% 19.25/19.48      inference('cnf', [status(esa)], [d5_xboole_0])).
% 19.25/19.48  thf('8', plain,
% 19.25/19.48      (![X0 : $i, X1 : $i]:
% 19.25/19.48         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 19.25/19.48          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 19.25/19.48          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 19.25/19.48          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 19.25/19.48      inference('sup-', [status(thm)], ['6', '7'])).
% 19.25/19.48  thf('9', plain,
% 19.25/19.48      (![X0 : $i, X1 : $i]:
% 19.25/19.48         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1)
% 19.25/19.48          | ~ (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 19.25/19.48          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 19.25/19.48      inference('simplify', [status(thm)], ['8'])).
% 19.25/19.48  thf('10', plain,
% 19.25/19.48      (![X0 : $i, X1 : $i]:
% 19.25/19.48         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 19.25/19.48          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 19.25/19.48      inference('eq_fact', [status(thm)], ['0'])).
% 19.25/19.48  thf('11', plain,
% 19.25/19.48      (![X0 : $i, X1 : $i]:
% 19.25/19.48         (((X0) = (k4_xboole_0 @ X0 @ X1))
% 19.25/19.48          | (r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X1))),
% 19.25/19.48      inference('clc', [status(thm)], ['9', '10'])).
% 19.25/19.48  thf('12', plain,
% 19.25/19.48      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 19.25/19.48         (~ (r2_hidden @ X10 @ X9)
% 19.25/19.48          | ~ (r2_hidden @ X10 @ X8)
% 19.25/19.48          | ((X9) != (k4_xboole_0 @ X7 @ X8)))),
% 19.25/19.48      inference('cnf', [status(esa)], [d5_xboole_0])).
% 19.25/19.48  thf('13', plain,
% 19.25/19.48      (![X7 : $i, X8 : $i, X10 : $i]:
% 19.25/19.48         (~ (r2_hidden @ X10 @ X8)
% 19.25/19.48          | ~ (r2_hidden @ X10 @ (k4_xboole_0 @ X7 @ X8)))),
% 19.25/19.48      inference('simplify', [status(thm)], ['12'])).
% 19.25/19.48  thf('14', plain,
% 19.25/19.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.25/19.48         (((X2) = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 19.25/19.48          | ~ (r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 19.25/19.48      inference('sup-', [status(thm)], ['11', '13'])).
% 19.25/19.48  thf('15', plain,
% 19.25/19.48      (![X0 : $i]:
% 19.25/19.48         (((sk_A) = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B)))
% 19.25/19.48          | ((sk_A) = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B))))),
% 19.25/19.48      inference('sup-', [status(thm)], ['5', '14'])).
% 19.25/19.48  thf('16', plain,
% 19.25/19.48      (![X0 : $i]: ((sk_A) = (k4_xboole_0 @ sk_A @ (k4_xboole_0 @ X0 @ sk_B)))),
% 19.25/19.48      inference('simplify', [status(thm)], ['15'])).
% 19.25/19.48  thf('17', plain,
% 19.25/19.48      (![X0 : $i, X1 : $i]:
% 19.25/19.48         ((r2_hidden @ (sk_D @ X0 @ X1 @ X0) @ X0)
% 19.25/19.48          | ((X0) = (k4_xboole_0 @ X0 @ X1)))),
% 19.25/19.48      inference('eq_fact', [status(thm)], ['0'])).
% 19.25/19.48  thf('18', plain,
% 19.25/19.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.25/19.48         (((X2) = (k4_xboole_0 @ X2 @ (k4_xboole_0 @ X1 @ X0)))
% 19.25/19.48          | ~ (r2_hidden @ (sk_D @ X2 @ (k4_xboole_0 @ X1 @ X0) @ X2) @ X0))),
% 19.25/19.48      inference('sup-', [status(thm)], ['11', '13'])).
% 19.25/19.48  thf('19', plain,
% 19.25/19.48      (![X0 : $i, X1 : $i]:
% 19.25/19.48         (((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))
% 19.25/19.48          | ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))))),
% 19.25/19.48      inference('sup-', [status(thm)], ['17', '18'])).
% 19.25/19.48  thf('20', plain,
% 19.25/19.48      (![X0 : $i, X1 : $i]:
% 19.25/19.48         ((X0) = (k4_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 19.25/19.48      inference('simplify', [status(thm)], ['19'])).
% 19.25/19.48  thf('21', plain,
% 19.25/19.48      (![X0 : $i]:
% 19.25/19.48         ((k4_xboole_0 @ X0 @ sk_B)
% 19.25/19.48           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ sk_B) @ sk_A))),
% 19.25/19.48      inference('sup+', [status(thm)], ['16', '20'])).
% 19.25/19.48  thf(commutativity_k2_xboole_0, axiom,
% 19.25/19.48    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 19.25/19.48  thf('22', plain,
% 19.25/19.48      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 19.25/19.48      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 19.25/19.48  thf(d10_xboole_0, axiom,
% 19.25/19.48    (![A:$i,B:$i]:
% 19.25/19.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 19.25/19.48  thf('23', plain,
% 19.25/19.48      (![X12 : $i, X13 : $i]: ((r1_tarski @ X12 @ X13) | ((X12) != (X13)))),
% 19.25/19.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 19.25/19.48  thf('24', plain, (![X13 : $i]: (r1_tarski @ X13 @ X13)),
% 19.25/19.48      inference('simplify', [status(thm)], ['23'])).
% 19.25/19.48  thf(t43_xboole_1, axiom,
% 19.25/19.48    (![A:$i,B:$i,C:$i]:
% 19.25/19.48     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 19.25/19.48       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 19.25/19.48  thf('25', plain,
% 19.25/19.48      (![X17 : $i, X18 : $i, X19 : $i]:
% 19.25/19.48         ((r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 19.25/19.48          | ~ (r1_tarski @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 19.25/19.48      inference('cnf', [status(esa)], [t43_xboole_1])).
% 19.25/19.48  thf('26', plain,
% 19.25/19.48      (![X0 : $i, X1 : $i]:
% 19.25/19.48         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 19.25/19.48      inference('sup-', [status(thm)], ['24', '25'])).
% 19.25/19.48  thf(t3_boole, axiom,
% 19.25/19.48    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 19.25/19.48  thf('27', plain, (![X16 : $i]: ((k4_xboole_0 @ X16 @ k1_xboole_0) = (X16))),
% 19.25/19.48      inference('cnf', [status(esa)], [t3_boole])).
% 19.25/19.48  thf('28', plain,
% 19.25/19.48      (![X0 : $i, X1 : $i]:
% 19.25/19.48         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 19.25/19.48      inference('sup-', [status(thm)], ['24', '25'])).
% 19.25/19.48  thf('29', plain,
% 19.25/19.48      (![X0 : $i]: (r1_tarski @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X0)),
% 19.25/19.48      inference('sup+', [status(thm)], ['27', '28'])).
% 19.25/19.48  thf('30', plain,
% 19.25/19.48      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 19.25/19.48      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 19.25/19.48  thf(t7_xboole_1, axiom,
% 19.25/19.48    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 19.25/19.48  thf('31', plain,
% 19.25/19.48      (![X23 : $i, X24 : $i]: (r1_tarski @ X23 @ (k2_xboole_0 @ X23 @ X24))),
% 19.25/19.48      inference('cnf', [status(esa)], [t7_xboole_1])).
% 19.25/19.48  thf('32', plain,
% 19.25/19.48      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 19.25/19.48      inference('sup+', [status(thm)], ['30', '31'])).
% 19.25/19.48  thf('33', plain,
% 19.25/19.48      (![X12 : $i, X14 : $i]:
% 19.25/19.48         (((X12) = (X14))
% 19.25/19.48          | ~ (r1_tarski @ X14 @ X12)
% 19.25/19.48          | ~ (r1_tarski @ X12 @ X14))),
% 19.25/19.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 19.25/19.48  thf('34', plain,
% 19.25/19.48      (![X0 : $i, X1 : $i]:
% 19.25/19.48         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 19.25/19.48          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 19.25/19.48      inference('sup-', [status(thm)], ['32', '33'])).
% 19.25/19.48  thf('35', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 19.25/19.48      inference('sup-', [status(thm)], ['29', '34'])).
% 19.25/19.48  thf('36', plain,
% 19.25/19.48      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 19.25/19.48      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 19.25/19.48  thf('37', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 19.25/19.48      inference('sup+', [status(thm)], ['35', '36'])).
% 19.25/19.48  thf('38', plain,
% 19.25/19.48      (![X17 : $i, X18 : $i, X19 : $i]:
% 19.25/19.48         ((r1_tarski @ (k4_xboole_0 @ X17 @ X18) @ X19)
% 19.25/19.48          | ~ (r1_tarski @ X17 @ (k2_xboole_0 @ X18 @ X19)))),
% 19.25/19.48      inference('cnf', [status(esa)], [t43_xboole_1])).
% 19.25/19.48  thf('39', plain,
% 19.25/19.48      (![X0 : $i, X1 : $i]:
% 19.25/19.48         (~ (r1_tarski @ X1 @ X0)
% 19.25/19.48          | (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 19.25/19.48      inference('sup-', [status(thm)], ['37', '38'])).
% 19.25/19.48  thf('40', plain,
% 19.25/19.48      (![X0 : $i, X1 : $i]:
% 19.25/19.48         (r1_tarski @ 
% 19.25/19.48          (k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0) @ 
% 19.25/19.48          k1_xboole_0)),
% 19.25/19.48      inference('sup-', [status(thm)], ['26', '39'])).
% 19.25/19.48  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 19.25/19.48  thf('41', plain, (![X15 : $i]: (r1_tarski @ k1_xboole_0 @ X15)),
% 19.25/19.48      inference('cnf', [status(esa)], [t2_xboole_1])).
% 19.25/19.48  thf('42', plain,
% 19.25/19.48      (![X12 : $i, X14 : $i]:
% 19.25/19.48         (((X12) = (X14))
% 19.25/19.48          | ~ (r1_tarski @ X14 @ X12)
% 19.25/19.48          | ~ (r1_tarski @ X12 @ X14))),
% 19.25/19.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 19.25/19.48  thf('43', plain,
% 19.25/19.48      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 19.25/19.48      inference('sup-', [status(thm)], ['41', '42'])).
% 19.25/19.48  thf('44', plain,
% 19.25/19.48      (![X0 : $i, X1 : $i]:
% 19.25/19.48         ((k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)
% 19.25/19.48           = (k1_xboole_0))),
% 19.25/19.48      inference('sup-', [status(thm)], ['40', '43'])).
% 19.25/19.48  thf('45', plain,
% 19.25/19.48      (![X0 : $i, X1 : $i]:
% 19.25/19.48         ((k4_xboole_0 @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X0) @ X1)
% 19.25/19.48           = (k1_xboole_0))),
% 19.25/19.48      inference('sup+', [status(thm)], ['22', '44'])).
% 19.25/19.48  thf('46', plain,
% 19.25/19.48      (((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0))),
% 19.25/19.48      inference('sup+', [status(thm)], ['21', '45'])).
% 19.25/19.48  thf('47', plain, (![X13 : $i]: (r1_tarski @ X13 @ X13)),
% 19.25/19.48      inference('simplify', [status(thm)], ['23'])).
% 19.25/19.48  thf(t44_xboole_1, axiom,
% 19.25/19.48    (![A:$i,B:$i,C:$i]:
% 19.25/19.48     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 19.25/19.48       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 19.25/19.48  thf('48', plain,
% 19.25/19.48      (![X20 : $i, X21 : $i, X22 : $i]:
% 19.25/19.48         ((r1_tarski @ X20 @ (k2_xboole_0 @ X21 @ X22))
% 19.25/19.48          | ~ (r1_tarski @ (k4_xboole_0 @ X20 @ X21) @ X22))),
% 19.25/19.48      inference('cnf', [status(esa)], [t44_xboole_1])).
% 19.25/19.48  thf('49', plain,
% 19.25/19.48      (![X0 : $i, X1 : $i]:
% 19.25/19.48         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 19.25/19.48      inference('sup-', [status(thm)], ['47', '48'])).
% 19.25/19.48  thf('50', plain,
% 19.25/19.48      (![X12 : $i, X14 : $i]:
% 19.25/19.48         (((X12) = (X14))
% 19.25/19.48          | ~ (r1_tarski @ X14 @ X12)
% 19.25/19.48          | ~ (r1_tarski @ X12 @ X14))),
% 19.25/19.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 19.25/19.48  thf('51', plain,
% 19.25/19.48      (![X0 : $i, X1 : $i]:
% 19.25/19.48         (~ (r1_tarski @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) @ X1)
% 19.25/19.48          | ((k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)) = (X1)))),
% 19.25/19.48      inference('sup-', [status(thm)], ['49', '50'])).
% 19.25/19.48  thf('52', plain,
% 19.25/19.48      ((~ (r1_tarski @ (k2_xboole_0 @ sk_B @ k1_xboole_0) @ 
% 19.25/19.48           (k2_xboole_0 @ sk_A @ sk_B))
% 19.25/19.48        | ((k2_xboole_0 @ sk_B @ 
% 19.25/19.48            (k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_B))
% 19.25/19.48            = (k2_xboole_0 @ sk_A @ sk_B)))),
% 19.25/19.48      inference('sup-', [status(thm)], ['46', '51'])).
% 19.25/19.48  thf('53', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 19.25/19.48      inference('sup+', [status(thm)], ['35', '36'])).
% 19.25/19.48  thf('54', plain,
% 19.25/19.48      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 19.25/19.48      inference('sup+', [status(thm)], ['30', '31'])).
% 19.25/19.48  thf('55', plain,
% 19.25/19.48      (((k4_xboole_0 @ (k2_xboole_0 @ sk_A @ sk_B) @ sk_B) = (k1_xboole_0))),
% 19.25/19.48      inference('sup+', [status(thm)], ['21', '45'])).
% 19.25/19.48  thf('56', plain, (![X0 : $i]: ((k2_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 19.25/19.48      inference('sup+', [status(thm)], ['35', '36'])).
% 19.25/19.48  thf('57', plain, (((sk_B) = (k2_xboole_0 @ sk_A @ sk_B))),
% 19.25/19.48      inference('demod', [status(thm)], ['52', '53', '54', '55', '56'])).
% 19.25/19.48  thf(t153_relat_1, axiom,
% 19.25/19.48    (![A:$i,B:$i,C:$i]:
% 19.25/19.48     ( ( v1_relat_1 @ C ) =>
% 19.25/19.48       ( ( k9_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 19.25/19.48         ( k2_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 19.25/19.48  thf('58', plain,
% 19.25/19.48      (![X25 : $i, X26 : $i, X27 : $i]:
% 19.25/19.48         (((k9_relat_1 @ X25 @ (k2_xboole_0 @ X26 @ X27))
% 19.25/19.48            = (k2_xboole_0 @ (k9_relat_1 @ X25 @ X26) @ 
% 19.25/19.48               (k9_relat_1 @ X25 @ X27)))
% 19.25/19.48          | ~ (v1_relat_1 @ X25))),
% 19.25/19.48      inference('cnf', [status(esa)], [t153_relat_1])).
% 19.25/19.48  thf('59', plain,
% 19.25/19.48      (![X23 : $i, X24 : $i]: (r1_tarski @ X23 @ (k2_xboole_0 @ X23 @ X24))),
% 19.25/19.48      inference('cnf', [status(esa)], [t7_xboole_1])).
% 19.25/19.48  thf('60', plain,
% 19.25/19.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.25/19.48         ((r1_tarski @ (k9_relat_1 @ X2 @ X1) @ 
% 19.25/19.48           (k9_relat_1 @ X2 @ (k2_xboole_0 @ X1 @ X0)))
% 19.25/19.48          | ~ (v1_relat_1 @ X2))),
% 19.25/19.48      inference('sup+', [status(thm)], ['58', '59'])).
% 19.25/19.48  thf('61', plain,
% 19.25/19.48      (![X0 : $i]:
% 19.25/19.48         ((r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 19.25/19.48          | ~ (v1_relat_1 @ X0))),
% 19.25/19.48      inference('sup+', [status(thm)], ['57', '60'])).
% 19.25/19.48  thf('62', plain,
% 19.25/19.48      (~ (r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ 
% 19.25/19.48          (k9_relat_1 @ sk_C_1 @ sk_B))),
% 19.25/19.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.25/19.48  thf('63', plain, (~ (v1_relat_1 @ sk_C_1)),
% 19.25/19.48      inference('sup-', [status(thm)], ['61', '62'])).
% 19.25/19.48  thf('64', plain, ((v1_relat_1 @ sk_C_1)),
% 19.25/19.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.25/19.48  thf('65', plain, ($false), inference('demod', [status(thm)], ['63', '64'])).
% 19.25/19.48  
% 19.25/19.48  % SZS output end Refutation
% 19.25/19.48  
% 19.25/19.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
