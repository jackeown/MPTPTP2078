%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0568+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.H80J0Rzljk

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:07 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :   42 (  45 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :  228 ( 237 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(o_1_6_relat_1_type,type,(
    o_1_6_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('1',plain,(
    ! [X12: $i] :
      ( ( X12 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t172_relat_1,conjecture,(
    ! [A: $i] :
      ( ( k10_relat_1 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( k10_relat_1 @ k1_xboole_0 @ A )
        = k1_xboole_0 ) ),
    inference('cnf.neg',[status(esa)],[t172_relat_1])).

thf('3',plain,(
    ( k10_relat_1 @ k1_xboole_0 @ sk_A )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ sk_A ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('6',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('7',plain,(
    ~ ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ sk_A ) ) ),
    inference('simplify_reflect+',[status(thm)],['5','6'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('8',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(dt_o_1_6_relat_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( o_1_6_relat_1 @ A ) @ ( k10_relat_1 @ k1_xboole_0 @ A ) ) )).

thf('9',plain,(
    ! [X9: $i] :
      ( m1_subset_1 @ ( o_1_6_relat_1 @ X9 ) @ ( k10_relat_1 @ k1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[dt_o_1_6_relat_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('10',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( o_1_6_relat_1 @ X0 ) @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(d14_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k10_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ B )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) )).

thf('12',plain,(
    ! [X2: $i,X3: $i,X5: $i,X6: $i] :
      ( ( X5
       != ( k10_relat_1 @ X3 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ X6 @ ( sk_E_1 @ X6 @ X2 @ X3 ) ) @ X3 )
      | ~ ( r2_hidden @ X6 @ X5 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d14_relat_1])).

thf('13',plain,(
    ! [X2: $i,X3: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( r2_hidden @ X6 @ ( k10_relat_1 @ X3 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ X6 @ ( sk_E_1 @ X6 @ X2 @ X3 ) ) @ X3 ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( o_1_6_relat_1 @ X0 ) @ ( sk_E_1 @ ( o_1_6_relat_1 @ X0 ) @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( o_1_6_relat_1 @ X0 ) @ ( sk_E_1 @ ( o_1_6_relat_1 @ X0 ) @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( o_1_6_relat_1 @ X0 ) @ ( sk_E_1 @ ( o_1_6_relat_1 @ X0 ) @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('18',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( v1_xboole_0 @ ( k10_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    $false ),
    inference(demod,[status(thm)],['7','21'])).


%------------------------------------------------------------------------------
