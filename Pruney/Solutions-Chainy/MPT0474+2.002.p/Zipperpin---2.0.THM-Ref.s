%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FkEsEfAgMS

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 126 expanded)
%              Number of leaves         :   17 (  42 expanded)
%              Depth                    :   26
%              Number of atoms          :  770 (1415 expanded)
%              Number of equality atoms :   25 (  51 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_relat_1_type,type,(
    k4_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('0',plain,(
    ! [X1: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('1',plain,(
    ! [X1: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('2',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(dt_k4_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ) )).

thf('3',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('4',plain,(
    ! [X1: $i] :
      ( ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( A = B )
          <=> ! [C: $i,D: $i] :
                ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
              <=> ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ X3 ) @ ( sk_D @ X2 @ X3 ) ) @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ X3 ) @ ( sk_D @ X2 @ X3 ) ) @ X2 )
      | ( X3 = X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d2_relat_1])).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('7',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ X1 @ X0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ X1 @ X0 ) ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ X1 @ X0 ) ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ X0 ) @ ( sk_D @ X1 @ X0 ) ) @ X1 )
      | ( X0 = X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0 = X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ k1_xboole_0 ) @ ( sk_D @ X1 @ k1_xboole_0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ k1_xboole_0 ) @ ( sk_D @ X1 @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ k1_xboole_0 ) @ ( sk_D @ X1 @ k1_xboole_0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ k1_xboole_0 ) @ ( sk_D @ X1 @ k1_xboole_0 ) ) @ X1 )
      | ( k1_xboole_0 = X1 ) ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('12',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ k1_xboole_0 ) @ ( sk_D @ X1 @ k1_xboole_0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ k1_xboole_0 ) @ ( sk_D @ X1 @ k1_xboole_0 ) ) @ X1 )
      | ( k1_xboole_0 = X1 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ k1_xboole_0 ) @ ( sk_D @ X0 @ k1_xboole_0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['13'])).

thf(d7_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( B
              = ( k4_relat_1 @ A ) )
          <=> ! [C: $i,D: $i] :
                ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B )
              <=> ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i,X14: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( X12
       != ( k4_relat_1 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ X16 @ X14 ) @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_1])).

thf('16',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k4_relat_1 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ X16 @ X14 ) @ X13 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( k1_xboole_0
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k4_relat_1 @ X0 ) @ k1_xboole_0 ) @ ( sk_C @ ( k4_relat_1 @ X0 ) @ k1_xboole_0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k4_relat_1 @ X0 ) @ k1_xboole_0 ) @ ( sk_C @ ( k4_relat_1 @ X0 ) @ k1_xboole_0 ) ) @ X0 )
      | ( k1_xboole_0
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k4_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k4_relat_1 @ X0 ) @ k1_xboole_0 ) @ ( sk_C @ ( k4_relat_1 @ X0 ) @ k1_xboole_0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k4_relat_1 @ X0 ) @ k1_xboole_0 ) @ ( sk_C @ ( k4_relat_1 @ X0 ) @ k1_xboole_0 ) ) @ X0 )
      | ( k1_xboole_0
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X9 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k4_relat_1 @ X0 ) @ k1_xboole_0 ) @ ( sk_C @ ( k4_relat_1 @ X0 ) @ k1_xboole_0 ) ) @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k4_relat_1 @ X0 ) @ k1_xboole_0 ) @ ( sk_C @ ( k4_relat_1 @ X0 ) @ k1_xboole_0 ) ) @ X1 )
      | ( k1_xboole_0
        = ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k4_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k4_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) @ ( sk_C @ ( k4_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','23'])).

thf(t66_relat_1,conjecture,
    ( ( k4_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf(zf_stmt_0,negated_conjecture,(
    ( k4_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('cnf.neg',[status(esa)],[t66_relat_1])).

thf('25',plain,(
    ( k4_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k4_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) @ ( sk_C @ ( k4_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k4_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) @ ( sk_C @ ( k4_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','26'])).

thf('28',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k4_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) @ ( sk_C @ ( k4_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X13: $i,X14: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X16 ) @ ( k4_relat_1 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ X16 @ X14 ) @ X13 )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k4_relat_1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k4_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) @ ( sk_D @ ( k4_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k4_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) @ ( sk_D @ ( k4_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference(clc,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ X3 ) @ ( sk_D @ X2 @ X3 ) ) @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ X3 ) @ ( sk_D @ X2 @ X3 ) ) @ X2 )
      | ( X3 = X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[d2_relat_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k4_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) @ ( sk_D @ ( k4_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ) @ ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k4_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) @ ( sk_D @ ( k4_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ) @ ( k4_relat_1 @ k1_xboole_0 ) )
    | ( k1_xboole_0
      = ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ( k4_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ~ ( v1_relat_1 @ ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k4_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) @ ( sk_D @ ( k4_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ) @ ( k4_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k4_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) @ ( sk_D @ ( k4_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ) @ ( k4_relat_1 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( k4_tarski @ ( sk_D @ ( k4_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) @ ( sk_C @ ( k4_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('42',plain,(
    ! [X17: $i] :
      ( ( v1_relat_1 @ ( k4_relat_1 @ X17 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_relat_1])).

thf('43',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( X12
       != ( k4_relat_1 @ X13 ) )
      | ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ X12 )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X14 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d7_relat_1])).

thf('44',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( r2_hidden @ ( k4_tarski @ X15 @ X14 ) @ X13 )
      | ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ ( k4_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ ( k4_relat_1 @ X13 ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k4_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['42','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k4_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ ( k4_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) @ ( sk_D @ ( k4_relat_1 @ k1_xboole_0 ) @ k1_xboole_0 ) ) @ ( k4_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','46'])).

thf('48',plain,(
    ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(clc,[status(thm)],['40','47'])).

thf('49',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','48'])).

thf('50',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['49','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FkEsEfAgMS
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:21:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 61 iterations in 0.056s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.21/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.51  thf(k4_relat_1_type, type, k4_relat_1: $i > $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(cc1_relat_1, axiom,
% 0.21/0.51    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.21/0.51  thf('0', plain, (![X1 : $i]: ((v1_relat_1 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.51  thf('1', plain, (![X1 : $i]: ((v1_relat_1 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.51  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.51  thf('2', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.51  thf(dt_k4_relat_1, axiom,
% 0.21/0.51    (![A:$i]: ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_relat_1 @ A ) ) ))).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (![X17 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X17)) | ~ (v1_relat_1 @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.21/0.51  thf('4', plain, (![X1 : $i]: ((v1_relat_1 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.21/0.51  thf('5', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.51      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.51  thf(d2_relat_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( v1_relat_1 @ B ) =>
% 0.21/0.51           ( ( ( A ) = ( B ) ) <=>
% 0.21/0.51             ( ![C:$i,D:$i]:
% 0.21/0.51               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) <=>
% 0.21/0.51                 ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ) ))).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X2 : $i, X3 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X2)
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ (sk_C @ X2 @ X3) @ (sk_D @ X2 @ X3)) @ X3)
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ (sk_C @ X2 @ X3) @ (sk_D @ X2 @ X3)) @ X2)
% 0.21/0.51          | ((X3) = (X2))
% 0.21/0.51          | ~ (v1_relat_1 @ X3))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_relat_1])).
% 0.21/0.51  thf(d3_relat_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.51           ( ![C:$i,D:$i]:
% 0.21/0.51             ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) =>
% 0.21/0.51               ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) ) ))).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.51         (~ (r1_tarski @ X8 @ X9)
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X10 @ X11) @ X9)
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X8)
% 0.21/0.51          | ~ (v1_relat_1 @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.21/0.51  thf('8', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X0)
% 0.21/0.51          | ((X0) = (X1))
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_D @ X1 @ X0)) @ X1)
% 0.21/0.51          | ~ (v1_relat_1 @ X1)
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_D @ X1 @ X0)) @ X2)
% 0.21/0.51          | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (r1_tarski @ X0 @ X2)
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_D @ X1 @ X0)) @ X2)
% 0.21/0.51          | ~ (v1_relat_1 @ X1)
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ (sk_C @ X1 @ X0) @ (sk_D @ X1 @ X0)) @ X1)
% 0.21/0.51          | ((X0) = (X1))
% 0.21/0.51          | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['8'])).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.51          | ((k1_xboole_0) = (X1))
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ (sk_C @ X1 @ k1_xboole_0) @ (sk_D @ X1 @ k1_xboole_0)) @ 
% 0.21/0.51             X1)
% 0.21/0.51          | ~ (v1_relat_1 @ X1)
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ (sk_C @ X1 @ k1_xboole_0) @ (sk_D @ X1 @ k1_xboole_0)) @ 
% 0.21/0.51             X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['5', '9'])).
% 0.21/0.51  thf('11', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ (sk_C @ X1 @ k1_xboole_0) @ (sk_D @ X1 @ k1_xboole_0)) @ 
% 0.21/0.51             X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X1)
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ (sk_C @ X1 @ k1_xboole_0) @ (sk_D @ X1 @ k1_xboole_0)) @ 
% 0.21/0.51             X1)
% 0.21/0.51          | ((k1_xboole_0) = (X1)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['4', '10'])).
% 0.21/0.51  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.51  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         ((r2_hidden @ 
% 0.21/0.51           (k4_tarski @ (sk_C @ X1 @ k1_xboole_0) @ (sk_D @ X1 @ k1_xboole_0)) @ 
% 0.21/0.51           X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X1)
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ (sk_C @ X1 @ k1_xboole_0) @ (sk_D @ X1 @ k1_xboole_0)) @ 
% 0.21/0.51             X1)
% 0.21/0.51          | ((k1_xboole_0) = (X1)))),
% 0.21/0.51      inference('demod', [status(thm)], ['11', '12'])).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (((k1_xboole_0) = (X0))
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ (sk_C @ X0 @ k1_xboole_0) @ (sk_D @ X0 @ k1_xboole_0)) @ 
% 0.21/0.51             X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('eq_fact', [status(thm)], ['13'])).
% 0.21/0.51  thf(d7_relat_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ A ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( v1_relat_1 @ B ) =>
% 0.21/0.51           ( ( ( B ) = ( k4_relat_1 @ A ) ) <=>
% 0.21/0.51             ( ![C:$i,D:$i]:
% 0.21/0.51               ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) <=>
% 0.21/0.51                 ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ) ) ))).
% 0.21/0.51  thf('15', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i, X14 : $i, X16 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X12)
% 0.21/0.51          | ((X12) != (k4_relat_1 @ X13))
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X16 @ X14) @ X13)
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X14 @ X16) @ X12)
% 0.21/0.51          | ~ (v1_relat_1 @ X13))),
% 0.21/0.51      inference('cnf', [status(esa)], [d7_relat_1])).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X13)
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X14 @ X16) @ (k4_relat_1 @ X13))
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X16 @ X14) @ X13)
% 0.21/0.51          | ~ (v1_relat_1 @ (k4_relat_1 @ X13)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.21/0.51          | ((k1_xboole_0) = (k4_relat_1 @ X0))
% 0.21/0.51          | ~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ (sk_D @ (k4_relat_1 @ X0) @ k1_xboole_0) @ 
% 0.21/0.51              (sk_C @ (k4_relat_1 @ X0) @ k1_xboole_0)) @ 
% 0.21/0.51             X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['14', '16'])).
% 0.21/0.51  thf('18', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X0)
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ (sk_D @ (k4_relat_1 @ X0) @ k1_xboole_0) @ 
% 0.21/0.51              (sk_C @ (k4_relat_1 @ X0) @ k1_xboole_0)) @ 
% 0.21/0.51             X0)
% 0.21/0.51          | ((k1_xboole_0) = (k4_relat_1 @ X0))
% 0.21/0.51          | ~ (v1_relat_1 @ (k4_relat_1 @ X0)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.51  thf('19', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X0)
% 0.21/0.51          | ((k1_xboole_0) = (k4_relat_1 @ X0))
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ (sk_D @ (k4_relat_1 @ X0) @ k1_xboole_0) @ 
% 0.21/0.51              (sk_C @ (k4_relat_1 @ X0) @ k1_xboole_0)) @ 
% 0.21/0.51             X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['3', '18'])).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r2_hidden @ 
% 0.21/0.51           (k4_tarski @ (sk_D @ (k4_relat_1 @ X0) @ k1_xboole_0) @ 
% 0.21/0.51            (sk_C @ (k4_relat_1 @ X0) @ k1_xboole_0)) @ 
% 0.21/0.51           X0)
% 0.21/0.51          | ((k1_xboole_0) = (k4_relat_1 @ X0))
% 0.21/0.51          | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['19'])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.51         (~ (r1_tarski @ X8 @ X9)
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X10 @ X11) @ X9)
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X8)
% 0.21/0.51          | ~ (v1_relat_1 @ X8))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_relat_1])).
% 0.21/0.51  thf('22', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X0)
% 0.21/0.51          | ((k1_xboole_0) = (k4_relat_1 @ X0))
% 0.21/0.51          | ~ (v1_relat_1 @ X0)
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ (sk_D @ (k4_relat_1 @ X0) @ k1_xboole_0) @ 
% 0.21/0.51              (sk_C @ (k4_relat_1 @ X0) @ k1_xboole_0)) @ 
% 0.21/0.51             X1)
% 0.21/0.51          | ~ (r1_tarski @ X0 @ X1))),
% 0.21/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i]:
% 0.21/0.51         (~ (r1_tarski @ X0 @ X1)
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ (sk_D @ (k4_relat_1 @ X0) @ k1_xboole_0) @ 
% 0.21/0.51              (sk_C @ (k4_relat_1 @ X0) @ k1_xboole_0)) @ 
% 0.21/0.51             X1)
% 0.21/0.51          | ((k1_xboole_0) = (k4_relat_1 @ X0))
% 0.21/0.51          | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['22'])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.51          | ((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ (sk_D @ (k4_relat_1 @ k1_xboole_0) @ k1_xboole_0) @ 
% 0.21/0.51              (sk_C @ (k4_relat_1 @ k1_xboole_0) @ k1_xboole_0)) @ 
% 0.21/0.51             X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['2', '23'])).
% 0.21/0.51  thf(t66_relat_1, conjecture,
% 0.21/0.51    (( k4_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (( k4_relat_1 @ k1_xboole_0 ) != ( k1_xboole_0 )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t66_relat_1])).
% 0.21/0.51  thf('25', plain, (((k4_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ (sk_D @ (k4_relat_1 @ k1_xboole_0) @ k1_xboole_0) @ 
% 0.21/0.51              (sk_C @ (k4_relat_1 @ k1_xboole_0) @ k1_xboole_0)) @ 
% 0.21/0.51             X0))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ (sk_D @ (k4_relat_1 @ k1_xboole_0) @ k1_xboole_0) @ 
% 0.21/0.51              (sk_C @ (k4_relat_1 @ k1_xboole_0) @ k1_xboole_0)) @ 
% 0.21/0.51             X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '26'])).
% 0.21/0.51  thf('28', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.51  thf('29', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (r2_hidden @ 
% 0.21/0.51          (k4_tarski @ (sk_D @ (k4_relat_1 @ k1_xboole_0) @ k1_xboole_0) @ 
% 0.21/0.51           (sk_C @ (k4_relat_1 @ k1_xboole_0) @ k1_xboole_0)) @ 
% 0.21/0.51          X0)),
% 0.21/0.51      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.51  thf('30', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i, X16 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X13)
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X14 @ X16) @ (k4_relat_1 @ X13))
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X16 @ X14) @ X13)
% 0.21/0.51          | ~ (v1_relat_1 @ (k4_relat_1 @ X13)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ (k4_relat_1 @ X0))
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ (sk_C @ (k4_relat_1 @ k1_xboole_0) @ k1_xboole_0) @ 
% 0.21/0.51              (sk_D @ (k4_relat_1 @ k1_xboole_0) @ k1_xboole_0)) @ 
% 0.21/0.51             X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.51  thf('32', plain,
% 0.21/0.51      (![X17 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X17)) | ~ (v1_relat_1 @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.21/0.51  thf('33', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X0)
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ (sk_C @ (k4_relat_1 @ k1_xboole_0) @ k1_xboole_0) @ 
% 0.21/0.51              (sk_D @ (k4_relat_1 @ k1_xboole_0) @ k1_xboole_0)) @ 
% 0.21/0.51             X0))),
% 0.21/0.51      inference('clc', [status(thm)], ['31', '32'])).
% 0.21/0.51  thf('34', plain,
% 0.21/0.51      (![X2 : $i, X3 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X2)
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ (sk_C @ X2 @ X3) @ (sk_D @ X2 @ X3)) @ 
% 0.21/0.51               X3)
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ (sk_C @ X2 @ X3) @ (sk_D @ X2 @ X3)) @ 
% 0.21/0.51               X2)
% 0.21/0.51          | ((X3) = (X2))
% 0.21/0.51          | ~ (v1_relat_1 @ X3))),
% 0.21/0.51      inference('cnf', [status(esa)], [d2_relat_1])).
% 0.21/0.51  thf('35', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.51        | ~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.51        | ((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))
% 0.21/0.51        | ~ (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ (sk_C @ (k4_relat_1 @ k1_xboole_0) @ k1_xboole_0) @ 
% 0.21/0.51              (sk_D @ (k4_relat_1 @ k1_xboole_0) @ k1_xboole_0)) @ 
% 0.21/0.51             (k4_relat_1 @ k1_xboole_0))
% 0.21/0.51        | ~ (v1_relat_1 @ (k4_relat_1 @ k1_xboole_0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.51  thf('36', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))
% 0.21/0.51        | ~ (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ (sk_C @ (k4_relat_1 @ k1_xboole_0) @ k1_xboole_0) @ 
% 0.21/0.51              (sk_D @ (k4_relat_1 @ k1_xboole_0) @ k1_xboole_0)) @ 
% 0.21/0.51             (k4_relat_1 @ k1_xboole_0))
% 0.21/0.51        | ((k1_xboole_0) = (k4_relat_1 @ k1_xboole_0))
% 0.21/0.51        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.51  thf('37', plain, (((k4_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('38', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ (k4_relat_1 @ k1_xboole_0))
% 0.21/0.51        | ~ (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ (sk_C @ (k4_relat_1 @ k1_xboole_0) @ k1_xboole_0) @ 
% 0.21/0.51              (sk_D @ (k4_relat_1 @ k1_xboole_0) @ k1_xboole_0)) @ 
% 0.21/0.51             (k4_relat_1 @ k1_xboole_0))
% 0.21/0.51        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.51      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 0.21/0.51  thf('39', plain,
% 0.21/0.51      (![X17 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X17)) | ~ (v1_relat_1 @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.21/0.51  thf('40', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.51        | ~ (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ (sk_C @ (k4_relat_1 @ k1_xboole_0) @ k1_xboole_0) @ 
% 0.21/0.51              (sk_D @ (k4_relat_1 @ k1_xboole_0) @ k1_xboole_0)) @ 
% 0.21/0.51             (k4_relat_1 @ k1_xboole_0)))),
% 0.21/0.51      inference('clc', [status(thm)], ['38', '39'])).
% 0.21/0.51  thf('41', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (r2_hidden @ 
% 0.21/0.51          (k4_tarski @ (sk_D @ (k4_relat_1 @ k1_xboole_0) @ k1_xboole_0) @ 
% 0.21/0.51           (sk_C @ (k4_relat_1 @ k1_xboole_0) @ k1_xboole_0)) @ 
% 0.21/0.51          X0)),
% 0.21/0.51      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.51  thf('42', plain,
% 0.21/0.51      (![X17 : $i]: ((v1_relat_1 @ (k4_relat_1 @ X17)) | ~ (v1_relat_1 @ X17))),
% 0.21/0.51      inference('cnf', [status(esa)], [dt_k4_relat_1])).
% 0.21/0.51  thf('43', plain,
% 0.21/0.51      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X12)
% 0.21/0.51          | ((X12) != (k4_relat_1 @ X13))
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X14 @ X15) @ X12)
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X15 @ X14) @ X13)
% 0.21/0.51          | ~ (v1_relat_1 @ X13))),
% 0.21/0.51      inference('cnf', [status(esa)], [d7_relat_1])).
% 0.21/0.51  thf('44', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X13)
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X15 @ X14) @ X13)
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X14 @ X15) @ (k4_relat_1 @ X13))
% 0.21/0.51          | ~ (v1_relat_1 @ (k4_relat_1 @ X13)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['43'])).
% 0.21/0.51  thf('45', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X0)
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X2 @ X1) @ (k4_relat_1 @ X0))
% 0.21/0.51          | ~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.21/0.51          | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('sup-', [status(thm)], ['42', '44'])).
% 0.21/0.51  thf('46', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (r2_hidden @ (k4_tarski @ X1 @ X2) @ X0)
% 0.21/0.51          | (r2_hidden @ (k4_tarski @ X2 @ X1) @ (k4_relat_1 @ X0))
% 0.21/0.51          | ~ (v1_relat_1 @ X0))),
% 0.21/0.51      inference('simplify', [status(thm)], ['45'])).
% 0.21/0.51  thf('47', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X0)
% 0.21/0.51          | (r2_hidden @ 
% 0.21/0.51             (k4_tarski @ (sk_C @ (k4_relat_1 @ k1_xboole_0) @ k1_xboole_0) @ 
% 0.21/0.51              (sk_D @ (k4_relat_1 @ k1_xboole_0) @ k1_xboole_0)) @ 
% 0.21/0.51             (k4_relat_1 @ X0)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['41', '46'])).
% 0.21/0.51  thf('48', plain, (~ (v1_relat_1 @ k1_xboole_0)),
% 0.21/0.51      inference('clc', [status(thm)], ['40', '47'])).
% 0.21/0.51  thf('49', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.51      inference('sup-', [status(thm)], ['0', '48'])).
% 0.21/0.51  thf('50', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.51      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.51  thf('51', plain, ($false), inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
