%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HXStuJGzij

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:27 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 343 expanded)
%              Number of leaves         :   29 ( 114 expanded)
%              Depth                    :   31
%              Number of atoms          :  765 (2256 expanded)
%              Number of equality atoms :   64 ( 172 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_relat_1 @ X22 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X27 @ X26 ) ) @ ( k2_relat_1 @ X26 ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

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

thf('4',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('5',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('6',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_relat_1 @ X22 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('7',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('8',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t44_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) )).

thf('9',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ X25 @ X24 ) ) @ ( k1_relat_1 @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t44_relat_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('12',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_zfmisc_1 @ X9 @ X10 )
        = k1_xboole_0 )
      | ( X10 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('16',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ X9 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t152_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ~ ( r2_hidden @ X11 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t152_zfmisc_1])).

thf('18',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X5: $i,X7: $i] :
      ( ( X5 = X7 )
      | ~ ( r1_tarski @ X7 @ X5 )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','21'])).

thf(fc8_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('23',plain,(
    ! [X23: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc8_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','28'])).

thf('30',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X13: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('33',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('35',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k5_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_relat_1 @ X22 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X21 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['43'])).

thf('45',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['3','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t56_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ! [B: $i,C: $i] :
            ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
       => ( A = k1_xboole_0 ) ) ) )).

thf('49',plain,(
    ! [X28: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ X28 ) @ ( sk_C_2 @ X28 ) ) @ X28 )
      | ( X28 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('50',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ X16 )
      | ( r2_hidden @ X15 @ X17 )
      | ( X17
       != ( k2_relat_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('51',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ ( k2_relat_1 @ X16 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ X16 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['48','56'])).

thf('58',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','59'])).

thf('61',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['4','44'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('65',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['65'])).

thf('67',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ sk_A @ X0 )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['64','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ ( k5_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('69',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('70',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X4: $i] :
      ( ( X4 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('73',plain,
    ( ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['65'])).

thf('74',plain,
    ( ! [X0: $i] :
        ( ( ( k5_relat_1 @ X0 @ sk_A )
         != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ X1 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('78',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_xboole_0 @ X1 )
        | ~ ( v1_xboole_0 @ ( k5_relat_1 @ X1 @ sk_A ) ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['76','77'])).

thf('79',plain,
    ( ( ~ ( v1_relat_1 @ sk_A )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','78'])).

thf('80',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('82',plain,
    ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['79','80','81'])).

thf('83',plain,
    ( ( ( k5_relat_1 @ sk_A @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( ( k5_relat_1 @ k1_xboole_0 @ sk_A )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['65'])).

thf('84',plain,(
    ( k5_relat_1 @ sk_A @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k5_relat_1 @ sk_A @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['67','84'])).

thf('86',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','85'])).

thf('87',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('89',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['86','87','88'])).

thf('90',plain,(
    $false ),
    inference(simplify,[status(thm)],['89'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HXStuJGzij
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:47:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.59/0.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.83  % Solved by: fo/fo7.sh
% 0.59/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.83  % done 845 iterations in 0.389s
% 0.59/0.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.83  % SZS output start Refutation
% 0.59/0.83  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.59/0.83  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.59/0.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.83  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.59/0.83  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.59/0.83  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.83  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.59/0.83  thf(sk_B_type, type, sk_B: $i > $i).
% 0.59/0.83  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 0.59/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.83  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.59/0.83  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.83  thf(dt_k5_relat_1, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.59/0.83       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.59/0.83  thf('0', plain,
% 0.59/0.83      (![X21 : $i, X22 : $i]:
% 0.59/0.83         (~ (v1_relat_1 @ X21)
% 0.59/0.83          | ~ (v1_relat_1 @ X22)
% 0.59/0.83          | (v1_relat_1 @ (k5_relat_1 @ X21 @ X22)))),
% 0.59/0.83      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.59/0.83  thf(t60_relat_1, axiom,
% 0.59/0.83    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.59/0.83     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.59/0.83  thf('1', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.83      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.59/0.83  thf(t45_relat_1, axiom,
% 0.59/0.83    (![A:$i]:
% 0.59/0.83     ( ( v1_relat_1 @ A ) =>
% 0.59/0.83       ( ![B:$i]:
% 0.59/0.83         ( ( v1_relat_1 @ B ) =>
% 0.59/0.83           ( r1_tarski @
% 0.59/0.83             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.59/0.83  thf('2', plain,
% 0.59/0.83      (![X26 : $i, X27 : $i]:
% 0.59/0.83         (~ (v1_relat_1 @ X26)
% 0.59/0.83          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X27 @ X26)) @ 
% 0.59/0.83             (k2_relat_1 @ X26))
% 0.59/0.83          | ~ (v1_relat_1 @ X27))),
% 0.59/0.83      inference('cnf', [status(esa)], [t45_relat_1])).
% 0.59/0.83  thf('3', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.59/0.83           k1_xboole_0)
% 0.59/0.83          | ~ (v1_relat_1 @ X0)
% 0.59/0.83          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.59/0.83      inference('sup+', [status(thm)], ['1', '2'])).
% 0.59/0.83  thf(t62_relat_1, conjecture,
% 0.59/0.83    (![A:$i]:
% 0.59/0.83     ( ( v1_relat_1 @ A ) =>
% 0.59/0.83       ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.59/0.83         ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ))).
% 0.59/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.83    (~( ![A:$i]:
% 0.59/0.83        ( ( v1_relat_1 @ A ) =>
% 0.59/0.83          ( ( ( k5_relat_1 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ) & 
% 0.59/0.83            ( ( k5_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ) ) )),
% 0.59/0.83    inference('cnf.neg', [status(esa)], [t62_relat_1])).
% 0.59/0.83  thf('4', plain, ((v1_relat_1 @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf(cc1_relat_1, axiom,
% 0.59/0.83    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.59/0.83  thf('5', plain, (![X13 : $i]: ((v1_relat_1 @ X13) | ~ (v1_xboole_0 @ X13))),
% 0.59/0.83      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.59/0.83  thf('6', plain,
% 0.59/0.83      (![X21 : $i, X22 : $i]:
% 0.59/0.83         (~ (v1_relat_1 @ X21)
% 0.59/0.83          | ~ (v1_relat_1 @ X22)
% 0.59/0.83          | (v1_relat_1 @ (k5_relat_1 @ X21 @ X22)))),
% 0.59/0.83      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.59/0.83  thf('7', plain, (![X13 : $i]: ((v1_relat_1 @ X13) | ~ (v1_xboole_0 @ X13))),
% 0.59/0.83      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.59/0.83  thf('8', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.83      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.59/0.83  thf(t44_relat_1, axiom,
% 0.59/0.83    (![A:$i]:
% 0.59/0.83     ( ( v1_relat_1 @ A ) =>
% 0.59/0.83       ( ![B:$i]:
% 0.59/0.83         ( ( v1_relat_1 @ B ) =>
% 0.59/0.83           ( r1_tarski @
% 0.59/0.83             ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k1_relat_1 @ A ) ) ) ) ))).
% 0.59/0.83  thf('9', plain,
% 0.59/0.83      (![X24 : $i, X25 : $i]:
% 0.59/0.83         (~ (v1_relat_1 @ X24)
% 0.59/0.83          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ X25 @ X24)) @ 
% 0.59/0.83             (k1_relat_1 @ X25))
% 0.59/0.83          | ~ (v1_relat_1 @ X25))),
% 0.59/0.83      inference('cnf', [status(esa)], [t44_relat_1])).
% 0.59/0.83  thf('10', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.59/0.83           k1_xboole_0)
% 0.59/0.83          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.59/0.83          | ~ (v1_relat_1 @ X0))),
% 0.59/0.83      inference('sup+', [status(thm)], ['8', '9'])).
% 0.59/0.83  thf('11', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.59/0.83          | ~ (v1_relat_1 @ X0)
% 0.59/0.83          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.59/0.83             k1_xboole_0))),
% 0.59/0.83      inference('sup-', [status(thm)], ['7', '10'])).
% 0.59/0.83  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.59/0.83  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.83      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.59/0.83  thf('13', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (v1_relat_1 @ X0)
% 0.59/0.83          | (r1_tarski @ (k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) @ 
% 0.59/0.83             k1_xboole_0))),
% 0.59/0.83      inference('demod', [status(thm)], ['11', '12'])).
% 0.59/0.83  thf(d3_tarski, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( r1_tarski @ A @ B ) <=>
% 0.59/0.83       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.59/0.83  thf('14', plain,
% 0.59/0.83      (![X1 : $i, X3 : $i]:
% 0.59/0.83         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.59/0.83      inference('cnf', [status(esa)], [d3_tarski])).
% 0.59/0.83  thf(t113_zfmisc_1, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.59/0.83       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.59/0.83  thf('15', plain,
% 0.59/0.83      (![X9 : $i, X10 : $i]:
% 0.59/0.83         (((k2_zfmisc_1 @ X9 @ X10) = (k1_xboole_0)) | ((X10) != (k1_xboole_0)))),
% 0.59/0.83      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.59/0.83  thf('16', plain,
% 0.59/0.83      (![X9 : $i]: ((k2_zfmisc_1 @ X9 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.83      inference('simplify', [status(thm)], ['15'])).
% 0.59/0.83  thf(t152_zfmisc_1, axiom,
% 0.59/0.83    (![A:$i,B:$i]: ( ~( r2_hidden @ A @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.59/0.83  thf('17', plain,
% 0.59/0.83      (![X11 : $i, X12 : $i]: ~ (r2_hidden @ X11 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.59/0.83      inference('cnf', [status(esa)], [t152_zfmisc_1])).
% 0.59/0.83  thf('18', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.59/0.83      inference('sup-', [status(thm)], ['16', '17'])).
% 0.59/0.83  thf('19', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.59/0.83      inference('sup-', [status(thm)], ['14', '18'])).
% 0.59/0.83  thf(d10_xboole_0, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.83  thf('20', plain,
% 0.59/0.83      (![X5 : $i, X7 : $i]:
% 0.59/0.83         (((X5) = (X7)) | ~ (r1_tarski @ X7 @ X5) | ~ (r1_tarski @ X5 @ X7))),
% 0.59/0.83      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.83  thf('21', plain,
% 0.59/0.83      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['19', '20'])).
% 0.59/0.83  thf('22', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (v1_relat_1 @ X0)
% 0.59/0.83          | ((k1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['13', '21'])).
% 0.59/0.83  thf(fc8_relat_1, axiom,
% 0.59/0.83    (![A:$i]:
% 0.59/0.83     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 0.59/0.83       ( ~( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) ))).
% 0.59/0.83  thf('23', plain,
% 0.59/0.83      (![X23 : $i]:
% 0.59/0.83         (~ (v1_xboole_0 @ (k1_relat_1 @ X23))
% 0.59/0.83          | ~ (v1_relat_1 @ X23)
% 0.59/0.83          | (v1_xboole_0 @ X23))),
% 0.59/0.83      inference('cnf', [status(esa)], [fc8_relat_1])).
% 0.59/0.83  thf('24', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.59/0.83          | ~ (v1_relat_1 @ X0)
% 0.59/0.83          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.59/0.83          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['22', '23'])).
% 0.59/0.83  thf('25', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.83      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.59/0.83  thf('26', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (v1_relat_1 @ X0)
% 0.59/0.83          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.59/0.83          | ~ (v1_relat_1 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.59/0.83      inference('demod', [status(thm)], ['24', '25'])).
% 0.59/0.83  thf('27', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (v1_relat_1 @ X0)
% 0.59/0.83          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.59/0.83          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.59/0.83          | ~ (v1_relat_1 @ X0))),
% 0.59/0.83      inference('sup-', [status(thm)], ['6', '26'])).
% 0.59/0.83  thf('28', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0))
% 0.59/0.83          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.59/0.83          | ~ (v1_relat_1 @ X0))),
% 0.59/0.83      inference('simplify', [status(thm)], ['27'])).
% 0.59/0.83  thf('29', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.59/0.83          | ~ (v1_relat_1 @ X0)
% 0.59/0.83          | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['5', '28'])).
% 0.59/0.83  thf('30', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.83      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.59/0.83  thf('31', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.59/0.83      inference('demod', [status(thm)], ['29', '30'])).
% 0.59/0.83  thf('32', plain, (![X13 : $i]: ((v1_relat_1 @ X13) | ~ (v1_xboole_0 @ X13))),
% 0.59/0.83      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.59/0.83  thf(l13_xboole_0, axiom,
% 0.59/0.83    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.59/0.83  thf('33', plain,
% 0.59/0.83      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.59/0.83      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.59/0.83  thf('34', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.59/0.83      inference('demod', [status(thm)], ['29', '30'])).
% 0.59/0.83  thf('35', plain,
% 0.59/0.83      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.59/0.83      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.59/0.83  thf('36', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (v1_relat_1 @ X0)
% 0.59/0.83          | ((k5_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['34', '35'])).
% 0.59/0.83  thf('37', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         (((k5_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.59/0.83          | ~ (v1_xboole_0 @ X0)
% 0.59/0.83          | ~ (v1_relat_1 @ X1))),
% 0.59/0.83      inference('sup+', [status(thm)], ['33', '36'])).
% 0.59/0.83  thf('38', plain,
% 0.59/0.83      (![X21 : $i, X22 : $i]:
% 0.59/0.83         (~ (v1_relat_1 @ X21)
% 0.59/0.83          | ~ (v1_relat_1 @ X22)
% 0.59/0.83          | (v1_relat_1 @ (k5_relat_1 @ X21 @ X22)))),
% 0.59/0.83      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.59/0.83  thf('39', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         ((v1_relat_1 @ k1_xboole_0)
% 0.59/0.83          | ~ (v1_relat_1 @ X0)
% 0.59/0.83          | ~ (v1_xboole_0 @ X1)
% 0.59/0.83          | ~ (v1_relat_1 @ X0)
% 0.59/0.83          | ~ (v1_relat_1 @ X1))),
% 0.59/0.83      inference('sup+', [status(thm)], ['37', '38'])).
% 0.59/0.83  thf('40', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         (~ (v1_relat_1 @ X1)
% 0.59/0.83          | ~ (v1_xboole_0 @ X1)
% 0.59/0.83          | ~ (v1_relat_1 @ X0)
% 0.59/0.83          | (v1_relat_1 @ k1_xboole_0))),
% 0.59/0.83      inference('simplify', [status(thm)], ['39'])).
% 0.59/0.83  thf('41', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         (~ (v1_xboole_0 @ X0)
% 0.59/0.83          | (v1_relat_1 @ k1_xboole_0)
% 0.59/0.83          | ~ (v1_relat_1 @ X1)
% 0.59/0.83          | ~ (v1_xboole_0 @ X0))),
% 0.59/0.83      inference('sup-', [status(thm)], ['32', '40'])).
% 0.59/0.83  thf('42', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         (~ (v1_relat_1 @ X1)
% 0.59/0.83          | (v1_relat_1 @ k1_xboole_0)
% 0.59/0.83          | ~ (v1_xboole_0 @ X0))),
% 0.59/0.83      inference('simplify', [status(thm)], ['41'])).
% 0.59/0.83  thf('43', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         (~ (v1_relat_1 @ X0)
% 0.59/0.83          | (v1_relat_1 @ k1_xboole_0)
% 0.59/0.83          | ~ (v1_relat_1 @ X1))),
% 0.59/0.83      inference('sup-', [status(thm)], ['31', '42'])).
% 0.59/0.83  thf('44', plain,
% 0.59/0.83      (![X0 : $i]: (~ (v1_relat_1 @ X0) | (v1_relat_1 @ k1_xboole_0))),
% 0.59/0.83      inference('condensation', [status(thm)], ['43'])).
% 0.59/0.83  thf('45', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.59/0.83      inference('sup-', [status(thm)], ['4', '44'])).
% 0.59/0.83  thf('46', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) @ 
% 0.59/0.83           k1_xboole_0)
% 0.59/0.83          | ~ (v1_relat_1 @ X0))),
% 0.59/0.83      inference('demod', [status(thm)], ['3', '45'])).
% 0.59/0.83  thf('47', plain,
% 0.59/0.83      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['19', '20'])).
% 0.59/0.83  thf('48', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (v1_relat_1 @ X0)
% 0.59/0.83          | ((k2_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['46', '47'])).
% 0.59/0.83  thf(t56_relat_1, axiom,
% 0.59/0.83    (![A:$i]:
% 0.59/0.83     ( ( v1_relat_1 @ A ) =>
% 0.59/0.83       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.59/0.83         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.59/0.83  thf('49', plain,
% 0.59/0.83      (![X28 : $i]:
% 0.59/0.83         ((r2_hidden @ (k4_tarski @ (sk_B @ X28) @ (sk_C_2 @ X28)) @ X28)
% 0.59/0.83          | ((X28) = (k1_xboole_0))
% 0.59/0.83          | ~ (v1_relat_1 @ X28))),
% 0.59/0.83      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.59/0.83  thf(d5_relat_1, axiom,
% 0.59/0.83    (![A:$i,B:$i]:
% 0.59/0.83     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.59/0.83       ( ![C:$i]:
% 0.59/0.83         ( ( r2_hidden @ C @ B ) <=>
% 0.59/0.83           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.59/0.83  thf('50', plain,
% 0.59/0.83      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.59/0.83         (~ (r2_hidden @ (k4_tarski @ X14 @ X15) @ X16)
% 0.59/0.83          | (r2_hidden @ X15 @ X17)
% 0.59/0.83          | ((X17) != (k2_relat_1 @ X16)))),
% 0.59/0.83      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.59/0.83  thf('51', plain,
% 0.59/0.83      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.59/0.83         ((r2_hidden @ X15 @ (k2_relat_1 @ X16))
% 0.59/0.83          | ~ (r2_hidden @ (k4_tarski @ X14 @ X15) @ X16))),
% 0.59/0.83      inference('simplify', [status(thm)], ['50'])).
% 0.59/0.83  thf('52', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (v1_relat_1 @ X0)
% 0.59/0.83          | ((X0) = (k1_xboole_0))
% 0.59/0.83          | (r2_hidden @ (sk_C_2 @ X0) @ (k2_relat_1 @ X0)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['49', '51'])).
% 0.59/0.83  thf('53', plain,
% 0.59/0.83      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.59/0.83      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.59/0.83  thf('54', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.59/0.83      inference('sup-', [status(thm)], ['16', '17'])).
% 0.59/0.83  thf('55', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.83      inference('sup-', [status(thm)], ['53', '54'])).
% 0.59/0.83  thf('56', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (((X0) = (k1_xboole_0))
% 0.59/0.83          | ~ (v1_relat_1 @ X0)
% 0.59/0.83          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['52', '55'])).
% 0.59/0.83  thf('57', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.59/0.83          | ~ (v1_relat_1 @ X0)
% 0.59/0.83          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.59/0.83          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.59/0.83      inference('sup-', [status(thm)], ['48', '56'])).
% 0.59/0.83  thf('58', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.83      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.59/0.83  thf('59', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (v1_relat_1 @ X0)
% 0.59/0.83          | ~ (v1_relat_1 @ (k5_relat_1 @ X0 @ k1_xboole_0))
% 0.59/0.83          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.59/0.83      inference('demod', [status(thm)], ['57', '58'])).
% 0.59/0.83  thf('60', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (v1_relat_1 @ k1_xboole_0)
% 0.59/0.83          | ~ (v1_relat_1 @ X0)
% 0.59/0.83          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.59/0.83          | ~ (v1_relat_1 @ X0))),
% 0.59/0.83      inference('sup-', [status(thm)], ['0', '59'])).
% 0.59/0.83  thf('61', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.59/0.83      inference('sup-', [status(thm)], ['4', '44'])).
% 0.59/0.83  thf('62', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (v1_relat_1 @ X0)
% 0.59/0.83          | ((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.59/0.83          | ~ (v1_relat_1 @ X0))),
% 0.59/0.83      inference('demod', [status(thm)], ['60', '61'])).
% 0.59/0.83  thf('63', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (((k5_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.59/0.83          | ~ (v1_relat_1 @ X0))),
% 0.59/0.83      inference('simplify', [status(thm)], ['62'])).
% 0.59/0.83  thf('64', plain,
% 0.59/0.83      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.59/0.83      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.59/0.83  thf('65', plain,
% 0.59/0.83      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0))
% 0.59/0.83        | ((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('66', plain,
% 0.59/0.83      ((((k5_relat_1 @ sk_A @ k1_xboole_0) != (k1_xboole_0)))
% 0.59/0.83         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.59/0.83      inference('split', [status(esa)], ['65'])).
% 0.59/0.83  thf('67', plain,
% 0.59/0.83      ((![X0 : $i]:
% 0.59/0.83          (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.59/0.83         <= (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))))),
% 0.59/0.83      inference('sup-', [status(thm)], ['64', '66'])).
% 0.59/0.83  thf('68', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (~ (v1_relat_1 @ X0) | (v1_xboole_0 @ (k5_relat_1 @ k1_xboole_0 @ X0)))),
% 0.59/0.83      inference('demod', [status(thm)], ['29', '30'])).
% 0.59/0.83  thf('69', plain,
% 0.59/0.83      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.59/0.83      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.59/0.83  thf('70', plain,
% 0.59/0.83      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.59/0.83      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.59/0.83  thf('71', plain,
% 0.59/0.83      (![X0 : $i, X1 : $i]:
% 0.59/0.83         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.59/0.83      inference('sup+', [status(thm)], ['69', '70'])).
% 0.59/0.83  thf('72', plain,
% 0.59/0.83      (![X4 : $i]: (((X4) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X4))),
% 0.59/0.83      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.59/0.83  thf('73', plain,
% 0.59/0.83      ((((k5_relat_1 @ k1_xboole_0 @ sk_A) != (k1_xboole_0)))
% 0.59/0.83         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.59/0.83      inference('split', [status(esa)], ['65'])).
% 0.59/0.83  thf('74', plain,
% 0.59/0.83      ((![X0 : $i]:
% 0.59/0.83          (((k5_relat_1 @ X0 @ sk_A) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0)))
% 0.59/0.83         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.59/0.83      inference('sup-', [status(thm)], ['72', '73'])).
% 0.59/0.83  thf('75', plain,
% 0.59/0.83      ((![X0 : $i, X1 : $i]:
% 0.59/0.83          (((X0) != (k1_xboole_0))
% 0.59/0.83           | ~ (v1_xboole_0 @ X0)
% 0.59/0.83           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.59/0.83           | ~ (v1_xboole_0 @ X1)))
% 0.59/0.83         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.59/0.83      inference('sup-', [status(thm)], ['71', '74'])).
% 0.59/0.83  thf('76', plain,
% 0.59/0.83      ((![X1 : $i]:
% 0.59/0.83          (~ (v1_xboole_0 @ X1)
% 0.59/0.83           | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))
% 0.59/0.83           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.59/0.83         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.59/0.83      inference('simplify', [status(thm)], ['75'])).
% 0.59/0.83  thf('77', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.83      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.59/0.83  thf('78', plain,
% 0.59/0.83      ((![X1 : $i]:
% 0.59/0.83          (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ (k5_relat_1 @ X1 @ sk_A))))
% 0.59/0.83         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.59/0.83      inference('simplify_reflect+', [status(thm)], ['76', '77'])).
% 0.59/0.83  thf('79', plain,
% 0.59/0.83      (((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.59/0.83         <= (~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0))))),
% 0.59/0.83      inference('sup-', [status(thm)], ['68', '78'])).
% 0.59/0.83  thf('80', plain, ((v1_relat_1 @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('81', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.83      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.59/0.83  thf('82', plain, ((((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.59/0.83      inference('demod', [status(thm)], ['79', '80', '81'])).
% 0.59/0.83  thf('83', plain,
% 0.59/0.83      (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0))) | 
% 0.59/0.83       ~ (((k5_relat_1 @ k1_xboole_0 @ sk_A) = (k1_xboole_0)))),
% 0.59/0.83      inference('split', [status(esa)], ['65'])).
% 0.59/0.83  thf('84', plain, (~ (((k5_relat_1 @ sk_A @ k1_xboole_0) = (k1_xboole_0)))),
% 0.59/0.83      inference('sat_resolution*', [status(thm)], ['82', '83'])).
% 0.59/0.83  thf('85', plain,
% 0.59/0.83      (![X0 : $i]:
% 0.59/0.83         (((k5_relat_1 @ sk_A @ X0) != (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.83      inference('simpl_trail', [status(thm)], ['67', '84'])).
% 0.59/0.83  thf('86', plain,
% 0.59/0.83      ((((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.83        | ~ (v1_relat_1 @ sk_A)
% 0.59/0.83        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.59/0.83      inference('sup-', [status(thm)], ['63', '85'])).
% 0.59/0.83  thf('87', plain, ((v1_relat_1 @ sk_A)),
% 0.59/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.83  thf('88', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.83      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.59/0.83  thf('89', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.59/0.83      inference('demod', [status(thm)], ['86', '87', '88'])).
% 0.59/0.83  thf('90', plain, ($false), inference('simplify', [status(thm)], ['89'])).
% 0.59/0.83  
% 0.59/0.83  % SZS output end Refutation
% 0.59/0.83  
% 0.71/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
