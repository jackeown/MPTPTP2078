%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gOdsTUI5Or

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:42 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 307 expanded)
%              Number of leaves         :   27 ( 106 expanded)
%              Depth                    :   25
%              Number of atoms          :  874 (2968 expanded)
%              Number of equality atoms :   90 ( 321 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_5_type,type,(
    sk_C_5: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(o_1_0_funct_1_type,type,(
    o_1_0_funct_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_4_type,type,(
    sk_C_4: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C_2 @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('2',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_2 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C_2 @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('7',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C_2 @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('14',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( X14 = X11 )
      | ( X13
       != ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('15',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14 = X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X1 )
      | ( ( sk_C_2 @ X1 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X1 )
      | ( ( sk_C_2 @ X1 @ k1_xboole_0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['13','15'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X2 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ k1_xboole_0 @ X2 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf(s3_funct_1__e1_27_1__funct_1,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ! [D: $i] :
          ( ( r2_hidden @ D @ B )
         => ( ( k1_funct_1 @ C @ D )
            = ( o_1_0_funct_1 @ A ) ) )
      & ( ( k1_relat_1 @ C )
        = B )
      & ( v1_funct_1 @ C )
      & ( v1_relat_1 @ C ) ) )).

thf('20',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_relat_1 @ ( sk_C_4 @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e1_27_1__funct_1])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('21',plain,(
    ! [X16: $i] :
      ( ( ( k1_relat_1 @ X16 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X16 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ X0 @ X1 ) )
      | ( ( k2_relat_1 @ ( sk_C_4 @ X0 @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X1: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_4 @ k1_xboole_0 @ X1 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ k1_xboole_0 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( sk_C_4 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e1_27_1__funct_1])).

thf('25',plain,(
    ! [X1: $i] :
      ( ( k2_relat_1 @ ( sk_C_4 @ k1_xboole_0 @ X1 ) )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['23','24'])).

thf(t18_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ~ ( ~ ( ( A = k1_xboole_0 )
            & ( B != k1_xboole_0 ) )
        & ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v1_funct_1 @ C ) )
           => ~ ( ( B
                  = ( k1_relat_1 @ C ) )
                & ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ~ ( ~ ( ( A = k1_xboole_0 )
              & ( B != k1_xboole_0 ) )
          & ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ~ ( ( B
                    = ( k1_relat_1 @ C ) )
                  & ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t18_funct_1])).

thf('26',plain,(
    ! [X22: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X22 ) @ sk_A )
      | ( sk_B
       != ( k1_relat_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
      | ~ ( v1_relat_1 @ ( sk_C_4 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_4 @ k1_xboole_0 @ X0 ) )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_4 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('29',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( sk_C_4 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e1_27_1__funct_1])).

thf('30',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_funct_1 @ ( sk_C_4 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e1_27_1__funct_1])).

thf('31',plain,(
    ! [X17: $i,X18: $i] :
      ( ( k1_relat_1 @ ( sk_C_4 @ X17 @ X18 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e1_27_1__funct_1])).

thf('32',plain,(
    sk_B != k1_xboole_0 ),
    inference(demod,[status(thm)],['27','28','29','30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B != X0 )
      | ( r1_xboole_0 @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['19','32'])).

thf('34',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X1 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','34'])).

thf('36',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( X12 != X11 )
      | ( r2_hidden @ X12 @ X13 )
      | ( X13
       != ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('37',plain,(
    ! [X11: $i] :
      ( r2_hidden @ X11 @ ( k1_tarski @ X11 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ X6 )
      | ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r1_xboole_0 @ X6 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ X0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','40'])).

thf('42',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C_2 @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t15_funct_1,axiom,(
    ! [A: $i] :
      ( ( A != k1_xboole_0 )
     => ! [B: $i] :
        ? [C: $i] :
          ( ( ( k2_relat_1 @ C )
            = ( k1_tarski @ B ) )
          & ( ( k1_relat_1 @ C )
            = A )
          & ( v1_funct_1 @ C )
          & ( v1_relat_1 @ C ) ) ) )).

thf('43',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k1_relat_1 @ ( sk_C_5 @ X20 @ X21 ) )
        = X21 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('44',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_relat_1 @ ( sk_C_5 @ X20 @ X21 ) )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('45',plain,(
    ! [X20: $i,X21: $i] :
      ( ( v1_funct_1 @ ( sk_C_5 @ X20 @ X21 ) )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('46',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('47',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('48',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14 = X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k1_tarski @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ ( sk_C @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf('54',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_5 @ X20 @ X21 ) )
        = ( k1_tarski @ X20 ) )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t15_funct_1])).

thf('55',plain,(
    ! [X22: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X22 ) @ sk_A )
      | ( sk_B
       != ( k1_relat_1 @ X22 ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ X0 ) @ sk_A )
      | ( X1 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_5 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_5 @ X0 @ X1 ) )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_5 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_5 @ ( sk_C @ X0 @ sk_A ) @ X1 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_5 @ ( sk_C @ X0 @ sk_A ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( sk_C_5 @ ( sk_C @ X0 @ sk_A ) @ X1 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_5 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_5 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_5 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_5 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_5 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['44','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_5 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B != X0 )
      | ( X0 = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r1_tarski @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','61'])).

thf('63',plain,(
    ! [X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,(
    sk_B != k1_xboole_0 ),
    inference(demod,[status(thm)],['27','28','29','30','31'])).

thf('65',plain,(
    ! [X1: $i] :
      ( r1_tarski @ sk_A @ X1 ) ),
    inference('simplify_reflect-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C_2 @ X0 @ sk_A ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['42','67'])).

thf('69',plain,(
    ! [X11: $i,X14: $i] :
      ( ( X14 = X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_tarski @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ sk_A @ X1 )
      | ( ( sk_C_2 @ X1 @ sk_A )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ sk_A @ X1 )
      | ( ( sk_C_2 @ X1 @ sk_A )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('72',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( r1_xboole_0 @ sk_A @ X2 )
      | ( r1_xboole_0 @ sk_A @ X2 ) ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ sk_A @ X2 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['72'])).

thf('74',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C_2 @ X7 @ X6 ) @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C_2 @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X2 )
      | ( r1_xboole_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['73','77'])).

thf('79',plain,(
    sk_B != k1_xboole_0 ),
    inference(demod,[status(thm)],['27','28','29','30','31'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_B != X0 )
      | ( r1_xboole_0 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ X1 @ sk_A ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_tarski @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('83',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_A ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['41','83'])).

thf('85',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['85'])).

thf('87',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['85'])).

thf('88',plain,(
    sk_B != k1_xboole_0 ),
    inference(demod,[status(thm)],['27','28','29','30','31'])).

thf('89',plain,
    ( ( sk_B != sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    sk_B != k1_xboole_0 ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['85'])).

thf('92',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['90','91'])).

thf('93',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['86','92'])).

thf('94',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['84','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.gOdsTUI5Or
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:39:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.40/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.40/0.57  % Solved by: fo/fo7.sh
% 0.40/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.57  % done 195 iterations in 0.120s
% 0.40/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.40/0.57  % SZS output start Refutation
% 0.40/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.40/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.57  thf(sk_C_5_type, type, sk_C_5: $i > $i > $i).
% 0.40/0.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.40/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.57  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.40/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.57  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.40/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.40/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.57  thf(o_1_0_funct_1_type, type, o_1_0_funct_1: $i > $i).
% 0.40/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.57  thf(sk_C_4_type, type, sk_C_4: $i > $i > $i).
% 0.40/0.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.40/0.57  thf(t2_tarski, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.40/0.57       ( ( A ) = ( B ) ) ))).
% 0.40/0.57  thf('0', plain,
% 0.40/0.57      (![X4 : $i, X5 : $i]:
% 0.40/0.57         (((X5) = (X4))
% 0.40/0.57          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 0.40/0.57          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 0.40/0.57      inference('cnf', [status(esa)], [t2_tarski])).
% 0.40/0.57  thf(t3_xboole_0, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.40/0.57            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.40/0.57       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.40/0.57            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.40/0.57  thf('1', plain,
% 0.40/0.57      (![X6 : $i, X7 : $i]:
% 0.40/0.57         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C_2 @ X7 @ X6) @ X7))),
% 0.40/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.57  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.40/0.57  thf('2', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.40/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.40/0.57  thf(d3_tarski, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( r1_tarski @ A @ B ) <=>
% 0.40/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.40/0.57  thf('3', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.57         (~ (r2_hidden @ X0 @ X1)
% 0.40/0.57          | (r2_hidden @ X0 @ X2)
% 0.40/0.57          | ~ (r1_tarski @ X1 @ X2))),
% 0.40/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.57  thf('4', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.40/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.40/0.57  thf('5', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         ((r1_xboole_0 @ X0 @ k1_xboole_0)
% 0.40/0.57          | (r2_hidden @ (sk_C_2 @ k1_xboole_0 @ X0) @ X1))),
% 0.40/0.57      inference('sup-', [status(thm)], ['1', '4'])).
% 0.40/0.57  thf('6', plain,
% 0.40/0.57      (![X6 : $i, X7 : $i]:
% 0.40/0.57         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C_2 @ X7 @ X6) @ X7))),
% 0.40/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.57  thf('7', plain,
% 0.40/0.57      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.40/0.57         (~ (r2_hidden @ X8 @ X6)
% 0.40/0.57          | ~ (r2_hidden @ X8 @ X9)
% 0.40/0.57          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.40/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.57  thf('8', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.57         ((r1_xboole_0 @ X1 @ X0)
% 0.40/0.57          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.40/0.57          | ~ (r2_hidden @ (sk_C_2 @ X0 @ X1) @ X2))),
% 0.40/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.40/0.57  thf('9', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         ((r1_xboole_0 @ X1 @ k1_xboole_0)
% 0.40/0.57          | ~ (r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.40/0.57          | (r1_xboole_0 @ X1 @ k1_xboole_0))),
% 0.40/0.57      inference('sup-', [status(thm)], ['5', '8'])).
% 0.40/0.57  thf('10', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         (~ (r1_xboole_0 @ k1_xboole_0 @ X0) | (r1_xboole_0 @ X1 @ k1_xboole_0))),
% 0.40/0.57      inference('simplify', [status(thm)], ['9'])).
% 0.40/0.57  thf('11', plain,
% 0.40/0.57      (![X6 : $i, X7 : $i]:
% 0.40/0.57         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C_2 @ X7 @ X6) @ X6))),
% 0.40/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.57  thf('12', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.40/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.40/0.57  thf('13', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         ((r1_xboole_0 @ k1_xboole_0 @ X0)
% 0.40/0.57          | (r2_hidden @ (sk_C_2 @ X0 @ k1_xboole_0) @ X1))),
% 0.40/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.40/0.57  thf(d1_tarski, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.40/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.40/0.57  thf('14', plain,
% 0.40/0.57      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.40/0.57         (~ (r2_hidden @ X14 @ X13)
% 0.40/0.57          | ((X14) = (X11))
% 0.40/0.57          | ((X13) != (k1_tarski @ X11)))),
% 0.40/0.57      inference('cnf', [status(esa)], [d1_tarski])).
% 0.40/0.57  thf('15', plain,
% 0.40/0.57      (![X11 : $i, X14 : $i]:
% 0.40/0.57         (((X14) = (X11)) | ~ (r2_hidden @ X14 @ (k1_tarski @ X11)))),
% 0.40/0.57      inference('simplify', [status(thm)], ['14'])).
% 0.40/0.57  thf('16', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         ((r1_xboole_0 @ k1_xboole_0 @ X1)
% 0.40/0.57          | ((sk_C_2 @ X1 @ k1_xboole_0) = (X0)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['13', '15'])).
% 0.40/0.57  thf('17', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         ((r1_xboole_0 @ k1_xboole_0 @ X1)
% 0.40/0.57          | ((sk_C_2 @ X1 @ k1_xboole_0) = (X0)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['13', '15'])).
% 0.40/0.57  thf('18', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.57         (((X0) = (X1))
% 0.40/0.57          | (r1_xboole_0 @ k1_xboole_0 @ X2)
% 0.40/0.57          | (r1_xboole_0 @ k1_xboole_0 @ X2))),
% 0.40/0.57      inference('sup+', [status(thm)], ['16', '17'])).
% 0.40/0.57  thf('19', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.57         ((r1_xboole_0 @ k1_xboole_0 @ X2) | ((X0) = (X1)))),
% 0.40/0.57      inference('simplify', [status(thm)], ['18'])).
% 0.40/0.57  thf(s3_funct_1__e1_27_1__funct_1, axiom,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ?[C:$i]:
% 0.40/0.57       ( ( ![D:$i]:
% 0.40/0.57           ( ( r2_hidden @ D @ B ) =>
% 0.40/0.57             ( ( k1_funct_1 @ C @ D ) = ( o_1_0_funct_1 @ A ) ) ) ) & 
% 0.40/0.57         ( ( k1_relat_1 @ C ) = ( B ) ) & ( v1_funct_1 @ C ) & 
% 0.40/0.57         ( v1_relat_1 @ C ) ) ))).
% 0.40/0.57  thf('20', plain,
% 0.40/0.57      (![X17 : $i, X18 : $i]: ((k1_relat_1 @ (sk_C_4 @ X17 @ X18)) = (X17))),
% 0.40/0.57      inference('cnf', [status(esa)], [s3_funct_1__e1_27_1__funct_1])).
% 0.40/0.57  thf(t65_relat_1, axiom,
% 0.40/0.57    (![A:$i]:
% 0.40/0.57     ( ( v1_relat_1 @ A ) =>
% 0.40/0.57       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.40/0.57         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.40/0.57  thf('21', plain,
% 0.40/0.57      (![X16 : $i]:
% 0.40/0.57         (((k1_relat_1 @ X16) != (k1_xboole_0))
% 0.40/0.57          | ((k2_relat_1 @ X16) = (k1_xboole_0))
% 0.40/0.57          | ~ (v1_relat_1 @ X16))),
% 0.40/0.57      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.40/0.57  thf('22', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         (((X0) != (k1_xboole_0))
% 0.40/0.57          | ~ (v1_relat_1 @ (sk_C_4 @ X0 @ X1))
% 0.40/0.57          | ((k2_relat_1 @ (sk_C_4 @ X0 @ X1)) = (k1_xboole_0)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['20', '21'])).
% 0.40/0.57  thf('23', plain,
% 0.40/0.57      (![X1 : $i]:
% 0.40/0.57         (((k2_relat_1 @ (sk_C_4 @ k1_xboole_0 @ X1)) = (k1_xboole_0))
% 0.40/0.57          | ~ (v1_relat_1 @ (sk_C_4 @ k1_xboole_0 @ X1)))),
% 0.40/0.57      inference('simplify', [status(thm)], ['22'])).
% 0.40/0.57  thf('24', plain,
% 0.40/0.57      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (sk_C_4 @ X17 @ X18))),
% 0.40/0.57      inference('cnf', [status(esa)], [s3_funct_1__e1_27_1__funct_1])).
% 0.40/0.57  thf('25', plain,
% 0.40/0.57      (![X1 : $i]: ((k2_relat_1 @ (sk_C_4 @ k1_xboole_0 @ X1)) = (k1_xboole_0))),
% 0.40/0.57      inference('demod', [status(thm)], ['23', '24'])).
% 0.40/0.57  thf(t18_funct_1, conjecture,
% 0.40/0.57    (![A:$i,B:$i]:
% 0.40/0.57     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.40/0.57          ( ![C:$i]:
% 0.40/0.57            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.40/0.57              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.40/0.57                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.40/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.57    (~( ![A:$i,B:$i]:
% 0.40/0.57        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.40/0.57             ( ![C:$i]:
% 0.40/0.57               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.40/0.57                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.40/0.57                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.40/0.57    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.40/0.57  thf('26', plain,
% 0.40/0.57      (![X22 : $i]:
% 0.40/0.57         (~ (r1_tarski @ (k2_relat_1 @ X22) @ sk_A)
% 0.40/0.57          | ((sk_B) != (k1_relat_1 @ X22))
% 0.40/0.57          | ~ (v1_funct_1 @ X22)
% 0.40/0.57          | ~ (v1_relat_1 @ X22))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('27', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         (~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 0.40/0.57          | ~ (v1_relat_1 @ (sk_C_4 @ k1_xboole_0 @ X0))
% 0.40/0.57          | ~ (v1_funct_1 @ (sk_C_4 @ k1_xboole_0 @ X0))
% 0.40/0.57          | ((sk_B) != (k1_relat_1 @ (sk_C_4 @ k1_xboole_0 @ X0))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['25', '26'])).
% 0.40/0.57  thf('28', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.40/0.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.40/0.57  thf('29', plain,
% 0.40/0.57      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (sk_C_4 @ X17 @ X18))),
% 0.40/0.57      inference('cnf', [status(esa)], [s3_funct_1__e1_27_1__funct_1])).
% 0.40/0.57  thf('30', plain,
% 0.40/0.57      (![X17 : $i, X18 : $i]: (v1_funct_1 @ (sk_C_4 @ X17 @ X18))),
% 0.40/0.57      inference('cnf', [status(esa)], [s3_funct_1__e1_27_1__funct_1])).
% 0.40/0.57  thf('31', plain,
% 0.40/0.57      (![X17 : $i, X18 : $i]: ((k1_relat_1 @ (sk_C_4 @ X17 @ X18)) = (X17))),
% 0.40/0.57      inference('cnf', [status(esa)], [s3_funct_1__e1_27_1__funct_1])).
% 0.40/0.57  thf('32', plain, (((sk_B) != (k1_xboole_0))),
% 0.40/0.57      inference('demod', [status(thm)], ['27', '28', '29', '30', '31'])).
% 0.40/0.57  thf('33', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         (((sk_B) != (X0)) | (r1_xboole_0 @ k1_xboole_0 @ X1))),
% 0.40/0.57      inference('sup-', [status(thm)], ['19', '32'])).
% 0.40/0.57  thf('34', plain, (![X1 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X1)),
% 0.40/0.57      inference('simplify', [status(thm)], ['33'])).
% 0.40/0.57  thf('35', plain, (![X1 : $i]: (r1_xboole_0 @ X1 @ k1_xboole_0)),
% 0.40/0.57      inference('demod', [status(thm)], ['10', '34'])).
% 0.40/0.57  thf('36', plain,
% 0.40/0.57      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.40/0.57         (((X12) != (X11))
% 0.40/0.57          | (r2_hidden @ X12 @ X13)
% 0.40/0.57          | ((X13) != (k1_tarski @ X11)))),
% 0.40/0.57      inference('cnf', [status(esa)], [d1_tarski])).
% 0.40/0.57  thf('37', plain, (![X11 : $i]: (r2_hidden @ X11 @ (k1_tarski @ X11))),
% 0.40/0.57      inference('simplify', [status(thm)], ['36'])).
% 0.40/0.57  thf('38', plain,
% 0.40/0.57      (![X6 : $i, X8 : $i, X9 : $i]:
% 0.40/0.57         (~ (r2_hidden @ X8 @ X6)
% 0.40/0.57          | ~ (r2_hidden @ X8 @ X9)
% 0.40/0.57          | ~ (r1_xboole_0 @ X6 @ X9))),
% 0.40/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.57  thf('39', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.40/0.57      inference('sup-', [status(thm)], ['37', '38'])).
% 0.40/0.57  thf('40', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.40/0.57      inference('sup-', [status(thm)], ['35', '39'])).
% 0.40/0.57  thf('41', plain,
% 0.40/0.57      (![X0 : $i]:
% 0.40/0.57         ((r2_hidden @ (sk_C_1 @ k1_xboole_0 @ X0) @ X0)
% 0.40/0.57          | ((X0) = (k1_xboole_0)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['0', '40'])).
% 0.40/0.57  thf('42', plain,
% 0.40/0.57      (![X6 : $i, X7 : $i]:
% 0.40/0.57         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C_2 @ X7 @ X6) @ X6))),
% 0.40/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.57  thf(t15_funct_1, axiom,
% 0.40/0.57    (![A:$i]:
% 0.40/0.57     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 0.40/0.57       ( ![B:$i]:
% 0.40/0.57         ( ?[C:$i]:
% 0.40/0.57           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 0.40/0.57             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.40/0.57             ( v1_relat_1 @ C ) ) ) ) ))).
% 0.40/0.57  thf('43', plain,
% 0.40/0.57      (![X20 : $i, X21 : $i]:
% 0.40/0.57         (((k1_relat_1 @ (sk_C_5 @ X20 @ X21)) = (X21))
% 0.40/0.57          | ((X21) = (k1_xboole_0)))),
% 0.40/0.57      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.40/0.57  thf('44', plain,
% 0.40/0.57      (![X20 : $i, X21 : $i]:
% 0.40/0.57         ((v1_relat_1 @ (sk_C_5 @ X20 @ X21)) | ((X21) = (k1_xboole_0)))),
% 0.40/0.57      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.40/0.57  thf('45', plain,
% 0.40/0.57      (![X20 : $i, X21 : $i]:
% 0.40/0.57         ((v1_funct_1 @ (sk_C_5 @ X20 @ X21)) | ((X21) = (k1_xboole_0)))),
% 0.40/0.57      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.40/0.57  thf('46', plain,
% 0.40/0.57      (![X1 : $i, X3 : $i]:
% 0.40/0.57         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.40/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.57  thf('47', plain,
% 0.40/0.57      (![X1 : $i, X3 : $i]:
% 0.40/0.57         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.40/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.57  thf('48', plain,
% 0.40/0.57      (![X11 : $i, X14 : $i]:
% 0.40/0.57         (((X14) = (X11)) | ~ (r2_hidden @ X14 @ (k1_tarski @ X11)))),
% 0.40/0.57      inference('simplify', [status(thm)], ['14'])).
% 0.40/0.57  thf('49', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         ((r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.40/0.57          | ((sk_C @ X1 @ (k1_tarski @ X0)) = (X0)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['47', '48'])).
% 0.40/0.57  thf('50', plain,
% 0.40/0.57      (![X1 : $i, X3 : $i]:
% 0.40/0.57         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.40/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.57  thf('51', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         (~ (r2_hidden @ X0 @ X1)
% 0.40/0.57          | (r1_tarski @ (k1_tarski @ X0) @ X1)
% 0.40/0.57          | (r1_tarski @ (k1_tarski @ X0) @ X1))),
% 0.40/0.57      inference('sup-', [status(thm)], ['49', '50'])).
% 0.40/0.57  thf('52', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         ((r1_tarski @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.40/0.57      inference('simplify', [status(thm)], ['51'])).
% 0.40/0.57  thf('53', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         ((r1_tarski @ X0 @ X1)
% 0.40/0.57          | (r1_tarski @ (k1_tarski @ (sk_C @ X1 @ X0)) @ X0))),
% 0.40/0.57      inference('sup-', [status(thm)], ['46', '52'])).
% 0.40/0.57  thf('54', plain,
% 0.40/0.57      (![X20 : $i, X21 : $i]:
% 0.40/0.57         (((k2_relat_1 @ (sk_C_5 @ X20 @ X21)) = (k1_tarski @ X20))
% 0.40/0.57          | ((X21) = (k1_xboole_0)))),
% 0.40/0.57      inference('cnf', [status(esa)], [t15_funct_1])).
% 0.40/0.57  thf('55', plain,
% 0.40/0.57      (![X22 : $i]:
% 0.40/0.57         (~ (r1_tarski @ (k2_relat_1 @ X22) @ sk_A)
% 0.40/0.57          | ((sk_B) != (k1_relat_1 @ X22))
% 0.40/0.57          | ~ (v1_funct_1 @ X22)
% 0.40/0.57          | ~ (v1_relat_1 @ X22))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('56', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         (~ (r1_tarski @ (k1_tarski @ X0) @ sk_A)
% 0.40/0.57          | ((X1) = (k1_xboole_0))
% 0.40/0.57          | ~ (v1_relat_1 @ (sk_C_5 @ X0 @ X1))
% 0.40/0.57          | ~ (v1_funct_1 @ (sk_C_5 @ X0 @ X1))
% 0.40/0.57          | ((sk_B) != (k1_relat_1 @ (sk_C_5 @ X0 @ X1))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['54', '55'])).
% 0.40/0.57  thf('57', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         ((r1_tarski @ sk_A @ X0)
% 0.40/0.57          | ((sk_B) != (k1_relat_1 @ (sk_C_5 @ (sk_C @ X0 @ sk_A) @ X1)))
% 0.40/0.57          | ~ (v1_funct_1 @ (sk_C_5 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.40/0.57          | ~ (v1_relat_1 @ (sk_C_5 @ (sk_C @ X0 @ sk_A) @ X1))
% 0.40/0.57          | ((X1) = (k1_xboole_0)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['53', '56'])).
% 0.40/0.57  thf('58', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         (((X0) = (k1_xboole_0))
% 0.40/0.57          | ((X0) = (k1_xboole_0))
% 0.40/0.57          | ~ (v1_relat_1 @ (sk_C_5 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.40/0.57          | ((sk_B) != (k1_relat_1 @ (sk_C_5 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.40/0.57          | (r1_tarski @ sk_A @ X1))),
% 0.40/0.57      inference('sup-', [status(thm)], ['45', '57'])).
% 0.40/0.57  thf('59', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         ((r1_tarski @ sk_A @ X1)
% 0.40/0.57          | ((sk_B) != (k1_relat_1 @ (sk_C_5 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.40/0.57          | ~ (v1_relat_1 @ (sk_C_5 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.40/0.57          | ((X0) = (k1_xboole_0)))),
% 0.40/0.57      inference('simplify', [status(thm)], ['58'])).
% 0.40/0.57  thf('60', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         (((X0) = (k1_xboole_0))
% 0.40/0.57          | ((X0) = (k1_xboole_0))
% 0.40/0.57          | ((sk_B) != (k1_relat_1 @ (sk_C_5 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.40/0.57          | (r1_tarski @ sk_A @ X1))),
% 0.40/0.57      inference('sup-', [status(thm)], ['44', '59'])).
% 0.40/0.57  thf('61', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         ((r1_tarski @ sk_A @ X1)
% 0.40/0.57          | ((sk_B) != (k1_relat_1 @ (sk_C_5 @ (sk_C @ X1 @ sk_A) @ X0)))
% 0.40/0.57          | ((X0) = (k1_xboole_0)))),
% 0.40/0.57      inference('simplify', [status(thm)], ['60'])).
% 0.40/0.57  thf('62', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         (((sk_B) != (X0))
% 0.40/0.57          | ((X0) = (k1_xboole_0))
% 0.40/0.57          | ((X0) = (k1_xboole_0))
% 0.40/0.57          | (r1_tarski @ sk_A @ X1))),
% 0.40/0.57      inference('sup-', [status(thm)], ['43', '61'])).
% 0.40/0.57  thf('63', plain,
% 0.40/0.57      (![X1 : $i]: ((r1_tarski @ sk_A @ X1) | ((sk_B) = (k1_xboole_0)))),
% 0.40/0.57      inference('simplify', [status(thm)], ['62'])).
% 0.40/0.57  thf('64', plain, (((sk_B) != (k1_xboole_0))),
% 0.40/0.57      inference('demod', [status(thm)], ['27', '28', '29', '30', '31'])).
% 0.40/0.57  thf('65', plain, (![X1 : $i]: (r1_tarski @ sk_A @ X1)),
% 0.40/0.57      inference('simplify_reflect-', [status(thm)], ['63', '64'])).
% 0.40/0.57  thf('66', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.57         (~ (r2_hidden @ X0 @ X1)
% 0.40/0.57          | (r2_hidden @ X0 @ X2)
% 0.40/0.57          | ~ (r1_tarski @ X1 @ X2))),
% 0.40/0.57      inference('cnf', [status(esa)], [d3_tarski])).
% 0.40/0.57  thf('67', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]: ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_A))),
% 0.40/0.57      inference('sup-', [status(thm)], ['65', '66'])).
% 0.40/0.57  thf('68', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         ((r1_xboole_0 @ sk_A @ X0) | (r2_hidden @ (sk_C_2 @ X0 @ sk_A) @ X1))),
% 0.40/0.57      inference('sup-', [status(thm)], ['42', '67'])).
% 0.40/0.57  thf('69', plain,
% 0.40/0.57      (![X11 : $i, X14 : $i]:
% 0.40/0.57         (((X14) = (X11)) | ~ (r2_hidden @ X14 @ (k1_tarski @ X11)))),
% 0.40/0.57      inference('simplify', [status(thm)], ['14'])).
% 0.40/0.57  thf('70', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         ((r1_xboole_0 @ sk_A @ X1) | ((sk_C_2 @ X1 @ sk_A) = (X0)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['68', '69'])).
% 0.40/0.57  thf('71', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         ((r1_xboole_0 @ sk_A @ X1) | ((sk_C_2 @ X1 @ sk_A) = (X0)))),
% 0.40/0.57      inference('sup-', [status(thm)], ['68', '69'])).
% 0.40/0.57  thf('72', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.57         (((X0) = (X1)) | (r1_xboole_0 @ sk_A @ X2) | (r1_xboole_0 @ sk_A @ X2))),
% 0.40/0.57      inference('sup+', [status(thm)], ['70', '71'])).
% 0.40/0.57  thf('73', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.57         ((r1_xboole_0 @ sk_A @ X2) | ((X0) = (X1)))),
% 0.40/0.57      inference('simplify', [status(thm)], ['72'])).
% 0.40/0.57  thf('74', plain,
% 0.40/0.57      (![X6 : $i, X7 : $i]:
% 0.40/0.57         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C_2 @ X7 @ X6) @ X6))),
% 0.40/0.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.40/0.57  thf('75', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.57         ((r1_xboole_0 @ X1 @ X0)
% 0.40/0.57          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.40/0.57          | ~ (r2_hidden @ (sk_C_2 @ X0 @ X1) @ X2))),
% 0.40/0.57      inference('sup-', [status(thm)], ['6', '7'])).
% 0.40/0.57  thf('76', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         ((r1_xboole_0 @ X0 @ X1)
% 0.40/0.57          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.40/0.57          | (r1_xboole_0 @ X0 @ X1))),
% 0.40/0.57      inference('sup-', [status(thm)], ['74', '75'])).
% 0.40/0.57  thf('77', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.40/0.57      inference('simplify', [status(thm)], ['76'])).
% 0.40/0.57  thf('78', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.40/0.57         (((X1) = (X2)) | (r1_xboole_0 @ X0 @ sk_A))),
% 0.40/0.57      inference('sup-', [status(thm)], ['73', '77'])).
% 0.40/0.57  thf('79', plain, (((sk_B) != (k1_xboole_0))),
% 0.40/0.57      inference('demod', [status(thm)], ['27', '28', '29', '30', '31'])).
% 0.40/0.57  thf('80', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]: (((sk_B) != (X0)) | (r1_xboole_0 @ X1 @ sk_A))),
% 0.40/0.57      inference('sup-', [status(thm)], ['78', '79'])).
% 0.40/0.57  thf('81', plain, (![X1 : $i]: (r1_xboole_0 @ X1 @ sk_A)),
% 0.40/0.57      inference('simplify', [status(thm)], ['80'])).
% 0.40/0.57  thf('82', plain,
% 0.40/0.57      (![X0 : $i, X1 : $i]:
% 0.40/0.57         (~ (r1_xboole_0 @ (k1_tarski @ X0) @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.40/0.57      inference('sup-', [status(thm)], ['37', '38'])).
% 0.40/0.57  thf('83', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_A)),
% 0.40/0.57      inference('sup-', [status(thm)], ['81', '82'])).
% 0.40/0.57  thf('84', plain, (((sk_A) = (k1_xboole_0))),
% 0.40/0.57      inference('sup-', [status(thm)], ['41', '83'])).
% 0.40/0.57  thf('85', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.40/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.57  thf('86', plain,
% 0.40/0.57      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.40/0.57      inference('split', [status(esa)], ['85'])).
% 0.40/0.57  thf('87', plain,
% 0.40/0.57      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.40/0.57      inference('split', [status(esa)], ['85'])).
% 0.40/0.57  thf('88', plain, (((sk_B) != (k1_xboole_0))),
% 0.40/0.57      inference('demod', [status(thm)], ['27', '28', '29', '30', '31'])).
% 0.40/0.57  thf('89', plain, ((((sk_B) != (sk_B))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.40/0.57      inference('sup-', [status(thm)], ['87', '88'])).
% 0.40/0.57  thf('90', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.40/0.57      inference('simplify', [status(thm)], ['89'])).
% 0.40/0.57  thf('91', plain, (~ (((sk_A) = (k1_xboole_0))) | (((sk_B) = (k1_xboole_0)))),
% 0.40/0.57      inference('split', [status(esa)], ['85'])).
% 0.40/0.57  thf('92', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.40/0.57      inference('sat_resolution*', [status(thm)], ['90', '91'])).
% 0.40/0.57  thf('93', plain, (((sk_A) != (k1_xboole_0))),
% 0.40/0.57      inference('simpl_trail', [status(thm)], ['86', '92'])).
% 0.40/0.57  thf('94', plain, ($false),
% 0.40/0.57      inference('simplify_reflect-', [status(thm)], ['84', '93'])).
% 0.40/0.57  
% 0.40/0.57  % SZS output end Refutation
% 0.40/0.57  
% 0.40/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
