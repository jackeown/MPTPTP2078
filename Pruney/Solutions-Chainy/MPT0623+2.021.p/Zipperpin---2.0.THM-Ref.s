%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Qtqy6cphM2

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:38 EST 2020

% Result     : Theorem 0.68s
% Output     : Refutation 0.68s
% Verified   : 
% Statistics : Number of formulae       :  148 ( 481 expanded)
%              Number of leaves         :   19 ( 158 expanded)
%              Depth                    :   27
%              Number of atoms          : 1518 (5739 expanded)
%              Number of equality atoms :   99 ( 480 expanded)
%              Maximal formula depth    :   15 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(s3_funct_1__e2_24__funct_1,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ! [D: $i] :
          ( ( r2_hidden @ D @ A )
         => ( ( k1_funct_1 @ C @ D )
            = B ) )
      & ( ( k1_relat_1 @ C )
        = A )
      & ( v1_funct_1 @ C )
      & ( v1_relat_1 @ C ) ) )).

thf('1',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('2',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ( X11
       != ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ ( sk_D_1 @ X12 @ X9 ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('4',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ ( sk_D_1 @ X12 @ X9 ) @ ( k1_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) ) @ ( sk_C_2 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['1','5'])).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('8',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) ) @ ( sk_C_2 @ X1 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('10',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X15 @ X16 ) @ X17 )
        = X15 )
      | ~ ( r2_hidden @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X3 @ X0 ) @ ( sk_D_1 @ ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) ) @ ( sk_C_2 @ X1 @ X0 ) ) )
        = X3 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ( X11
       != ( k2_relat_1 @ X9 ) )
      | ( X12
        = ( k1_funct_1 @ X9 @ ( sk_D_1 @ X12 @ X9 ) ) )
      | ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('14',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( X12
        = ( k1_funct_1 @ X9 @ ( sk_D_1 @ X12 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X1 ) ) )
        = X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X1 ) ) @ X2 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['11','15'])).

thf('17',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('18',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X1 ) ) )
        = X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X1 ) ) @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X1 ) ) @ X2 )
      | ( ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X1 ) ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) ) @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ ( sk_C @ X1 @ X0 ) @ X2 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','23'])).

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

thf('25',plain,(
    ! [X18: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ sk_A )
      | ( sk_B
       != ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ ( sk_C @ X1 @ sk_A ) @ X0 ) )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C @ X1 @ sk_A ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('28',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('29',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X1 )
      | ( sk_B != X0 ) ) ),
    inference(demod,[status(thm)],['26','27','28','29'])).

thf('31',plain,(
    ! [X1: $i] :
      ( r1_tarski @ sk_A @ X1 ) ),
    inference(simplify,[status(thm)],['30'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('32',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X3 @ X0 ) @ ( sk_D_1 @ ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) ) @ ( sk_C_2 @ X1 @ X0 ) ) )
        = X3 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','4'])).

thf('40',plain,(
    ! [X9: $i,X11: $i,X13: $i,X14: $i] :
      ( ( X11
       != ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ X13 @ X11 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X9 ) )
      | ( X13
       != ( k1_funct_1 @ X9 @ X14 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('41',plain,(
    ! [X9: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X9 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X9 @ X14 ) @ ( k2_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) @ ( k2_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X1 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X1 ) ) @ X2 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['38','43'])).

thf('45',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('46',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X1 ) ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X1 ) ) @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X1 ) ) @ X2 )
      | ( r2_hidden @ X0 @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X1 ) ) ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X18: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ sk_A )
      | ( sk_B
       != ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('52',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('53',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
      | ( sk_B != X0 ) ) ),
    inference(demod,[status(thm)],['50','51','52','53'])).

thf('55',plain,(
    ! [X1: $i] :
      ( r2_hidden @ X1 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ ( sk_D_1 @ X12 @ X9 ) @ ( k1_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ X0 @ ( sk_C_2 @ X0 @ sk_B ) ) @ ( k1_relat_1 @ ( sk_C_2 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('59',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('60',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( r2_hidden @ ( sk_D_1 @ X0 @ ( sk_C_2 @ X0 @ sk_B ) ) @ sk_B ) ),
    inference(demod,[status(thm)],['57','58','59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) ) @ ( sk_C_2 @ X1 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('63',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('64',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('65',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B @ X0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('67',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ X1 @ X0 )
        | ~ ( r2_hidden @ X1 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ sk_B ) ) @ X1 )
        | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ sk_B ) ) ) @ ( sk_C_2 @ X0 @ sk_B ) ) @ X2 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','67'])).

thf('69',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X15 @ X16 ) @ X17 )
        = X15 )
      | ~ ( r2_hidden @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('70',plain,
    ( ! [X0: $i,X1: $i,X2: $i,X3: $i] :
        ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ sk_B ) ) @ X2 )
        | ( ( k1_funct_1 @ ( sk_C_2 @ X3 @ X0 ) @ ( sk_D_1 @ ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ sk_B ) ) ) @ ( sk_C_2 @ X1 @ sk_B ) ) )
          = X3 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('72',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( sk_C @ X1 @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ sk_B ) ) )
          = X0 )
        | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ sk_B ) ) @ X1 )
        | ~ ( v1_relat_1 @ ( sk_C_2 @ X0 @ sk_B ) )
        | ~ ( v1_funct_1 @ ( sk_C_2 @ X0 @ sk_B ) )
        | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ sk_B ) ) @ X1 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('74',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('75',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( ( sk_C @ X1 @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ sk_B ) ) )
          = X0 )
        | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ sk_B ) ) @ X1 )
        | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ sk_B ) ) @ X1 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ sk_B ) ) @ X1 )
        | ( ( sk_C @ X1 @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ sk_B ) ) )
          = X0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('78',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r2_hidden @ X0 @ X1 )
        | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ sk_B ) ) @ X1 )
        | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ sk_B ) ) @ X1 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ sk_B ) ) @ X1 )
        | ~ ( r2_hidden @ X0 @ X1 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('81',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('82',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) ) @ ( sk_C_2 @ X1 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['6','7','8'])).

thf('83',plain,(
    ! [X7: $i] :
      ( r1_tarski @ k1_xboole_0 @ X7 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) ) @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) ) ) @ ( sk_C_2 @ X0 @ k1_xboole_0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['82','85'])).

thf('87',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X15 @ X16 ) @ X17 )
        = X15 )
      | ~ ( r2_hidden @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ k1_xboole_0 ) ) @ X2 )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X3 @ X0 ) @ ( sk_D_1 @ ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ k1_xboole_0 ) ) ) @ ( sk_C_2 @ X1 @ k1_xboole_0 ) ) )
        = X3 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X1 @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) ) )
        = X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) ) @ X1 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('92',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('93',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C @ X1 @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) ) )
        = X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) ) @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['90','91','92'])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) ) @ X1 )
      | ( ( sk_C @ X1 @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) ) )
        = X0 ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) ) @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ k1_xboole_0 ) ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ ( sk_C @ X1 @ X0 ) @ k1_xboole_0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','97'])).

thf('99',plain,(
    ! [X18: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ sk_A )
      | ( sk_B
       != ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_C @ X0 @ sk_A ) @ k1_xboole_0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ ( sk_C @ X0 @ sk_A ) @ k1_xboole_0 ) )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C @ X0 @ sk_A ) @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('102',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('103',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( sk_B != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['100','101','102','103'])).

thf('105',plain,
    ( ! [X0: $i] :
        ( ( sk_B != sk_B )
        | ( r1_tarski @ sk_A @ X0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','104'])).

thf('106',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_A @ X0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B @ X0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['63','64'])).

thf('108',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('109',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_B )
        | ( X0 = sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( sk_A = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf('111',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ sk_A ) ) @ X1 )
        | ~ ( r2_hidden @ X0 @ X1 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','110'])).

thf('112',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ ( sk_D_1 @ X0 @ ( sk_C_2 @ X0 @ sk_B ) ) @ sk_A ) ) @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','111'])).

thf('113',plain,
    ( ( sk_A = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf('114',plain,
    ( ( sk_A = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf('115',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ ( sk_D_1 @ X0 @ ( sk_C_2 @ X0 @ sk_A ) ) @ sk_A ) ) @ sk_A )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['112','113','114'])).

thf('116',plain,(
    ! [X18: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ sk_A )
      | ( sk_B
       != ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_D_1 @ X0 @ ( sk_C_2 @ X0 @ sk_A ) ) @ sk_A ) )
        | ~ ( v1_funct_1 @ ( sk_C_2 @ ( sk_D_1 @ X0 @ ( sk_C_2 @ X0 @ sk_A ) ) @ sk_A ) )
        | ( sk_B
         != ( k1_relat_1 @ ( sk_C_2 @ ( sk_D_1 @ X0 @ ( sk_C_2 @ X0 @ sk_A ) ) @ sk_A ) ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('119',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('120',plain,
    ( ( sk_A = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf('121',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('122',plain,
    ( ( sk_A != sk_A )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['117','118','119','120','121'])).

thf('123',plain,(
    sk_B != k1_xboole_0 ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['36'])).

thf('125',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['123','124'])).

thf('126',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['37','125'])).

thf('127',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['35','126'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Qtqy6cphM2
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:38:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.68/0.88  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.68/0.88  % Solved by: fo/fo7.sh
% 0.68/0.88  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.68/0.88  % done 361 iterations in 0.424s
% 0.68/0.88  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.68/0.88  % SZS output start Refutation
% 0.68/0.88  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.68/0.88  thf(sk_A_type, type, sk_A: $i).
% 0.68/0.88  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.68/0.88  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.68/0.88  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 0.68/0.88  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.68/0.88  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.68/0.88  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.68/0.88  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.68/0.88  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.68/0.88  thf(sk_B_type, type, sk_B: $i).
% 0.68/0.88  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.68/0.88  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.68/0.88  thf(d3_tarski, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( r1_tarski @ A @ B ) <=>
% 0.68/0.88       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.68/0.88  thf('0', plain,
% 0.68/0.88      (![X1 : $i, X3 : $i]:
% 0.68/0.88         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.68/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.68/0.88  thf(s3_funct_1__e2_24__funct_1, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ?[C:$i]:
% 0.68/0.88       ( ( ![D:$i]:
% 0.68/0.88           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 0.68/0.88         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.68/0.88         ( v1_relat_1 @ C ) ) ))).
% 0.68/0.88  thf('1', plain,
% 0.68/0.88      (![X15 : $i, X16 : $i]: ((k1_relat_1 @ (sk_C_2 @ X15 @ X16)) = (X16))),
% 0.68/0.88      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.68/0.88  thf('2', plain,
% 0.68/0.88      (![X1 : $i, X3 : $i]:
% 0.68/0.88         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.68/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.68/0.88  thf(d5_funct_1, axiom,
% 0.68/0.88    (![A:$i]:
% 0.68/0.88     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.68/0.88       ( ![B:$i]:
% 0.68/0.88         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.68/0.88           ( ![C:$i]:
% 0.68/0.88             ( ( r2_hidden @ C @ B ) <=>
% 0.68/0.88               ( ?[D:$i]:
% 0.68/0.88                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.68/0.88                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.68/0.88  thf('3', plain,
% 0.68/0.88      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.68/0.88         (((X11) != (k2_relat_1 @ X9))
% 0.68/0.88          | (r2_hidden @ (sk_D_1 @ X12 @ X9) @ (k1_relat_1 @ X9))
% 0.68/0.88          | ~ (r2_hidden @ X12 @ X11)
% 0.68/0.88          | ~ (v1_funct_1 @ X9)
% 0.68/0.88          | ~ (v1_relat_1 @ X9))),
% 0.68/0.88      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.68/0.88  thf('4', plain,
% 0.68/0.88      (![X9 : $i, X12 : $i]:
% 0.68/0.88         (~ (v1_relat_1 @ X9)
% 0.68/0.88          | ~ (v1_funct_1 @ X9)
% 0.68/0.88          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 0.68/0.88          | (r2_hidden @ (sk_D_1 @ X12 @ X9) @ (k1_relat_1 @ X9)))),
% 0.68/0.88      inference('simplify', [status(thm)], ['3'])).
% 0.68/0.88  thf('5', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.68/0.88          | (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 0.68/0.88             (k1_relat_1 @ X0))
% 0.68/0.88          | ~ (v1_funct_1 @ X0)
% 0.68/0.88          | ~ (v1_relat_1 @ X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['2', '4'])).
% 0.68/0.88  thf('6', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((r2_hidden @ 
% 0.68/0.88           (sk_D_1 @ (sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) @ 
% 0.68/0.88            (sk_C_2 @ X1 @ X0)) @ 
% 0.68/0.88           X0)
% 0.68/0.88          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0))
% 0.68/0.88          | ~ (v1_funct_1 @ (sk_C_2 @ X1 @ X0))
% 0.68/0.88          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2))),
% 0.68/0.88      inference('sup+', [status(thm)], ['1', '5'])).
% 0.68/0.88  thf('7', plain, (![X15 : $i, X16 : $i]: (v1_relat_1 @ (sk_C_2 @ X15 @ X16))),
% 0.68/0.88      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.68/0.88  thf('8', plain, (![X15 : $i, X16 : $i]: (v1_funct_1 @ (sk_C_2 @ X15 @ X16))),
% 0.68/0.88      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.68/0.88  thf('9', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((r2_hidden @ 
% 0.68/0.88           (sk_D_1 @ (sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) @ 
% 0.68/0.88            (sk_C_2 @ X1 @ X0)) @ 
% 0.68/0.88           X0)
% 0.68/0.88          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2))),
% 0.68/0.88      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.68/0.88  thf('10', plain,
% 0.68/0.88      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.68/0.88         (((k1_funct_1 @ (sk_C_2 @ X15 @ X16) @ X17) = (X15))
% 0.68/0.88          | ~ (r2_hidden @ X17 @ X16))),
% 0.68/0.88      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.68/0.88  thf('11', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.88         ((r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2)
% 0.68/0.88          | ((k1_funct_1 @ (sk_C_2 @ X3 @ X0) @ 
% 0.68/0.88              (sk_D_1 @ (sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) @ 
% 0.68/0.88               (sk_C_2 @ X1 @ X0)))
% 0.68/0.88              = (X3)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['9', '10'])).
% 0.68/0.88  thf('12', plain,
% 0.68/0.88      (![X1 : $i, X3 : $i]:
% 0.68/0.88         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.68/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.68/0.88  thf('13', plain,
% 0.68/0.88      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.68/0.88         (((X11) != (k2_relat_1 @ X9))
% 0.68/0.88          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9)))
% 0.68/0.88          | ~ (r2_hidden @ X12 @ X11)
% 0.68/0.88          | ~ (v1_funct_1 @ X9)
% 0.68/0.88          | ~ (v1_relat_1 @ X9))),
% 0.68/0.88      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.68/0.88  thf('14', plain,
% 0.68/0.88      (![X9 : $i, X12 : $i]:
% 0.68/0.88         (~ (v1_relat_1 @ X9)
% 0.68/0.88          | ~ (v1_funct_1 @ X9)
% 0.68/0.88          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 0.68/0.88          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9))))),
% 0.68/0.88      inference('simplify', [status(thm)], ['13'])).
% 0.68/0.88  thf('15', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.68/0.88          | ((sk_C @ X1 @ (k2_relat_1 @ X0))
% 0.68/0.88              = (k1_funct_1 @ X0 @ 
% 0.68/0.88                 (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)))
% 0.68/0.88          | ~ (v1_funct_1 @ X0)
% 0.68/0.88          | ~ (v1_relat_1 @ X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['12', '14'])).
% 0.68/0.88  thf('16', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X0 @ X1))) = (X0))
% 0.68/0.88          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X1)) @ X2)
% 0.68/0.88          | ~ (v1_relat_1 @ (sk_C_2 @ X0 @ X1))
% 0.68/0.88          | ~ (v1_funct_1 @ (sk_C_2 @ X0 @ X1))
% 0.68/0.88          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X1)) @ X2))),
% 0.68/0.88      inference('sup+', [status(thm)], ['11', '15'])).
% 0.68/0.88  thf('17', plain,
% 0.68/0.88      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (sk_C_2 @ X15 @ X16))),
% 0.68/0.88      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.68/0.88  thf('18', plain,
% 0.68/0.88      (![X15 : $i, X16 : $i]: (v1_funct_1 @ (sk_C_2 @ X15 @ X16))),
% 0.68/0.88      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.68/0.88  thf('19', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X0 @ X1))) = (X0))
% 0.68/0.88          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X1)) @ X2)
% 0.68/0.88          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X1)) @ X2))),
% 0.68/0.88      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.68/0.88  thf('20', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X1)) @ X2)
% 0.68/0.88          | ((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X0 @ X1))) = (X0)))),
% 0.68/0.88      inference('simplify', [status(thm)], ['19'])).
% 0.68/0.88  thf('21', plain,
% 0.68/0.88      (![X1 : $i, X3 : $i]:
% 0.68/0.88         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.68/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.68/0.88  thf('22', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (~ (r2_hidden @ X0 @ X1)
% 0.68/0.88          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X2)) @ X1)
% 0.68/0.88          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X2)) @ X1))),
% 0.68/0.88      inference('sup-', [status(thm)], ['20', '21'])).
% 0.68/0.88  thf('23', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X2)) @ X1)
% 0.68/0.88          | ~ (r2_hidden @ X0 @ X1))),
% 0.68/0.88      inference('simplify', [status(thm)], ['22'])).
% 0.68/0.88  thf('24', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((r1_tarski @ X0 @ X1)
% 0.68/0.88          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ (sk_C @ X1 @ X0) @ X2)) @ X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['0', '23'])).
% 0.68/0.88  thf(t18_funct_1, conjecture,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.68/0.88          ( ![C:$i]:
% 0.68/0.88            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.68/0.88              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.68/0.88                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 0.68/0.88  thf(zf_stmt_0, negated_conjecture,
% 0.68/0.88    (~( ![A:$i,B:$i]:
% 0.68/0.88        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 0.68/0.88             ( ![C:$i]:
% 0.68/0.88               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.68/0.88                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 0.68/0.88                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 0.68/0.88    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 0.68/0.88  thf('25', plain,
% 0.68/0.88      (![X18 : $i]:
% 0.68/0.88         (~ (r1_tarski @ (k2_relat_1 @ X18) @ sk_A)
% 0.68/0.88          | ((sk_B) != (k1_relat_1 @ X18))
% 0.68/0.88          | ~ (v1_funct_1 @ X18)
% 0.68/0.88          | ~ (v1_relat_1 @ X18))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('26', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((r1_tarski @ sk_A @ X1)
% 0.68/0.88          | ~ (v1_relat_1 @ (sk_C_2 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.68/0.88          | ~ (v1_funct_1 @ (sk_C_2 @ (sk_C @ X1 @ sk_A) @ X0))
% 0.68/0.88          | ((sk_B) != (k1_relat_1 @ (sk_C_2 @ (sk_C @ X1 @ sk_A) @ X0))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['24', '25'])).
% 0.68/0.88  thf('27', plain,
% 0.68/0.88      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (sk_C_2 @ X15 @ X16))),
% 0.68/0.88      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.68/0.88  thf('28', plain,
% 0.68/0.88      (![X15 : $i, X16 : $i]: (v1_funct_1 @ (sk_C_2 @ X15 @ X16))),
% 0.68/0.88      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.68/0.88  thf('29', plain,
% 0.68/0.88      (![X15 : $i, X16 : $i]: ((k1_relat_1 @ (sk_C_2 @ X15 @ X16)) = (X16))),
% 0.68/0.88      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.68/0.88  thf('30', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]: ((r1_tarski @ sk_A @ X1) | ((sk_B) != (X0)))),
% 0.68/0.88      inference('demod', [status(thm)], ['26', '27', '28', '29'])).
% 0.68/0.88  thf('31', plain, (![X1 : $i]: (r1_tarski @ sk_A @ X1)),
% 0.68/0.88      inference('simplify', [status(thm)], ['30'])).
% 0.68/0.88  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.68/0.88  thf('32', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.68/0.88      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.68/0.88  thf(d10_xboole_0, axiom,
% 0.68/0.88    (![A:$i,B:$i]:
% 0.68/0.88     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.68/0.88  thf('33', plain,
% 0.68/0.88      (![X4 : $i, X6 : $i]:
% 0.68/0.88         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.68/0.88      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.68/0.88  thf('34', plain,
% 0.68/0.88      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['32', '33'])).
% 0.68/0.88  thf('35', plain, (((sk_A) = (k1_xboole_0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['31', '34'])).
% 0.68/0.88  thf('36', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('37', plain,
% 0.68/0.88      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 0.68/0.88      inference('split', [status(esa)], ['36'])).
% 0.68/0.88  thf('38', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.88         ((r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2)
% 0.68/0.88          | ((k1_funct_1 @ (sk_C_2 @ X3 @ X0) @ 
% 0.68/0.88              (sk_D_1 @ (sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) @ 
% 0.68/0.88               (sk_C_2 @ X1 @ X0)))
% 0.68/0.88              = (X3)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['9', '10'])).
% 0.68/0.88  thf('39', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.68/0.88          | (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 0.68/0.88             (k1_relat_1 @ X0))
% 0.68/0.88          | ~ (v1_funct_1 @ X0)
% 0.68/0.88          | ~ (v1_relat_1 @ X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['2', '4'])).
% 0.68/0.88  thf('40', plain,
% 0.68/0.88      (![X9 : $i, X11 : $i, X13 : $i, X14 : $i]:
% 0.68/0.88         (((X11) != (k2_relat_1 @ X9))
% 0.68/0.88          | (r2_hidden @ X13 @ X11)
% 0.68/0.88          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X9))
% 0.68/0.88          | ((X13) != (k1_funct_1 @ X9 @ X14))
% 0.68/0.88          | ~ (v1_funct_1 @ X9)
% 0.68/0.88          | ~ (v1_relat_1 @ X9))),
% 0.68/0.88      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.68/0.88  thf('41', plain,
% 0.68/0.88      (![X9 : $i, X14 : $i]:
% 0.68/0.88         (~ (v1_relat_1 @ X9)
% 0.68/0.88          | ~ (v1_funct_1 @ X9)
% 0.68/0.88          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X9))
% 0.68/0.88          | (r2_hidden @ (k1_funct_1 @ X9 @ X14) @ (k2_relat_1 @ X9)))),
% 0.68/0.88      inference('simplify', [status(thm)], ['40'])).
% 0.68/0.88  thf('42', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         (~ (v1_relat_1 @ X0)
% 0.68/0.88          | ~ (v1_funct_1 @ X0)
% 0.68/0.88          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.68/0.88          | (r2_hidden @ 
% 0.68/0.88             (k1_funct_1 @ X0 @ (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)) @ 
% 0.68/0.88             (k2_relat_1 @ X0))
% 0.68/0.88          | ~ (v1_funct_1 @ X0)
% 0.68/0.88          | ~ (v1_relat_1 @ X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['39', '41'])).
% 0.68/0.88  thf('43', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((r2_hidden @ 
% 0.68/0.88           (k1_funct_1 @ X0 @ (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)) @ 
% 0.68/0.88           (k2_relat_1 @ X0))
% 0.68/0.88          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.68/0.88          | ~ (v1_funct_1 @ X0)
% 0.68/0.88          | ~ (v1_relat_1 @ X0))),
% 0.68/0.88      inference('simplify', [status(thm)], ['42'])).
% 0.68/0.88  thf('44', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((r2_hidden @ X0 @ (k2_relat_1 @ (sk_C_2 @ X0 @ X1)))
% 0.68/0.88          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X1)) @ X2)
% 0.68/0.88          | ~ (v1_relat_1 @ (sk_C_2 @ X0 @ X1))
% 0.68/0.88          | ~ (v1_funct_1 @ (sk_C_2 @ X0 @ X1))
% 0.68/0.88          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X1)) @ X2))),
% 0.68/0.88      inference('sup+', [status(thm)], ['38', '43'])).
% 0.68/0.88  thf('45', plain,
% 0.68/0.88      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (sk_C_2 @ X15 @ X16))),
% 0.68/0.88      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.68/0.88  thf('46', plain,
% 0.68/0.88      (![X15 : $i, X16 : $i]: (v1_funct_1 @ (sk_C_2 @ X15 @ X16))),
% 0.68/0.88      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.68/0.88  thf('47', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((r2_hidden @ X0 @ (k2_relat_1 @ (sk_C_2 @ X0 @ X1)))
% 0.68/0.88          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X1)) @ X2)
% 0.68/0.88          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X1)) @ X2))),
% 0.68/0.88      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.68/0.88  thf('48', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X1)) @ X2)
% 0.68/0.88          | (r2_hidden @ X0 @ (k2_relat_1 @ (sk_C_2 @ X0 @ X1))))),
% 0.68/0.88      inference('simplify', [status(thm)], ['47'])).
% 0.68/0.88  thf('49', plain,
% 0.68/0.88      (![X18 : $i]:
% 0.68/0.88         (~ (r1_tarski @ (k2_relat_1 @ X18) @ sk_A)
% 0.68/0.88          | ((sk_B) != (k1_relat_1 @ X18))
% 0.68/0.88          | ~ (v1_funct_1 @ X18)
% 0.68/0.88          | ~ (v1_relat_1 @ X18))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('50', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((r2_hidden @ X1 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)))
% 0.68/0.88          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0))
% 0.68/0.88          | ~ (v1_funct_1 @ (sk_C_2 @ X1 @ X0))
% 0.68/0.88          | ((sk_B) != (k1_relat_1 @ (sk_C_2 @ X1 @ X0))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['48', '49'])).
% 0.68/0.88  thf('51', plain,
% 0.68/0.88      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (sk_C_2 @ X15 @ X16))),
% 0.68/0.88      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.68/0.88  thf('52', plain,
% 0.68/0.88      (![X15 : $i, X16 : $i]: (v1_funct_1 @ (sk_C_2 @ X15 @ X16))),
% 0.68/0.88      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.68/0.88  thf('53', plain,
% 0.68/0.88      (![X15 : $i, X16 : $i]: ((k1_relat_1 @ (sk_C_2 @ X15 @ X16)) = (X16))),
% 0.68/0.88      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.68/0.88  thf('54', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((r2_hidden @ X1 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)))
% 0.68/0.88          | ((sk_B) != (X0)))),
% 0.68/0.88      inference('demod', [status(thm)], ['50', '51', '52', '53'])).
% 0.68/0.88  thf('55', plain,
% 0.68/0.88      (![X1 : $i]: (r2_hidden @ X1 @ (k2_relat_1 @ (sk_C_2 @ X1 @ sk_B)))),
% 0.68/0.88      inference('simplify', [status(thm)], ['54'])).
% 0.68/0.88  thf('56', plain,
% 0.68/0.88      (![X9 : $i, X12 : $i]:
% 0.68/0.88         (~ (v1_relat_1 @ X9)
% 0.68/0.88          | ~ (v1_funct_1 @ X9)
% 0.68/0.88          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 0.68/0.88          | (r2_hidden @ (sk_D_1 @ X12 @ X9) @ (k1_relat_1 @ X9)))),
% 0.68/0.88      inference('simplify', [status(thm)], ['3'])).
% 0.68/0.88  thf('57', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((r2_hidden @ (sk_D_1 @ X0 @ (sk_C_2 @ X0 @ sk_B)) @ 
% 0.68/0.88           (k1_relat_1 @ (sk_C_2 @ X0 @ sk_B)))
% 0.68/0.88          | ~ (v1_funct_1 @ (sk_C_2 @ X0 @ sk_B))
% 0.68/0.88          | ~ (v1_relat_1 @ (sk_C_2 @ X0 @ sk_B)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['55', '56'])).
% 0.68/0.88  thf('58', plain,
% 0.68/0.88      (![X15 : $i, X16 : $i]: ((k1_relat_1 @ (sk_C_2 @ X15 @ X16)) = (X16))),
% 0.68/0.88      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.68/0.88  thf('59', plain,
% 0.68/0.88      (![X15 : $i, X16 : $i]: (v1_funct_1 @ (sk_C_2 @ X15 @ X16))),
% 0.68/0.88      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.68/0.88  thf('60', plain,
% 0.68/0.88      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (sk_C_2 @ X15 @ X16))),
% 0.68/0.88      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.68/0.88  thf('61', plain,
% 0.68/0.88      (![X0 : $i]: (r2_hidden @ (sk_D_1 @ X0 @ (sk_C_2 @ X0 @ sk_B)) @ sk_B)),
% 0.68/0.88      inference('demod', [status(thm)], ['57', '58', '59', '60'])).
% 0.68/0.88  thf('62', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((r2_hidden @ 
% 0.68/0.88           (sk_D_1 @ (sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) @ 
% 0.68/0.88            (sk_C_2 @ X1 @ X0)) @ 
% 0.68/0.88           X0)
% 0.68/0.88          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2))),
% 0.68/0.88      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.68/0.88  thf('63', plain,
% 0.68/0.88      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.68/0.88      inference('split', [status(esa)], ['36'])).
% 0.68/0.88  thf('64', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.68/0.88      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.68/0.88  thf('65', plain,
% 0.68/0.88      ((![X0 : $i]: (r1_tarski @ sk_B @ X0)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.68/0.88      inference('sup+', [status(thm)], ['63', '64'])).
% 0.68/0.88  thf('66', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (~ (r2_hidden @ X0 @ X1)
% 0.68/0.88          | (r2_hidden @ X0 @ X2)
% 0.68/0.88          | ~ (r1_tarski @ X1 @ X2))),
% 0.68/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.68/0.88  thf('67', plain,
% 0.68/0.88      ((![X0 : $i, X1 : $i]:
% 0.68/0.88          ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ sk_B)))
% 0.68/0.88         <= ((((sk_B) = (k1_xboole_0))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['65', '66'])).
% 0.68/0.88  thf('68', plain,
% 0.68/0.88      ((![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88          ((r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ sk_B)) @ X1)
% 0.68/0.88           | (r2_hidden @ 
% 0.68/0.88              (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ (sk_C_2 @ X0 @ sk_B))) @ 
% 0.68/0.88               (sk_C_2 @ X0 @ sk_B)) @ 
% 0.68/0.88              X2)))
% 0.68/0.88         <= ((((sk_B) = (k1_xboole_0))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['62', '67'])).
% 0.68/0.88  thf('69', plain,
% 0.68/0.88      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.68/0.88         (((k1_funct_1 @ (sk_C_2 @ X15 @ X16) @ X17) = (X15))
% 0.68/0.88          | ~ (r2_hidden @ X17 @ X16))),
% 0.68/0.88      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.68/0.88  thf('70', plain,
% 0.68/0.88      ((![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.88          ((r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ sk_B)) @ X2)
% 0.68/0.88           | ((k1_funct_1 @ (sk_C_2 @ X3 @ X0) @ 
% 0.68/0.88               (sk_D_1 @ (sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ sk_B))) @ 
% 0.68/0.88                (sk_C_2 @ X1 @ sk_B)))
% 0.68/0.88               = (X3))))
% 0.68/0.88         <= ((((sk_B) = (k1_xboole_0))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['68', '69'])).
% 0.68/0.88  thf('71', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.68/0.88          | ((sk_C @ X1 @ (k2_relat_1 @ X0))
% 0.68/0.88              = (k1_funct_1 @ X0 @ 
% 0.68/0.88                 (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)))
% 0.68/0.88          | ~ (v1_funct_1 @ X0)
% 0.68/0.88          | ~ (v1_relat_1 @ X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['12', '14'])).
% 0.68/0.88  thf('72', plain,
% 0.68/0.88      ((![X0 : $i, X1 : $i]:
% 0.68/0.88          (((sk_C @ X1 @ (k2_relat_1 @ (sk_C_2 @ X0 @ sk_B))) = (X0))
% 0.68/0.88           | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ sk_B)) @ X1)
% 0.68/0.88           | ~ (v1_relat_1 @ (sk_C_2 @ X0 @ sk_B))
% 0.68/0.88           | ~ (v1_funct_1 @ (sk_C_2 @ X0 @ sk_B))
% 0.68/0.88           | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ sk_B)) @ X1)))
% 0.68/0.88         <= ((((sk_B) = (k1_xboole_0))))),
% 0.68/0.88      inference('sup+', [status(thm)], ['70', '71'])).
% 0.68/0.88  thf('73', plain,
% 0.68/0.88      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (sk_C_2 @ X15 @ X16))),
% 0.68/0.88      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.68/0.88  thf('74', plain,
% 0.68/0.88      (![X15 : $i, X16 : $i]: (v1_funct_1 @ (sk_C_2 @ X15 @ X16))),
% 0.68/0.88      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.68/0.88  thf('75', plain,
% 0.68/0.88      ((![X0 : $i, X1 : $i]:
% 0.68/0.88          (((sk_C @ X1 @ (k2_relat_1 @ (sk_C_2 @ X0 @ sk_B))) = (X0))
% 0.68/0.88           | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ sk_B)) @ X1)
% 0.68/0.88           | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ sk_B)) @ X1)))
% 0.68/0.88         <= ((((sk_B) = (k1_xboole_0))))),
% 0.68/0.88      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.68/0.88  thf('76', plain,
% 0.68/0.88      ((![X0 : $i, X1 : $i]:
% 0.68/0.88          ((r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ sk_B)) @ X1)
% 0.68/0.88           | ((sk_C @ X1 @ (k2_relat_1 @ (sk_C_2 @ X0 @ sk_B))) = (X0))))
% 0.68/0.88         <= ((((sk_B) = (k1_xboole_0))))),
% 0.68/0.88      inference('simplify', [status(thm)], ['75'])).
% 0.68/0.88  thf('77', plain,
% 0.68/0.88      (![X1 : $i, X3 : $i]:
% 0.68/0.88         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.68/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.68/0.88  thf('78', plain,
% 0.68/0.88      ((![X0 : $i, X1 : $i]:
% 0.68/0.88          (~ (r2_hidden @ X0 @ X1)
% 0.68/0.88           | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ sk_B)) @ X1)
% 0.68/0.88           | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ sk_B)) @ X1)))
% 0.68/0.88         <= ((((sk_B) = (k1_xboole_0))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['76', '77'])).
% 0.68/0.88  thf('79', plain,
% 0.68/0.88      ((![X0 : $i, X1 : $i]:
% 0.68/0.88          ((r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ sk_B)) @ X1)
% 0.68/0.88           | ~ (r2_hidden @ X0 @ X1)))
% 0.68/0.88         <= ((((sk_B) = (k1_xboole_0))))),
% 0.68/0.88      inference('simplify', [status(thm)], ['78'])).
% 0.68/0.88  thf('80', plain,
% 0.68/0.88      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.68/0.88      inference('split', [status(esa)], ['36'])).
% 0.68/0.88  thf('81', plain,
% 0.68/0.88      (![X1 : $i, X3 : $i]:
% 0.68/0.88         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.68/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.68/0.88  thf('82', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((r2_hidden @ 
% 0.68/0.88           (sk_D_1 @ (sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) @ 
% 0.68/0.88            (sk_C_2 @ X1 @ X0)) @ 
% 0.68/0.88           X0)
% 0.68/0.88          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2))),
% 0.68/0.88      inference('demod', [status(thm)], ['6', '7', '8'])).
% 0.68/0.88  thf('83', plain, (![X7 : $i]: (r1_tarski @ k1_xboole_0 @ X7)),
% 0.68/0.88      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.68/0.88  thf('84', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         (~ (r2_hidden @ X0 @ X1)
% 0.68/0.88          | (r2_hidden @ X0 @ X2)
% 0.68/0.88          | ~ (r1_tarski @ X1 @ X2))),
% 0.68/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.68/0.88  thf('85', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['83', '84'])).
% 0.68/0.88  thf('86', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.68/0.88         ((r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ k1_xboole_0)) @ X1)
% 0.68/0.88          | (r2_hidden @ 
% 0.68/0.88             (sk_D_1 @ 
% 0.68/0.88              (sk_C @ X1 @ (k2_relat_1 @ (sk_C_2 @ X0 @ k1_xboole_0))) @ 
% 0.68/0.88              (sk_C_2 @ X0 @ k1_xboole_0)) @ 
% 0.68/0.88             X2))),
% 0.68/0.88      inference('sup-', [status(thm)], ['82', '85'])).
% 0.68/0.88  thf('87', plain,
% 0.68/0.88      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.68/0.88         (((k1_funct_1 @ (sk_C_2 @ X15 @ X16) @ X17) = (X15))
% 0.68/0.88          | ~ (r2_hidden @ X17 @ X16))),
% 0.68/0.88      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.68/0.88  thf('88', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.68/0.88         ((r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ k1_xboole_0)) @ X2)
% 0.68/0.88          | ((k1_funct_1 @ (sk_C_2 @ X3 @ X0) @ 
% 0.68/0.88              (sk_D_1 @ 
% 0.68/0.88               (sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ k1_xboole_0))) @ 
% 0.68/0.88               (sk_C_2 @ X1 @ k1_xboole_0)))
% 0.68/0.88              = (X3)))),
% 0.68/0.88      inference('sup-', [status(thm)], ['86', '87'])).
% 0.68/0.88  thf('89', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 0.68/0.88          | ((sk_C @ X1 @ (k2_relat_1 @ X0))
% 0.68/0.88              = (k1_funct_1 @ X0 @ 
% 0.68/0.88                 (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)))
% 0.68/0.88          | ~ (v1_funct_1 @ X0)
% 0.68/0.88          | ~ (v1_relat_1 @ X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['12', '14'])).
% 0.68/0.88  thf('90', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         (((sk_C @ X1 @ (k2_relat_1 @ (sk_C_2 @ X0 @ k1_xboole_0))) = (X0))
% 0.68/0.88          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ k1_xboole_0)) @ X1)
% 0.68/0.88          | ~ (v1_relat_1 @ (sk_C_2 @ X0 @ k1_xboole_0))
% 0.68/0.88          | ~ (v1_funct_1 @ (sk_C_2 @ X0 @ k1_xboole_0))
% 0.68/0.88          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ k1_xboole_0)) @ X1))),
% 0.68/0.88      inference('sup+', [status(thm)], ['88', '89'])).
% 0.68/0.88  thf('91', plain,
% 0.68/0.88      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (sk_C_2 @ X15 @ X16))),
% 0.68/0.88      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.68/0.88  thf('92', plain,
% 0.68/0.88      (![X15 : $i, X16 : $i]: (v1_funct_1 @ (sk_C_2 @ X15 @ X16))),
% 0.68/0.88      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.68/0.88  thf('93', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         (((sk_C @ X1 @ (k2_relat_1 @ (sk_C_2 @ X0 @ k1_xboole_0))) = (X0))
% 0.68/0.88          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ k1_xboole_0)) @ X1)
% 0.68/0.88          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ k1_xboole_0)) @ X1))),
% 0.68/0.88      inference('demod', [status(thm)], ['90', '91', '92'])).
% 0.68/0.88  thf('94', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ k1_xboole_0)) @ X1)
% 0.68/0.88          | ((sk_C @ X1 @ (k2_relat_1 @ (sk_C_2 @ X0 @ k1_xboole_0))) = (X0)))),
% 0.68/0.88      inference('simplify', [status(thm)], ['93'])).
% 0.68/0.88  thf('95', plain,
% 0.68/0.88      (![X1 : $i, X3 : $i]:
% 0.68/0.88         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.68/0.88      inference('cnf', [status(esa)], [d3_tarski])).
% 0.68/0.88  thf('96', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         (~ (r2_hidden @ X0 @ X1)
% 0.68/0.88          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ k1_xboole_0)) @ X1)
% 0.68/0.88          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ k1_xboole_0)) @ X1))),
% 0.68/0.88      inference('sup-', [status(thm)], ['94', '95'])).
% 0.68/0.88  thf('97', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ k1_xboole_0)) @ X1)
% 0.68/0.88          | ~ (r2_hidden @ X0 @ X1))),
% 0.68/0.88      inference('simplify', [status(thm)], ['96'])).
% 0.68/0.88  thf('98', plain,
% 0.68/0.88      (![X0 : $i, X1 : $i]:
% 0.68/0.88         ((r1_tarski @ X0 @ X1)
% 0.68/0.88          | (r1_tarski @ 
% 0.68/0.88             (k2_relat_1 @ (sk_C_2 @ (sk_C @ X1 @ X0) @ k1_xboole_0)) @ X0))),
% 0.68/0.88      inference('sup-', [status(thm)], ['81', '97'])).
% 0.68/0.88  thf('99', plain,
% 0.68/0.88      (![X18 : $i]:
% 0.68/0.88         (~ (r1_tarski @ (k2_relat_1 @ X18) @ sk_A)
% 0.68/0.88          | ((sk_B) != (k1_relat_1 @ X18))
% 0.68/0.88          | ~ (v1_funct_1 @ X18)
% 0.68/0.88          | ~ (v1_relat_1 @ X18))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('100', plain,
% 0.68/0.88      (![X0 : $i]:
% 0.68/0.88         ((r1_tarski @ sk_A @ X0)
% 0.68/0.88          | ~ (v1_relat_1 @ (sk_C_2 @ (sk_C @ X0 @ sk_A) @ k1_xboole_0))
% 0.68/0.88          | ~ (v1_funct_1 @ (sk_C_2 @ (sk_C @ X0 @ sk_A) @ k1_xboole_0))
% 0.68/0.88          | ((sk_B)
% 0.68/0.88              != (k1_relat_1 @ (sk_C_2 @ (sk_C @ X0 @ sk_A) @ k1_xboole_0))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['98', '99'])).
% 0.68/0.88  thf('101', plain,
% 0.68/0.88      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (sk_C_2 @ X15 @ X16))),
% 0.68/0.88      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.68/0.88  thf('102', plain,
% 0.68/0.88      (![X15 : $i, X16 : $i]: (v1_funct_1 @ (sk_C_2 @ X15 @ X16))),
% 0.68/0.88      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.68/0.88  thf('103', plain,
% 0.68/0.88      (![X15 : $i, X16 : $i]: ((k1_relat_1 @ (sk_C_2 @ X15 @ X16)) = (X16))),
% 0.68/0.88      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.68/0.88  thf('104', plain,
% 0.68/0.88      (![X0 : $i]: ((r1_tarski @ sk_A @ X0) | ((sk_B) != (k1_xboole_0)))),
% 0.68/0.88      inference('demod', [status(thm)], ['100', '101', '102', '103'])).
% 0.68/0.88  thf('105', plain,
% 0.68/0.88      ((![X0 : $i]: (((sk_B) != (sk_B)) | (r1_tarski @ sk_A @ X0)))
% 0.68/0.88         <= ((((sk_B) = (k1_xboole_0))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['80', '104'])).
% 0.68/0.88  thf('106', plain,
% 0.68/0.88      ((![X0 : $i]: (r1_tarski @ sk_A @ X0)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.68/0.88      inference('simplify', [status(thm)], ['105'])).
% 0.68/0.88  thf('107', plain,
% 0.68/0.88      ((![X0 : $i]: (r1_tarski @ sk_B @ X0)) <= ((((sk_B) = (k1_xboole_0))))),
% 0.68/0.88      inference('sup+', [status(thm)], ['63', '64'])).
% 0.68/0.88  thf('108', plain,
% 0.68/0.88      (![X4 : $i, X6 : $i]:
% 0.68/0.88         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 0.68/0.88      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.68/0.88  thf('109', plain,
% 0.68/0.88      ((![X0 : $i]: (~ (r1_tarski @ X0 @ sk_B) | ((X0) = (sk_B))))
% 0.68/0.88         <= ((((sk_B) = (k1_xboole_0))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['107', '108'])).
% 0.68/0.88  thf('110', plain, ((((sk_A) = (sk_B))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['106', '109'])).
% 0.68/0.88  thf('111', plain,
% 0.68/0.88      ((![X0 : $i, X1 : $i]:
% 0.68/0.88          ((r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ sk_A)) @ X1)
% 0.68/0.88           | ~ (r2_hidden @ X0 @ X1)))
% 0.68/0.88         <= ((((sk_B) = (k1_xboole_0))))),
% 0.68/0.88      inference('demod', [status(thm)], ['79', '110'])).
% 0.68/0.88  thf('112', plain,
% 0.68/0.88      ((![X0 : $i]:
% 0.68/0.88          (r1_tarski @ 
% 0.68/0.88           (k2_relat_1 @ (sk_C_2 @ (sk_D_1 @ X0 @ (sk_C_2 @ X0 @ sk_B)) @ sk_A)) @ 
% 0.68/0.88           sk_B))
% 0.68/0.88         <= ((((sk_B) = (k1_xboole_0))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['61', '111'])).
% 0.68/0.88  thf('113', plain, ((((sk_A) = (sk_B))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['106', '109'])).
% 0.68/0.88  thf('114', plain, ((((sk_A) = (sk_B))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['106', '109'])).
% 0.68/0.88  thf('115', plain,
% 0.68/0.88      ((![X0 : $i]:
% 0.68/0.88          (r1_tarski @ 
% 0.68/0.88           (k2_relat_1 @ (sk_C_2 @ (sk_D_1 @ X0 @ (sk_C_2 @ X0 @ sk_A)) @ sk_A)) @ 
% 0.68/0.88           sk_A))
% 0.68/0.88         <= ((((sk_B) = (k1_xboole_0))))),
% 0.68/0.88      inference('demod', [status(thm)], ['112', '113', '114'])).
% 0.68/0.88  thf('116', plain,
% 0.68/0.88      (![X18 : $i]:
% 0.68/0.88         (~ (r1_tarski @ (k2_relat_1 @ X18) @ sk_A)
% 0.68/0.88          | ((sk_B) != (k1_relat_1 @ X18))
% 0.68/0.88          | ~ (v1_funct_1 @ X18)
% 0.68/0.88          | ~ (v1_relat_1 @ X18))),
% 0.68/0.88      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.68/0.88  thf('117', plain,
% 0.68/0.88      ((![X0 : $i]:
% 0.68/0.88          (~ (v1_relat_1 @ 
% 0.68/0.88              (sk_C_2 @ (sk_D_1 @ X0 @ (sk_C_2 @ X0 @ sk_A)) @ sk_A))
% 0.68/0.88           | ~ (v1_funct_1 @ 
% 0.68/0.88                (sk_C_2 @ (sk_D_1 @ X0 @ (sk_C_2 @ X0 @ sk_A)) @ sk_A))
% 0.68/0.88           | ((sk_B)
% 0.68/0.88               != (k1_relat_1 @ 
% 0.68/0.88                   (sk_C_2 @ (sk_D_1 @ X0 @ (sk_C_2 @ X0 @ sk_A)) @ sk_A)))))
% 0.68/0.88         <= ((((sk_B) = (k1_xboole_0))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['115', '116'])).
% 0.68/0.88  thf('118', plain,
% 0.68/0.88      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (sk_C_2 @ X15 @ X16))),
% 0.68/0.88      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.68/0.88  thf('119', plain,
% 0.68/0.88      (![X15 : $i, X16 : $i]: (v1_funct_1 @ (sk_C_2 @ X15 @ X16))),
% 0.68/0.88      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.68/0.88  thf('120', plain, ((((sk_A) = (sk_B))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.68/0.88      inference('sup-', [status(thm)], ['106', '109'])).
% 0.68/0.88  thf('121', plain,
% 0.68/0.88      (![X15 : $i, X16 : $i]: ((k1_relat_1 @ (sk_C_2 @ X15 @ X16)) = (X16))),
% 0.68/0.88      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.68/0.88  thf('122', plain, ((((sk_A) != (sk_A))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.68/0.88      inference('demod', [status(thm)], ['117', '118', '119', '120', '121'])).
% 0.68/0.88  thf('123', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.68/0.88      inference('simplify', [status(thm)], ['122'])).
% 0.68/0.88  thf('124', plain,
% 0.68/0.88      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B) = (k1_xboole_0)))),
% 0.68/0.88      inference('split', [status(esa)], ['36'])).
% 0.68/0.88  thf('125', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.68/0.88      inference('sat_resolution*', [status(thm)], ['123', '124'])).
% 0.68/0.88  thf('126', plain, (((sk_A) != (k1_xboole_0))),
% 0.68/0.88      inference('simpl_trail', [status(thm)], ['37', '125'])).
% 0.68/0.88  thf('127', plain, ($false),
% 0.68/0.88      inference('simplify_reflect-', [status(thm)], ['35', '126'])).
% 0.68/0.88  
% 0.68/0.88  % SZS output end Refutation
% 0.68/0.88  
% 0.68/0.88  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
