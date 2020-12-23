%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1JQONlvAxH

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:27 EST 2020

% Result     : Theorem 16.27s
% Output     : Refutation 16.27s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 531 expanded)
%              Number of leaves         :   20 ( 175 expanded)
%              Depth                    :   28
%              Number of atoms          : 1308 (5995 expanded)
%              Number of equality atoms :  157 ( 816 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf('0',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X16 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X8: $i] :
      ( ( ( k1_relat_1 @ X8 )
       != k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ( ( sk_C_2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_C_2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X1: $i] :
      ( ( sk_C_2 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X16 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('7',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['5','6'])).

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

thf('8',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X9 @ X10 ) @ X9 )
      | ( r2_hidden @ ( sk_D @ X9 @ X10 ) @ ( k1_relat_1 @ X10 ) )
      | ( X9
        = ( k2_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X1: $i] :
      ( ( sk_C_2 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('11',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('12',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X1: $i] :
      ( ( sk_C_2 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('15',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['9','12','15'])).

thf('17',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X16 @ X17 ) @ X18 )
        = X16 )
      | ~ ( r2_hidden @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X1 @ k1_xboole_0 ) @ ( sk_D @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X1: $i] :
      ( ( sk_C_2 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( X2
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ k1_xboole_0 ) @ X2 )
      | ( X2
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ k1_xboole_0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X2 @ k1_xboole_0 ) @ X2 )
      | ( X2
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(condensation,[status(thm)],['23'])).

thf('25',plain,(
    ! [X1: $i] :
      ( ( sk_C_2 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(condensation,[status(thm)],['23'])).

thf('27',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X16 @ X17 ) @ X18 )
        = X16 )
      | ~ ( r2_hidden @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) @ ( sk_C_1 @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 ) )
        = X0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 ) )
        = X0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['25','28'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','33'])).

thf('35',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X16 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('36',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('37',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('38',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('39',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X9 @ X10 ) @ X9 )
      | ( r2_hidden @ ( sk_D @ X9 @ X10 ) @ ( k1_relat_1 @ X10 ) )
      | ( X9
        = ( k2_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('40',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('41',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('42',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k2_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ ( k2_tarski @ X0 @ X0 ) @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ( ( sk_C_1 @ ( k2_tarski @ X0 @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ( ( sk_C_1 @ ( k2_tarski @ X0 @ X0 ) @ X1 )
        = X0 )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k2_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['38','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k2_relat_1 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['37','45'])).

thf(t15_funct_1,conjecture,(
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

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( A != k1_xboole_0 )
       => ! [B: $i] :
          ? [C: $i] :
            ( ( ( k2_relat_1 @ C )
              = ( k1_tarski @ B ) )
            & ( ( k1_relat_1 @ C )
              = A )
            & ( v1_funct_1 @ C )
            & ( v1_relat_1 @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t15_funct_1])).

thf('47',plain,(
    ! [X19: $i] :
      ( ( ( k2_relat_1 @ X19 )
       != ( k1_tarski @ sk_B ) )
      | ( ( k1_relat_1 @ X19 )
       != sk_A )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_tarski @ X0 @ X0 )
       != ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ( ( k2_tarski @ X0 @ X0 )
       != ( k1_tarski @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_B ) )
      | ( r2_hidden @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A ) ) ),
    inference('sup-',[status(thm)],['36','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != sk_A )
      | ( ( sk_C_1 @ ( k1_tarski @ sk_B ) @ X0 )
        = sk_B )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_B ) @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(eq_res,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_B ) @ ( sk_C_2 @ X1 @ X0 ) ) @ ( k1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ sk_B ) @ ( sk_C_2 @ X1 @ X0 ) )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['35','51'])).

thf('53',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X16 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('54',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('55',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_B ) @ ( sk_C_2 @ X1 @ X0 ) ) @ X0 )
      | ( ( sk_C_1 @ ( k1_tarski @ sk_B ) @ ( sk_C_2 @ X1 @ X0 ) )
        = sk_B ) ) ),
    inference(demod,[status(thm)],['52','53','54','55'])).

thf('57',plain,(
    ! [X1: $i] :
      ( ( ( sk_C_1 @ ( k1_tarski @ sk_B ) @ ( sk_C_2 @ X1 @ sk_A ) )
        = sk_B )
      | ( r2_hidden @ ( sk_D @ ( k1_tarski @ sk_B ) @ ( sk_C_2 @ X1 @ sk_A ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X16 @ X17 ) @ X18 )
        = X16 )
      | ~ ( r2_hidden @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C_1 @ ( k1_tarski @ sk_B ) @ ( sk_C_2 @ X0 @ sk_A ) )
        = sk_B )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X1 @ sk_A ) @ ( sk_D @ ( k1_tarski @ sk_B ) @ ( sk_C_2 @ X0 @ sk_A ) ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('61',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X9 @ X10 ) @ X9 )
      | ( ( sk_C_1 @ X9 @ X10 )
        = ( k1_funct_1 @ X10 @ ( sk_D @ X9 @ X10 ) ) )
      | ( X9
        = ( k2_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( X1 = X0 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k2_relat_1 @ X1 ) )
      | ( ( sk_C_1 @ ( k2_tarski @ X0 @ X0 ) @ X1 )
        = ( k1_funct_1 @ X1 @ ( sk_D @ ( k2_tarski @ X0 @ X0 ) @ X1 ) ) )
      | ( ( sk_C_1 @ ( k2_tarski @ X0 @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C_1 @ ( k2_tarski @ X0 @ X0 ) @ X1 )
        = ( k1_funct_1 @ X1 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 ) ) )
      | ( ( sk_C_1 @ ( k2_tarski @ X0 @ X0 ) @ X1 )
        = X0 )
      | ( ( k2_tarski @ X0 @ X0 )
        = ( k2_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['60','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ X0 @ ( sk_D @ ( k1_tarski @ X1 ) @ X0 ) )
       != X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_tarski @ X1 @ X1 )
        = ( k2_relat_1 @ X0 ) )
      | ( ( sk_C_1 @ ( k2_tarski @ X1 @ X1 ) @ X0 )
        = X1 ) ) ),
    inference(eq_fact,[status(thm)],['64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B )
      | ( ( sk_C_1 @ ( k1_tarski @ sk_B ) @ ( sk_C_2 @ X0 @ sk_A ) )
        = sk_B )
      | ( ( sk_C_1 @ ( k2_tarski @ sk_B @ sk_B ) @ ( sk_C_2 @ X0 @ sk_A ) )
        = sk_B )
      | ( ( k2_tarski @ sk_B @ sk_B )
        = ( k2_relat_1 @ ( sk_C_2 @ X0 @ sk_A ) ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X0 @ sk_A ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X0 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['59','65'])).

thf('67',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('68',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('69',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('70',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( X0 != sk_B )
      | ( ( sk_C_1 @ ( k1_tarski @ sk_B ) @ ( sk_C_2 @ X0 @ sk_A ) )
        = sk_B )
      | ( ( sk_C_1 @ ( k1_tarski @ sk_B ) @ ( sk_C_2 @ X0 @ sk_A ) )
        = sk_B )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ ( sk_C_2 @ X0 @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['66','67','68','69','70'])).

thf('72',plain,
    ( ( ( k1_tarski @ sk_B )
      = ( k2_relat_1 @ ( sk_C_2 @ sk_B @ sk_A ) ) )
    | ( ( sk_C_1 @ ( k1_tarski @ sk_B ) @ ( sk_C_2 @ sk_B @ sk_A ) )
      = sk_B ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,
    ( ( ( k1_tarski @ sk_B )
      = ( k2_relat_1 @ ( sk_C_2 @ sk_B @ sk_A ) ) )
    | ( ( sk_C_1 @ ( k1_tarski @ sk_B ) @ ( sk_C_2 @ sk_B @ sk_A ) )
      = sk_B ) ),
    inference(simplify,[status(thm)],['71'])).

thf('74',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X9 @ X10 ) @ X9 )
      | ( ( sk_C_1 @ X9 @ X10 )
       != ( k1_funct_1 @ X10 @ X11 ) )
      | ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X10 ) )
      | ( X9
        = ( k2_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_B @ ( k1_tarski @ sk_B ) )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ ( sk_C_2 @ sk_B @ sk_A ) ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ sk_B @ sk_A ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ sk_B @ sk_A ) )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ ( sk_C_2 @ sk_B @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ ( sk_C_2 @ sk_B @ sk_A ) ) )
      | ( ( sk_C_1 @ ( k1_tarski @ sk_B ) @ ( sk_C_2 @ sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('77',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('79',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('80',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X16 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ ( sk_C_2 @ sk_B @ sk_A ) ) )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ ( sk_C_2 @ sk_B @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( sk_C_1 @ ( k1_tarski @ sk_B ) @ ( sk_C_2 @ sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['75','77','78','79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( ( sk_C_1 @ ( k1_tarski @ sk_B ) @ ( sk_C_2 @ sk_B @ sk_A ) )
       != ( k1_funct_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ ( sk_C_2 @ sk_B @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( sk_B
       != ( k1_funct_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ X0 ) )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ ( sk_C_2 @ sk_B @ sk_A ) ) )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ ( sk_C_2 @ sk_B @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['72','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ ( sk_C_2 @ sk_B @ sk_A ) ) )
      | ( sk_B
       != ( k1_funct_1 @ ( sk_C_2 @ sk_B @ sk_A ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X16 @ X17 ) @ X18 )
        = X16 )
      | ~ ( r2_hidden @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ sk_B )
        = ( k2_relat_1 @ ( sk_C_2 @ sk_B @ sk_A ) ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_tarski @ sk_B )
      = ( k2_relat_1 @ ( sk_C_2 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','86'])).

thf('88',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( k1_tarski @ sk_B )
    = ( k2_relat_1 @ ( sk_C_2 @ sk_B @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X19: $i] :
      ( ( ( k2_relat_1 @ X19 )
       != ( k1_tarski @ sk_B ) )
      | ( ( k1_relat_1 @ X19 )
       != sk_A )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( ( k1_tarski @ sk_B )
     != ( k1_tarski @ sk_B ) )
    | ~ ( v1_relat_1 @ ( sk_C_2 @ sk_B @ sk_A ) )
    | ~ ( v1_funct_1 @ ( sk_C_2 @ sk_B @ sk_A ) )
    | ( ( k1_relat_1 @ ( sk_C_2 @ sk_B @ sk_A ) )
     != sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('93',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('94',plain,(
    ! [X16: $i,X17: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X16 @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('95',plain,
    ( ( ( k1_tarski @ sk_B )
     != ( k1_tarski @ sk_B ) )
    | ( sk_A != sk_A ) ),
    inference(demod,[status(thm)],['91','92','93','94'])).

thf('96',plain,(
    $false ),
    inference(simplify,[status(thm)],['95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1JQONlvAxH
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:02:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 16.27/16.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 16.27/16.49  % Solved by: fo/fo7.sh
% 16.27/16.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 16.27/16.49  % done 2546 iterations in 16.032s
% 16.27/16.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 16.27/16.49  % SZS output start Refutation
% 16.27/16.49  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 16.27/16.49  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 16.27/16.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 16.27/16.49  thf(sk_B_type, type, sk_B: $i).
% 16.27/16.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 16.27/16.49  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 16.27/16.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 16.27/16.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 16.27/16.49  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 16.27/16.49  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 16.27/16.49  thf(sk_A_type, type, sk_A: $i).
% 16.27/16.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 16.27/16.49  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 16.27/16.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 16.27/16.49  thf(s3_funct_1__e2_24__funct_1, axiom,
% 16.27/16.49    (![A:$i,B:$i]:
% 16.27/16.49     ( ?[C:$i]:
% 16.27/16.49       ( ( ![D:$i]:
% 16.27/16.49           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 16.27/16.49         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 16.27/16.49         ( v1_relat_1 @ C ) ) ))).
% 16.27/16.49  thf('0', plain,
% 16.27/16.49      (![X16 : $i, X17 : $i]: ((k1_relat_1 @ (sk_C_2 @ X16 @ X17)) = (X17))),
% 16.27/16.49      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 16.27/16.49  thf(t64_relat_1, axiom,
% 16.27/16.49    (![A:$i]:
% 16.27/16.49     ( ( v1_relat_1 @ A ) =>
% 16.27/16.49       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 16.27/16.49           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 16.27/16.49         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 16.27/16.49  thf('1', plain,
% 16.27/16.49      (![X8 : $i]:
% 16.27/16.49         (((k1_relat_1 @ X8) != (k1_xboole_0))
% 16.27/16.49          | ((X8) = (k1_xboole_0))
% 16.27/16.49          | ~ (v1_relat_1 @ X8))),
% 16.27/16.49      inference('cnf', [status(esa)], [t64_relat_1])).
% 16.27/16.49  thf('2', plain,
% 16.27/16.49      (![X0 : $i, X1 : $i]:
% 16.27/16.49         (((X0) != (k1_xboole_0))
% 16.27/16.49          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0))
% 16.27/16.49          | ((sk_C_2 @ X1 @ X0) = (k1_xboole_0)))),
% 16.27/16.49      inference('sup-', [status(thm)], ['0', '1'])).
% 16.27/16.49  thf('3', plain, (![X16 : $i, X17 : $i]: (v1_relat_1 @ (sk_C_2 @ X16 @ X17))),
% 16.27/16.49      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 16.27/16.49  thf('4', plain,
% 16.27/16.49      (![X0 : $i, X1 : $i]:
% 16.27/16.49         (((X0) != (k1_xboole_0)) | ((sk_C_2 @ X1 @ X0) = (k1_xboole_0)))),
% 16.27/16.49      inference('demod', [status(thm)], ['2', '3'])).
% 16.27/16.49  thf('5', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 16.27/16.49      inference('simplify', [status(thm)], ['4'])).
% 16.27/16.49  thf('6', plain,
% 16.27/16.49      (![X16 : $i, X17 : $i]: ((k1_relat_1 @ (sk_C_2 @ X16 @ X17)) = (X17))),
% 16.27/16.49      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 16.27/16.49  thf('7', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 16.27/16.49      inference('sup+', [status(thm)], ['5', '6'])).
% 16.27/16.49  thf(d5_funct_1, axiom,
% 16.27/16.49    (![A:$i]:
% 16.27/16.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 16.27/16.49       ( ![B:$i]:
% 16.27/16.49         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 16.27/16.49           ( ![C:$i]:
% 16.27/16.49             ( ( r2_hidden @ C @ B ) <=>
% 16.27/16.49               ( ?[D:$i]:
% 16.27/16.49                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 16.27/16.49                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 16.27/16.49  thf('8', plain,
% 16.27/16.49      (![X9 : $i, X10 : $i]:
% 16.27/16.49         ((r2_hidden @ (sk_C_1 @ X9 @ X10) @ X9)
% 16.27/16.49          | (r2_hidden @ (sk_D @ X9 @ X10) @ (k1_relat_1 @ X10))
% 16.27/16.49          | ((X9) = (k2_relat_1 @ X10))
% 16.27/16.49          | ~ (v1_funct_1 @ X10)
% 16.27/16.49          | ~ (v1_relat_1 @ X10))),
% 16.27/16.49      inference('cnf', [status(esa)], [d5_funct_1])).
% 16.27/16.49  thf('9', plain,
% 16.27/16.49      (![X0 : $i]:
% 16.27/16.49         ((r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 16.27/16.49          | ~ (v1_relat_1 @ k1_xboole_0)
% 16.27/16.49          | ~ (v1_funct_1 @ k1_xboole_0)
% 16.27/16.49          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 16.27/16.49          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 16.27/16.49      inference('sup+', [status(thm)], ['7', '8'])).
% 16.27/16.49  thf('10', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 16.27/16.49      inference('simplify', [status(thm)], ['4'])).
% 16.27/16.49  thf('11', plain,
% 16.27/16.49      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (sk_C_2 @ X16 @ X17))),
% 16.27/16.49      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 16.27/16.49  thf('12', plain, ((v1_relat_1 @ k1_xboole_0)),
% 16.27/16.49      inference('sup+', [status(thm)], ['10', '11'])).
% 16.27/16.49  thf('13', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 16.27/16.49      inference('simplify', [status(thm)], ['4'])).
% 16.27/16.49  thf('14', plain,
% 16.27/16.49      (![X16 : $i, X17 : $i]: (v1_funct_1 @ (sk_C_2 @ X16 @ X17))),
% 16.27/16.49      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 16.27/16.49  thf('15', plain, ((v1_funct_1 @ k1_xboole_0)),
% 16.27/16.49      inference('sup+', [status(thm)], ['13', '14'])).
% 16.27/16.49  thf('16', plain,
% 16.27/16.49      (![X0 : $i]:
% 16.27/16.49         ((r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 16.27/16.49          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 16.27/16.49          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 16.27/16.49      inference('demod', [status(thm)], ['9', '12', '15'])).
% 16.27/16.49  thf('17', plain,
% 16.27/16.49      (![X16 : $i, X17 : $i, X18 : $i]:
% 16.27/16.49         (((k1_funct_1 @ (sk_C_2 @ X16 @ X17) @ X18) = (X16))
% 16.27/16.49          | ~ (r2_hidden @ X18 @ X17))),
% 16.27/16.49      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 16.27/16.49  thf('18', plain,
% 16.27/16.49      (![X0 : $i, X1 : $i]:
% 16.27/16.49         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 16.27/16.49          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 16.27/16.49          | ((k1_funct_1 @ (sk_C_2 @ X1 @ k1_xboole_0) @ 
% 16.27/16.49              (sk_D @ X0 @ k1_xboole_0)) = (X1)))),
% 16.27/16.49      inference('sup-', [status(thm)], ['16', '17'])).
% 16.27/16.49  thf('19', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 16.27/16.49      inference('simplify', [status(thm)], ['4'])).
% 16.27/16.49  thf('20', plain,
% 16.27/16.49      (![X0 : $i, X1 : $i]:
% 16.27/16.49         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 16.27/16.49          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 16.27/16.49          | ((k1_funct_1 @ k1_xboole_0 @ (sk_D @ X0 @ k1_xboole_0)) = (X1)))),
% 16.27/16.49      inference('demod', [status(thm)], ['18', '19'])).
% 16.27/16.49  thf('21', plain,
% 16.27/16.49      (![X0 : $i, X1 : $i]:
% 16.27/16.49         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 16.27/16.49          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 16.27/16.49          | ((k1_funct_1 @ k1_xboole_0 @ (sk_D @ X0 @ k1_xboole_0)) = (X1)))),
% 16.27/16.49      inference('demod', [status(thm)], ['18', '19'])).
% 16.27/16.49  thf('22', plain,
% 16.27/16.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.27/16.49         (((X0) = (X1))
% 16.27/16.49          | ((X2) = (k2_relat_1 @ k1_xboole_0))
% 16.27/16.49          | (r2_hidden @ (sk_C_1 @ X2 @ k1_xboole_0) @ X2)
% 16.27/16.49          | ((X2) = (k2_relat_1 @ k1_xboole_0))
% 16.27/16.49          | (r2_hidden @ (sk_C_1 @ X2 @ k1_xboole_0) @ X2))),
% 16.27/16.49      inference('sup+', [status(thm)], ['20', '21'])).
% 16.27/16.49  thf('23', plain,
% 16.27/16.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.27/16.49         ((r2_hidden @ (sk_C_1 @ X2 @ k1_xboole_0) @ X2)
% 16.27/16.49          | ((X2) = (k2_relat_1 @ k1_xboole_0))
% 16.27/16.49          | ((X0) = (X1)))),
% 16.27/16.49      inference('simplify', [status(thm)], ['22'])).
% 16.27/16.49  thf('24', plain,
% 16.27/16.49      (![X0 : $i]:
% 16.27/16.49         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 16.27/16.49          | ((X0) = (k2_relat_1 @ k1_xboole_0)))),
% 16.27/16.49      inference('condensation', [status(thm)], ['23'])).
% 16.27/16.49  thf('25', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 16.27/16.49      inference('simplify', [status(thm)], ['4'])).
% 16.27/16.49  thf('26', plain,
% 16.27/16.49      (![X0 : $i]:
% 16.27/16.49         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 16.27/16.49          | ((X0) = (k2_relat_1 @ k1_xboole_0)))),
% 16.27/16.49      inference('condensation', [status(thm)], ['23'])).
% 16.27/16.49  thf('27', plain,
% 16.27/16.49      (![X16 : $i, X17 : $i, X18 : $i]:
% 16.27/16.49         (((k1_funct_1 @ (sk_C_2 @ X16 @ X17) @ X18) = (X16))
% 16.27/16.49          | ~ (r2_hidden @ X18 @ X17))),
% 16.27/16.49      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 16.27/16.49  thf('28', plain,
% 16.27/16.49      (![X0 : $i, X1 : $i]:
% 16.27/16.49         (((X0) = (k2_relat_1 @ k1_xboole_0))
% 16.27/16.49          | ((k1_funct_1 @ (sk_C_2 @ X1 @ X0) @ (sk_C_1 @ X0 @ k1_xboole_0))
% 16.27/16.49              = (X1)))),
% 16.27/16.49      inference('sup-', [status(thm)], ['26', '27'])).
% 16.27/16.49  thf('29', plain,
% 16.27/16.49      (![X0 : $i]:
% 16.27/16.49         (((k1_funct_1 @ k1_xboole_0 @ (sk_C_1 @ k1_xboole_0 @ k1_xboole_0))
% 16.27/16.49            = (X0))
% 16.27/16.49          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0)))),
% 16.27/16.49      inference('sup+', [status(thm)], ['25', '28'])).
% 16.27/16.49  thf('30', plain,
% 16.27/16.49      (![X0 : $i]:
% 16.27/16.49         (((k1_funct_1 @ k1_xboole_0 @ (sk_C_1 @ k1_xboole_0 @ k1_xboole_0))
% 16.27/16.49            = (X0))
% 16.27/16.49          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0)))),
% 16.27/16.49      inference('sup+', [status(thm)], ['25', '28'])).
% 16.27/16.49  thf('31', plain,
% 16.27/16.49      (![X0 : $i, X1 : $i]:
% 16.27/16.49         (((X0) = (X1))
% 16.27/16.49          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 16.27/16.49          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0)))),
% 16.27/16.49      inference('sup+', [status(thm)], ['29', '30'])).
% 16.27/16.49  thf('32', plain,
% 16.27/16.49      (![X0 : $i, X1 : $i]:
% 16.27/16.49         (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0)) | ((X0) = (X1)))),
% 16.27/16.49      inference('simplify', [status(thm)], ['31'])).
% 16.27/16.49  thf('33', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 16.27/16.49      inference('condensation', [status(thm)], ['32'])).
% 16.27/16.49  thf('34', plain,
% 16.27/16.49      (![X0 : $i]:
% 16.27/16.49         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 16.27/16.49          | ((X0) = (k1_xboole_0)))),
% 16.27/16.49      inference('demod', [status(thm)], ['24', '33'])).
% 16.27/16.49  thf('35', plain,
% 16.27/16.49      (![X16 : $i, X17 : $i]: ((k1_relat_1 @ (sk_C_2 @ X16 @ X17)) = (X17))),
% 16.27/16.49      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 16.27/16.49  thf(t69_enumset1, axiom,
% 16.27/16.49    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 16.27/16.49  thf('36', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 16.27/16.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 16.27/16.49  thf('37', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 16.27/16.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 16.27/16.49  thf('38', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 16.27/16.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 16.27/16.49  thf('39', plain,
% 16.27/16.49      (![X9 : $i, X10 : $i]:
% 16.27/16.49         ((r2_hidden @ (sk_C_1 @ X9 @ X10) @ X9)
% 16.27/16.49          | (r2_hidden @ (sk_D @ X9 @ X10) @ (k1_relat_1 @ X10))
% 16.27/16.49          | ((X9) = (k2_relat_1 @ X10))
% 16.27/16.49          | ~ (v1_funct_1 @ X10)
% 16.27/16.49          | ~ (v1_relat_1 @ X10))),
% 16.27/16.49      inference('cnf', [status(esa)], [d5_funct_1])).
% 16.27/16.49  thf('40', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 16.27/16.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 16.27/16.49  thf(d1_tarski, axiom,
% 16.27/16.49    (![A:$i,B:$i]:
% 16.27/16.49     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 16.27/16.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 16.27/16.49  thf('41', plain,
% 16.27/16.49      (![X0 : $i, X2 : $i, X3 : $i]:
% 16.27/16.49         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 16.27/16.49      inference('cnf', [status(esa)], [d1_tarski])).
% 16.27/16.49  thf('42', plain,
% 16.27/16.49      (![X0 : $i, X3 : $i]:
% 16.27/16.49         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 16.27/16.49      inference('simplify', [status(thm)], ['41'])).
% 16.27/16.49  thf('43', plain,
% 16.27/16.49      (![X0 : $i, X1 : $i]:
% 16.27/16.49         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0)) | ((X1) = (X0)))),
% 16.27/16.49      inference('sup-', [status(thm)], ['40', '42'])).
% 16.27/16.49  thf('44', plain,
% 16.27/16.49      (![X0 : $i, X1 : $i]:
% 16.27/16.49         (~ (v1_relat_1 @ X1)
% 16.27/16.49          | ~ (v1_funct_1 @ X1)
% 16.27/16.49          | ((k2_tarski @ X0 @ X0) = (k2_relat_1 @ X1))
% 16.27/16.49          | (r2_hidden @ (sk_D @ (k2_tarski @ X0 @ X0) @ X1) @ 
% 16.27/16.49             (k1_relat_1 @ X1))
% 16.27/16.49          | ((sk_C_1 @ (k2_tarski @ X0 @ X0) @ X1) = (X0)))),
% 16.27/16.49      inference('sup-', [status(thm)], ['39', '43'])).
% 16.27/16.49  thf('45', plain,
% 16.27/16.49      (![X0 : $i, X1 : $i]:
% 16.27/16.49         ((r2_hidden @ (sk_D @ (k1_tarski @ X0) @ X1) @ (k1_relat_1 @ X1))
% 16.27/16.49          | ((sk_C_1 @ (k2_tarski @ X0 @ X0) @ X1) = (X0))
% 16.27/16.49          | ((k2_tarski @ X0 @ X0) = (k2_relat_1 @ X1))
% 16.27/16.49          | ~ (v1_funct_1 @ X1)
% 16.27/16.49          | ~ (v1_relat_1 @ X1))),
% 16.27/16.49      inference('sup+', [status(thm)], ['38', '44'])).
% 16.27/16.49  thf('46', plain,
% 16.27/16.49      (![X0 : $i, X1 : $i]:
% 16.27/16.49         (((sk_C_1 @ (k1_tarski @ X0) @ X1) = (X0))
% 16.27/16.49          | ~ (v1_relat_1 @ X1)
% 16.27/16.49          | ~ (v1_funct_1 @ X1)
% 16.27/16.49          | ((k2_tarski @ X0 @ X0) = (k2_relat_1 @ X1))
% 16.27/16.49          | (r2_hidden @ (sk_D @ (k1_tarski @ X0) @ X1) @ (k1_relat_1 @ X1)))),
% 16.27/16.49      inference('sup+', [status(thm)], ['37', '45'])).
% 16.27/16.49  thf(t15_funct_1, conjecture,
% 16.27/16.49    (![A:$i]:
% 16.27/16.49     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 16.27/16.49       ( ![B:$i]:
% 16.27/16.49         ( ?[C:$i]:
% 16.27/16.49           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 16.27/16.49             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 16.27/16.49             ( v1_relat_1 @ C ) ) ) ) ))).
% 16.27/16.49  thf(zf_stmt_0, negated_conjecture,
% 16.27/16.49    (~( ![A:$i]:
% 16.27/16.49        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 16.27/16.49          ( ![B:$i]:
% 16.27/16.49            ( ?[C:$i]:
% 16.27/16.49              ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 16.27/16.49                ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 16.27/16.49                ( v1_relat_1 @ C ) ) ) ) ) )),
% 16.27/16.49    inference('cnf.neg', [status(esa)], [t15_funct_1])).
% 16.27/16.49  thf('47', plain,
% 16.27/16.49      (![X19 : $i]:
% 16.27/16.49         (((k2_relat_1 @ X19) != (k1_tarski @ sk_B))
% 16.27/16.49          | ((k1_relat_1 @ X19) != (sk_A))
% 16.27/16.49          | ~ (v1_funct_1 @ X19)
% 16.27/16.49          | ~ (v1_relat_1 @ X19))),
% 16.27/16.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.27/16.49  thf('48', plain,
% 16.27/16.49      (![X0 : $i, X1 : $i]:
% 16.27/16.49         (((k2_tarski @ X0 @ X0) != (k1_tarski @ sk_B))
% 16.27/16.49          | (r2_hidden @ (sk_D @ (k1_tarski @ X0) @ X1) @ (k1_relat_1 @ X1))
% 16.27/16.49          | ~ (v1_funct_1 @ X1)
% 16.27/16.49          | ~ (v1_relat_1 @ X1)
% 16.27/16.49          | ((sk_C_1 @ (k1_tarski @ X0) @ X1) = (X0))
% 16.27/16.49          | ~ (v1_relat_1 @ X1)
% 16.27/16.49          | ~ (v1_funct_1 @ X1)
% 16.27/16.49          | ((k1_relat_1 @ X1) != (sk_A)))),
% 16.27/16.49      inference('sup-', [status(thm)], ['46', '47'])).
% 16.27/16.49  thf('49', plain,
% 16.27/16.49      (![X0 : $i, X1 : $i]:
% 16.27/16.49         (((k1_relat_1 @ X1) != (sk_A))
% 16.27/16.49          | ((sk_C_1 @ (k1_tarski @ X0) @ X1) = (X0))
% 16.27/16.49          | ~ (v1_relat_1 @ X1)
% 16.27/16.49          | ~ (v1_funct_1 @ X1)
% 16.27/16.49          | (r2_hidden @ (sk_D @ (k1_tarski @ X0) @ X1) @ (k1_relat_1 @ X1))
% 16.27/16.49          | ((k2_tarski @ X0 @ X0) != (k1_tarski @ sk_B)))),
% 16.27/16.49      inference('simplify', [status(thm)], ['48'])).
% 16.27/16.49  thf('50', plain,
% 16.27/16.49      (![X0 : $i, X1 : $i]:
% 16.27/16.49         (((k1_tarski @ X0) != (k1_tarski @ sk_B))
% 16.27/16.49          | (r2_hidden @ (sk_D @ (k1_tarski @ X0) @ X1) @ (k1_relat_1 @ X1))
% 16.27/16.49          | ~ (v1_funct_1 @ X1)
% 16.27/16.49          | ~ (v1_relat_1 @ X1)
% 16.27/16.49          | ((sk_C_1 @ (k1_tarski @ X0) @ X1) = (X0))
% 16.27/16.49          | ((k1_relat_1 @ X1) != (sk_A)))),
% 16.27/16.49      inference('sup-', [status(thm)], ['36', '49'])).
% 16.27/16.49  thf('51', plain,
% 16.27/16.49      (![X0 : $i]:
% 16.27/16.49         (((k1_relat_1 @ X0) != (sk_A))
% 16.27/16.49          | ((sk_C_1 @ (k1_tarski @ sk_B) @ X0) = (sk_B))
% 16.27/16.49          | ~ (v1_relat_1 @ X0)
% 16.27/16.49          | ~ (v1_funct_1 @ X0)
% 16.27/16.49          | (r2_hidden @ (sk_D @ (k1_tarski @ sk_B) @ X0) @ (k1_relat_1 @ X0)))),
% 16.27/16.49      inference('eq_res', [status(thm)], ['50'])).
% 16.27/16.49  thf('52', plain,
% 16.27/16.49      (![X0 : $i, X1 : $i]:
% 16.27/16.49         (((X0) != (sk_A))
% 16.27/16.49          | (r2_hidden @ (sk_D @ (k1_tarski @ sk_B) @ (sk_C_2 @ X1 @ X0)) @ 
% 16.27/16.49             (k1_relat_1 @ (sk_C_2 @ X1 @ X0)))
% 16.27/16.49          | ~ (v1_funct_1 @ (sk_C_2 @ X1 @ X0))
% 16.27/16.49          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0))
% 16.27/16.49          | ((sk_C_1 @ (k1_tarski @ sk_B) @ (sk_C_2 @ X1 @ X0)) = (sk_B)))),
% 16.27/16.49      inference('sup-', [status(thm)], ['35', '51'])).
% 16.27/16.49  thf('53', plain,
% 16.27/16.49      (![X16 : $i, X17 : $i]: ((k1_relat_1 @ (sk_C_2 @ X16 @ X17)) = (X17))),
% 16.27/16.49      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 16.27/16.49  thf('54', plain,
% 16.27/16.49      (![X16 : $i, X17 : $i]: (v1_funct_1 @ (sk_C_2 @ X16 @ X17))),
% 16.27/16.49      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 16.27/16.49  thf('55', plain,
% 16.27/16.49      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (sk_C_2 @ X16 @ X17))),
% 16.27/16.49      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 16.27/16.49  thf('56', plain,
% 16.27/16.49      (![X0 : $i, X1 : $i]:
% 16.27/16.49         (((X0) != (sk_A))
% 16.27/16.49          | (r2_hidden @ (sk_D @ (k1_tarski @ sk_B) @ (sk_C_2 @ X1 @ X0)) @ X0)
% 16.27/16.49          | ((sk_C_1 @ (k1_tarski @ sk_B) @ (sk_C_2 @ X1 @ X0)) = (sk_B)))),
% 16.27/16.49      inference('demod', [status(thm)], ['52', '53', '54', '55'])).
% 16.27/16.49  thf('57', plain,
% 16.27/16.49      (![X1 : $i]:
% 16.27/16.49         (((sk_C_1 @ (k1_tarski @ sk_B) @ (sk_C_2 @ X1 @ sk_A)) = (sk_B))
% 16.27/16.49          | (r2_hidden @ (sk_D @ (k1_tarski @ sk_B) @ (sk_C_2 @ X1 @ sk_A)) @ 
% 16.27/16.49             sk_A))),
% 16.27/16.49      inference('simplify', [status(thm)], ['56'])).
% 16.27/16.49  thf('58', plain,
% 16.27/16.49      (![X16 : $i, X17 : $i, X18 : $i]:
% 16.27/16.49         (((k1_funct_1 @ (sk_C_2 @ X16 @ X17) @ X18) = (X16))
% 16.27/16.49          | ~ (r2_hidden @ X18 @ X17))),
% 16.27/16.49      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 16.27/16.49  thf('59', plain,
% 16.27/16.49      (![X0 : $i, X1 : $i]:
% 16.27/16.49         (((sk_C_1 @ (k1_tarski @ sk_B) @ (sk_C_2 @ X0 @ sk_A)) = (sk_B))
% 16.27/16.49          | ((k1_funct_1 @ (sk_C_2 @ X1 @ sk_A) @ 
% 16.27/16.49              (sk_D @ (k1_tarski @ sk_B) @ (sk_C_2 @ X0 @ sk_A))) = (X1)))),
% 16.27/16.49      inference('sup-', [status(thm)], ['57', '58'])).
% 16.27/16.49  thf('60', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 16.27/16.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 16.27/16.49  thf('61', plain,
% 16.27/16.49      (![X9 : $i, X10 : $i]:
% 16.27/16.49         ((r2_hidden @ (sk_C_1 @ X9 @ X10) @ X9)
% 16.27/16.49          | ((sk_C_1 @ X9 @ X10) = (k1_funct_1 @ X10 @ (sk_D @ X9 @ X10)))
% 16.27/16.49          | ((X9) = (k2_relat_1 @ X10))
% 16.27/16.49          | ~ (v1_funct_1 @ X10)
% 16.27/16.49          | ~ (v1_relat_1 @ X10))),
% 16.27/16.49      inference('cnf', [status(esa)], [d5_funct_1])).
% 16.27/16.49  thf('62', plain,
% 16.27/16.49      (![X0 : $i, X1 : $i]:
% 16.27/16.49         (~ (r2_hidden @ X1 @ (k2_tarski @ X0 @ X0)) | ((X1) = (X0)))),
% 16.27/16.49      inference('sup-', [status(thm)], ['40', '42'])).
% 16.27/16.49  thf('63', plain,
% 16.27/16.49      (![X0 : $i, X1 : $i]:
% 16.27/16.49         (~ (v1_relat_1 @ X1)
% 16.27/16.49          | ~ (v1_funct_1 @ X1)
% 16.27/16.49          | ((k2_tarski @ X0 @ X0) = (k2_relat_1 @ X1))
% 16.27/16.49          | ((sk_C_1 @ (k2_tarski @ X0 @ X0) @ X1)
% 16.27/16.49              = (k1_funct_1 @ X1 @ (sk_D @ (k2_tarski @ X0 @ X0) @ X1)))
% 16.27/16.49          | ((sk_C_1 @ (k2_tarski @ X0 @ X0) @ X1) = (X0)))),
% 16.27/16.49      inference('sup-', [status(thm)], ['61', '62'])).
% 16.27/16.49  thf('64', plain,
% 16.27/16.49      (![X0 : $i, X1 : $i]:
% 16.27/16.49         (((sk_C_1 @ (k2_tarski @ X0 @ X0) @ X1)
% 16.27/16.49            = (k1_funct_1 @ X1 @ (sk_D @ (k1_tarski @ X0) @ X1)))
% 16.27/16.49          | ((sk_C_1 @ (k2_tarski @ X0 @ X0) @ X1) = (X0))
% 16.27/16.49          | ((k2_tarski @ X0 @ X0) = (k2_relat_1 @ X1))
% 16.27/16.49          | ~ (v1_funct_1 @ X1)
% 16.27/16.49          | ~ (v1_relat_1 @ X1))),
% 16.27/16.49      inference('sup+', [status(thm)], ['60', '63'])).
% 16.27/16.49  thf('65', plain,
% 16.27/16.49      (![X0 : $i, X1 : $i]:
% 16.27/16.49         (((k1_funct_1 @ X0 @ (sk_D @ (k1_tarski @ X1) @ X0)) != (X1))
% 16.27/16.49          | ~ (v1_relat_1 @ X0)
% 16.27/16.49          | ~ (v1_funct_1 @ X0)
% 16.27/16.49          | ((k2_tarski @ X1 @ X1) = (k2_relat_1 @ X0))
% 16.27/16.49          | ((sk_C_1 @ (k2_tarski @ X1 @ X1) @ X0) = (X1)))),
% 16.27/16.49      inference('eq_fact', [status(thm)], ['64'])).
% 16.27/16.49  thf('66', plain,
% 16.27/16.49      (![X0 : $i]:
% 16.27/16.49         (((X0) != (sk_B))
% 16.27/16.49          | ((sk_C_1 @ (k1_tarski @ sk_B) @ (sk_C_2 @ X0 @ sk_A)) = (sk_B))
% 16.27/16.49          | ((sk_C_1 @ (k2_tarski @ sk_B @ sk_B) @ (sk_C_2 @ X0 @ sk_A))
% 16.27/16.49              = (sk_B))
% 16.27/16.49          | ((k2_tarski @ sk_B @ sk_B) = (k2_relat_1 @ (sk_C_2 @ X0 @ sk_A)))
% 16.27/16.49          | ~ (v1_funct_1 @ (sk_C_2 @ X0 @ sk_A))
% 16.27/16.49          | ~ (v1_relat_1 @ (sk_C_2 @ X0 @ sk_A)))),
% 16.27/16.49      inference('sup-', [status(thm)], ['59', '65'])).
% 16.27/16.49  thf('67', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 16.27/16.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 16.27/16.49  thf('68', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 16.27/16.49      inference('cnf', [status(esa)], [t69_enumset1])).
% 16.27/16.49  thf('69', plain,
% 16.27/16.49      (![X16 : $i, X17 : $i]: (v1_funct_1 @ (sk_C_2 @ X16 @ X17))),
% 16.27/16.49      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 16.27/16.49  thf('70', plain,
% 16.27/16.49      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (sk_C_2 @ X16 @ X17))),
% 16.27/16.49      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 16.27/16.49  thf('71', plain,
% 16.27/16.49      (![X0 : $i]:
% 16.27/16.49         (((X0) != (sk_B))
% 16.27/16.49          | ((sk_C_1 @ (k1_tarski @ sk_B) @ (sk_C_2 @ X0 @ sk_A)) = (sk_B))
% 16.27/16.49          | ((sk_C_1 @ (k1_tarski @ sk_B) @ (sk_C_2 @ X0 @ sk_A)) = (sk_B))
% 16.27/16.49          | ((k1_tarski @ sk_B) = (k2_relat_1 @ (sk_C_2 @ X0 @ sk_A))))),
% 16.27/16.49      inference('demod', [status(thm)], ['66', '67', '68', '69', '70'])).
% 16.27/16.49  thf('72', plain,
% 16.27/16.49      ((((k1_tarski @ sk_B) = (k2_relat_1 @ (sk_C_2 @ sk_B @ sk_A)))
% 16.27/16.49        | ((sk_C_1 @ (k1_tarski @ sk_B) @ (sk_C_2 @ sk_B @ sk_A)) = (sk_B)))),
% 16.27/16.49      inference('simplify', [status(thm)], ['71'])).
% 16.27/16.49  thf('73', plain,
% 16.27/16.49      ((((k1_tarski @ sk_B) = (k2_relat_1 @ (sk_C_2 @ sk_B @ sk_A)))
% 16.27/16.49        | ((sk_C_1 @ (k1_tarski @ sk_B) @ (sk_C_2 @ sk_B @ sk_A)) = (sk_B)))),
% 16.27/16.49      inference('simplify', [status(thm)], ['71'])).
% 16.27/16.49  thf('74', plain,
% 16.27/16.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 16.27/16.49         (~ (r2_hidden @ (sk_C_1 @ X9 @ X10) @ X9)
% 16.27/16.49          | ((sk_C_1 @ X9 @ X10) != (k1_funct_1 @ X10 @ X11))
% 16.27/16.49          | ~ (r2_hidden @ X11 @ (k1_relat_1 @ X10))
% 16.27/16.49          | ((X9) = (k2_relat_1 @ X10))
% 16.27/16.49          | ~ (v1_funct_1 @ X10)
% 16.27/16.49          | ~ (v1_relat_1 @ X10))),
% 16.27/16.49      inference('cnf', [status(esa)], [d5_funct_1])).
% 16.27/16.49  thf('75', plain,
% 16.27/16.49      (![X0 : $i]:
% 16.27/16.49         (~ (r2_hidden @ sk_B @ (k1_tarski @ sk_B))
% 16.27/16.49          | ((k1_tarski @ sk_B) = (k2_relat_1 @ (sk_C_2 @ sk_B @ sk_A)))
% 16.27/16.49          | ~ (v1_relat_1 @ (sk_C_2 @ sk_B @ sk_A))
% 16.27/16.49          | ~ (v1_funct_1 @ (sk_C_2 @ sk_B @ sk_A))
% 16.27/16.49          | ((k1_tarski @ sk_B) = (k2_relat_1 @ (sk_C_2 @ sk_B @ sk_A)))
% 16.27/16.49          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ (sk_C_2 @ sk_B @ sk_A)))
% 16.27/16.49          | ((sk_C_1 @ (k1_tarski @ sk_B) @ (sk_C_2 @ sk_B @ sk_A))
% 16.27/16.49              != (k1_funct_1 @ (sk_C_2 @ sk_B @ sk_A) @ X0)))),
% 16.27/16.49      inference('sup-', [status(thm)], ['73', '74'])).
% 16.27/16.49  thf('76', plain,
% 16.27/16.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.27/16.49         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 16.27/16.49      inference('cnf', [status(esa)], [d1_tarski])).
% 16.27/16.49  thf('77', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 16.27/16.49      inference('simplify', [status(thm)], ['76'])).
% 16.27/16.49  thf('78', plain,
% 16.27/16.49      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (sk_C_2 @ X16 @ X17))),
% 16.27/16.49      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 16.27/16.49  thf('79', plain,
% 16.27/16.49      (![X16 : $i, X17 : $i]: (v1_funct_1 @ (sk_C_2 @ X16 @ X17))),
% 16.27/16.49      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 16.27/16.49  thf('80', plain,
% 16.27/16.49      (![X16 : $i, X17 : $i]: ((k1_relat_1 @ (sk_C_2 @ X16 @ X17)) = (X17))),
% 16.27/16.49      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 16.27/16.49  thf('81', plain,
% 16.27/16.49      (![X0 : $i]:
% 16.27/16.49         (((k1_tarski @ sk_B) = (k2_relat_1 @ (sk_C_2 @ sk_B @ sk_A)))
% 16.27/16.49          | ((k1_tarski @ sk_B) = (k2_relat_1 @ (sk_C_2 @ sk_B @ sk_A)))
% 16.27/16.49          | ~ (r2_hidden @ X0 @ sk_A)
% 16.27/16.49          | ((sk_C_1 @ (k1_tarski @ sk_B) @ (sk_C_2 @ sk_B @ sk_A))
% 16.27/16.49              != (k1_funct_1 @ (sk_C_2 @ sk_B @ sk_A) @ X0)))),
% 16.27/16.49      inference('demod', [status(thm)], ['75', '77', '78', '79', '80'])).
% 16.27/16.49  thf('82', plain,
% 16.27/16.49      (![X0 : $i]:
% 16.27/16.49         (((sk_C_1 @ (k1_tarski @ sk_B) @ (sk_C_2 @ sk_B @ sk_A))
% 16.27/16.49            != (k1_funct_1 @ (sk_C_2 @ sk_B @ sk_A) @ X0))
% 16.27/16.49          | ~ (r2_hidden @ X0 @ sk_A)
% 16.27/16.49          | ((k1_tarski @ sk_B) = (k2_relat_1 @ (sk_C_2 @ sk_B @ sk_A))))),
% 16.27/16.49      inference('simplify', [status(thm)], ['81'])).
% 16.27/16.49  thf('83', plain,
% 16.27/16.49      (![X0 : $i]:
% 16.27/16.49         (((sk_B) != (k1_funct_1 @ (sk_C_2 @ sk_B @ sk_A) @ X0))
% 16.27/16.49          | ((k1_tarski @ sk_B) = (k2_relat_1 @ (sk_C_2 @ sk_B @ sk_A)))
% 16.27/16.49          | ((k1_tarski @ sk_B) = (k2_relat_1 @ (sk_C_2 @ sk_B @ sk_A)))
% 16.27/16.49          | ~ (r2_hidden @ X0 @ sk_A))),
% 16.27/16.49      inference('sup-', [status(thm)], ['72', '82'])).
% 16.27/16.49  thf('84', plain,
% 16.27/16.49      (![X0 : $i]:
% 16.27/16.49         (~ (r2_hidden @ X0 @ sk_A)
% 16.27/16.49          | ((k1_tarski @ sk_B) = (k2_relat_1 @ (sk_C_2 @ sk_B @ sk_A)))
% 16.27/16.49          | ((sk_B) != (k1_funct_1 @ (sk_C_2 @ sk_B @ sk_A) @ X0)))),
% 16.27/16.49      inference('simplify', [status(thm)], ['83'])).
% 16.27/16.49  thf('85', plain,
% 16.27/16.49      (![X16 : $i, X17 : $i, X18 : $i]:
% 16.27/16.49         (((k1_funct_1 @ (sk_C_2 @ X16 @ X17) @ X18) = (X16))
% 16.27/16.49          | ~ (r2_hidden @ X18 @ X17))),
% 16.27/16.49      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 16.27/16.49  thf('86', plain,
% 16.27/16.49      (![X0 : $i]:
% 16.27/16.49         (((k1_tarski @ sk_B) = (k2_relat_1 @ (sk_C_2 @ sk_B @ sk_A)))
% 16.27/16.49          | ~ (r2_hidden @ X0 @ sk_A))),
% 16.27/16.49      inference('clc', [status(thm)], ['84', '85'])).
% 16.27/16.49  thf('87', plain,
% 16.27/16.49      ((((sk_A) = (k1_xboole_0))
% 16.27/16.49        | ((k1_tarski @ sk_B) = (k2_relat_1 @ (sk_C_2 @ sk_B @ sk_A))))),
% 16.27/16.49      inference('sup-', [status(thm)], ['34', '86'])).
% 16.27/16.49  thf('88', plain, (((sk_A) != (k1_xboole_0))),
% 16.27/16.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.27/16.49  thf('89', plain,
% 16.27/16.49      (((k1_tarski @ sk_B) = (k2_relat_1 @ (sk_C_2 @ sk_B @ sk_A)))),
% 16.27/16.49      inference('simplify_reflect-', [status(thm)], ['87', '88'])).
% 16.27/16.49  thf('90', plain,
% 16.27/16.49      (![X19 : $i]:
% 16.27/16.49         (((k2_relat_1 @ X19) != (k1_tarski @ sk_B))
% 16.27/16.49          | ((k1_relat_1 @ X19) != (sk_A))
% 16.27/16.49          | ~ (v1_funct_1 @ X19)
% 16.27/16.49          | ~ (v1_relat_1 @ X19))),
% 16.27/16.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.27/16.49  thf('91', plain,
% 16.27/16.49      ((((k1_tarski @ sk_B) != (k1_tarski @ sk_B))
% 16.27/16.49        | ~ (v1_relat_1 @ (sk_C_2 @ sk_B @ sk_A))
% 16.27/16.49        | ~ (v1_funct_1 @ (sk_C_2 @ sk_B @ sk_A))
% 16.27/16.49        | ((k1_relat_1 @ (sk_C_2 @ sk_B @ sk_A)) != (sk_A)))),
% 16.27/16.49      inference('sup-', [status(thm)], ['89', '90'])).
% 16.27/16.49  thf('92', plain,
% 16.27/16.49      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (sk_C_2 @ X16 @ X17))),
% 16.27/16.49      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 16.27/16.49  thf('93', plain,
% 16.27/16.49      (![X16 : $i, X17 : $i]: (v1_funct_1 @ (sk_C_2 @ X16 @ X17))),
% 16.27/16.49      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 16.27/16.49  thf('94', plain,
% 16.27/16.49      (![X16 : $i, X17 : $i]: ((k1_relat_1 @ (sk_C_2 @ X16 @ X17)) = (X17))),
% 16.27/16.49      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 16.27/16.49  thf('95', plain,
% 16.27/16.49      ((((k1_tarski @ sk_B) != (k1_tarski @ sk_B)) | ((sk_A) != (sk_A)))),
% 16.27/16.49      inference('demod', [status(thm)], ['91', '92', '93', '94'])).
% 16.27/16.49  thf('96', plain, ($false), inference('simplify', [status(thm)], ['95'])).
% 16.27/16.49  
% 16.27/16.49  % SZS output end Refutation
% 16.27/16.49  
% 16.34/16.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
