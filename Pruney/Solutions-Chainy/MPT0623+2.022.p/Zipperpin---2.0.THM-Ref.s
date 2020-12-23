%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.C6YfhWZpYw

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:38 EST 2020

% Result     : Theorem 26.39s
% Output     : Refutation 26.39s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 947 expanded)
%              Number of leaves         :   21 ( 296 expanded)
%              Depth                    :   24
%              Number of atoms          : 1118 (9723 expanded)
%              Number of equality atoms :  119 (1233 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ! [X15: $i,X16: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) )
      = X16 ) ),
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
    ! [X7: $i] :
      ( ( ( k1_relat_1 @ X7 )
       != k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ( ( sk_C_2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X1: $i] :
      ( ( ( sk_C_2 @ X1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('5',plain,(
    ! [X1: $i] :
      ( ( sk_C_2 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) )
      = X16 ) ),
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
    ! [X8: $i,X9: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X8 @ X9 ) @ X8 )
      | ( r2_hidden @ ( sk_D @ X8 @ X9 ) @ ( k1_relat_1 @ X9 ) )
      | ( X8
        = ( k2_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
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
    inference(demod,[status(thm)],['3','4'])).

thf('11',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('12',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X1: $i] :
      ( ( sk_C_2 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
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

thf('17',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['5','6'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('19',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ( X11
       != ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ ( sk_D_1 @ X12 @ X9 ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('20',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( r2_hidden @ ( sk_D_1 @ X12 @ X9 ) @ ( k1_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ k1_xboole_0 ) ) @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['17','21'])).

thf('23',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['10','11'])).

thf('24',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['13','14'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ k1_xboole_0 ) ) @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X15 @ X16 ) @ X17 )
        = X15 )
      | ~ ( r2_hidden @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X1 @ k1_xboole_0 ) @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ k1_xboole_0 ) ) @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X1: $i] :
      ( ( sk_C_2 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ k1_xboole_0 ) ) @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ k1_xboole_0 ) ) @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X2 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X1: $i] :
      ( ( sk_C_2 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('34',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('35',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X15 @ X16 ) @ X17 )
        = X15 )
      | ~ ( r2_hidden @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X2 @ X0 ) @ ( sk_C @ X1 @ X0 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ X1 @ k1_xboole_0 ) )
        = X0 )
      | ( r1_tarski @ k1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ X1 @ k1_xboole_0 ) )
        = X0 )
      | ( r1_tarski @ k1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['33','36'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( r1_tarski @ k1_xboole_0 @ X2 )
      | ( r1_tarski @ k1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X2 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('41',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 = X2 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( ( k2_relat_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['32','43'])).

thf('45',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(condensation,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['16','45'])).

thf('47',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X15 @ X16 ) @ X17 )
        = X15 )
      | ~ ( r2_hidden @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X1 @ k1_xboole_0 ) @ ( sk_D @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X1: $i] :
      ( ( sk_C_2 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( X2 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ k1_xboole_0 ) @ X2 )
      | ( X2 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ k1_xboole_0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X2 @ k1_xboole_0 ) @ X2 )
      | ( X2 = k1_xboole_0 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['53'])).

thf('55',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('56',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ( X11
       != ( k2_relat_1 @ X9 ) )
      | ( X12
        = ( k1_funct_1 @ X9 @ ( sk_D_1 @ X12 @ X9 ) ) )
      | ~ ( r2_hidden @ X12 @ X11 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('57',plain,(
    ! [X9: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k2_relat_1 @ X9 ) )
      | ( X12
        = ( k1_funct_1 @ X9 @ ( sk_D_1 @ X12 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('61',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X15 @ X16 ) @ X17 )
        = X15 )
      | ~ ( r2_hidden @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X2 @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) @ ( sk_D_1 @ ( sk_C @ X3 @ ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) ) @ ( sk_C_2 @ X2 @ X0 ) ) )
        = X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) @ X3 )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('65',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) @ ( sk_D_1 @ ( sk_C @ X3 @ ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) ) @ ( sk_C_2 @ X2 @ X0 ) ) )
        = X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) @ X3 ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
        = X1 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['58','66'])).

thf('68',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('69',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
        = X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 )
      | ( ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['70'])).

thf('72',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('73',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) ) @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['54','74'])).

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

thf('76',plain,(
    ! [X18: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ sk_A )
      | ( sk_B
       != ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('79',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('80',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X15 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( sk_B != X0 ) ) ),
    inference(demod,[status(thm)],['77','78','79','80'])).

thf('82',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['81'])).

thf('83',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['83'])).

thf('85',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('86',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['83'])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X2 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('89',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( X1 = X2 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['83'])).

thf('91',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(condensation,[status(thm)],['44'])).

thf('92',plain,(
    ! [X18: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ sk_A )
      | ( sk_B
       != ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B
     != ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['10','11'])).

thf('95',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['13','14'])).

thf('96',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['5','6'])).

thf('97',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ( sk_B != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['93','94','95','96'])).

thf('98',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_A )
      | ( sk_B != k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['90','97'])).

thf('99',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['83'])).

thf('100',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_A )
      | ( sk_B != sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,
    ( ! [X0: $i,X1: $i] : ( X0 = X1 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['89','101'])).

thf('103',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['100'])).

thf('104',plain,
    ( ! [X0: $i] :
        ~ ( r1_tarski @ sk_B @ X0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    sk_B != k1_xboole_0 ),
    inference('sup-',[status(thm)],['86','104'])).

thf('106',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['83'])).

thf('107',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['105','106'])).

thf('108',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['84','107'])).

thf('109',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['82','108'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.C6YfhWZpYw
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:40:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 26.39/26.60  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 26.39/26.60  % Solved by: fo/fo7.sh
% 26.39/26.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 26.39/26.60  % done 4707 iterations in 26.137s
% 26.39/26.60  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 26.39/26.60  % SZS output start Refutation
% 26.39/26.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 26.39/26.60  thf(sk_A_type, type, sk_A: $i).
% 26.39/26.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 26.39/26.60  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 26.39/26.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 26.39/26.60  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 26.39/26.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 26.39/26.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 26.39/26.60  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 26.39/26.60  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 26.39/26.60  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 26.39/26.60  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 26.39/26.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 26.39/26.60  thf(sk_B_type, type, sk_B: $i).
% 26.39/26.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 26.39/26.60  thf(s3_funct_1__e2_24__funct_1, axiom,
% 26.39/26.60    (![A:$i,B:$i]:
% 26.39/26.60     ( ?[C:$i]:
% 26.39/26.60       ( ( ![D:$i]:
% 26.39/26.60           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 26.39/26.60         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 26.39/26.60         ( v1_relat_1 @ C ) ) ))).
% 26.39/26.60  thf('0', plain,
% 26.39/26.60      (![X15 : $i, X16 : $i]: ((k1_relat_1 @ (sk_C_2 @ X15 @ X16)) = (X16))),
% 26.39/26.60      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 26.39/26.60  thf(t64_relat_1, axiom,
% 26.39/26.60    (![A:$i]:
% 26.39/26.60     ( ( v1_relat_1 @ A ) =>
% 26.39/26.60       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 26.39/26.60           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 26.39/26.60         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 26.39/26.60  thf('1', plain,
% 26.39/26.60      (![X7 : $i]:
% 26.39/26.60         (((k1_relat_1 @ X7) != (k1_xboole_0))
% 26.39/26.60          | ((X7) = (k1_xboole_0))
% 26.39/26.60          | ~ (v1_relat_1 @ X7))),
% 26.39/26.60      inference('cnf', [status(esa)], [t64_relat_1])).
% 26.39/26.60  thf('2', plain,
% 26.39/26.60      (![X0 : $i, X1 : $i]:
% 26.39/26.60         (((X0) != (k1_xboole_0))
% 26.39/26.60          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0))
% 26.39/26.60          | ((sk_C_2 @ X1 @ X0) = (k1_xboole_0)))),
% 26.39/26.60      inference('sup-', [status(thm)], ['0', '1'])).
% 26.39/26.60  thf('3', plain,
% 26.39/26.60      (![X1 : $i]:
% 26.39/26.60         (((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))
% 26.39/26.60          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ k1_xboole_0)))),
% 26.39/26.60      inference('simplify', [status(thm)], ['2'])).
% 26.39/26.60  thf('4', plain, (![X15 : $i, X16 : $i]: (v1_relat_1 @ (sk_C_2 @ X15 @ X16))),
% 26.39/26.60      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 26.39/26.60  thf('5', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 26.39/26.60      inference('demod', [status(thm)], ['3', '4'])).
% 26.39/26.60  thf('6', plain,
% 26.39/26.60      (![X15 : $i, X16 : $i]: ((k1_relat_1 @ (sk_C_2 @ X15 @ X16)) = (X16))),
% 26.39/26.60      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 26.39/26.60  thf('7', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 26.39/26.60      inference('sup+', [status(thm)], ['5', '6'])).
% 26.39/26.60  thf(d5_funct_1, axiom,
% 26.39/26.60    (![A:$i]:
% 26.39/26.60     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 26.39/26.60       ( ![B:$i]:
% 26.39/26.60         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 26.39/26.60           ( ![C:$i]:
% 26.39/26.60             ( ( r2_hidden @ C @ B ) <=>
% 26.39/26.60               ( ?[D:$i]:
% 26.39/26.60                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 26.39/26.60                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 26.39/26.60  thf('8', plain,
% 26.39/26.60      (![X8 : $i, X9 : $i]:
% 26.39/26.60         ((r2_hidden @ (sk_C_1 @ X8 @ X9) @ X8)
% 26.39/26.60          | (r2_hidden @ (sk_D @ X8 @ X9) @ (k1_relat_1 @ X9))
% 26.39/26.60          | ((X8) = (k2_relat_1 @ X9))
% 26.39/26.60          | ~ (v1_funct_1 @ X9)
% 26.39/26.60          | ~ (v1_relat_1 @ X9))),
% 26.39/26.60      inference('cnf', [status(esa)], [d5_funct_1])).
% 26.39/26.60  thf('9', plain,
% 26.39/26.60      (![X0 : $i]:
% 26.39/26.60         ((r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 26.39/26.60          | ~ (v1_relat_1 @ k1_xboole_0)
% 26.39/26.60          | ~ (v1_funct_1 @ k1_xboole_0)
% 26.39/26.60          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 26.39/26.60          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 26.39/26.60      inference('sup+', [status(thm)], ['7', '8'])).
% 26.39/26.60  thf('10', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 26.39/26.60      inference('demod', [status(thm)], ['3', '4'])).
% 26.39/26.60  thf('11', plain,
% 26.39/26.60      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (sk_C_2 @ X15 @ X16))),
% 26.39/26.60      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 26.39/26.60  thf('12', plain, ((v1_relat_1 @ k1_xboole_0)),
% 26.39/26.60      inference('sup+', [status(thm)], ['10', '11'])).
% 26.39/26.60  thf('13', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 26.39/26.60      inference('demod', [status(thm)], ['3', '4'])).
% 26.39/26.60  thf('14', plain,
% 26.39/26.60      (![X15 : $i, X16 : $i]: (v1_funct_1 @ (sk_C_2 @ X15 @ X16))),
% 26.39/26.60      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 26.39/26.60  thf('15', plain, ((v1_funct_1 @ k1_xboole_0)),
% 26.39/26.60      inference('sup+', [status(thm)], ['13', '14'])).
% 26.39/26.60  thf('16', plain,
% 26.39/26.60      (![X0 : $i]:
% 26.39/26.60         ((r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 26.39/26.60          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 26.39/26.60          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 26.39/26.60      inference('demod', [status(thm)], ['9', '12', '15'])).
% 26.39/26.60  thf('17', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 26.39/26.60      inference('sup+', [status(thm)], ['5', '6'])).
% 26.39/26.60  thf(d3_tarski, axiom,
% 26.39/26.60    (![A:$i,B:$i]:
% 26.39/26.60     ( ( r1_tarski @ A @ B ) <=>
% 26.39/26.60       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 26.39/26.60  thf('18', plain,
% 26.39/26.60      (![X1 : $i, X3 : $i]:
% 26.39/26.60         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 26.39/26.60      inference('cnf', [status(esa)], [d3_tarski])).
% 26.39/26.60  thf('19', plain,
% 26.39/26.60      (![X9 : $i, X11 : $i, X12 : $i]:
% 26.39/26.60         (((X11) != (k2_relat_1 @ X9))
% 26.39/26.60          | (r2_hidden @ (sk_D_1 @ X12 @ X9) @ (k1_relat_1 @ X9))
% 26.39/26.60          | ~ (r2_hidden @ X12 @ X11)
% 26.39/26.60          | ~ (v1_funct_1 @ X9)
% 26.39/26.60          | ~ (v1_relat_1 @ X9))),
% 26.39/26.60      inference('cnf', [status(esa)], [d5_funct_1])).
% 26.39/26.60  thf('20', plain,
% 26.39/26.60      (![X9 : $i, X12 : $i]:
% 26.39/26.60         (~ (v1_relat_1 @ X9)
% 26.39/26.60          | ~ (v1_funct_1 @ X9)
% 26.39/26.60          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 26.39/26.60          | (r2_hidden @ (sk_D_1 @ X12 @ X9) @ (k1_relat_1 @ X9)))),
% 26.39/26.60      inference('simplify', [status(thm)], ['19'])).
% 26.39/26.60  thf('21', plain,
% 26.39/26.60      (![X0 : $i, X1 : $i]:
% 26.39/26.60         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 26.39/26.60          | (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 26.39/26.60             (k1_relat_1 @ X0))
% 26.39/26.60          | ~ (v1_funct_1 @ X0)
% 26.39/26.60          | ~ (v1_relat_1 @ X0))),
% 26.39/26.60      inference('sup-', [status(thm)], ['18', '20'])).
% 26.39/26.60  thf('22', plain,
% 26.39/26.60      (![X0 : $i]:
% 26.39/26.60         ((r2_hidden @ 
% 26.39/26.60           (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ k1_xboole_0)) @ k1_xboole_0) @ 
% 26.39/26.60           k1_xboole_0)
% 26.39/26.60          | ~ (v1_relat_1 @ k1_xboole_0)
% 26.39/26.60          | ~ (v1_funct_1 @ k1_xboole_0)
% 26.39/26.60          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0))),
% 26.39/26.60      inference('sup+', [status(thm)], ['17', '21'])).
% 26.39/26.60  thf('23', plain, ((v1_relat_1 @ k1_xboole_0)),
% 26.39/26.60      inference('sup+', [status(thm)], ['10', '11'])).
% 26.39/26.60  thf('24', plain, ((v1_funct_1 @ k1_xboole_0)),
% 26.39/26.60      inference('sup+', [status(thm)], ['13', '14'])).
% 26.39/26.60  thf('25', plain,
% 26.39/26.60      (![X0 : $i]:
% 26.39/26.60         ((r2_hidden @ 
% 26.39/26.60           (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ k1_xboole_0)) @ k1_xboole_0) @ 
% 26.39/26.60           k1_xboole_0)
% 26.39/26.60          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0))),
% 26.39/26.60      inference('demod', [status(thm)], ['22', '23', '24'])).
% 26.39/26.60  thf('26', plain,
% 26.39/26.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 26.39/26.60         (((k1_funct_1 @ (sk_C_2 @ X15 @ X16) @ X17) = (X15))
% 26.39/26.60          | ~ (r2_hidden @ X17 @ X16))),
% 26.39/26.60      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 26.39/26.60  thf('27', plain,
% 26.39/26.60      (![X0 : $i, X1 : $i]:
% 26.39/26.60         ((r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)
% 26.39/26.60          | ((k1_funct_1 @ (sk_C_2 @ X1 @ k1_xboole_0) @ 
% 26.39/26.60              (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ k1_xboole_0)) @ k1_xboole_0))
% 26.39/26.60              = (X1)))),
% 26.39/26.60      inference('sup-', [status(thm)], ['25', '26'])).
% 26.39/26.60  thf('28', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 26.39/26.60      inference('demod', [status(thm)], ['3', '4'])).
% 26.39/26.60  thf('29', plain,
% 26.39/26.60      (![X0 : $i, X1 : $i]:
% 26.39/26.60         ((r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)
% 26.39/26.60          | ((k1_funct_1 @ k1_xboole_0 @ 
% 26.39/26.60              (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ k1_xboole_0)) @ k1_xboole_0))
% 26.39/26.60              = (X1)))),
% 26.39/26.60      inference('demod', [status(thm)], ['27', '28'])).
% 26.39/26.60  thf('30', plain,
% 26.39/26.60      (![X0 : $i, X1 : $i]:
% 26.39/26.60         ((r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)
% 26.39/26.60          | ((k1_funct_1 @ k1_xboole_0 @ 
% 26.39/26.60              (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ k1_xboole_0)) @ k1_xboole_0))
% 26.39/26.60              = (X1)))),
% 26.39/26.60      inference('demod', [status(thm)], ['27', '28'])).
% 26.39/26.60  thf('31', plain,
% 26.39/26.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.39/26.60         (((X0) = (X1))
% 26.39/26.60          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X2)
% 26.39/26.60          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X2))),
% 26.39/26.60      inference('sup+', [status(thm)], ['29', '30'])).
% 26.39/26.60  thf('32', plain,
% 26.39/26.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.39/26.60         ((r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X2) | ((X0) = (X1)))),
% 26.39/26.60      inference('simplify', [status(thm)], ['31'])).
% 26.39/26.60  thf('33', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 26.39/26.60      inference('demod', [status(thm)], ['3', '4'])).
% 26.39/26.60  thf('34', plain,
% 26.39/26.60      (![X1 : $i, X3 : $i]:
% 26.39/26.60         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 26.39/26.60      inference('cnf', [status(esa)], [d3_tarski])).
% 26.39/26.60  thf('35', plain,
% 26.39/26.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 26.39/26.60         (((k1_funct_1 @ (sk_C_2 @ X15 @ X16) @ X17) = (X15))
% 26.39/26.60          | ~ (r2_hidden @ X17 @ X16))),
% 26.39/26.60      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 26.39/26.60  thf('36', plain,
% 26.39/26.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.39/26.60         ((r1_tarski @ X0 @ X1)
% 26.39/26.60          | ((k1_funct_1 @ (sk_C_2 @ X2 @ X0) @ (sk_C @ X1 @ X0)) = (X2)))),
% 26.39/26.60      inference('sup-', [status(thm)], ['34', '35'])).
% 26.39/26.60  thf('37', plain,
% 26.39/26.60      (![X0 : $i, X1 : $i]:
% 26.39/26.60         (((k1_funct_1 @ k1_xboole_0 @ (sk_C @ X1 @ k1_xboole_0)) = (X0))
% 26.39/26.60          | (r1_tarski @ k1_xboole_0 @ X1))),
% 26.39/26.60      inference('sup+', [status(thm)], ['33', '36'])).
% 26.39/26.60  thf('38', plain,
% 26.39/26.60      (![X0 : $i, X1 : $i]:
% 26.39/26.60         (((k1_funct_1 @ k1_xboole_0 @ (sk_C @ X1 @ k1_xboole_0)) = (X0))
% 26.39/26.60          | (r1_tarski @ k1_xboole_0 @ X1))),
% 26.39/26.60      inference('sup+', [status(thm)], ['33', '36'])).
% 26.39/26.60  thf('39', plain,
% 26.39/26.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.39/26.60         (((X0) = (X1))
% 26.39/26.60          | (r1_tarski @ k1_xboole_0 @ X2)
% 26.39/26.60          | (r1_tarski @ k1_xboole_0 @ X2))),
% 26.39/26.60      inference('sup+', [status(thm)], ['37', '38'])).
% 26.39/26.60  thf('40', plain,
% 26.39/26.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.39/26.60         ((r1_tarski @ k1_xboole_0 @ X2) | ((X0) = (X1)))),
% 26.39/26.60      inference('simplify', [status(thm)], ['39'])).
% 26.39/26.60  thf(d10_xboole_0, axiom,
% 26.39/26.60    (![A:$i,B:$i]:
% 26.39/26.60     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 26.39/26.60  thf('41', plain,
% 26.39/26.60      (![X4 : $i, X6 : $i]:
% 26.39/26.60         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 26.39/26.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 26.39/26.60  thf('42', plain,
% 26.39/26.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.39/26.60         (((X1) = (X2))
% 26.39/26.60          | ~ (r1_tarski @ X0 @ k1_xboole_0)
% 26.39/26.60          | ((X0) = (k1_xboole_0)))),
% 26.39/26.60      inference('sup-', [status(thm)], ['40', '41'])).
% 26.39/26.60  thf('43', plain,
% 26.39/26.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 26.39/26.60      inference('condensation', [status(thm)], ['42'])).
% 26.39/26.60  thf('44', plain,
% 26.39/26.60      (![X0 : $i, X1 : $i]:
% 26.39/26.60         (((X0) = (X1)) | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 26.39/26.60      inference('sup-', [status(thm)], ['32', '43'])).
% 26.39/26.60  thf('45', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 26.39/26.60      inference('condensation', [status(thm)], ['44'])).
% 26.39/26.60  thf('46', plain,
% 26.39/26.60      (![X0 : $i]:
% 26.39/26.60         ((r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 26.39/26.60          | ((X0) = (k1_xboole_0))
% 26.39/26.60          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 26.39/26.60      inference('demod', [status(thm)], ['16', '45'])).
% 26.39/26.60  thf('47', plain,
% 26.39/26.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 26.39/26.60         (((k1_funct_1 @ (sk_C_2 @ X15 @ X16) @ X17) = (X15))
% 26.39/26.60          | ~ (r2_hidden @ X17 @ X16))),
% 26.39/26.60      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 26.39/26.60  thf('48', plain,
% 26.39/26.60      (![X0 : $i, X1 : $i]:
% 26.39/26.60         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 26.39/26.60          | ((X0) = (k1_xboole_0))
% 26.39/26.60          | ((k1_funct_1 @ (sk_C_2 @ X1 @ k1_xboole_0) @ 
% 26.39/26.60              (sk_D @ X0 @ k1_xboole_0)) = (X1)))),
% 26.39/26.60      inference('sup-', [status(thm)], ['46', '47'])).
% 26.39/26.60  thf('49', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 26.39/26.60      inference('demod', [status(thm)], ['3', '4'])).
% 26.39/26.60  thf('50', plain,
% 26.39/26.60      (![X0 : $i, X1 : $i]:
% 26.39/26.60         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 26.39/26.60          | ((X0) = (k1_xboole_0))
% 26.39/26.60          | ((k1_funct_1 @ k1_xboole_0 @ (sk_D @ X0 @ k1_xboole_0)) = (X1)))),
% 26.39/26.60      inference('demod', [status(thm)], ['48', '49'])).
% 26.39/26.60  thf('51', plain,
% 26.39/26.60      (![X0 : $i, X1 : $i]:
% 26.39/26.60         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 26.39/26.60          | ((X0) = (k1_xboole_0))
% 26.39/26.60          | ((k1_funct_1 @ k1_xboole_0 @ (sk_D @ X0 @ k1_xboole_0)) = (X1)))),
% 26.39/26.60      inference('demod', [status(thm)], ['48', '49'])).
% 26.39/26.60  thf('52', plain,
% 26.39/26.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.39/26.60         (((X0) = (X1))
% 26.39/26.60          | ((X2) = (k1_xboole_0))
% 26.39/26.60          | (r2_hidden @ (sk_C_1 @ X2 @ k1_xboole_0) @ X2)
% 26.39/26.60          | ((X2) = (k1_xboole_0))
% 26.39/26.60          | (r2_hidden @ (sk_C_1 @ X2 @ k1_xboole_0) @ X2))),
% 26.39/26.60      inference('sup+', [status(thm)], ['50', '51'])).
% 26.39/26.60  thf('53', plain,
% 26.39/26.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.39/26.60         ((r2_hidden @ (sk_C_1 @ X2 @ k1_xboole_0) @ X2)
% 26.39/26.60          | ((X2) = (k1_xboole_0))
% 26.39/26.60          | ((X0) = (X1)))),
% 26.39/26.60      inference('simplify', [status(thm)], ['52'])).
% 26.39/26.60  thf('54', plain,
% 26.39/26.60      (![X0 : $i]:
% 26.39/26.60         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 26.39/26.60          | ((X0) = (k1_xboole_0)))),
% 26.39/26.60      inference('condensation', [status(thm)], ['53'])).
% 26.39/26.60  thf('55', plain,
% 26.39/26.60      (![X1 : $i, X3 : $i]:
% 26.39/26.60         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 26.39/26.60      inference('cnf', [status(esa)], [d3_tarski])).
% 26.39/26.60  thf('56', plain,
% 26.39/26.60      (![X9 : $i, X11 : $i, X12 : $i]:
% 26.39/26.60         (((X11) != (k2_relat_1 @ X9))
% 26.39/26.60          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9)))
% 26.39/26.60          | ~ (r2_hidden @ X12 @ X11)
% 26.39/26.60          | ~ (v1_funct_1 @ X9)
% 26.39/26.60          | ~ (v1_relat_1 @ X9))),
% 26.39/26.60      inference('cnf', [status(esa)], [d5_funct_1])).
% 26.39/26.60  thf('57', plain,
% 26.39/26.60      (![X9 : $i, X12 : $i]:
% 26.39/26.60         (~ (v1_relat_1 @ X9)
% 26.39/26.60          | ~ (v1_funct_1 @ X9)
% 26.39/26.60          | ~ (r2_hidden @ X12 @ (k2_relat_1 @ X9))
% 26.39/26.60          | ((X12) = (k1_funct_1 @ X9 @ (sk_D_1 @ X12 @ X9))))),
% 26.39/26.60      inference('simplify', [status(thm)], ['56'])).
% 26.39/26.60  thf('58', plain,
% 26.39/26.60      (![X0 : $i, X1 : $i]:
% 26.39/26.60         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 26.39/26.60          | ((sk_C @ X1 @ (k2_relat_1 @ X0))
% 26.39/26.60              = (k1_funct_1 @ X0 @ 
% 26.39/26.60                 (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)))
% 26.39/26.60          | ~ (v1_funct_1 @ X0)
% 26.39/26.60          | ~ (v1_relat_1 @ X0))),
% 26.39/26.60      inference('sup-', [status(thm)], ['55', '57'])).
% 26.39/26.60  thf('59', plain,
% 26.39/26.60      (![X15 : $i, X16 : $i]: ((k1_relat_1 @ (sk_C_2 @ X15 @ X16)) = (X16))),
% 26.39/26.60      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 26.39/26.60  thf('60', plain,
% 26.39/26.60      (![X0 : $i, X1 : $i]:
% 26.39/26.60         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 26.39/26.60          | (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 26.39/26.60             (k1_relat_1 @ X0))
% 26.39/26.60          | ~ (v1_funct_1 @ X0)
% 26.39/26.60          | ~ (v1_relat_1 @ X0))),
% 26.39/26.60      inference('sup-', [status(thm)], ['18', '20'])).
% 26.39/26.60  thf('61', plain,
% 26.39/26.60      (![X15 : $i, X16 : $i, X17 : $i]:
% 26.39/26.60         (((k1_funct_1 @ (sk_C_2 @ X15 @ X16) @ X17) = (X15))
% 26.39/26.60          | ~ (r2_hidden @ X17 @ X16))),
% 26.39/26.60      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 26.39/26.60  thf('62', plain,
% 26.39/26.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.39/26.60         (~ (v1_relat_1 @ X0)
% 26.39/26.60          | ~ (v1_funct_1 @ X0)
% 26.39/26.60          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 26.39/26.60          | ((k1_funct_1 @ (sk_C_2 @ X2 @ (k1_relat_1 @ X0)) @ 
% 26.39/26.60              (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)) = (X2)))),
% 26.39/26.60      inference('sup-', [status(thm)], ['60', '61'])).
% 26.39/26.60  thf('63', plain,
% 26.39/26.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 26.39/26.60         (((k1_funct_1 @ (sk_C_2 @ X1 @ X0) @ 
% 26.39/26.60            (sk_D_1 @ (sk_C @ X3 @ (k2_relat_1 @ (sk_C_2 @ X2 @ X0))) @ 
% 26.39/26.60             (sk_C_2 @ X2 @ X0)))
% 26.39/26.60            = (X1))
% 26.39/26.60          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X2 @ X0)) @ X3)
% 26.39/26.60          | ~ (v1_funct_1 @ (sk_C_2 @ X2 @ X0))
% 26.39/26.60          | ~ (v1_relat_1 @ (sk_C_2 @ X2 @ X0)))),
% 26.39/26.60      inference('sup+', [status(thm)], ['59', '62'])).
% 26.39/26.60  thf('64', plain,
% 26.39/26.60      (![X15 : $i, X16 : $i]: (v1_funct_1 @ (sk_C_2 @ X15 @ X16))),
% 26.39/26.60      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 26.39/26.60  thf('65', plain,
% 26.39/26.60      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (sk_C_2 @ X15 @ X16))),
% 26.39/26.60      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 26.39/26.60  thf('66', plain,
% 26.39/26.60      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 26.39/26.60         (((k1_funct_1 @ (sk_C_2 @ X1 @ X0) @ 
% 26.39/26.60            (sk_D_1 @ (sk_C @ X3 @ (k2_relat_1 @ (sk_C_2 @ X2 @ X0))) @ 
% 26.39/26.60             (sk_C_2 @ X2 @ X0)))
% 26.39/26.60            = (X1))
% 26.39/26.60          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X2 @ X0)) @ X3))),
% 26.39/26.60      inference('demod', [status(thm)], ['63', '64', '65'])).
% 26.39/26.60  thf('67', plain,
% 26.39/26.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.39/26.60         (((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) = (X1))
% 26.39/26.60          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0))
% 26.39/26.60          | ~ (v1_funct_1 @ (sk_C_2 @ X1 @ X0))
% 26.39/26.60          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2)
% 26.39/26.60          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2))),
% 26.39/26.60      inference('sup+', [status(thm)], ['58', '66'])).
% 26.39/26.60  thf('68', plain,
% 26.39/26.60      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (sk_C_2 @ X15 @ X16))),
% 26.39/26.60      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 26.39/26.60  thf('69', plain,
% 26.39/26.60      (![X15 : $i, X16 : $i]: (v1_funct_1 @ (sk_C_2 @ X15 @ X16))),
% 26.39/26.60      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 26.39/26.60  thf('70', plain,
% 26.39/26.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.39/26.60         (((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) = (X1))
% 26.39/26.60          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2)
% 26.39/26.60          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2))),
% 26.39/26.60      inference('demod', [status(thm)], ['67', '68', '69'])).
% 26.39/26.60  thf('71', plain,
% 26.39/26.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.39/26.60         ((r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2)
% 26.39/26.60          | ((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) = (X1)))),
% 26.39/26.60      inference('simplify', [status(thm)], ['70'])).
% 26.39/26.60  thf('72', plain,
% 26.39/26.60      (![X1 : $i, X3 : $i]:
% 26.39/26.60         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 26.39/26.60      inference('cnf', [status(esa)], [d3_tarski])).
% 26.39/26.60  thf('73', plain,
% 26.39/26.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.39/26.60         (~ (r2_hidden @ X0 @ X1)
% 26.39/26.60          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X2)) @ X1)
% 26.39/26.60          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X2)) @ X1))),
% 26.39/26.60      inference('sup-', [status(thm)], ['71', '72'])).
% 26.39/26.60  thf('74', plain,
% 26.39/26.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.39/26.60         ((r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X2)) @ X1)
% 26.39/26.60          | ~ (r2_hidden @ X0 @ X1))),
% 26.39/26.60      inference('simplify', [status(thm)], ['73'])).
% 26.39/26.60  thf('75', plain,
% 26.39/26.60      (![X0 : $i, X1 : $i]:
% 26.39/26.60         (((X0) = (k1_xboole_0))
% 26.39/26.60          | (r1_tarski @ 
% 26.39/26.60             (k2_relat_1 @ (sk_C_2 @ (sk_C_1 @ X0 @ k1_xboole_0) @ X1)) @ X0))),
% 26.39/26.60      inference('sup-', [status(thm)], ['54', '74'])).
% 26.39/26.60  thf(t18_funct_1, conjecture,
% 26.39/26.60    (![A:$i,B:$i]:
% 26.39/26.60     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 26.39/26.60          ( ![C:$i]:
% 26.39/26.60            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 26.39/26.60              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 26.39/26.60                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 26.39/26.60  thf(zf_stmt_0, negated_conjecture,
% 26.39/26.60    (~( ![A:$i,B:$i]:
% 26.39/26.60        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 26.39/26.60             ( ![C:$i]:
% 26.39/26.60               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 26.39/26.60                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 26.39/26.60                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 26.39/26.60    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 26.39/26.60  thf('76', plain,
% 26.39/26.60      (![X18 : $i]:
% 26.39/26.60         (~ (r1_tarski @ (k2_relat_1 @ X18) @ sk_A)
% 26.39/26.60          | ((sk_B) != (k1_relat_1 @ X18))
% 26.39/26.60          | ~ (v1_funct_1 @ X18)
% 26.39/26.60          | ~ (v1_relat_1 @ X18))),
% 26.39/26.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.39/26.60  thf('77', plain,
% 26.39/26.60      (![X0 : $i]:
% 26.39/26.60         (((sk_A) = (k1_xboole_0))
% 26.39/26.60          | ~ (v1_relat_1 @ (sk_C_2 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0))
% 26.39/26.60          | ~ (v1_funct_1 @ (sk_C_2 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0))
% 26.39/26.60          | ((sk_B)
% 26.39/26.60              != (k1_relat_1 @ (sk_C_2 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0))))),
% 26.39/26.60      inference('sup-', [status(thm)], ['75', '76'])).
% 26.39/26.60  thf('78', plain,
% 26.39/26.60      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (sk_C_2 @ X15 @ X16))),
% 26.39/26.60      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 26.39/26.60  thf('79', plain,
% 26.39/26.60      (![X15 : $i, X16 : $i]: (v1_funct_1 @ (sk_C_2 @ X15 @ X16))),
% 26.39/26.60      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 26.39/26.60  thf('80', plain,
% 26.39/26.60      (![X15 : $i, X16 : $i]: ((k1_relat_1 @ (sk_C_2 @ X15 @ X16)) = (X16))),
% 26.39/26.60      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 26.39/26.60  thf('81', plain, (![X0 : $i]: (((sk_A) = (k1_xboole_0)) | ((sk_B) != (X0)))),
% 26.39/26.60      inference('demod', [status(thm)], ['77', '78', '79', '80'])).
% 26.39/26.60  thf('82', plain, (((sk_A) = (k1_xboole_0))),
% 26.39/26.60      inference('simplify', [status(thm)], ['81'])).
% 26.39/26.60  thf('83', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 26.39/26.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.39/26.60  thf('84', plain,
% 26.39/26.60      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 26.39/26.60      inference('split', [status(esa)], ['83'])).
% 26.39/26.60  thf('85', plain,
% 26.39/26.60      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 26.39/26.60      inference('cnf', [status(esa)], [d10_xboole_0])).
% 26.39/26.60  thf('86', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 26.39/26.60      inference('simplify', [status(thm)], ['85'])).
% 26.39/26.60  thf('87', plain,
% 26.39/26.60      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 26.39/26.60      inference('split', [status(esa)], ['83'])).
% 26.39/26.60  thf('88', plain,
% 26.39/26.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 26.39/26.60         ((r1_tarski @ k1_xboole_0 @ X2) | ((X0) = (X1)))),
% 26.39/26.60      inference('simplify', [status(thm)], ['39'])).
% 26.39/26.60  thf('89', plain,
% 26.39/26.60      ((![X0 : $i, X1 : $i, X2 : $i]: ((r1_tarski @ sk_B @ X0) | ((X1) = (X2))))
% 26.39/26.60         <= ((((sk_B) = (k1_xboole_0))))),
% 26.39/26.60      inference('sup+', [status(thm)], ['87', '88'])).
% 26.39/26.60  thf('90', plain,
% 26.39/26.60      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 26.39/26.60      inference('split', [status(esa)], ['83'])).
% 26.39/26.60  thf('91', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 26.39/26.60      inference('condensation', [status(thm)], ['44'])).
% 26.39/26.60  thf('92', plain,
% 26.39/26.60      (![X18 : $i]:
% 26.39/26.60         (~ (r1_tarski @ (k2_relat_1 @ X18) @ sk_A)
% 26.39/26.60          | ((sk_B) != (k1_relat_1 @ X18))
% 26.39/26.60          | ~ (v1_funct_1 @ X18)
% 26.39/26.60          | ~ (v1_relat_1 @ X18))),
% 26.39/26.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 26.39/26.60  thf('93', plain,
% 26.39/26.60      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 26.39/26.60        | ~ (v1_relat_1 @ k1_xboole_0)
% 26.39/26.60        | ~ (v1_funct_1 @ k1_xboole_0)
% 26.39/26.60        | ((sk_B) != (k1_relat_1 @ k1_xboole_0)))),
% 26.39/26.60      inference('sup-', [status(thm)], ['91', '92'])).
% 26.39/26.60  thf('94', plain, ((v1_relat_1 @ k1_xboole_0)),
% 26.39/26.60      inference('sup+', [status(thm)], ['10', '11'])).
% 26.39/26.60  thf('95', plain, ((v1_funct_1 @ k1_xboole_0)),
% 26.39/26.60      inference('sup+', [status(thm)], ['13', '14'])).
% 26.39/26.60  thf('96', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 26.39/26.60      inference('sup+', [status(thm)], ['5', '6'])).
% 26.39/26.60  thf('97', plain,
% 26.39/26.60      ((~ (r1_tarski @ k1_xboole_0 @ sk_A) | ((sk_B) != (k1_xboole_0)))),
% 26.39/26.60      inference('demod', [status(thm)], ['93', '94', '95', '96'])).
% 26.39/26.60  thf('98', plain,
% 26.39/26.60      (((~ (r1_tarski @ sk_B @ sk_A) | ((sk_B) != (k1_xboole_0))))
% 26.39/26.60         <= ((((sk_B) = (k1_xboole_0))))),
% 26.39/26.60      inference('sup-', [status(thm)], ['90', '97'])).
% 26.39/26.60  thf('99', plain,
% 26.39/26.60      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 26.39/26.60      inference('split', [status(esa)], ['83'])).
% 26.39/26.60  thf('100', plain,
% 26.39/26.60      (((~ (r1_tarski @ sk_B @ sk_A) | ((sk_B) != (sk_B))))
% 26.39/26.60         <= ((((sk_B) = (k1_xboole_0))))),
% 26.39/26.60      inference('demod', [status(thm)], ['98', '99'])).
% 26.39/26.60  thf('101', plain,
% 26.39/26.60      ((~ (r1_tarski @ sk_B @ sk_A)) <= ((((sk_B) = (k1_xboole_0))))),
% 26.39/26.60      inference('simplify', [status(thm)], ['100'])).
% 26.39/26.60  thf('102', plain,
% 26.39/26.60      ((![X0 : $i, X1 : $i]: ((X0) = (X1))) <= ((((sk_B) = (k1_xboole_0))))),
% 26.39/26.60      inference('sup-', [status(thm)], ['89', '101'])).
% 26.39/26.60  thf('103', plain,
% 26.39/26.60      ((~ (r1_tarski @ sk_B @ sk_A)) <= ((((sk_B) = (k1_xboole_0))))),
% 26.39/26.60      inference('simplify', [status(thm)], ['100'])).
% 26.39/26.60  thf('104', plain,
% 26.39/26.60      ((![X0 : $i]: ~ (r1_tarski @ sk_B @ X0)) <= ((((sk_B) = (k1_xboole_0))))),
% 26.39/26.60      inference('sup-', [status(thm)], ['102', '103'])).
% 26.39/26.60  thf('105', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 26.39/26.60      inference('sup-', [status(thm)], ['86', '104'])).
% 26.39/26.60  thf('106', plain,
% 26.39/26.60      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B) = (k1_xboole_0)))),
% 26.39/26.60      inference('split', [status(esa)], ['83'])).
% 26.39/26.60  thf('107', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 26.39/26.60      inference('sat_resolution*', [status(thm)], ['105', '106'])).
% 26.39/26.60  thf('108', plain, (((sk_A) != (k1_xboole_0))),
% 26.39/26.60      inference('simpl_trail', [status(thm)], ['84', '107'])).
% 26.39/26.60  thf('109', plain, ($false),
% 26.39/26.60      inference('simplify_reflect-', [status(thm)], ['82', '108'])).
% 26.39/26.60  
% 26.39/26.60  % SZS output end Refutation
% 26.39/26.60  
% 26.39/26.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
