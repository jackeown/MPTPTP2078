%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rb654aIcWb

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:43 EST 2020

% Result     : Theorem 17.60s
% Output     : Refutation 17.60s
% Verified   : 
% Statistics : Number of formulae       :  139 (1123 expanded)
%              Number of leaves         :   23 ( 355 expanded)
%              Depth                    :   23
%              Number of atoms          : 1174 (11728 expanded)
%              Number of equality atoms :  132 (1601 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(o_1_0_funct_1_type,type,(
    o_1_0_funct_1: $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

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

thf('0',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e1_27_1__funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('1',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
       != k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X0 @ X1 ) )
      | ( ( sk_C_2 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e1_27_1__funct_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_C_2 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X1: $i] :
      ( ( sk_C_2 @ k1_xboole_0 @ X1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X12 @ X13 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e1_27_1__funct_1])).

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
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X5 @ X6 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X5 @ X6 ) @ ( k1_relat_1 @ X6 ) )
      | ( X5
        = ( k2_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
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
      ( ( sk_C_2 @ k1_xboole_0 @ X1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e1_27_1__funct_1])).

thf('12',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X1: $i] :
      ( ( sk_C_2 @ k1_xboole_0 @ X1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e1_27_1__funct_1])).

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

thf('17',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_3 @ X15 @ X16 ) @ X17 )
        = X15 )
      | ~ ( r2_hidden @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_funct_1 @ ( sk_C_3 @ X1 @ k1_xboole_0 ) @ ( sk_D @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_relat_1 @ ( sk_C_3 @ X15 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('20',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
       != k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ X1 @ X0 ) )
      | ( ( sk_C_3 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( sk_C_3 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_C_3 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X1: $i] :
      ( ( sk_C_3 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['18','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['18','24'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( X2
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ k1_xboole_0 ) @ X2 )
      | ( X2
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ k1_xboole_0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X2 @ k1_xboole_0 ) @ X2 )
      | ( X2
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(condensation,[status(thm)],['28'])).

thf('30',plain,(
    ! [X1: $i] :
      ( ( sk_C_3 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(condensation,[status(thm)],['28'])).

thf('32',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_3 @ X15 @ X16 ) @ X17 )
        = X15 )
      | ~ ( r2_hidden @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_funct_1 @ ( sk_C_3 @ X1 @ X0 ) @ ( sk_C_1 @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 ) )
        = X0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 ) )
        = X0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['30','33'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['29','38'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('40',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('41',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ( X8
       != ( k2_relat_1 @ X6 ) )
      | ( X9
        = ( k1_funct_1 @ X6 @ ( sk_D_1 @ X9 @ X6 ) ) )
      | ~ ( r2_hidden @ X9 @ X8 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('42',plain,(
    ! [X6: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( r2_hidden @ X9 @ ( k2_relat_1 @ X6 ) )
      | ( X9
        = ( k1_funct_1 @ X6 @ ( sk_D_1 @ X9 @ X6 ) ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_relat_1 @ ( sk_C_3 @ X15 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('45',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('46',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ( X8
       != ( k2_relat_1 @ X6 ) )
      | ( r2_hidden @ ( sk_D_1 @ X9 @ X6 ) @ ( k1_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ X9 @ X8 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('47',plain,(
    ! [X6: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( r2_hidden @ X9 @ ( k2_relat_1 @ X6 ) )
      | ( r2_hidden @ ( sk_D_1 @ X9 @ X6 ) @ ( k1_relat_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_3 @ X15 @ X16 ) @ X17 )
        = X15 )
      | ~ ( r2_hidden @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( ( k1_funct_1 @ ( sk_C_3 @ X2 @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_3 @ X1 @ X0 ) @ ( sk_D_1 @ ( sk_C @ X3 @ ( k2_relat_1 @ ( sk_C_3 @ X2 @ X0 ) ) ) @ ( sk_C_3 @ X2 @ X0 ) ) )
        = X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_3 @ X2 @ X0 ) ) @ X3 )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','50'])).

thf('52',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_funct_1 @ ( sk_C_3 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('53',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( sk_C_3 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_3 @ X1 @ X0 ) @ ( sk_D_1 @ ( sk_C @ X3 @ ( k2_relat_1 @ ( sk_C_3 @ X2 @ X0 ) ) ) @ ( sk_C_3 @ X2 @ X0 ) ) )
        = X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_3 @ X2 @ X0 ) ) @ X3 ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_3 @ X1 @ X0 ) ) )
        = X1 )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_3 @ X1 @ X0 ) ) @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_3 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['43','54'])).

thf('56',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( sk_C_3 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('57',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_funct_1 @ ( sk_C_3 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_3 @ X1 @ X0 ) ) )
        = X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_3 @ X1 @ X0 ) ) @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_3 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C_3 @ X1 @ X0 ) ) @ X2 )
      | ( ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_3 @ X1 @ X0 ) ) )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_3 @ X0 @ X2 ) ) @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_3 @ X0 @ X2 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C_3 @ X0 @ X2 ) ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_3 @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','62'])).

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

thf('64',plain,(
    ! [X18: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ sk_A )
      | ( sk_B
       != ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_3 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_3 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_3 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_relat_1 @ ( sk_C_3 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('67',plain,(
    ! [X15: $i,X16: $i] :
      ( v1_funct_1 @ ( sk_C_3 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('68',plain,(
    ! [X15: $i,X16: $i] :
      ( ( k1_relat_1 @ ( sk_C_3 @ X15 @ X16 ) )
      = X16 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( sk_B != X0 ) ) ),
    inference(demod,[status(thm)],['65','66','67','68'])).

thf('70',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['71'])).

thf('73',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('74',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['71'])).

thf('78',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['5','6'])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ k1_xboole_0 ) ) @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['10','11'])).

thf('82',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['13','14'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ k1_xboole_0 ) ) @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_3 @ X15 @ X16 ) @ X17 )
        = X15 )
      | ~ ( r2_hidden @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 )
      | ( ( k1_funct_1 @ ( sk_C_3 @ X1 @ k1_xboole_0 ) @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ k1_xboole_0 ) ) @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X1: $i] :
      ( ( sk_C_3 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ k1_xboole_0 ) ) @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D_1 @ ( sk_C @ X0 @ ( k2_relat_1 @ k1_xboole_0 ) ) @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['85','86'])).

thf('89',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X2 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,(
    ! [X18: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ sk_A )
      | ( sk_B
       != ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( sk_B
       != ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['10','11'])).

thf('94',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['13','14'])).

thf('95',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['5','6'])).

thf('96',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( sk_B != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['92','93','94','95'])).

thf('97',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_B != sk_B )
        | ( X0 = X1 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','96'])).

thf('98',plain,
    ( ! [X0: $i,X1: $i] : ( X0 = X1 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,(
    ! [X18: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ sk_A )
      | ( sk_B
       != ( k1_relat_1 @ X18 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_A )
        | ~ ( v1_relat_1 @ X1 )
        | ~ ( v1_funct_1 @ X1 )
        | ( sk_B
         != ( k1_relat_1 @ X1 ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ! [X0: $i,X1: $i] : ( X0 = X1 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['97'])).

thf('102',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['10','11'])).

thf('103',plain,
    ( ! [X0: $i] :
        ( v1_relat_1 @ X0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,
    ( ! [X0: $i,X1: $i] : ( X0 = X1 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['97'])).

thf('105',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['13','14'])).

thf('106',plain,
    ( ! [X0: $i] :
        ( v1_funct_1 @ X0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,
    ( ! [X0: $i,X1: $i] :
        ( ~ ( r1_tarski @ X0 @ sk_A )
        | ( sk_B
         != ( k1_relat_1 @ X1 ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['100','103','106'])).

thf('108',plain,
    ( ! [X0: $i,X1: $i] : ( X0 = X1 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['97'])).

thf('109',plain,
    ( ! [X0: $i] :
        ~ ( r1_tarski @ X0 @ sk_A )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,(
    sk_B != k1_xboole_0 ),
    inference('sup-',[status(thm)],['76','109'])).

thf('111',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['71'])).

thf('112',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['110','111'])).

thf('113',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['72','112'])).

thf('114',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['70','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.rb654aIcWb
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:27:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 17.60/17.81  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 17.60/17.81  % Solved by: fo/fo7.sh
% 17.60/17.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 17.60/17.81  % done 7387 iterations in 17.338s
% 17.60/17.81  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 17.60/17.81  % SZS output start Refutation
% 17.60/17.81  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 17.60/17.81  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 17.60/17.81  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 17.60/17.81  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 17.60/17.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 17.60/17.81  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 17.60/17.81  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 17.60/17.81  thf(sk_A_type, type, sk_A: $i).
% 17.60/17.81  thf(o_1_0_funct_1_type, type, o_1_0_funct_1: $i > $i).
% 17.60/17.81  thf(sk_C_3_type, type, sk_C_3: $i > $i > $i).
% 17.60/17.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 17.60/17.81  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 17.60/17.81  thf(sk_B_type, type, sk_B: $i).
% 17.60/17.81  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 17.60/17.81  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 17.60/17.81  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 17.60/17.81  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 17.60/17.81  thf(s3_funct_1__e1_27_1__funct_1, axiom,
% 17.60/17.81    (![A:$i,B:$i]:
% 17.60/17.81     ( ?[C:$i]:
% 17.60/17.81       ( ( ![D:$i]:
% 17.60/17.81           ( ( r2_hidden @ D @ B ) =>
% 17.60/17.81             ( ( k1_funct_1 @ C @ D ) = ( o_1_0_funct_1 @ A ) ) ) ) & 
% 17.60/17.81         ( ( k1_relat_1 @ C ) = ( B ) ) & ( v1_funct_1 @ C ) & 
% 17.60/17.81         ( v1_relat_1 @ C ) ) ))).
% 17.60/17.81  thf('0', plain,
% 17.60/17.81      (![X12 : $i, X13 : $i]: ((k1_relat_1 @ (sk_C_2 @ X12 @ X13)) = (X12))),
% 17.60/17.81      inference('cnf', [status(esa)], [s3_funct_1__e1_27_1__funct_1])).
% 17.60/17.81  thf(t64_relat_1, axiom,
% 17.60/17.81    (![A:$i]:
% 17.60/17.81     ( ( v1_relat_1 @ A ) =>
% 17.60/17.81       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 17.60/17.81           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 17.60/17.81         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 17.60/17.81  thf('1', plain,
% 17.60/17.81      (![X4 : $i]:
% 17.60/17.81         (((k1_relat_1 @ X4) != (k1_xboole_0))
% 17.60/17.81          | ((X4) = (k1_xboole_0))
% 17.60/17.81          | ~ (v1_relat_1 @ X4))),
% 17.60/17.81      inference('cnf', [status(esa)], [t64_relat_1])).
% 17.60/17.81  thf('2', plain,
% 17.60/17.81      (![X0 : $i, X1 : $i]:
% 17.60/17.81         (((X0) != (k1_xboole_0))
% 17.60/17.81          | ~ (v1_relat_1 @ (sk_C_2 @ X0 @ X1))
% 17.60/17.81          | ((sk_C_2 @ X0 @ X1) = (k1_xboole_0)))),
% 17.60/17.81      inference('sup-', [status(thm)], ['0', '1'])).
% 17.60/17.81  thf('3', plain, (![X12 : $i, X13 : $i]: (v1_relat_1 @ (sk_C_2 @ X12 @ X13))),
% 17.60/17.81      inference('cnf', [status(esa)], [s3_funct_1__e1_27_1__funct_1])).
% 17.60/17.81  thf('4', plain,
% 17.60/17.81      (![X0 : $i, X1 : $i]:
% 17.60/17.81         (((X0) != (k1_xboole_0)) | ((sk_C_2 @ X0 @ X1) = (k1_xboole_0)))),
% 17.60/17.81      inference('demod', [status(thm)], ['2', '3'])).
% 17.60/17.81  thf('5', plain, (![X1 : $i]: ((sk_C_2 @ k1_xboole_0 @ X1) = (k1_xboole_0))),
% 17.60/17.81      inference('simplify', [status(thm)], ['4'])).
% 17.60/17.81  thf('6', plain,
% 17.60/17.81      (![X12 : $i, X13 : $i]: ((k1_relat_1 @ (sk_C_2 @ X12 @ X13)) = (X12))),
% 17.60/17.81      inference('cnf', [status(esa)], [s3_funct_1__e1_27_1__funct_1])).
% 17.60/17.81  thf('7', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 17.60/17.81      inference('sup+', [status(thm)], ['5', '6'])).
% 17.60/17.81  thf(d5_funct_1, axiom,
% 17.60/17.81    (![A:$i]:
% 17.60/17.81     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 17.60/17.81       ( ![B:$i]:
% 17.60/17.81         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 17.60/17.81           ( ![C:$i]:
% 17.60/17.81             ( ( r2_hidden @ C @ B ) <=>
% 17.60/17.81               ( ?[D:$i]:
% 17.60/17.81                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 17.60/17.81                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 17.60/17.81  thf('8', plain,
% 17.60/17.81      (![X5 : $i, X6 : $i]:
% 17.60/17.81         ((r2_hidden @ (sk_C_1 @ X5 @ X6) @ X5)
% 17.60/17.81          | (r2_hidden @ (sk_D @ X5 @ X6) @ (k1_relat_1 @ X6))
% 17.60/17.81          | ((X5) = (k2_relat_1 @ X6))
% 17.60/17.81          | ~ (v1_funct_1 @ X6)
% 17.60/17.81          | ~ (v1_relat_1 @ X6))),
% 17.60/17.81      inference('cnf', [status(esa)], [d5_funct_1])).
% 17.60/17.81  thf('9', plain,
% 17.60/17.81      (![X0 : $i]:
% 17.60/17.81         ((r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 17.60/17.81          | ~ (v1_relat_1 @ k1_xboole_0)
% 17.60/17.81          | ~ (v1_funct_1 @ k1_xboole_0)
% 17.60/17.81          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 17.60/17.81          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 17.60/17.81      inference('sup+', [status(thm)], ['7', '8'])).
% 17.60/17.81  thf('10', plain, (![X1 : $i]: ((sk_C_2 @ k1_xboole_0 @ X1) = (k1_xboole_0))),
% 17.60/17.81      inference('simplify', [status(thm)], ['4'])).
% 17.60/17.81  thf('11', plain,
% 17.60/17.81      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (sk_C_2 @ X12 @ X13))),
% 17.60/17.81      inference('cnf', [status(esa)], [s3_funct_1__e1_27_1__funct_1])).
% 17.60/17.81  thf('12', plain, ((v1_relat_1 @ k1_xboole_0)),
% 17.60/17.81      inference('sup+', [status(thm)], ['10', '11'])).
% 17.60/17.81  thf('13', plain, (![X1 : $i]: ((sk_C_2 @ k1_xboole_0 @ X1) = (k1_xboole_0))),
% 17.60/17.81      inference('simplify', [status(thm)], ['4'])).
% 17.60/17.81  thf('14', plain,
% 17.60/17.81      (![X12 : $i, X13 : $i]: (v1_funct_1 @ (sk_C_2 @ X12 @ X13))),
% 17.60/17.81      inference('cnf', [status(esa)], [s3_funct_1__e1_27_1__funct_1])).
% 17.60/17.81  thf('15', plain, ((v1_funct_1 @ k1_xboole_0)),
% 17.60/17.81      inference('sup+', [status(thm)], ['13', '14'])).
% 17.60/17.81  thf('16', plain,
% 17.60/17.81      (![X0 : $i]:
% 17.60/17.81         ((r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 17.60/17.81          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 17.60/17.81          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 17.60/17.81      inference('demod', [status(thm)], ['9', '12', '15'])).
% 17.60/17.81  thf(s3_funct_1__e2_24__funct_1, axiom,
% 17.60/17.81    (![A:$i,B:$i]:
% 17.60/17.81     ( ?[C:$i]:
% 17.60/17.81       ( ( ![D:$i]:
% 17.60/17.81           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 17.60/17.81         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 17.60/17.81         ( v1_relat_1 @ C ) ) ))).
% 17.60/17.81  thf('17', plain,
% 17.60/17.81      (![X15 : $i, X16 : $i, X17 : $i]:
% 17.60/17.81         (((k1_funct_1 @ (sk_C_3 @ X15 @ X16) @ X17) = (X15))
% 17.60/17.81          | ~ (r2_hidden @ X17 @ X16))),
% 17.60/17.81      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 17.60/17.81  thf('18', plain,
% 17.60/17.81      (![X0 : $i, X1 : $i]:
% 17.60/17.81         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 17.60/17.81          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 17.60/17.81          | ((k1_funct_1 @ (sk_C_3 @ X1 @ k1_xboole_0) @ 
% 17.60/17.81              (sk_D @ X0 @ k1_xboole_0)) = (X1)))),
% 17.60/17.81      inference('sup-', [status(thm)], ['16', '17'])).
% 17.60/17.81  thf('19', plain,
% 17.60/17.81      (![X15 : $i, X16 : $i]: ((k1_relat_1 @ (sk_C_3 @ X15 @ X16)) = (X16))),
% 17.60/17.81      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 17.60/17.81  thf('20', plain,
% 17.60/17.81      (![X4 : $i]:
% 17.60/17.81         (((k1_relat_1 @ X4) != (k1_xboole_0))
% 17.60/17.81          | ((X4) = (k1_xboole_0))
% 17.60/17.81          | ~ (v1_relat_1 @ X4))),
% 17.60/17.81      inference('cnf', [status(esa)], [t64_relat_1])).
% 17.60/17.81  thf('21', plain,
% 17.60/17.81      (![X0 : $i, X1 : $i]:
% 17.60/17.81         (((X0) != (k1_xboole_0))
% 17.60/17.81          | ~ (v1_relat_1 @ (sk_C_3 @ X1 @ X0))
% 17.60/17.81          | ((sk_C_3 @ X1 @ X0) = (k1_xboole_0)))),
% 17.60/17.81      inference('sup-', [status(thm)], ['19', '20'])).
% 17.60/17.81  thf('22', plain,
% 17.60/17.81      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (sk_C_3 @ X15 @ X16))),
% 17.60/17.81      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 17.60/17.81  thf('23', plain,
% 17.60/17.81      (![X0 : $i, X1 : $i]:
% 17.60/17.81         (((X0) != (k1_xboole_0)) | ((sk_C_3 @ X1 @ X0) = (k1_xboole_0)))),
% 17.60/17.81      inference('demod', [status(thm)], ['21', '22'])).
% 17.60/17.81  thf('24', plain, (![X1 : $i]: ((sk_C_3 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 17.60/17.81      inference('simplify', [status(thm)], ['23'])).
% 17.60/17.81  thf('25', plain,
% 17.60/17.81      (![X0 : $i, X1 : $i]:
% 17.60/17.81         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 17.60/17.81          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 17.60/17.81          | ((k1_funct_1 @ k1_xboole_0 @ (sk_D @ X0 @ k1_xboole_0)) = (X1)))),
% 17.60/17.81      inference('demod', [status(thm)], ['18', '24'])).
% 17.60/17.81  thf('26', plain,
% 17.60/17.81      (![X0 : $i, X1 : $i]:
% 17.60/17.81         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 17.60/17.81          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 17.60/17.81          | ((k1_funct_1 @ k1_xboole_0 @ (sk_D @ X0 @ k1_xboole_0)) = (X1)))),
% 17.60/17.81      inference('demod', [status(thm)], ['18', '24'])).
% 17.60/17.81  thf('27', plain,
% 17.60/17.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.60/17.81         (((X0) = (X1))
% 17.60/17.81          | ((X2) = (k2_relat_1 @ k1_xboole_0))
% 17.60/17.81          | (r2_hidden @ (sk_C_1 @ X2 @ k1_xboole_0) @ X2)
% 17.60/17.81          | ((X2) = (k2_relat_1 @ k1_xboole_0))
% 17.60/17.81          | (r2_hidden @ (sk_C_1 @ X2 @ k1_xboole_0) @ X2))),
% 17.60/17.81      inference('sup+', [status(thm)], ['25', '26'])).
% 17.60/17.81  thf('28', plain,
% 17.60/17.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.60/17.81         ((r2_hidden @ (sk_C_1 @ X2 @ k1_xboole_0) @ X2)
% 17.60/17.81          | ((X2) = (k2_relat_1 @ k1_xboole_0))
% 17.60/17.81          | ((X0) = (X1)))),
% 17.60/17.81      inference('simplify', [status(thm)], ['27'])).
% 17.60/17.81  thf('29', plain,
% 17.60/17.81      (![X0 : $i]:
% 17.60/17.81         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 17.60/17.81          | ((X0) = (k2_relat_1 @ k1_xboole_0)))),
% 17.60/17.81      inference('condensation', [status(thm)], ['28'])).
% 17.60/17.81  thf('30', plain, (![X1 : $i]: ((sk_C_3 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 17.60/17.81      inference('simplify', [status(thm)], ['23'])).
% 17.60/17.81  thf('31', plain,
% 17.60/17.81      (![X0 : $i]:
% 17.60/17.81         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 17.60/17.81          | ((X0) = (k2_relat_1 @ k1_xboole_0)))),
% 17.60/17.81      inference('condensation', [status(thm)], ['28'])).
% 17.60/17.81  thf('32', plain,
% 17.60/17.81      (![X15 : $i, X16 : $i, X17 : $i]:
% 17.60/17.81         (((k1_funct_1 @ (sk_C_3 @ X15 @ X16) @ X17) = (X15))
% 17.60/17.81          | ~ (r2_hidden @ X17 @ X16))),
% 17.60/17.81      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 17.60/17.81  thf('33', plain,
% 17.60/17.81      (![X0 : $i, X1 : $i]:
% 17.60/17.81         (((X0) = (k2_relat_1 @ k1_xboole_0))
% 17.60/17.81          | ((k1_funct_1 @ (sk_C_3 @ X1 @ X0) @ (sk_C_1 @ X0 @ k1_xboole_0))
% 17.60/17.81              = (X1)))),
% 17.60/17.81      inference('sup-', [status(thm)], ['31', '32'])).
% 17.60/17.81  thf('34', plain,
% 17.60/17.81      (![X0 : $i]:
% 17.60/17.81         (((k1_funct_1 @ k1_xboole_0 @ (sk_C_1 @ k1_xboole_0 @ k1_xboole_0))
% 17.60/17.81            = (X0))
% 17.60/17.81          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0)))),
% 17.60/17.81      inference('sup+', [status(thm)], ['30', '33'])).
% 17.60/17.81  thf('35', plain,
% 17.60/17.81      (![X0 : $i]:
% 17.60/17.81         (((k1_funct_1 @ k1_xboole_0 @ (sk_C_1 @ k1_xboole_0 @ k1_xboole_0))
% 17.60/17.81            = (X0))
% 17.60/17.81          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0)))),
% 17.60/17.81      inference('sup+', [status(thm)], ['30', '33'])).
% 17.60/17.81  thf('36', plain,
% 17.60/17.81      (![X0 : $i, X1 : $i]:
% 17.60/17.81         (((X0) = (X1))
% 17.60/17.81          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 17.60/17.81          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0)))),
% 17.60/17.81      inference('sup+', [status(thm)], ['34', '35'])).
% 17.60/17.81  thf('37', plain,
% 17.60/17.81      (![X0 : $i, X1 : $i]:
% 17.60/17.81         (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0)) | ((X0) = (X1)))),
% 17.60/17.81      inference('simplify', [status(thm)], ['36'])).
% 17.60/17.81  thf('38', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 17.60/17.81      inference('condensation', [status(thm)], ['37'])).
% 17.60/17.81  thf('39', plain,
% 17.60/17.81      (![X0 : $i]:
% 17.60/17.81         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 17.60/17.81          | ((X0) = (k1_xboole_0)))),
% 17.60/17.81      inference('demod', [status(thm)], ['29', '38'])).
% 17.60/17.81  thf(d3_tarski, axiom,
% 17.60/17.81    (![A:$i,B:$i]:
% 17.60/17.81     ( ( r1_tarski @ A @ B ) <=>
% 17.60/17.81       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 17.60/17.81  thf('40', plain,
% 17.60/17.81      (![X1 : $i, X3 : $i]:
% 17.60/17.81         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 17.60/17.81      inference('cnf', [status(esa)], [d3_tarski])).
% 17.60/17.81  thf('41', plain,
% 17.60/17.81      (![X6 : $i, X8 : $i, X9 : $i]:
% 17.60/17.81         (((X8) != (k2_relat_1 @ X6))
% 17.60/17.81          | ((X9) = (k1_funct_1 @ X6 @ (sk_D_1 @ X9 @ X6)))
% 17.60/17.81          | ~ (r2_hidden @ X9 @ X8)
% 17.60/17.81          | ~ (v1_funct_1 @ X6)
% 17.60/17.81          | ~ (v1_relat_1 @ X6))),
% 17.60/17.81      inference('cnf', [status(esa)], [d5_funct_1])).
% 17.60/17.81  thf('42', plain,
% 17.60/17.81      (![X6 : $i, X9 : $i]:
% 17.60/17.81         (~ (v1_relat_1 @ X6)
% 17.60/17.81          | ~ (v1_funct_1 @ X6)
% 17.60/17.81          | ~ (r2_hidden @ X9 @ (k2_relat_1 @ X6))
% 17.60/17.81          | ((X9) = (k1_funct_1 @ X6 @ (sk_D_1 @ X9 @ X6))))),
% 17.60/17.81      inference('simplify', [status(thm)], ['41'])).
% 17.60/17.81  thf('43', plain,
% 17.60/17.81      (![X0 : $i, X1 : $i]:
% 17.60/17.81         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 17.60/17.81          | ((sk_C @ X1 @ (k2_relat_1 @ X0))
% 17.60/17.81              = (k1_funct_1 @ X0 @ 
% 17.60/17.81                 (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)))
% 17.60/17.81          | ~ (v1_funct_1 @ X0)
% 17.60/17.81          | ~ (v1_relat_1 @ X0))),
% 17.60/17.81      inference('sup-', [status(thm)], ['40', '42'])).
% 17.60/17.81  thf('44', plain,
% 17.60/17.81      (![X15 : $i, X16 : $i]: ((k1_relat_1 @ (sk_C_3 @ X15 @ X16)) = (X16))),
% 17.60/17.81      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 17.60/17.81  thf('45', plain,
% 17.60/17.81      (![X1 : $i, X3 : $i]:
% 17.60/17.81         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 17.60/17.81      inference('cnf', [status(esa)], [d3_tarski])).
% 17.60/17.81  thf('46', plain,
% 17.60/17.81      (![X6 : $i, X8 : $i, X9 : $i]:
% 17.60/17.81         (((X8) != (k2_relat_1 @ X6))
% 17.60/17.81          | (r2_hidden @ (sk_D_1 @ X9 @ X6) @ (k1_relat_1 @ X6))
% 17.60/17.81          | ~ (r2_hidden @ X9 @ X8)
% 17.60/17.81          | ~ (v1_funct_1 @ X6)
% 17.60/17.81          | ~ (v1_relat_1 @ X6))),
% 17.60/17.81      inference('cnf', [status(esa)], [d5_funct_1])).
% 17.60/17.81  thf('47', plain,
% 17.60/17.81      (![X6 : $i, X9 : $i]:
% 17.60/17.81         (~ (v1_relat_1 @ X6)
% 17.60/17.81          | ~ (v1_funct_1 @ X6)
% 17.60/17.81          | ~ (r2_hidden @ X9 @ (k2_relat_1 @ X6))
% 17.60/17.81          | (r2_hidden @ (sk_D_1 @ X9 @ X6) @ (k1_relat_1 @ X6)))),
% 17.60/17.81      inference('simplify', [status(thm)], ['46'])).
% 17.60/17.81  thf('48', plain,
% 17.60/17.81      (![X0 : $i, X1 : $i]:
% 17.60/17.81         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 17.60/17.81          | (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 17.60/17.81             (k1_relat_1 @ X0))
% 17.60/17.81          | ~ (v1_funct_1 @ X0)
% 17.60/17.81          | ~ (v1_relat_1 @ X0))),
% 17.60/17.81      inference('sup-', [status(thm)], ['45', '47'])).
% 17.60/17.81  thf('49', plain,
% 17.60/17.81      (![X15 : $i, X16 : $i, X17 : $i]:
% 17.60/17.81         (((k1_funct_1 @ (sk_C_3 @ X15 @ X16) @ X17) = (X15))
% 17.60/17.81          | ~ (r2_hidden @ X17 @ X16))),
% 17.60/17.81      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 17.60/17.81  thf('50', plain,
% 17.60/17.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.60/17.81         (~ (v1_relat_1 @ X0)
% 17.60/17.81          | ~ (v1_funct_1 @ X0)
% 17.60/17.81          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 17.60/17.81          | ((k1_funct_1 @ (sk_C_3 @ X2 @ (k1_relat_1 @ X0)) @ 
% 17.60/17.81              (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)) = (X2)))),
% 17.60/17.81      inference('sup-', [status(thm)], ['48', '49'])).
% 17.60/17.81  thf('51', plain,
% 17.60/17.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 17.60/17.81         (((k1_funct_1 @ (sk_C_3 @ X1 @ X0) @ 
% 17.60/17.81            (sk_D_1 @ (sk_C @ X3 @ (k2_relat_1 @ (sk_C_3 @ X2 @ X0))) @ 
% 17.60/17.81             (sk_C_3 @ X2 @ X0)))
% 17.60/17.81            = (X1))
% 17.60/17.81          | (r1_tarski @ (k2_relat_1 @ (sk_C_3 @ X2 @ X0)) @ X3)
% 17.60/17.81          | ~ (v1_funct_1 @ (sk_C_3 @ X2 @ X0))
% 17.60/17.81          | ~ (v1_relat_1 @ (sk_C_3 @ X2 @ X0)))),
% 17.60/17.81      inference('sup+', [status(thm)], ['44', '50'])).
% 17.60/17.81  thf('52', plain,
% 17.60/17.81      (![X15 : $i, X16 : $i]: (v1_funct_1 @ (sk_C_3 @ X15 @ X16))),
% 17.60/17.81      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 17.60/17.81  thf('53', plain,
% 17.60/17.81      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (sk_C_3 @ X15 @ X16))),
% 17.60/17.81      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 17.60/17.81  thf('54', plain,
% 17.60/17.81      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 17.60/17.81         (((k1_funct_1 @ (sk_C_3 @ X1 @ X0) @ 
% 17.60/17.81            (sk_D_1 @ (sk_C @ X3 @ (k2_relat_1 @ (sk_C_3 @ X2 @ X0))) @ 
% 17.60/17.81             (sk_C_3 @ X2 @ X0)))
% 17.60/17.81            = (X1))
% 17.60/17.81          | (r1_tarski @ (k2_relat_1 @ (sk_C_3 @ X2 @ X0)) @ X3))),
% 17.60/17.81      inference('demod', [status(thm)], ['51', '52', '53'])).
% 17.60/17.81  thf('55', plain,
% 17.60/17.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.60/17.81         (((sk_C @ X2 @ (k2_relat_1 @ (sk_C_3 @ X1 @ X0))) = (X1))
% 17.60/17.81          | ~ (v1_relat_1 @ (sk_C_3 @ X1 @ X0))
% 17.60/17.81          | ~ (v1_funct_1 @ (sk_C_3 @ X1 @ X0))
% 17.60/17.81          | (r1_tarski @ (k2_relat_1 @ (sk_C_3 @ X1 @ X0)) @ X2)
% 17.60/17.81          | (r1_tarski @ (k2_relat_1 @ (sk_C_3 @ X1 @ X0)) @ X2))),
% 17.60/17.81      inference('sup+', [status(thm)], ['43', '54'])).
% 17.60/17.81  thf('56', plain,
% 17.60/17.81      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (sk_C_3 @ X15 @ X16))),
% 17.60/17.81      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 17.60/17.81  thf('57', plain,
% 17.60/17.81      (![X15 : $i, X16 : $i]: (v1_funct_1 @ (sk_C_3 @ X15 @ X16))),
% 17.60/17.81      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 17.60/17.81  thf('58', plain,
% 17.60/17.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.60/17.81         (((sk_C @ X2 @ (k2_relat_1 @ (sk_C_3 @ X1 @ X0))) = (X1))
% 17.60/17.81          | (r1_tarski @ (k2_relat_1 @ (sk_C_3 @ X1 @ X0)) @ X2)
% 17.60/17.81          | (r1_tarski @ (k2_relat_1 @ (sk_C_3 @ X1 @ X0)) @ X2))),
% 17.60/17.81      inference('demod', [status(thm)], ['55', '56', '57'])).
% 17.60/17.81  thf('59', plain,
% 17.60/17.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.60/17.81         ((r1_tarski @ (k2_relat_1 @ (sk_C_3 @ X1 @ X0)) @ X2)
% 17.60/17.81          | ((sk_C @ X2 @ (k2_relat_1 @ (sk_C_3 @ X1 @ X0))) = (X1)))),
% 17.60/17.81      inference('simplify', [status(thm)], ['58'])).
% 17.60/17.81  thf('60', plain,
% 17.60/17.81      (![X1 : $i, X3 : $i]:
% 17.60/17.81         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 17.60/17.81      inference('cnf', [status(esa)], [d3_tarski])).
% 17.60/17.81  thf('61', plain,
% 17.60/17.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.60/17.81         (~ (r2_hidden @ X0 @ X1)
% 17.60/17.81          | (r1_tarski @ (k2_relat_1 @ (sk_C_3 @ X0 @ X2)) @ X1)
% 17.60/17.81          | (r1_tarski @ (k2_relat_1 @ (sk_C_3 @ X0 @ X2)) @ X1))),
% 17.60/17.81      inference('sup-', [status(thm)], ['59', '60'])).
% 17.60/17.81  thf('62', plain,
% 17.60/17.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.60/17.81         ((r1_tarski @ (k2_relat_1 @ (sk_C_3 @ X0 @ X2)) @ X1)
% 17.60/17.81          | ~ (r2_hidden @ X0 @ X1))),
% 17.60/17.81      inference('simplify', [status(thm)], ['61'])).
% 17.60/17.81  thf('63', plain,
% 17.60/17.81      (![X0 : $i, X1 : $i]:
% 17.60/17.81         (((X0) = (k1_xboole_0))
% 17.60/17.81          | (r1_tarski @ 
% 17.60/17.81             (k2_relat_1 @ (sk_C_3 @ (sk_C_1 @ X0 @ k1_xboole_0) @ X1)) @ X0))),
% 17.60/17.81      inference('sup-', [status(thm)], ['39', '62'])).
% 17.60/17.81  thf(t18_funct_1, conjecture,
% 17.60/17.81    (![A:$i,B:$i]:
% 17.60/17.81     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 17.60/17.81          ( ![C:$i]:
% 17.60/17.81            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 17.60/17.81              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 17.60/17.81                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 17.60/17.81  thf(zf_stmt_0, negated_conjecture,
% 17.60/17.81    (~( ![A:$i,B:$i]:
% 17.60/17.81        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 17.60/17.81             ( ![C:$i]:
% 17.60/17.81               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 17.60/17.81                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 17.60/17.81                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 17.60/17.81    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 17.60/17.81  thf('64', plain,
% 17.60/17.81      (![X18 : $i]:
% 17.60/17.81         (~ (r1_tarski @ (k2_relat_1 @ X18) @ sk_A)
% 17.60/17.81          | ((sk_B) != (k1_relat_1 @ X18))
% 17.60/17.81          | ~ (v1_funct_1 @ X18)
% 17.60/17.81          | ~ (v1_relat_1 @ X18))),
% 17.60/17.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.60/17.81  thf('65', plain,
% 17.60/17.81      (![X0 : $i]:
% 17.60/17.81         (((sk_A) = (k1_xboole_0))
% 17.60/17.81          | ~ (v1_relat_1 @ (sk_C_3 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0))
% 17.60/17.81          | ~ (v1_funct_1 @ (sk_C_3 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0))
% 17.60/17.81          | ((sk_B)
% 17.60/17.81              != (k1_relat_1 @ (sk_C_3 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0))))),
% 17.60/17.81      inference('sup-', [status(thm)], ['63', '64'])).
% 17.60/17.81  thf('66', plain,
% 17.60/17.81      (![X15 : $i, X16 : $i]: (v1_relat_1 @ (sk_C_3 @ X15 @ X16))),
% 17.60/17.81      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 17.60/17.81  thf('67', plain,
% 17.60/17.81      (![X15 : $i, X16 : $i]: (v1_funct_1 @ (sk_C_3 @ X15 @ X16))),
% 17.60/17.81      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 17.60/17.81  thf('68', plain,
% 17.60/17.81      (![X15 : $i, X16 : $i]: ((k1_relat_1 @ (sk_C_3 @ X15 @ X16)) = (X16))),
% 17.60/17.81      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 17.60/17.81  thf('69', plain, (![X0 : $i]: (((sk_A) = (k1_xboole_0)) | ((sk_B) != (X0)))),
% 17.60/17.81      inference('demod', [status(thm)], ['65', '66', '67', '68'])).
% 17.60/17.81  thf('70', plain, (((sk_A) = (k1_xboole_0))),
% 17.60/17.81      inference('simplify', [status(thm)], ['69'])).
% 17.60/17.81  thf('71', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 17.60/17.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.60/17.81  thf('72', plain,
% 17.60/17.81      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 17.60/17.81      inference('split', [status(esa)], ['71'])).
% 17.60/17.81  thf('73', plain,
% 17.60/17.81      (![X1 : $i, X3 : $i]:
% 17.60/17.81         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 17.60/17.81      inference('cnf', [status(esa)], [d3_tarski])).
% 17.60/17.81  thf('74', plain,
% 17.60/17.81      (![X1 : $i, X3 : $i]:
% 17.60/17.81         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 17.60/17.81      inference('cnf', [status(esa)], [d3_tarski])).
% 17.60/17.81  thf('75', plain,
% 17.60/17.81      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 17.60/17.81      inference('sup-', [status(thm)], ['73', '74'])).
% 17.60/17.81  thf('76', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 17.60/17.81      inference('simplify', [status(thm)], ['75'])).
% 17.60/17.81  thf('77', plain,
% 17.60/17.81      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 17.60/17.81      inference('split', [status(esa)], ['71'])).
% 17.60/17.81  thf('78', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 17.60/17.81      inference('sup+', [status(thm)], ['5', '6'])).
% 17.60/17.81  thf('79', plain,
% 17.60/17.81      (![X0 : $i, X1 : $i]:
% 17.60/17.81         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 17.60/17.81          | (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 17.60/17.81             (k1_relat_1 @ X0))
% 17.60/17.81          | ~ (v1_funct_1 @ X0)
% 17.60/17.81          | ~ (v1_relat_1 @ X0))),
% 17.60/17.81      inference('sup-', [status(thm)], ['45', '47'])).
% 17.60/17.81  thf('80', plain,
% 17.60/17.81      (![X0 : $i]:
% 17.60/17.81         ((r2_hidden @ 
% 17.60/17.81           (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ k1_xboole_0)) @ k1_xboole_0) @ 
% 17.60/17.81           k1_xboole_0)
% 17.60/17.81          | ~ (v1_relat_1 @ k1_xboole_0)
% 17.60/17.81          | ~ (v1_funct_1 @ k1_xboole_0)
% 17.60/17.81          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0))),
% 17.60/17.81      inference('sup+', [status(thm)], ['78', '79'])).
% 17.60/17.81  thf('81', plain, ((v1_relat_1 @ k1_xboole_0)),
% 17.60/17.81      inference('sup+', [status(thm)], ['10', '11'])).
% 17.60/17.81  thf('82', plain, ((v1_funct_1 @ k1_xboole_0)),
% 17.60/17.81      inference('sup+', [status(thm)], ['13', '14'])).
% 17.60/17.81  thf('83', plain,
% 17.60/17.81      (![X0 : $i]:
% 17.60/17.81         ((r2_hidden @ 
% 17.60/17.81           (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ k1_xboole_0)) @ k1_xboole_0) @ 
% 17.60/17.81           k1_xboole_0)
% 17.60/17.81          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0))),
% 17.60/17.81      inference('demod', [status(thm)], ['80', '81', '82'])).
% 17.60/17.81  thf('84', plain,
% 17.60/17.81      (![X15 : $i, X16 : $i, X17 : $i]:
% 17.60/17.81         (((k1_funct_1 @ (sk_C_3 @ X15 @ X16) @ X17) = (X15))
% 17.60/17.81          | ~ (r2_hidden @ X17 @ X16))),
% 17.60/17.81      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 17.60/17.81  thf('85', plain,
% 17.60/17.81      (![X0 : $i, X1 : $i]:
% 17.60/17.81         ((r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)
% 17.60/17.81          | ((k1_funct_1 @ (sk_C_3 @ X1 @ k1_xboole_0) @ 
% 17.60/17.81              (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ k1_xboole_0)) @ k1_xboole_0))
% 17.60/17.81              = (X1)))),
% 17.60/17.81      inference('sup-', [status(thm)], ['83', '84'])).
% 17.60/17.81  thf('86', plain, (![X1 : $i]: ((sk_C_3 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 17.60/17.81      inference('simplify', [status(thm)], ['23'])).
% 17.60/17.81  thf('87', plain,
% 17.60/17.81      (![X0 : $i, X1 : $i]:
% 17.60/17.81         ((r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)
% 17.60/17.81          | ((k1_funct_1 @ k1_xboole_0 @ 
% 17.60/17.81              (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ k1_xboole_0)) @ k1_xboole_0))
% 17.60/17.81              = (X1)))),
% 17.60/17.81      inference('demod', [status(thm)], ['85', '86'])).
% 17.60/17.81  thf('88', plain,
% 17.60/17.81      (![X0 : $i, X1 : $i]:
% 17.60/17.81         ((r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)
% 17.60/17.81          | ((k1_funct_1 @ k1_xboole_0 @ 
% 17.60/17.81              (sk_D_1 @ (sk_C @ X0 @ (k2_relat_1 @ k1_xboole_0)) @ k1_xboole_0))
% 17.60/17.81              = (X1)))),
% 17.60/17.81      inference('demod', [status(thm)], ['85', '86'])).
% 17.60/17.81  thf('89', plain,
% 17.60/17.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.60/17.81         (((X0) = (X1))
% 17.60/17.81          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X2)
% 17.60/17.81          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X2))),
% 17.60/17.81      inference('sup+', [status(thm)], ['87', '88'])).
% 17.60/17.81  thf('90', plain,
% 17.60/17.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 17.60/17.81         ((r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X2) | ((X0) = (X1)))),
% 17.60/17.81      inference('simplify', [status(thm)], ['89'])).
% 17.60/17.81  thf('91', plain,
% 17.60/17.81      (![X18 : $i]:
% 17.60/17.81         (~ (r1_tarski @ (k2_relat_1 @ X18) @ sk_A)
% 17.60/17.81          | ((sk_B) != (k1_relat_1 @ X18))
% 17.60/17.81          | ~ (v1_funct_1 @ X18)
% 17.60/17.81          | ~ (v1_relat_1 @ X18))),
% 17.60/17.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.60/17.81  thf('92', plain,
% 17.60/17.81      (![X0 : $i, X1 : $i]:
% 17.60/17.81         (((X0) = (X1))
% 17.60/17.81          | ~ (v1_relat_1 @ k1_xboole_0)
% 17.60/17.81          | ~ (v1_funct_1 @ k1_xboole_0)
% 17.60/17.81          | ((sk_B) != (k1_relat_1 @ k1_xboole_0)))),
% 17.60/17.81      inference('sup-', [status(thm)], ['90', '91'])).
% 17.60/17.81  thf('93', plain, ((v1_relat_1 @ k1_xboole_0)),
% 17.60/17.81      inference('sup+', [status(thm)], ['10', '11'])).
% 17.60/17.81  thf('94', plain, ((v1_funct_1 @ k1_xboole_0)),
% 17.60/17.81      inference('sup+', [status(thm)], ['13', '14'])).
% 17.60/17.81  thf('95', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 17.60/17.81      inference('sup+', [status(thm)], ['5', '6'])).
% 17.60/17.81  thf('96', plain,
% 17.60/17.81      (![X0 : $i, X1 : $i]: (((X0) = (X1)) | ((sk_B) != (k1_xboole_0)))),
% 17.60/17.81      inference('demod', [status(thm)], ['92', '93', '94', '95'])).
% 17.60/17.81  thf('97', plain,
% 17.60/17.81      ((![X0 : $i, X1 : $i]: (((sk_B) != (sk_B)) | ((X0) = (X1))))
% 17.60/17.81         <= ((((sk_B) = (k1_xboole_0))))),
% 17.60/17.81      inference('sup-', [status(thm)], ['77', '96'])).
% 17.60/17.81  thf('98', plain,
% 17.60/17.81      ((![X0 : $i, X1 : $i]: ((X0) = (X1))) <= ((((sk_B) = (k1_xboole_0))))),
% 17.60/17.81      inference('simplify', [status(thm)], ['97'])).
% 17.60/17.81  thf('99', plain,
% 17.60/17.81      (![X18 : $i]:
% 17.60/17.81         (~ (r1_tarski @ (k2_relat_1 @ X18) @ sk_A)
% 17.60/17.81          | ((sk_B) != (k1_relat_1 @ X18))
% 17.60/17.81          | ~ (v1_funct_1 @ X18)
% 17.60/17.81          | ~ (v1_relat_1 @ X18))),
% 17.60/17.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 17.60/17.81  thf('100', plain,
% 17.60/17.81      ((![X0 : $i, X1 : $i]:
% 17.60/17.81          (~ (r1_tarski @ X0 @ sk_A)
% 17.60/17.81           | ~ (v1_relat_1 @ X1)
% 17.60/17.81           | ~ (v1_funct_1 @ X1)
% 17.60/17.81           | ((sk_B) != (k1_relat_1 @ X1))))
% 17.60/17.81         <= ((((sk_B) = (k1_xboole_0))))),
% 17.60/17.81      inference('sup-', [status(thm)], ['98', '99'])).
% 17.60/17.81  thf('101', plain,
% 17.60/17.81      ((![X0 : $i, X1 : $i]: ((X0) = (X1))) <= ((((sk_B) = (k1_xboole_0))))),
% 17.60/17.81      inference('simplify', [status(thm)], ['97'])).
% 17.60/17.81  thf('102', plain, ((v1_relat_1 @ k1_xboole_0)),
% 17.60/17.81      inference('sup+', [status(thm)], ['10', '11'])).
% 17.60/17.81  thf('103', plain,
% 17.60/17.81      ((![X0 : $i]: (v1_relat_1 @ X0)) <= ((((sk_B) = (k1_xboole_0))))),
% 17.60/17.81      inference('sup+', [status(thm)], ['101', '102'])).
% 17.60/17.81  thf('104', plain,
% 17.60/17.81      ((![X0 : $i, X1 : $i]: ((X0) = (X1))) <= ((((sk_B) = (k1_xboole_0))))),
% 17.60/17.81      inference('simplify', [status(thm)], ['97'])).
% 17.60/17.81  thf('105', plain, ((v1_funct_1 @ k1_xboole_0)),
% 17.60/17.81      inference('sup+', [status(thm)], ['13', '14'])).
% 17.60/17.81  thf('106', plain,
% 17.60/17.81      ((![X0 : $i]: (v1_funct_1 @ X0)) <= ((((sk_B) = (k1_xboole_0))))),
% 17.60/17.81      inference('sup+', [status(thm)], ['104', '105'])).
% 17.60/17.81  thf('107', plain,
% 17.60/17.81      ((![X0 : $i, X1 : $i]:
% 17.60/17.81          (~ (r1_tarski @ X0 @ sk_A) | ((sk_B) != (k1_relat_1 @ X1))))
% 17.60/17.81         <= ((((sk_B) = (k1_xboole_0))))),
% 17.60/17.81      inference('demod', [status(thm)], ['100', '103', '106'])).
% 17.60/17.81  thf('108', plain,
% 17.60/17.81      ((![X0 : $i, X1 : $i]: ((X0) = (X1))) <= ((((sk_B) = (k1_xboole_0))))),
% 17.60/17.81      inference('simplify', [status(thm)], ['97'])).
% 17.60/17.81  thf('109', plain,
% 17.60/17.81      ((![X0 : $i]: ~ (r1_tarski @ X0 @ sk_A)) <= ((((sk_B) = (k1_xboole_0))))),
% 17.60/17.81      inference('clc', [status(thm)], ['107', '108'])).
% 17.60/17.81  thf('110', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 17.60/17.81      inference('sup-', [status(thm)], ['76', '109'])).
% 17.60/17.81  thf('111', plain,
% 17.60/17.81      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B) = (k1_xboole_0)))),
% 17.60/17.81      inference('split', [status(esa)], ['71'])).
% 17.60/17.81  thf('112', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 17.60/17.81      inference('sat_resolution*', [status(thm)], ['110', '111'])).
% 17.60/17.81  thf('113', plain, (((sk_A) != (k1_xboole_0))),
% 17.60/17.81      inference('simpl_trail', [status(thm)], ['72', '112'])).
% 17.60/17.81  thf('114', plain, ($false),
% 17.60/17.81      inference('simplify_reflect-', [status(thm)], ['70', '113'])).
% 17.60/17.81  
% 17.60/17.81  % SZS output end Refutation
% 17.60/17.81  
% 17.65/17.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
