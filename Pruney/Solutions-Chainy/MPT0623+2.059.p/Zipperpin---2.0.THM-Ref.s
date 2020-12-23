%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u6UBjQVxMS

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:44 EST 2020

% Result     : Theorem 1.73s
% Output     : Refutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 310 expanded)
%              Number of leaves         :   21 ( 103 expanded)
%              Depth                    :   16
%              Number of atoms          : 1024 (3097 expanded)
%              Number of equality atoms :  123 ( 441 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('0',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

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

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X5 @ X6 ) @ X5 )
      | ( r2_hidden @ ( sk_D @ X5 @ X6 ) @ ( k1_relat_1 @ X6 ) )
      | ( X5
        = ( k2_relat_1 @ X6 ) )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

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

thf('3',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X12 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('4',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
       != k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ( ( sk_C_2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_C_2 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X1: $i] :
      ( ( sk_C_2 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('10',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X1: $i] :
      ( ( sk_C_2 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('12',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('13',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['2','10','13','14'])).

thf('16',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X12 @ X13 ) @ X14 )
        = X12 )
      | ~ ( r2_hidden @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X1 @ k1_xboole_0 ) @ ( sk_D @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X1: $i] :
      ( ( sk_C_2 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( X2 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ k1_xboole_0 ) @ X2 )
      | ( X2 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ k1_xboole_0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X2 @ k1_xboole_0 ) @ X2 )
      | ( X2 = k1_xboole_0 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['22'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('24',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ( X8
       != ( k2_relat_1 @ X6 ) )
      | ( X9
        = ( k1_funct_1 @ X6 @ ( sk_D_1 @ X9 @ X6 ) ) )
      | ~ ( r2_hidden @ X9 @ X8 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('26',plain,(
    ! [X6: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( r2_hidden @ X9 @ ( k2_relat_1 @ X6 ) )
      | ( X9
        = ( k1_funct_1 @ X6 @ ( sk_D_1 @ X9 @ X6 ) ) ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['24','26'])).

thf('28',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X12 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('29',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    ! [X6: $i,X8: $i,X9: $i] :
      ( ( X8
       != ( k2_relat_1 @ X6 ) )
      | ( r2_hidden @ ( sk_D_1 @ X9 @ X6 ) @ ( k1_relat_1 @ X6 ) )
      | ~ ( r2_hidden @ X9 @ X8 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('31',plain,(
    ! [X6: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( r2_hidden @ X9 @ ( k2_relat_1 @ X6 ) )
      | ( r2_hidden @ ( sk_D_1 @ X9 @ X6 ) @ ( k1_relat_1 @ X6 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) ) @ ( sk_C_2 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['28','32'])).

thf('34',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('35',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) ) @ ( sk_C_2 @ X1 @ X0 ) ) @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X12 @ X13 ) @ X14 )
        = X12 )
      | ~ ( r2_hidden @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X3 @ X0 ) @ ( sk_D_1 @ ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) ) @ ( sk_C_2 @ X1 @ X0 ) ) )
        = X3 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
        = X1 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['27','38'])).

thf('40',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('41',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
        = X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 )
      | ( ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) ) @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','46'])).

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

thf('48',plain,(
    ! [X15: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X15 ) @ sk_A )
      | ( sk_B
       != ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('51',plain,(
    ! [X12: $i,X13: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('52',plain,(
    ! [X12: $i,X13: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X12 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( sk_B != X0 ) ) ),
    inference(demod,[status(thm)],['49','50','51','52'])).

thf('54',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['55'])).

thf('57',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('58',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['55'])).

thf('62',plain,(
    ! [X1: $i] :
      ( ( sk_C_2 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('63',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('64',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X12 @ X13 ) @ X14 )
        = X12 )
      | ~ ( r2_hidden @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X2 @ X0 ) @ ( sk_C @ X1 @ X0 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ X1 @ k1_xboole_0 ) )
        = X0 )
      | ( r1_tarski @ k1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ X1 @ k1_xboole_0 ) )
        = X0 )
      | ( r1_tarski @ k1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['62','65'])).

thf('68',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( r1_tarski @ k1_xboole_0 @ X2 )
      | ( r1_tarski @ k1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ k1_xboole_0 @ X2 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('71',plain,(
    ! [X15: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X15 ) @ sk_A )
      | ( sk_B
       != ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ( sk_B
     != ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['8','9'])).

thf('74',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['11','12'])).

thf('75',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('76',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_A )
    | ( sk_B != k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','73','74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( sk_B != k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['69','76'])).

thf('78',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_B != sk_B )
        | ( X0 = X1 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','77'])).

thf('79',plain,
    ( ! [X0: $i,X1: $i] : ( X0 = X1 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['55'])).

thf('81',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('82',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['55'])).

thf('84',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X15: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X15 ) @ sk_A )
      | ( sk_B
       != ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( sk_B
       != ( k1_relat_1 @ sk_B ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['55'])).

thf('88',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['8','9'])).

thf('89',plain,
    ( ( v1_relat_1 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['55'])).

thf('91',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['11','12'])).

thf('92',plain,
    ( ( v1_funct_1 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['55'])).

thf('94',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('95',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['55'])).

thf('97',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_A )
      | ( sk_B != sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['86','89','92','97'])).

thf('99',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,
    ( ! [X0: $i] :
        ~ ( r1_tarski @ sk_B @ X0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','99'])).

thf('101',plain,(
    sk_B != k1_xboole_0 ),
    inference('sup-',[status(thm)],['60','100'])).

thf('102',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['55'])).

thf('103',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['101','102'])).

thf('104',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['56','103'])).

thf('105',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['54','104'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.u6UBjQVxMS
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:36:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.73/1.91  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.73/1.91  % Solved by: fo/fo7.sh
% 1.73/1.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.73/1.91  % done 698 iterations in 1.455s
% 1.73/1.91  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.73/1.91  % SZS output start Refutation
% 1.73/1.91  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.73/1.91  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 1.73/1.91  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 1.73/1.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.73/1.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.73/1.91  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.73/1.91  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.73/1.91  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.73/1.91  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 1.73/1.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.73/1.91  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 1.73/1.91  thf(sk_B_type, type, sk_B: $i).
% 1.73/1.91  thf(sk_A_type, type, sk_A: $i).
% 1.73/1.91  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.73/1.91  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.73/1.91  thf(t60_relat_1, axiom,
% 1.73/1.91    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 1.73/1.91     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.73/1.91  thf('0', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.73/1.91      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.73/1.91  thf(d5_funct_1, axiom,
% 1.73/1.91    (![A:$i]:
% 1.73/1.91     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.73/1.91       ( ![B:$i]:
% 1.73/1.91         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 1.73/1.91           ( ![C:$i]:
% 1.73/1.91             ( ( r2_hidden @ C @ B ) <=>
% 1.73/1.91               ( ?[D:$i]:
% 1.73/1.91                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 1.73/1.91                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 1.73/1.91  thf('1', plain,
% 1.73/1.91      (![X5 : $i, X6 : $i]:
% 1.73/1.91         ((r2_hidden @ (sk_C_1 @ X5 @ X6) @ X5)
% 1.73/1.91          | (r2_hidden @ (sk_D @ X5 @ X6) @ (k1_relat_1 @ X6))
% 1.73/1.91          | ((X5) = (k2_relat_1 @ X6))
% 1.73/1.91          | ~ (v1_funct_1 @ X6)
% 1.73/1.91          | ~ (v1_relat_1 @ X6))),
% 1.73/1.91      inference('cnf', [status(esa)], [d5_funct_1])).
% 1.73/1.91  thf('2', plain,
% 1.73/1.91      (![X0 : $i]:
% 1.73/1.91         ((r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 1.73/1.91          | ~ (v1_relat_1 @ k1_xboole_0)
% 1.73/1.91          | ~ (v1_funct_1 @ k1_xboole_0)
% 1.73/1.91          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 1.73/1.91          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 1.73/1.91      inference('sup+', [status(thm)], ['0', '1'])).
% 1.73/1.91  thf(s3_funct_1__e2_24__funct_1, axiom,
% 1.73/1.91    (![A:$i,B:$i]:
% 1.73/1.91     ( ?[C:$i]:
% 1.73/1.91       ( ( ![D:$i]:
% 1.73/1.91           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 1.73/1.91         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 1.73/1.91         ( v1_relat_1 @ C ) ) ))).
% 1.73/1.91  thf('3', plain,
% 1.73/1.91      (![X12 : $i, X13 : $i]: ((k1_relat_1 @ (sk_C_2 @ X12 @ X13)) = (X13))),
% 1.73/1.91      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 1.73/1.91  thf(t64_relat_1, axiom,
% 1.73/1.91    (![A:$i]:
% 1.73/1.91     ( ( v1_relat_1 @ A ) =>
% 1.73/1.91       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 1.73/1.91           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 1.73/1.91         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 1.73/1.91  thf('4', plain,
% 1.73/1.91      (![X4 : $i]:
% 1.73/1.91         (((k1_relat_1 @ X4) != (k1_xboole_0))
% 1.73/1.91          | ((X4) = (k1_xboole_0))
% 1.73/1.91          | ~ (v1_relat_1 @ X4))),
% 1.73/1.91      inference('cnf', [status(esa)], [t64_relat_1])).
% 1.73/1.91  thf('5', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i]:
% 1.73/1.91         (((X0) != (k1_xboole_0))
% 1.73/1.91          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0))
% 1.73/1.91          | ((sk_C_2 @ X1 @ X0) = (k1_xboole_0)))),
% 1.73/1.91      inference('sup-', [status(thm)], ['3', '4'])).
% 1.73/1.91  thf('6', plain, (![X12 : $i, X13 : $i]: (v1_relat_1 @ (sk_C_2 @ X12 @ X13))),
% 1.73/1.91      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 1.73/1.91  thf('7', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i]:
% 1.73/1.91         (((X0) != (k1_xboole_0)) | ((sk_C_2 @ X1 @ X0) = (k1_xboole_0)))),
% 1.73/1.91      inference('demod', [status(thm)], ['5', '6'])).
% 1.73/1.91  thf('8', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.73/1.91      inference('simplify', [status(thm)], ['7'])).
% 1.73/1.91  thf('9', plain, (![X12 : $i, X13 : $i]: (v1_relat_1 @ (sk_C_2 @ X12 @ X13))),
% 1.73/1.91      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 1.73/1.91  thf('10', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.73/1.91      inference('sup+', [status(thm)], ['8', '9'])).
% 1.73/1.91  thf('11', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.73/1.91      inference('simplify', [status(thm)], ['7'])).
% 1.73/1.91  thf('12', plain,
% 1.73/1.91      (![X12 : $i, X13 : $i]: (v1_funct_1 @ (sk_C_2 @ X12 @ X13))),
% 1.73/1.91      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 1.73/1.91  thf('13', plain, ((v1_funct_1 @ k1_xboole_0)),
% 1.73/1.91      inference('sup+', [status(thm)], ['11', '12'])).
% 1.73/1.91  thf('14', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.73/1.91      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.73/1.91  thf('15', plain,
% 1.73/1.91      (![X0 : $i]:
% 1.73/1.91         ((r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 1.73/1.91          | ((X0) = (k1_xboole_0))
% 1.73/1.91          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 1.73/1.91      inference('demod', [status(thm)], ['2', '10', '13', '14'])).
% 1.73/1.91  thf('16', plain,
% 1.73/1.91      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.73/1.91         (((k1_funct_1 @ (sk_C_2 @ X12 @ X13) @ X14) = (X12))
% 1.73/1.91          | ~ (r2_hidden @ X14 @ X13))),
% 1.73/1.91      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 1.73/1.91  thf('17', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i]:
% 1.73/1.91         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 1.73/1.91          | ((X0) = (k1_xboole_0))
% 1.73/1.91          | ((k1_funct_1 @ (sk_C_2 @ X1 @ k1_xboole_0) @ 
% 1.73/1.91              (sk_D @ X0 @ k1_xboole_0)) = (X1)))),
% 1.73/1.91      inference('sup-', [status(thm)], ['15', '16'])).
% 1.73/1.91  thf('18', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.73/1.91      inference('simplify', [status(thm)], ['7'])).
% 1.73/1.91  thf('19', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i]:
% 1.73/1.91         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 1.73/1.91          | ((X0) = (k1_xboole_0))
% 1.73/1.91          | ((k1_funct_1 @ k1_xboole_0 @ (sk_D @ X0 @ k1_xboole_0)) = (X1)))),
% 1.73/1.91      inference('demod', [status(thm)], ['17', '18'])).
% 1.73/1.91  thf('20', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i]:
% 1.73/1.91         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 1.73/1.91          | ((X0) = (k1_xboole_0))
% 1.73/1.91          | ((k1_funct_1 @ k1_xboole_0 @ (sk_D @ X0 @ k1_xboole_0)) = (X1)))),
% 1.73/1.91      inference('demod', [status(thm)], ['17', '18'])).
% 1.73/1.91  thf('21', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.73/1.91         (((X0) = (X1))
% 1.73/1.91          | ((X2) = (k1_xboole_0))
% 1.73/1.91          | (r2_hidden @ (sk_C_1 @ X2 @ k1_xboole_0) @ X2)
% 1.73/1.91          | ((X2) = (k1_xboole_0))
% 1.73/1.91          | (r2_hidden @ (sk_C_1 @ X2 @ k1_xboole_0) @ X2))),
% 1.73/1.91      inference('sup+', [status(thm)], ['19', '20'])).
% 1.73/1.91  thf('22', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.73/1.91         ((r2_hidden @ (sk_C_1 @ X2 @ k1_xboole_0) @ X2)
% 1.73/1.91          | ((X2) = (k1_xboole_0))
% 1.73/1.91          | ((X0) = (X1)))),
% 1.73/1.91      inference('simplify', [status(thm)], ['21'])).
% 1.73/1.91  thf('23', plain,
% 1.73/1.91      (![X0 : $i]:
% 1.73/1.91         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 1.73/1.91          | ((X0) = (k1_xboole_0)))),
% 1.73/1.91      inference('condensation', [status(thm)], ['22'])).
% 1.73/1.91  thf(d3_tarski, axiom,
% 1.73/1.91    (![A:$i,B:$i]:
% 1.73/1.91     ( ( r1_tarski @ A @ B ) <=>
% 1.73/1.91       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.73/1.91  thf('24', plain,
% 1.73/1.91      (![X1 : $i, X3 : $i]:
% 1.73/1.91         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.73/1.91      inference('cnf', [status(esa)], [d3_tarski])).
% 1.73/1.91  thf('25', plain,
% 1.73/1.91      (![X6 : $i, X8 : $i, X9 : $i]:
% 1.73/1.91         (((X8) != (k2_relat_1 @ X6))
% 1.73/1.91          | ((X9) = (k1_funct_1 @ X6 @ (sk_D_1 @ X9 @ X6)))
% 1.73/1.91          | ~ (r2_hidden @ X9 @ X8)
% 1.73/1.91          | ~ (v1_funct_1 @ X6)
% 1.73/1.91          | ~ (v1_relat_1 @ X6))),
% 1.73/1.91      inference('cnf', [status(esa)], [d5_funct_1])).
% 1.73/1.91  thf('26', plain,
% 1.73/1.91      (![X6 : $i, X9 : $i]:
% 1.73/1.91         (~ (v1_relat_1 @ X6)
% 1.73/1.91          | ~ (v1_funct_1 @ X6)
% 1.73/1.91          | ~ (r2_hidden @ X9 @ (k2_relat_1 @ X6))
% 1.73/1.91          | ((X9) = (k1_funct_1 @ X6 @ (sk_D_1 @ X9 @ X6))))),
% 1.73/1.91      inference('simplify', [status(thm)], ['25'])).
% 1.73/1.91  thf('27', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i]:
% 1.73/1.91         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 1.73/1.91          | ((sk_C @ X1 @ (k2_relat_1 @ X0))
% 1.73/1.91              = (k1_funct_1 @ X0 @ 
% 1.73/1.91                 (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)))
% 1.73/1.91          | ~ (v1_funct_1 @ X0)
% 1.73/1.91          | ~ (v1_relat_1 @ X0))),
% 1.73/1.91      inference('sup-', [status(thm)], ['24', '26'])).
% 1.73/1.91  thf('28', plain,
% 1.73/1.91      (![X12 : $i, X13 : $i]: ((k1_relat_1 @ (sk_C_2 @ X12 @ X13)) = (X13))),
% 1.73/1.91      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 1.73/1.91  thf('29', plain,
% 1.73/1.91      (![X1 : $i, X3 : $i]:
% 1.73/1.91         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.73/1.91      inference('cnf', [status(esa)], [d3_tarski])).
% 1.73/1.91  thf('30', plain,
% 1.73/1.91      (![X6 : $i, X8 : $i, X9 : $i]:
% 1.73/1.91         (((X8) != (k2_relat_1 @ X6))
% 1.73/1.91          | (r2_hidden @ (sk_D_1 @ X9 @ X6) @ (k1_relat_1 @ X6))
% 1.73/1.91          | ~ (r2_hidden @ X9 @ X8)
% 1.73/1.91          | ~ (v1_funct_1 @ X6)
% 1.73/1.91          | ~ (v1_relat_1 @ X6))),
% 1.73/1.91      inference('cnf', [status(esa)], [d5_funct_1])).
% 1.73/1.91  thf('31', plain,
% 1.73/1.91      (![X6 : $i, X9 : $i]:
% 1.73/1.91         (~ (v1_relat_1 @ X6)
% 1.73/1.91          | ~ (v1_funct_1 @ X6)
% 1.73/1.91          | ~ (r2_hidden @ X9 @ (k2_relat_1 @ X6))
% 1.73/1.91          | (r2_hidden @ (sk_D_1 @ X9 @ X6) @ (k1_relat_1 @ X6)))),
% 1.73/1.91      inference('simplify', [status(thm)], ['30'])).
% 1.73/1.91  thf('32', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i]:
% 1.73/1.91         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 1.73/1.91          | (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 1.73/1.91             (k1_relat_1 @ X0))
% 1.73/1.91          | ~ (v1_funct_1 @ X0)
% 1.73/1.91          | ~ (v1_relat_1 @ X0))),
% 1.73/1.91      inference('sup-', [status(thm)], ['29', '31'])).
% 1.73/1.91  thf('33', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.73/1.91         ((r2_hidden @ 
% 1.73/1.91           (sk_D_1 @ (sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) @ 
% 1.73/1.91            (sk_C_2 @ X1 @ X0)) @ 
% 1.73/1.91           X0)
% 1.73/1.91          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0))
% 1.73/1.91          | ~ (v1_funct_1 @ (sk_C_2 @ X1 @ X0))
% 1.73/1.91          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2))),
% 1.73/1.91      inference('sup+', [status(thm)], ['28', '32'])).
% 1.73/1.91  thf('34', plain,
% 1.73/1.91      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (sk_C_2 @ X12 @ X13))),
% 1.73/1.91      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 1.73/1.91  thf('35', plain,
% 1.73/1.91      (![X12 : $i, X13 : $i]: (v1_funct_1 @ (sk_C_2 @ X12 @ X13))),
% 1.73/1.91      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 1.73/1.91  thf('36', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.73/1.91         ((r2_hidden @ 
% 1.73/1.91           (sk_D_1 @ (sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) @ 
% 1.73/1.91            (sk_C_2 @ X1 @ X0)) @ 
% 1.73/1.91           X0)
% 1.73/1.91          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2))),
% 1.73/1.91      inference('demod', [status(thm)], ['33', '34', '35'])).
% 1.73/1.91  thf('37', plain,
% 1.73/1.91      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.73/1.91         (((k1_funct_1 @ (sk_C_2 @ X12 @ X13) @ X14) = (X12))
% 1.73/1.91          | ~ (r2_hidden @ X14 @ X13))),
% 1.73/1.91      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 1.73/1.91  thf('38', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.73/1.91         ((r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2)
% 1.73/1.91          | ((k1_funct_1 @ (sk_C_2 @ X3 @ X0) @ 
% 1.73/1.91              (sk_D_1 @ (sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) @ 
% 1.73/1.91               (sk_C_2 @ X1 @ X0)))
% 1.73/1.91              = (X3)))),
% 1.73/1.91      inference('sup-', [status(thm)], ['36', '37'])).
% 1.73/1.91  thf('39', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.73/1.91         (((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) = (X1))
% 1.73/1.91          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0))
% 1.73/1.91          | ~ (v1_funct_1 @ (sk_C_2 @ X1 @ X0))
% 1.73/1.91          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2)
% 1.73/1.91          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2))),
% 1.73/1.91      inference('sup+', [status(thm)], ['27', '38'])).
% 1.73/1.91  thf('40', plain,
% 1.73/1.91      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (sk_C_2 @ X12 @ X13))),
% 1.73/1.91      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 1.73/1.91  thf('41', plain,
% 1.73/1.91      (![X12 : $i, X13 : $i]: (v1_funct_1 @ (sk_C_2 @ X12 @ X13))),
% 1.73/1.91      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 1.73/1.91  thf('42', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.73/1.91         (((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) = (X1))
% 1.73/1.91          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2)
% 1.73/1.91          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2))),
% 1.73/1.91      inference('demod', [status(thm)], ['39', '40', '41'])).
% 1.73/1.91  thf('43', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.73/1.91         ((r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2)
% 1.73/1.91          | ((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) = (X1)))),
% 1.73/1.91      inference('simplify', [status(thm)], ['42'])).
% 1.73/1.91  thf('44', plain,
% 1.73/1.91      (![X1 : $i, X3 : $i]:
% 1.73/1.91         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.73/1.91      inference('cnf', [status(esa)], [d3_tarski])).
% 1.73/1.91  thf('45', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.73/1.91         (~ (r2_hidden @ X0 @ X1)
% 1.73/1.91          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X2)) @ X1)
% 1.73/1.91          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X2)) @ X1))),
% 1.73/1.91      inference('sup-', [status(thm)], ['43', '44'])).
% 1.73/1.91  thf('46', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.73/1.91         ((r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X2)) @ X1)
% 1.73/1.91          | ~ (r2_hidden @ X0 @ X1))),
% 1.73/1.91      inference('simplify', [status(thm)], ['45'])).
% 1.73/1.91  thf('47', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i]:
% 1.73/1.91         (((X0) = (k1_xboole_0))
% 1.73/1.91          | (r1_tarski @ 
% 1.73/1.91             (k2_relat_1 @ (sk_C_2 @ (sk_C_1 @ X0 @ k1_xboole_0) @ X1)) @ X0))),
% 1.73/1.91      inference('sup-', [status(thm)], ['23', '46'])).
% 1.73/1.91  thf(t18_funct_1, conjecture,
% 1.73/1.91    (![A:$i,B:$i]:
% 1.73/1.91     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 1.73/1.91          ( ![C:$i]:
% 1.73/1.91            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.73/1.91              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 1.73/1.91                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 1.73/1.91  thf(zf_stmt_0, negated_conjecture,
% 1.73/1.91    (~( ![A:$i,B:$i]:
% 1.73/1.91        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 1.73/1.91             ( ![C:$i]:
% 1.73/1.91               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.73/1.91                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 1.73/1.91                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 1.73/1.91    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 1.73/1.91  thf('48', plain,
% 1.73/1.91      (![X15 : $i]:
% 1.73/1.91         (~ (r1_tarski @ (k2_relat_1 @ X15) @ sk_A)
% 1.73/1.91          | ((sk_B) != (k1_relat_1 @ X15))
% 1.73/1.91          | ~ (v1_funct_1 @ X15)
% 1.73/1.91          | ~ (v1_relat_1 @ X15))),
% 1.73/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.91  thf('49', plain,
% 1.73/1.91      (![X0 : $i]:
% 1.73/1.91         (((sk_A) = (k1_xboole_0))
% 1.73/1.91          | ~ (v1_relat_1 @ (sk_C_2 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0))
% 1.73/1.91          | ~ (v1_funct_1 @ (sk_C_2 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0))
% 1.73/1.91          | ((sk_B)
% 1.73/1.91              != (k1_relat_1 @ (sk_C_2 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0))))),
% 1.73/1.91      inference('sup-', [status(thm)], ['47', '48'])).
% 1.73/1.91  thf('50', plain,
% 1.73/1.91      (![X12 : $i, X13 : $i]: (v1_relat_1 @ (sk_C_2 @ X12 @ X13))),
% 1.73/1.91      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 1.73/1.91  thf('51', plain,
% 1.73/1.91      (![X12 : $i, X13 : $i]: (v1_funct_1 @ (sk_C_2 @ X12 @ X13))),
% 1.73/1.91      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 1.73/1.91  thf('52', plain,
% 1.73/1.91      (![X12 : $i, X13 : $i]: ((k1_relat_1 @ (sk_C_2 @ X12 @ X13)) = (X13))),
% 1.73/1.91      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 1.73/1.91  thf('53', plain, (![X0 : $i]: (((sk_A) = (k1_xboole_0)) | ((sk_B) != (X0)))),
% 1.73/1.91      inference('demod', [status(thm)], ['49', '50', '51', '52'])).
% 1.73/1.91  thf('54', plain, (((sk_A) = (k1_xboole_0))),
% 1.73/1.91      inference('simplify', [status(thm)], ['53'])).
% 1.73/1.91  thf('55', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 1.73/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.91  thf('56', plain,
% 1.73/1.91      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 1.73/1.91      inference('split', [status(esa)], ['55'])).
% 1.73/1.91  thf('57', plain,
% 1.73/1.91      (![X1 : $i, X3 : $i]:
% 1.73/1.91         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.73/1.91      inference('cnf', [status(esa)], [d3_tarski])).
% 1.73/1.91  thf('58', plain,
% 1.73/1.91      (![X1 : $i, X3 : $i]:
% 1.73/1.91         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.73/1.91      inference('cnf', [status(esa)], [d3_tarski])).
% 1.73/1.91  thf('59', plain,
% 1.73/1.91      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 1.73/1.91      inference('sup-', [status(thm)], ['57', '58'])).
% 1.73/1.91  thf('60', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 1.73/1.91      inference('simplify', [status(thm)], ['59'])).
% 1.73/1.91  thf('61', plain,
% 1.73/1.91      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.73/1.91      inference('split', [status(esa)], ['55'])).
% 1.73/1.91  thf('62', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.73/1.91      inference('simplify', [status(thm)], ['7'])).
% 1.73/1.91  thf('63', plain,
% 1.73/1.91      (![X1 : $i, X3 : $i]:
% 1.73/1.91         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.73/1.91      inference('cnf', [status(esa)], [d3_tarski])).
% 1.73/1.91  thf('64', plain,
% 1.73/1.91      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.73/1.91         (((k1_funct_1 @ (sk_C_2 @ X12 @ X13) @ X14) = (X12))
% 1.73/1.91          | ~ (r2_hidden @ X14 @ X13))),
% 1.73/1.91      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 1.73/1.91  thf('65', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.73/1.91         ((r1_tarski @ X0 @ X1)
% 1.73/1.91          | ((k1_funct_1 @ (sk_C_2 @ X2 @ X0) @ (sk_C @ X1 @ X0)) = (X2)))),
% 1.73/1.91      inference('sup-', [status(thm)], ['63', '64'])).
% 1.73/1.91  thf('66', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i]:
% 1.73/1.91         (((k1_funct_1 @ k1_xboole_0 @ (sk_C @ X1 @ k1_xboole_0)) = (X0))
% 1.73/1.91          | (r1_tarski @ k1_xboole_0 @ X1))),
% 1.73/1.91      inference('sup+', [status(thm)], ['62', '65'])).
% 1.73/1.91  thf('67', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i]:
% 1.73/1.91         (((k1_funct_1 @ k1_xboole_0 @ (sk_C @ X1 @ k1_xboole_0)) = (X0))
% 1.73/1.91          | (r1_tarski @ k1_xboole_0 @ X1))),
% 1.73/1.91      inference('sup+', [status(thm)], ['62', '65'])).
% 1.73/1.91  thf('68', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.73/1.91         (((X0) = (X1))
% 1.73/1.91          | (r1_tarski @ k1_xboole_0 @ X2)
% 1.73/1.91          | (r1_tarski @ k1_xboole_0 @ X2))),
% 1.73/1.91      inference('sup+', [status(thm)], ['66', '67'])).
% 1.73/1.91  thf('69', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.73/1.91         ((r1_tarski @ k1_xboole_0 @ X2) | ((X0) = (X1)))),
% 1.73/1.91      inference('simplify', [status(thm)], ['68'])).
% 1.73/1.91  thf('70', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.73/1.91      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.73/1.91  thf('71', plain,
% 1.73/1.91      (![X15 : $i]:
% 1.73/1.91         (~ (r1_tarski @ (k2_relat_1 @ X15) @ sk_A)
% 1.73/1.91          | ((sk_B) != (k1_relat_1 @ X15))
% 1.73/1.91          | ~ (v1_funct_1 @ X15)
% 1.73/1.91          | ~ (v1_relat_1 @ X15))),
% 1.73/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.91  thf('72', plain,
% 1.73/1.91      ((~ (r1_tarski @ k1_xboole_0 @ sk_A)
% 1.73/1.91        | ~ (v1_relat_1 @ k1_xboole_0)
% 1.73/1.91        | ~ (v1_funct_1 @ k1_xboole_0)
% 1.73/1.91        | ((sk_B) != (k1_relat_1 @ k1_xboole_0)))),
% 1.73/1.91      inference('sup-', [status(thm)], ['70', '71'])).
% 1.73/1.91  thf('73', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.73/1.91      inference('sup+', [status(thm)], ['8', '9'])).
% 1.73/1.91  thf('74', plain, ((v1_funct_1 @ k1_xboole_0)),
% 1.73/1.91      inference('sup+', [status(thm)], ['11', '12'])).
% 1.73/1.91  thf('75', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.73/1.91      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.73/1.91  thf('76', plain,
% 1.73/1.91      ((~ (r1_tarski @ k1_xboole_0 @ sk_A) | ((sk_B) != (k1_xboole_0)))),
% 1.73/1.91      inference('demod', [status(thm)], ['72', '73', '74', '75'])).
% 1.73/1.91  thf('77', plain,
% 1.73/1.91      (![X0 : $i, X1 : $i]: (((X0) = (X1)) | ((sk_B) != (k1_xboole_0)))),
% 1.73/1.91      inference('sup-', [status(thm)], ['69', '76'])).
% 1.73/1.91  thf('78', plain,
% 1.73/1.91      ((![X0 : $i, X1 : $i]: (((sk_B) != (sk_B)) | ((X0) = (X1))))
% 1.73/1.91         <= ((((sk_B) = (k1_xboole_0))))),
% 1.73/1.91      inference('sup-', [status(thm)], ['61', '77'])).
% 1.73/1.91  thf('79', plain,
% 1.73/1.91      ((![X0 : $i, X1 : $i]: ((X0) = (X1))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.73/1.91      inference('simplify', [status(thm)], ['78'])).
% 1.73/1.91  thf('80', plain,
% 1.73/1.91      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.73/1.91      inference('split', [status(esa)], ['55'])).
% 1.73/1.91  thf('81', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.73/1.91      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.73/1.91  thf('82', plain,
% 1.73/1.91      ((((k2_relat_1 @ sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.73/1.91      inference('sup+', [status(thm)], ['80', '81'])).
% 1.73/1.91  thf('83', plain,
% 1.73/1.91      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.73/1.91      inference('split', [status(esa)], ['55'])).
% 1.73/1.91  thf('84', plain,
% 1.73/1.91      ((((k2_relat_1 @ sk_B) = (sk_B))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.73/1.91      inference('demod', [status(thm)], ['82', '83'])).
% 1.73/1.91  thf('85', plain,
% 1.73/1.91      (![X15 : $i]:
% 1.73/1.91         (~ (r1_tarski @ (k2_relat_1 @ X15) @ sk_A)
% 1.73/1.91          | ((sk_B) != (k1_relat_1 @ X15))
% 1.73/1.91          | ~ (v1_funct_1 @ X15)
% 1.73/1.91          | ~ (v1_relat_1 @ X15))),
% 1.73/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.73/1.91  thf('86', plain,
% 1.73/1.91      (((~ (r1_tarski @ sk_B @ sk_A)
% 1.73/1.91         | ~ (v1_relat_1 @ sk_B)
% 1.73/1.91         | ~ (v1_funct_1 @ sk_B)
% 1.73/1.91         | ((sk_B) != (k1_relat_1 @ sk_B)))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.73/1.91      inference('sup-', [status(thm)], ['84', '85'])).
% 1.73/1.91  thf('87', plain,
% 1.73/1.91      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.73/1.91      inference('split', [status(esa)], ['55'])).
% 1.73/1.91  thf('88', plain, ((v1_relat_1 @ k1_xboole_0)),
% 1.73/1.91      inference('sup+', [status(thm)], ['8', '9'])).
% 1.73/1.91  thf('89', plain, (((v1_relat_1 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 1.73/1.91      inference('sup+', [status(thm)], ['87', '88'])).
% 1.73/1.91  thf('90', plain,
% 1.73/1.91      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.73/1.91      inference('split', [status(esa)], ['55'])).
% 1.73/1.91  thf('91', plain, ((v1_funct_1 @ k1_xboole_0)),
% 1.73/1.91      inference('sup+', [status(thm)], ['11', '12'])).
% 1.73/1.91  thf('92', plain, (((v1_funct_1 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 1.73/1.91      inference('sup+', [status(thm)], ['90', '91'])).
% 1.73/1.91  thf('93', plain,
% 1.73/1.91      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.73/1.91      inference('split', [status(esa)], ['55'])).
% 1.73/1.91  thf('94', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.73/1.91      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.73/1.91  thf('95', plain,
% 1.73/1.91      ((((k1_relat_1 @ sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.73/1.91      inference('sup+', [status(thm)], ['93', '94'])).
% 1.73/1.91  thf('96', plain,
% 1.73/1.91      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.73/1.91      inference('split', [status(esa)], ['55'])).
% 1.73/1.91  thf('97', plain,
% 1.73/1.91      ((((k1_relat_1 @ sk_B) = (sk_B))) <= ((((sk_B) = (k1_xboole_0))))),
% 1.73/1.91      inference('demod', [status(thm)], ['95', '96'])).
% 1.73/1.91  thf('98', plain,
% 1.73/1.91      (((~ (r1_tarski @ sk_B @ sk_A) | ((sk_B) != (sk_B))))
% 1.73/1.91         <= ((((sk_B) = (k1_xboole_0))))),
% 1.73/1.91      inference('demod', [status(thm)], ['86', '89', '92', '97'])).
% 1.73/1.91  thf('99', plain,
% 1.73/1.91      ((~ (r1_tarski @ sk_B @ sk_A)) <= ((((sk_B) = (k1_xboole_0))))),
% 1.73/1.91      inference('simplify', [status(thm)], ['98'])).
% 1.73/1.91  thf('100', plain,
% 1.73/1.91      ((![X0 : $i]: ~ (r1_tarski @ sk_B @ X0)) <= ((((sk_B) = (k1_xboole_0))))),
% 1.73/1.91      inference('sup-', [status(thm)], ['79', '99'])).
% 1.73/1.91  thf('101', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 1.73/1.91      inference('sup-', [status(thm)], ['60', '100'])).
% 1.73/1.91  thf('102', plain,
% 1.73/1.91      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B) = (k1_xboole_0)))),
% 1.73/1.91      inference('split', [status(esa)], ['55'])).
% 1.73/1.91  thf('103', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 1.73/1.91      inference('sat_resolution*', [status(thm)], ['101', '102'])).
% 1.73/1.91  thf('104', plain, (((sk_A) != (k1_xboole_0))),
% 1.73/1.91      inference('simpl_trail', [status(thm)], ['56', '103'])).
% 1.73/1.91  thf('105', plain, ($false),
% 1.73/1.91      inference('simplify_reflect-', [status(thm)], ['54', '104'])).
% 1.73/1.91  
% 1.73/1.91  % SZS output end Refutation
% 1.73/1.91  
% 1.73/1.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
