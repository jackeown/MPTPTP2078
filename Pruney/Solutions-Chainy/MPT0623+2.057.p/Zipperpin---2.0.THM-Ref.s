%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nOLQPUhgwA

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:44 EST 2020

% Result     : Theorem 5.63s
% Output     : Refutation 5.63s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 898 expanded)
%              Number of leaves         :   21 ( 269 expanded)
%              Depth                    :   25
%              Number of atoms          : 1285 (9556 expanded)
%              Number of equality atoms :  169 (1436 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X13: $i,X14: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) )
      = X14 ) ),
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
    ! [X5: $i] :
      ( ( ( k1_relat_1 @ X5 )
       != k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('5',plain,(
    ! [X1: $i] :
      ( ( sk_C_2 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) )
      = X14 ) ),
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
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X6 @ X7 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X6 @ X7 ) @ ( k1_relat_1 @ X7 ) )
      | ( X6
        = ( k2_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X13 @ X14 ) @ X15 )
        = X13 )
      | ~ ( r2_hidden @ X15 @ X14 ) ) ),
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
    inference(demod,[status(thm)],['3','4'])).

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
    inference(demod,[status(thm)],['3','4'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference(condensation,[status(thm)],['23'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('27',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X13 @ X14 ) @ X15 )
        = X13 )
      | ~ ( r2_hidden @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) @ ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 ) )
        = X0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['25','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C_1 @ k1_xboole_0 @ k1_xboole_0 ) )
        = X0 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['25','32'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = X1 )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k2_relat_1 @ k1_xboole_0 ) )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','37'])).

thf('39',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('40',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ( X9
       != ( k2_relat_1 @ X7 ) )
      | ( X10
        = ( k1_funct_1 @ X7 @ ( sk_D_1 @ X10 @ X7 ) ) )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('41',plain,(
    ! [X7: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k2_relat_1 @ X7 ) )
      | ( X10
        = ( k1_funct_1 @ X7 @ ( sk_D_1 @ X10 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','41'])).

thf('43',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('44',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('45',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ( X9
       != ( k2_relat_1 @ X7 ) )
      | ( r2_hidden @ ( sk_D_1 @ X10 @ X7 ) @ ( k1_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('46',plain,(
    ! [X7: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k2_relat_1 @ X7 ) )
      | ( r2_hidden @ ( sk_D_1 @ X10 @ X7 ) @ ( k1_relat_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','46'])).

thf('48',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X13 @ X14 ) @ X15 )
        = X13 )
      | ~ ( r2_hidden @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X2 @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) @ ( sk_D_1 @ ( sk_C @ X3 @ ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) ) @ ( sk_C_2 @ X2 @ X0 ) ) )
        = X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) @ X3 )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['43','49'])).

thf('51',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('52',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) @ ( sk_D_1 @ ( sk_C @ X3 @ ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) ) @ ( sk_C_2 @ X2 @ X0 ) ) )
        = X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) @ X3 ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
        = X1 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['42','53'])).

thf('55',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('56',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
        = X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 )
      | ( ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) ) @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','61'])).

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

thf('63',plain,(
    ! [X16: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X16 ) @ sk_A )
      | ( sk_B
       != ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('66',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('67',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( sk_B != X0 ) ) ),
    inference(demod,[status(thm)],['64','65','66','67'])).

thf('69',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['70'])).

thf('72',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['70'])).

thf('73',plain,(
    ! [X1: $i] :
      ( ( sk_C_2 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('74',plain,
    ( ! [X0: $i] :
        ( ( sk_C_2 @ X0 @ sk_B )
        = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['72','73'])).

thf('75',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['70'])).

thf('76',plain,
    ( ! [X0: $i] :
        ( ( sk_C_2 @ X0 @ sk_B )
        = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['70'])).

thf('78',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['5','6'])).

thf('79',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['77','78'])).

thf('80',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['70'])).

thf('81',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X6 @ X7 ) @ X6 )
      | ( r2_hidden @ ( sk_D @ X6 @ X7 ) @ ( k1_relat_1 @ X7 ) )
      | ( X6
        = ( k2_relat_1 @ X7 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('83',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D @ X0 @ sk_B ) @ sk_B )
        | ~ ( v1_relat_1 @ sk_B )
        | ~ ( v1_funct_1 @ sk_B )
        | ( X0
          = ( k2_relat_1 @ sk_B ) )
        | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ X0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['81','82'])).

thf('84',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['70'])).

thf('85',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['10','11'])).

thf('86',plain,
    ( ( v1_relat_1 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['70'])).

thf('88',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['13','14'])).

thf('89',plain,
    ( ( v1_funct_1 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,
    ( ! [X0: $i] :
        ( ( r2_hidden @ ( sk_D @ X0 @ sk_B ) @ sk_B )
        | ( X0
          = ( k2_relat_1 @ sk_B ) )
        | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_B ) @ X0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['83','86','89'])).

thf('91',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X13 @ X14 ) @ X15 )
        = X13 )
      | ~ ( r2_hidden @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('92',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0
          = ( k2_relat_1 @ sk_B ) )
        | ( r2_hidden @ ( sk_D @ X0 @ sk_B ) @ sk_B )
        | ( ( k1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) @ ( sk_C_1 @ X0 @ sk_B ) )
          = X1 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ sk_B ) )
          = X0 )
        | ( r2_hidden @ ( sk_D @ sk_B @ sk_B ) @ sk_B )
        | ( sk_B
          = ( k2_relat_1 @ sk_B ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['76','92'])).

thf('94',plain,
    ( ! [X0: $i] :
        ( ( ( k1_funct_1 @ sk_B @ ( sk_C_1 @ sk_B @ sk_B ) )
          = X0 )
        | ( r2_hidden @ ( sk_D @ sk_B @ sk_B ) @ sk_B )
        | ( sk_B
          = ( k2_relat_1 @ sk_B ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['76','92'])).

thf('95',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 = X1 )
        | ( sk_B
          = ( k2_relat_1 @ sk_B ) )
        | ( r2_hidden @ ( sk_D @ sk_B @ sk_B ) @ sk_B )
        | ( sk_B
          = ( k2_relat_1 @ sk_B ) )
        | ( r2_hidden @ ( sk_D @ sk_B @ sk_B ) @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B ) @ sk_B )
        | ( sk_B
          = ( k2_relat_1 @ sk_B ) )
        | ( X0 = X1 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,
    ( ( ( r2_hidden @ ( sk_D @ sk_B @ sk_B ) @ sk_B )
      | ( sk_B
        = ( k2_relat_1 @ sk_B ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['96'])).

thf('98',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X13 @ X14 ) @ X15 )
        = X13 )
      | ~ ( r2_hidden @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('99',plain,
    ( ! [X0: $i] :
        ( ( sk_B
          = ( k2_relat_1 @ sk_B ) )
        | ( ( k1_funct_1 @ ( sk_C_2 @ X0 @ sk_B ) @ ( sk_D @ sk_B @ sk_B ) )
          = X0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ! [X0: $i] :
        ( ( sk_C_2 @ X0 @ sk_B )
        = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('101',plain,
    ( ! [X0: $i] :
        ( ( sk_B
          = ( k2_relat_1 @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ ( sk_D @ sk_B @ sk_B ) )
          = X0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ! [X0: $i] :
        ( ( sk_B
          = ( k2_relat_1 @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ ( sk_D @ sk_B @ sk_B ) )
          = X0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('103',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 = X1 )
        | ( sk_B
          = ( k2_relat_1 @ sk_B ) )
        | ( sk_B
          = ( k2_relat_1 @ sk_B ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['101','102'])).

thf('104',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( sk_B
          = ( k2_relat_1 @ sk_B ) )
        | ( X0 = X1 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,
    ( ( sk_B
      = ( k2_relat_1 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(condensation,[status(thm)],['104'])).

thf('106',plain,(
    ! [X16: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X16 ) @ sk_A )
      | ( sk_B
       != ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( sk_B
       != ( k1_relat_1 @ sk_B ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['105','106'])).

thf('108',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['70'])).

thf('109',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('110',plain,
    ( ! [X0: $i] :
        ( r1_tarski @ sk_B @ X0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( v1_relat_1 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('112',plain,
    ( ( v1_funct_1 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('113',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('114',plain,
    ( ( sk_B != sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['107','110','111','112','113'])).

thf('115',plain,(
    sk_B != k1_xboole_0 ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['70'])).

thf('117',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['115','116'])).

thf('118',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['71','117'])).

thf('119',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['69','118'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.nOLQPUhgwA
% 0.16/0.37  % Computer   : n003.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 12:12:12 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 5.63/5.83  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 5.63/5.83  % Solved by: fo/fo7.sh
% 5.63/5.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.63/5.83  % done 3284 iterations in 5.342s
% 5.63/5.83  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 5.63/5.83  % SZS output start Refutation
% 5.63/5.83  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 5.63/5.83  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 5.63/5.83  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 5.63/5.83  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.63/5.83  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 5.63/5.83  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.63/5.83  thf(sk_B_type, type, sk_B: $i).
% 5.63/5.83  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 5.63/5.83  thf(sk_A_type, type, sk_A: $i).
% 5.63/5.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 5.63/5.83  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 5.63/5.83  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 5.63/5.83  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.63/5.83  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 5.63/5.83  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.63/5.83  thf(s3_funct_1__e2_24__funct_1, axiom,
% 5.63/5.83    (![A:$i,B:$i]:
% 5.63/5.83     ( ?[C:$i]:
% 5.63/5.83       ( ( ![D:$i]:
% 5.63/5.83           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 5.63/5.83         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 5.63/5.83         ( v1_relat_1 @ C ) ) ))).
% 5.63/5.83  thf('0', plain,
% 5.63/5.83      (![X13 : $i, X14 : $i]: ((k1_relat_1 @ (sk_C_2 @ X13 @ X14)) = (X14))),
% 5.63/5.83      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 5.63/5.83  thf(t64_relat_1, axiom,
% 5.63/5.83    (![A:$i]:
% 5.63/5.83     ( ( v1_relat_1 @ A ) =>
% 5.63/5.83       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 5.63/5.83           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 5.63/5.83         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 5.63/5.83  thf('1', plain,
% 5.63/5.83      (![X5 : $i]:
% 5.63/5.83         (((k1_relat_1 @ X5) != (k1_xboole_0))
% 5.63/5.83          | ((X5) = (k1_xboole_0))
% 5.63/5.83          | ~ (v1_relat_1 @ X5))),
% 5.63/5.83      inference('cnf', [status(esa)], [t64_relat_1])).
% 5.63/5.83  thf('2', plain,
% 5.63/5.83      (![X0 : $i, X1 : $i]:
% 5.63/5.83         (((X0) != (k1_xboole_0))
% 5.63/5.83          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0))
% 5.63/5.83          | ((sk_C_2 @ X1 @ X0) = (k1_xboole_0)))),
% 5.63/5.83      inference('sup-', [status(thm)], ['0', '1'])).
% 5.63/5.83  thf('3', plain,
% 5.63/5.83      (![X1 : $i]:
% 5.63/5.83         (((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))
% 5.63/5.83          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ k1_xboole_0)))),
% 5.63/5.83      inference('simplify', [status(thm)], ['2'])).
% 5.63/5.83  thf('4', plain, (![X13 : $i, X14 : $i]: (v1_relat_1 @ (sk_C_2 @ X13 @ X14))),
% 5.63/5.83      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 5.63/5.83  thf('5', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 5.63/5.83      inference('demod', [status(thm)], ['3', '4'])).
% 5.63/5.83  thf('6', plain,
% 5.63/5.83      (![X13 : $i, X14 : $i]: ((k1_relat_1 @ (sk_C_2 @ X13 @ X14)) = (X14))),
% 5.63/5.83      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 5.63/5.83  thf('7', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 5.63/5.83      inference('sup+', [status(thm)], ['5', '6'])).
% 5.63/5.83  thf(d5_funct_1, axiom,
% 5.63/5.83    (![A:$i]:
% 5.63/5.83     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 5.63/5.83       ( ![B:$i]:
% 5.63/5.83         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 5.63/5.83           ( ![C:$i]:
% 5.63/5.83             ( ( r2_hidden @ C @ B ) <=>
% 5.63/5.83               ( ?[D:$i]:
% 5.63/5.83                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 5.63/5.83                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 5.63/5.83  thf('8', plain,
% 5.63/5.83      (![X6 : $i, X7 : $i]:
% 5.63/5.83         ((r2_hidden @ (sk_C_1 @ X6 @ X7) @ X6)
% 5.63/5.83          | (r2_hidden @ (sk_D @ X6 @ X7) @ (k1_relat_1 @ X7))
% 5.63/5.83          | ((X6) = (k2_relat_1 @ X7))
% 5.63/5.83          | ~ (v1_funct_1 @ X7)
% 5.63/5.83          | ~ (v1_relat_1 @ X7))),
% 5.63/5.83      inference('cnf', [status(esa)], [d5_funct_1])).
% 5.63/5.83  thf('9', plain,
% 5.63/5.83      (![X0 : $i]:
% 5.63/5.83         ((r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 5.63/5.83          | ~ (v1_relat_1 @ k1_xboole_0)
% 5.63/5.83          | ~ (v1_funct_1 @ k1_xboole_0)
% 5.63/5.83          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 5.63/5.83          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 5.63/5.83      inference('sup+', [status(thm)], ['7', '8'])).
% 5.63/5.83  thf('10', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 5.63/5.83      inference('demod', [status(thm)], ['3', '4'])).
% 5.63/5.83  thf('11', plain,
% 5.63/5.83      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (sk_C_2 @ X13 @ X14))),
% 5.63/5.83      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 5.63/5.83  thf('12', plain, ((v1_relat_1 @ k1_xboole_0)),
% 5.63/5.83      inference('sup+', [status(thm)], ['10', '11'])).
% 5.63/5.83  thf('13', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 5.63/5.83      inference('demod', [status(thm)], ['3', '4'])).
% 5.63/5.83  thf('14', plain,
% 5.63/5.83      (![X13 : $i, X14 : $i]: (v1_funct_1 @ (sk_C_2 @ X13 @ X14))),
% 5.63/5.83      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 5.63/5.83  thf('15', plain, ((v1_funct_1 @ k1_xboole_0)),
% 5.63/5.83      inference('sup+', [status(thm)], ['13', '14'])).
% 5.63/5.83  thf('16', plain,
% 5.63/5.83      (![X0 : $i]:
% 5.63/5.83         ((r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 5.63/5.83          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 5.63/5.83          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 5.63/5.83      inference('demod', [status(thm)], ['9', '12', '15'])).
% 5.63/5.83  thf('17', plain,
% 5.63/5.83      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.63/5.83         (((k1_funct_1 @ (sk_C_2 @ X13 @ X14) @ X15) = (X13))
% 5.63/5.83          | ~ (r2_hidden @ X15 @ X14))),
% 5.63/5.83      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 5.63/5.83  thf('18', plain,
% 5.63/5.83      (![X0 : $i, X1 : $i]:
% 5.63/5.83         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 5.63/5.83          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 5.63/5.83          | ((k1_funct_1 @ (sk_C_2 @ X1 @ k1_xboole_0) @ 
% 5.63/5.83              (sk_D @ X0 @ k1_xboole_0)) = (X1)))),
% 5.63/5.83      inference('sup-', [status(thm)], ['16', '17'])).
% 5.63/5.83  thf('19', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 5.63/5.83      inference('demod', [status(thm)], ['3', '4'])).
% 5.63/5.83  thf('20', plain,
% 5.63/5.83      (![X0 : $i, X1 : $i]:
% 5.63/5.83         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 5.63/5.83          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 5.63/5.83          | ((k1_funct_1 @ k1_xboole_0 @ (sk_D @ X0 @ k1_xboole_0)) = (X1)))),
% 5.63/5.83      inference('demod', [status(thm)], ['18', '19'])).
% 5.63/5.83  thf('21', plain,
% 5.63/5.83      (![X0 : $i, X1 : $i]:
% 5.63/5.83         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 5.63/5.83          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 5.63/5.83          | ((k1_funct_1 @ k1_xboole_0 @ (sk_D @ X0 @ k1_xboole_0)) = (X1)))),
% 5.63/5.83      inference('demod', [status(thm)], ['18', '19'])).
% 5.63/5.83  thf('22', plain,
% 5.63/5.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.63/5.83         (((X0) = (X1))
% 5.63/5.83          | ((X2) = (k2_relat_1 @ k1_xboole_0))
% 5.63/5.83          | (r2_hidden @ (sk_C_1 @ X2 @ k1_xboole_0) @ X2)
% 5.63/5.83          | ((X2) = (k2_relat_1 @ k1_xboole_0))
% 5.63/5.83          | (r2_hidden @ (sk_C_1 @ X2 @ k1_xboole_0) @ X2))),
% 5.63/5.83      inference('sup+', [status(thm)], ['20', '21'])).
% 5.63/5.83  thf('23', plain,
% 5.63/5.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.63/5.83         ((r2_hidden @ (sk_C_1 @ X2 @ k1_xboole_0) @ X2)
% 5.63/5.83          | ((X2) = (k2_relat_1 @ k1_xboole_0))
% 5.63/5.83          | ((X0) = (X1)))),
% 5.63/5.83      inference('simplify', [status(thm)], ['22'])).
% 5.63/5.83  thf('24', plain,
% 5.63/5.83      (![X0 : $i]:
% 5.63/5.83         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 5.63/5.83          | ((X0) = (k2_relat_1 @ k1_xboole_0)))),
% 5.63/5.83      inference('condensation', [status(thm)], ['23'])).
% 5.63/5.83  thf('25', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 5.63/5.83      inference('demod', [status(thm)], ['3', '4'])).
% 5.63/5.83  thf('26', plain,
% 5.63/5.83      (![X0 : $i]:
% 5.63/5.83         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 5.63/5.83          | ((X0) = (k2_relat_1 @ k1_xboole_0)))),
% 5.63/5.83      inference('condensation', [status(thm)], ['23'])).
% 5.63/5.83  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 5.63/5.83  thf('27', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 5.63/5.83      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.63/5.83  thf(d3_tarski, axiom,
% 5.63/5.83    (![A:$i,B:$i]:
% 5.63/5.83     ( ( r1_tarski @ A @ B ) <=>
% 5.63/5.83       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 5.63/5.83  thf('28', plain,
% 5.63/5.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.63/5.83         (~ (r2_hidden @ X0 @ X1)
% 5.63/5.83          | (r2_hidden @ X0 @ X2)
% 5.63/5.83          | ~ (r1_tarski @ X1 @ X2))),
% 5.63/5.83      inference('cnf', [status(esa)], [d3_tarski])).
% 5.63/5.83  thf('29', plain,
% 5.63/5.83      (![X0 : $i, X1 : $i]:
% 5.63/5.83         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 5.63/5.83      inference('sup-', [status(thm)], ['27', '28'])).
% 5.63/5.83  thf('30', plain,
% 5.63/5.83      (![X0 : $i]:
% 5.63/5.83         (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 5.63/5.83          | (r2_hidden @ (sk_C_1 @ k1_xboole_0 @ k1_xboole_0) @ X0))),
% 5.63/5.83      inference('sup-', [status(thm)], ['26', '29'])).
% 5.63/5.83  thf('31', plain,
% 5.63/5.83      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.63/5.83         (((k1_funct_1 @ (sk_C_2 @ X13 @ X14) @ X15) = (X13))
% 5.63/5.83          | ~ (r2_hidden @ X15 @ X14))),
% 5.63/5.83      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 5.63/5.83  thf('32', plain,
% 5.63/5.83      (![X0 : $i, X1 : $i]:
% 5.63/5.83         (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 5.63/5.83          | ((k1_funct_1 @ (sk_C_2 @ X1 @ X0) @ 
% 5.63/5.83              (sk_C_1 @ k1_xboole_0 @ k1_xboole_0)) = (X1)))),
% 5.63/5.83      inference('sup-', [status(thm)], ['30', '31'])).
% 5.63/5.83  thf('33', plain,
% 5.63/5.83      (![X0 : $i]:
% 5.63/5.83         (((k1_funct_1 @ k1_xboole_0 @ (sk_C_1 @ k1_xboole_0 @ k1_xboole_0))
% 5.63/5.83            = (X0))
% 5.63/5.83          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0)))),
% 5.63/5.83      inference('sup+', [status(thm)], ['25', '32'])).
% 5.63/5.83  thf('34', plain,
% 5.63/5.83      (![X0 : $i]:
% 5.63/5.83         (((k1_funct_1 @ k1_xboole_0 @ (sk_C_1 @ k1_xboole_0 @ k1_xboole_0))
% 5.63/5.83            = (X0))
% 5.63/5.83          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0)))),
% 5.63/5.83      inference('sup+', [status(thm)], ['25', '32'])).
% 5.63/5.83  thf('35', plain,
% 5.63/5.83      (![X0 : $i, X1 : $i]:
% 5.63/5.83         (((X0) = (X1))
% 5.63/5.83          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 5.63/5.83          | ((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0)))),
% 5.63/5.83      inference('sup+', [status(thm)], ['33', '34'])).
% 5.63/5.83  thf('36', plain,
% 5.63/5.83      (![X0 : $i, X1 : $i]:
% 5.63/5.83         (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0)) | ((X0) = (X1)))),
% 5.63/5.83      inference('simplify', [status(thm)], ['35'])).
% 5.63/5.83  thf('37', plain, (((k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 5.63/5.83      inference('condensation', [status(thm)], ['36'])).
% 5.63/5.83  thf('38', plain,
% 5.63/5.83      (![X0 : $i]:
% 5.63/5.83         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 5.63/5.83          | ((X0) = (k1_xboole_0)))),
% 5.63/5.83      inference('demod', [status(thm)], ['24', '37'])).
% 5.63/5.83  thf('39', plain,
% 5.63/5.83      (![X1 : $i, X3 : $i]:
% 5.63/5.83         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 5.63/5.83      inference('cnf', [status(esa)], [d3_tarski])).
% 5.63/5.83  thf('40', plain,
% 5.63/5.83      (![X7 : $i, X9 : $i, X10 : $i]:
% 5.63/5.83         (((X9) != (k2_relat_1 @ X7))
% 5.63/5.83          | ((X10) = (k1_funct_1 @ X7 @ (sk_D_1 @ X10 @ X7)))
% 5.63/5.83          | ~ (r2_hidden @ X10 @ X9)
% 5.63/5.83          | ~ (v1_funct_1 @ X7)
% 5.63/5.83          | ~ (v1_relat_1 @ X7))),
% 5.63/5.83      inference('cnf', [status(esa)], [d5_funct_1])).
% 5.63/5.83  thf('41', plain,
% 5.63/5.83      (![X7 : $i, X10 : $i]:
% 5.63/5.83         (~ (v1_relat_1 @ X7)
% 5.63/5.83          | ~ (v1_funct_1 @ X7)
% 5.63/5.83          | ~ (r2_hidden @ X10 @ (k2_relat_1 @ X7))
% 5.63/5.83          | ((X10) = (k1_funct_1 @ X7 @ (sk_D_1 @ X10 @ X7))))),
% 5.63/5.83      inference('simplify', [status(thm)], ['40'])).
% 5.63/5.83  thf('42', plain,
% 5.63/5.83      (![X0 : $i, X1 : $i]:
% 5.63/5.83         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 5.63/5.83          | ((sk_C @ X1 @ (k2_relat_1 @ X0))
% 5.63/5.83              = (k1_funct_1 @ X0 @ 
% 5.63/5.83                 (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)))
% 5.63/5.83          | ~ (v1_funct_1 @ X0)
% 5.63/5.83          | ~ (v1_relat_1 @ X0))),
% 5.63/5.83      inference('sup-', [status(thm)], ['39', '41'])).
% 5.63/5.83  thf('43', plain,
% 5.63/5.83      (![X13 : $i, X14 : $i]: ((k1_relat_1 @ (sk_C_2 @ X13 @ X14)) = (X14))),
% 5.63/5.83      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 5.63/5.83  thf('44', plain,
% 5.63/5.83      (![X1 : $i, X3 : $i]:
% 5.63/5.83         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 5.63/5.83      inference('cnf', [status(esa)], [d3_tarski])).
% 5.63/5.83  thf('45', plain,
% 5.63/5.83      (![X7 : $i, X9 : $i, X10 : $i]:
% 5.63/5.83         (((X9) != (k2_relat_1 @ X7))
% 5.63/5.83          | (r2_hidden @ (sk_D_1 @ X10 @ X7) @ (k1_relat_1 @ X7))
% 5.63/5.83          | ~ (r2_hidden @ X10 @ X9)
% 5.63/5.83          | ~ (v1_funct_1 @ X7)
% 5.63/5.83          | ~ (v1_relat_1 @ X7))),
% 5.63/5.83      inference('cnf', [status(esa)], [d5_funct_1])).
% 5.63/5.83  thf('46', plain,
% 5.63/5.83      (![X7 : $i, X10 : $i]:
% 5.63/5.83         (~ (v1_relat_1 @ X7)
% 5.63/5.83          | ~ (v1_funct_1 @ X7)
% 5.63/5.83          | ~ (r2_hidden @ X10 @ (k2_relat_1 @ X7))
% 5.63/5.83          | (r2_hidden @ (sk_D_1 @ X10 @ X7) @ (k1_relat_1 @ X7)))),
% 5.63/5.83      inference('simplify', [status(thm)], ['45'])).
% 5.63/5.83  thf('47', plain,
% 5.63/5.83      (![X0 : $i, X1 : $i]:
% 5.63/5.83         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 5.63/5.83          | (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 5.63/5.83             (k1_relat_1 @ X0))
% 5.63/5.83          | ~ (v1_funct_1 @ X0)
% 5.63/5.83          | ~ (v1_relat_1 @ X0))),
% 5.63/5.83      inference('sup-', [status(thm)], ['44', '46'])).
% 5.63/5.83  thf('48', plain,
% 5.63/5.83      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.63/5.83         (((k1_funct_1 @ (sk_C_2 @ X13 @ X14) @ X15) = (X13))
% 5.63/5.83          | ~ (r2_hidden @ X15 @ X14))),
% 5.63/5.83      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 5.63/5.83  thf('49', plain,
% 5.63/5.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.63/5.83         (~ (v1_relat_1 @ X0)
% 5.63/5.83          | ~ (v1_funct_1 @ X0)
% 5.63/5.83          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 5.63/5.83          | ((k1_funct_1 @ (sk_C_2 @ X2 @ (k1_relat_1 @ X0)) @ 
% 5.63/5.83              (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)) = (X2)))),
% 5.63/5.83      inference('sup-', [status(thm)], ['47', '48'])).
% 5.63/5.83  thf('50', plain,
% 5.63/5.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.63/5.83         (((k1_funct_1 @ (sk_C_2 @ X1 @ X0) @ 
% 5.63/5.83            (sk_D_1 @ (sk_C @ X3 @ (k2_relat_1 @ (sk_C_2 @ X2 @ X0))) @ 
% 5.63/5.83             (sk_C_2 @ X2 @ X0)))
% 5.63/5.83            = (X1))
% 5.63/5.83          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X2 @ X0)) @ X3)
% 5.63/5.83          | ~ (v1_funct_1 @ (sk_C_2 @ X2 @ X0))
% 5.63/5.83          | ~ (v1_relat_1 @ (sk_C_2 @ X2 @ X0)))),
% 5.63/5.83      inference('sup+', [status(thm)], ['43', '49'])).
% 5.63/5.83  thf('51', plain,
% 5.63/5.83      (![X13 : $i, X14 : $i]: (v1_funct_1 @ (sk_C_2 @ X13 @ X14))),
% 5.63/5.83      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 5.63/5.83  thf('52', plain,
% 5.63/5.83      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (sk_C_2 @ X13 @ X14))),
% 5.63/5.83      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 5.63/5.83  thf('53', plain,
% 5.63/5.83      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.63/5.83         (((k1_funct_1 @ (sk_C_2 @ X1 @ X0) @ 
% 5.63/5.83            (sk_D_1 @ (sk_C @ X3 @ (k2_relat_1 @ (sk_C_2 @ X2 @ X0))) @ 
% 5.63/5.83             (sk_C_2 @ X2 @ X0)))
% 5.63/5.83            = (X1))
% 5.63/5.83          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X2 @ X0)) @ X3))),
% 5.63/5.83      inference('demod', [status(thm)], ['50', '51', '52'])).
% 5.63/5.83  thf('54', plain,
% 5.63/5.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.63/5.83         (((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) = (X1))
% 5.63/5.83          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0))
% 5.63/5.83          | ~ (v1_funct_1 @ (sk_C_2 @ X1 @ X0))
% 5.63/5.83          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2)
% 5.63/5.83          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2))),
% 5.63/5.83      inference('sup+', [status(thm)], ['42', '53'])).
% 5.63/5.83  thf('55', plain,
% 5.63/5.83      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (sk_C_2 @ X13 @ X14))),
% 5.63/5.83      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 5.63/5.83  thf('56', plain,
% 5.63/5.83      (![X13 : $i, X14 : $i]: (v1_funct_1 @ (sk_C_2 @ X13 @ X14))),
% 5.63/5.83      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 5.63/5.83  thf('57', plain,
% 5.63/5.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.63/5.83         (((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) = (X1))
% 5.63/5.83          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2)
% 5.63/5.83          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2))),
% 5.63/5.83      inference('demod', [status(thm)], ['54', '55', '56'])).
% 5.63/5.83  thf('58', plain,
% 5.63/5.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.63/5.83         ((r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2)
% 5.63/5.83          | ((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) = (X1)))),
% 5.63/5.83      inference('simplify', [status(thm)], ['57'])).
% 5.63/5.83  thf('59', plain,
% 5.63/5.83      (![X1 : $i, X3 : $i]:
% 5.63/5.83         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 5.63/5.83      inference('cnf', [status(esa)], [d3_tarski])).
% 5.63/5.83  thf('60', plain,
% 5.63/5.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.63/5.83         (~ (r2_hidden @ X0 @ X1)
% 5.63/5.83          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X2)) @ X1)
% 5.63/5.83          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X2)) @ X1))),
% 5.63/5.83      inference('sup-', [status(thm)], ['58', '59'])).
% 5.63/5.83  thf('61', plain,
% 5.63/5.83      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.63/5.83         ((r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X2)) @ X1)
% 5.63/5.83          | ~ (r2_hidden @ X0 @ X1))),
% 5.63/5.83      inference('simplify', [status(thm)], ['60'])).
% 5.63/5.83  thf('62', plain,
% 5.63/5.83      (![X0 : $i, X1 : $i]:
% 5.63/5.83         (((X0) = (k1_xboole_0))
% 5.63/5.83          | (r1_tarski @ 
% 5.63/5.83             (k2_relat_1 @ (sk_C_2 @ (sk_C_1 @ X0 @ k1_xboole_0) @ X1)) @ X0))),
% 5.63/5.83      inference('sup-', [status(thm)], ['38', '61'])).
% 5.63/5.83  thf(t18_funct_1, conjecture,
% 5.63/5.83    (![A:$i,B:$i]:
% 5.63/5.83     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 5.63/5.83          ( ![C:$i]:
% 5.63/5.83            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 5.63/5.83              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 5.63/5.83                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 5.63/5.83  thf(zf_stmt_0, negated_conjecture,
% 5.63/5.83    (~( ![A:$i,B:$i]:
% 5.63/5.83        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 5.63/5.83             ( ![C:$i]:
% 5.63/5.83               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 5.63/5.83                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 5.63/5.83                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 5.63/5.83    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 5.63/5.83  thf('63', plain,
% 5.63/5.83      (![X16 : $i]:
% 5.63/5.83         (~ (r1_tarski @ (k2_relat_1 @ X16) @ sk_A)
% 5.63/5.83          | ((sk_B) != (k1_relat_1 @ X16))
% 5.63/5.83          | ~ (v1_funct_1 @ X16)
% 5.63/5.83          | ~ (v1_relat_1 @ X16))),
% 5.63/5.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.63/5.83  thf('64', plain,
% 5.63/5.83      (![X0 : $i]:
% 5.63/5.83         (((sk_A) = (k1_xboole_0))
% 5.63/5.83          | ~ (v1_relat_1 @ (sk_C_2 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0))
% 5.63/5.83          | ~ (v1_funct_1 @ (sk_C_2 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0))
% 5.63/5.83          | ((sk_B)
% 5.63/5.83              != (k1_relat_1 @ (sk_C_2 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0))))),
% 5.63/5.83      inference('sup-', [status(thm)], ['62', '63'])).
% 5.63/5.83  thf('65', plain,
% 5.63/5.83      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (sk_C_2 @ X13 @ X14))),
% 5.63/5.83      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 5.63/5.83  thf('66', plain,
% 5.63/5.83      (![X13 : $i, X14 : $i]: (v1_funct_1 @ (sk_C_2 @ X13 @ X14))),
% 5.63/5.83      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 5.63/5.83  thf('67', plain,
% 5.63/5.83      (![X13 : $i, X14 : $i]: ((k1_relat_1 @ (sk_C_2 @ X13 @ X14)) = (X14))),
% 5.63/5.83      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 5.63/5.83  thf('68', plain, (![X0 : $i]: (((sk_A) = (k1_xboole_0)) | ((sk_B) != (X0)))),
% 5.63/5.83      inference('demod', [status(thm)], ['64', '65', '66', '67'])).
% 5.63/5.83  thf('69', plain, (((sk_A) = (k1_xboole_0))),
% 5.63/5.83      inference('simplify', [status(thm)], ['68'])).
% 5.63/5.83  thf('70', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 5.63/5.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.63/5.83  thf('71', plain,
% 5.63/5.83      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 5.63/5.83      inference('split', [status(esa)], ['70'])).
% 5.63/5.83  thf('72', plain,
% 5.63/5.83      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 5.63/5.83      inference('split', [status(esa)], ['70'])).
% 5.63/5.83  thf('73', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 5.63/5.83      inference('demod', [status(thm)], ['3', '4'])).
% 5.63/5.83  thf('74', plain,
% 5.63/5.83      ((![X0 : $i]: ((sk_C_2 @ X0 @ sk_B) = (k1_xboole_0)))
% 5.63/5.83         <= ((((sk_B) = (k1_xboole_0))))),
% 5.63/5.83      inference('sup+', [status(thm)], ['72', '73'])).
% 5.63/5.83  thf('75', plain,
% 5.63/5.83      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 5.63/5.83      inference('split', [status(esa)], ['70'])).
% 5.63/5.83  thf('76', plain,
% 5.63/5.83      ((![X0 : $i]: ((sk_C_2 @ X0 @ sk_B) = (sk_B)))
% 5.63/5.83         <= ((((sk_B) = (k1_xboole_0))))),
% 5.63/5.83      inference('demod', [status(thm)], ['74', '75'])).
% 5.63/5.83  thf('77', plain,
% 5.63/5.83      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 5.63/5.83      inference('split', [status(esa)], ['70'])).
% 5.63/5.83  thf('78', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 5.63/5.83      inference('sup+', [status(thm)], ['5', '6'])).
% 5.63/5.83  thf('79', plain,
% 5.63/5.83      ((((k1_relat_1 @ sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 5.63/5.83      inference('sup+', [status(thm)], ['77', '78'])).
% 5.63/5.83  thf('80', plain,
% 5.63/5.83      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 5.63/5.83      inference('split', [status(esa)], ['70'])).
% 5.63/5.83  thf('81', plain,
% 5.63/5.83      ((((k1_relat_1 @ sk_B) = (sk_B))) <= ((((sk_B) = (k1_xboole_0))))),
% 5.63/5.83      inference('demod', [status(thm)], ['79', '80'])).
% 5.63/5.83  thf('82', plain,
% 5.63/5.83      (![X6 : $i, X7 : $i]:
% 5.63/5.83         ((r2_hidden @ (sk_C_1 @ X6 @ X7) @ X6)
% 5.63/5.83          | (r2_hidden @ (sk_D @ X6 @ X7) @ (k1_relat_1 @ X7))
% 5.63/5.83          | ((X6) = (k2_relat_1 @ X7))
% 5.63/5.83          | ~ (v1_funct_1 @ X7)
% 5.63/5.83          | ~ (v1_relat_1 @ X7))),
% 5.63/5.83      inference('cnf', [status(esa)], [d5_funct_1])).
% 5.63/5.83  thf('83', plain,
% 5.63/5.83      ((![X0 : $i]:
% 5.63/5.83          ((r2_hidden @ (sk_D @ X0 @ sk_B) @ sk_B)
% 5.63/5.83           | ~ (v1_relat_1 @ sk_B)
% 5.63/5.83           | ~ (v1_funct_1 @ sk_B)
% 5.63/5.83           | ((X0) = (k2_relat_1 @ sk_B))
% 5.63/5.83           | (r2_hidden @ (sk_C_1 @ X0 @ sk_B) @ X0)))
% 5.63/5.83         <= ((((sk_B) = (k1_xboole_0))))),
% 5.63/5.83      inference('sup+', [status(thm)], ['81', '82'])).
% 5.63/5.83  thf('84', plain,
% 5.63/5.83      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 5.63/5.83      inference('split', [status(esa)], ['70'])).
% 5.63/5.83  thf('85', plain, ((v1_relat_1 @ k1_xboole_0)),
% 5.63/5.83      inference('sup+', [status(thm)], ['10', '11'])).
% 5.63/5.83  thf('86', plain, (((v1_relat_1 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 5.63/5.83      inference('sup+', [status(thm)], ['84', '85'])).
% 5.63/5.83  thf('87', plain,
% 5.63/5.83      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 5.63/5.83      inference('split', [status(esa)], ['70'])).
% 5.63/5.83  thf('88', plain, ((v1_funct_1 @ k1_xboole_0)),
% 5.63/5.83      inference('sup+', [status(thm)], ['13', '14'])).
% 5.63/5.83  thf('89', plain, (((v1_funct_1 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 5.63/5.83      inference('sup+', [status(thm)], ['87', '88'])).
% 5.63/5.83  thf('90', plain,
% 5.63/5.83      ((![X0 : $i]:
% 5.63/5.83          ((r2_hidden @ (sk_D @ X0 @ sk_B) @ sk_B)
% 5.63/5.83           | ((X0) = (k2_relat_1 @ sk_B))
% 5.63/5.83           | (r2_hidden @ (sk_C_1 @ X0 @ sk_B) @ X0)))
% 5.63/5.83         <= ((((sk_B) = (k1_xboole_0))))),
% 5.63/5.83      inference('demod', [status(thm)], ['83', '86', '89'])).
% 5.63/5.83  thf('91', plain,
% 5.63/5.83      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.63/5.83         (((k1_funct_1 @ (sk_C_2 @ X13 @ X14) @ X15) = (X13))
% 5.63/5.83          | ~ (r2_hidden @ X15 @ X14))),
% 5.63/5.83      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 5.63/5.83  thf('92', plain,
% 5.63/5.83      ((![X0 : $i, X1 : $i]:
% 5.63/5.83          (((X0) = (k2_relat_1 @ sk_B))
% 5.63/5.83           | (r2_hidden @ (sk_D @ X0 @ sk_B) @ sk_B)
% 5.63/5.83           | ((k1_funct_1 @ (sk_C_2 @ X1 @ X0) @ (sk_C_1 @ X0 @ sk_B)) = (X1))))
% 5.63/5.83         <= ((((sk_B) = (k1_xboole_0))))),
% 5.63/5.83      inference('sup-', [status(thm)], ['90', '91'])).
% 5.63/5.83  thf('93', plain,
% 5.63/5.83      ((![X0 : $i]:
% 5.63/5.83          (((k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ sk_B)) = (X0))
% 5.63/5.83           | (r2_hidden @ (sk_D @ sk_B @ sk_B) @ sk_B)
% 5.63/5.83           | ((sk_B) = (k2_relat_1 @ sk_B))))
% 5.63/5.83         <= ((((sk_B) = (k1_xboole_0))))),
% 5.63/5.83      inference('sup+', [status(thm)], ['76', '92'])).
% 5.63/5.83  thf('94', plain,
% 5.63/5.83      ((![X0 : $i]:
% 5.63/5.83          (((k1_funct_1 @ sk_B @ (sk_C_1 @ sk_B @ sk_B)) = (X0))
% 5.63/5.83           | (r2_hidden @ (sk_D @ sk_B @ sk_B) @ sk_B)
% 5.63/5.83           | ((sk_B) = (k2_relat_1 @ sk_B))))
% 5.63/5.83         <= ((((sk_B) = (k1_xboole_0))))),
% 5.63/5.83      inference('sup+', [status(thm)], ['76', '92'])).
% 5.63/5.83  thf('95', plain,
% 5.63/5.83      ((![X0 : $i, X1 : $i]:
% 5.63/5.83          (((X0) = (X1))
% 5.63/5.83           | ((sk_B) = (k2_relat_1 @ sk_B))
% 5.63/5.83           | (r2_hidden @ (sk_D @ sk_B @ sk_B) @ sk_B)
% 5.63/5.83           | ((sk_B) = (k2_relat_1 @ sk_B))
% 5.63/5.83           | (r2_hidden @ (sk_D @ sk_B @ sk_B) @ sk_B)))
% 5.63/5.83         <= ((((sk_B) = (k1_xboole_0))))),
% 5.63/5.83      inference('sup+', [status(thm)], ['93', '94'])).
% 5.63/5.83  thf('96', plain,
% 5.63/5.83      ((![X0 : $i, X1 : $i]:
% 5.63/5.83          ((r2_hidden @ (sk_D @ sk_B @ sk_B) @ sk_B)
% 5.63/5.83           | ((sk_B) = (k2_relat_1 @ sk_B))
% 5.63/5.83           | ((X0) = (X1))))
% 5.63/5.83         <= ((((sk_B) = (k1_xboole_0))))),
% 5.63/5.83      inference('simplify', [status(thm)], ['95'])).
% 5.63/5.83  thf('97', plain,
% 5.63/5.83      ((((r2_hidden @ (sk_D @ sk_B @ sk_B) @ sk_B)
% 5.63/5.83         | ((sk_B) = (k2_relat_1 @ sk_B)))) <= ((((sk_B) = (k1_xboole_0))))),
% 5.63/5.83      inference('condensation', [status(thm)], ['96'])).
% 5.63/5.83  thf('98', plain,
% 5.63/5.83      (![X13 : $i, X14 : $i, X15 : $i]:
% 5.63/5.83         (((k1_funct_1 @ (sk_C_2 @ X13 @ X14) @ X15) = (X13))
% 5.63/5.83          | ~ (r2_hidden @ X15 @ X14))),
% 5.63/5.83      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 5.63/5.83  thf('99', plain,
% 5.63/5.83      ((![X0 : $i]:
% 5.63/5.83          (((sk_B) = (k2_relat_1 @ sk_B))
% 5.63/5.83           | ((k1_funct_1 @ (sk_C_2 @ X0 @ sk_B) @ (sk_D @ sk_B @ sk_B)) = (X0))))
% 5.63/5.83         <= ((((sk_B) = (k1_xboole_0))))),
% 5.63/5.83      inference('sup-', [status(thm)], ['97', '98'])).
% 5.63/5.83  thf('100', plain,
% 5.63/5.83      ((![X0 : $i]: ((sk_C_2 @ X0 @ sk_B) = (sk_B)))
% 5.63/5.83         <= ((((sk_B) = (k1_xboole_0))))),
% 5.63/5.83      inference('demod', [status(thm)], ['74', '75'])).
% 5.63/5.83  thf('101', plain,
% 5.63/5.83      ((![X0 : $i]:
% 5.63/5.83          (((sk_B) = (k2_relat_1 @ sk_B))
% 5.63/5.83           | ((k1_funct_1 @ sk_B @ (sk_D @ sk_B @ sk_B)) = (X0))))
% 5.63/5.83         <= ((((sk_B) = (k1_xboole_0))))),
% 5.63/5.83      inference('demod', [status(thm)], ['99', '100'])).
% 5.63/5.83  thf('102', plain,
% 5.63/5.83      ((![X0 : $i]:
% 5.63/5.83          (((sk_B) = (k2_relat_1 @ sk_B))
% 5.63/5.83           | ((k1_funct_1 @ sk_B @ (sk_D @ sk_B @ sk_B)) = (X0))))
% 5.63/5.83         <= ((((sk_B) = (k1_xboole_0))))),
% 5.63/5.83      inference('demod', [status(thm)], ['99', '100'])).
% 5.63/5.83  thf('103', plain,
% 5.63/5.83      ((![X0 : $i, X1 : $i]:
% 5.63/5.83          (((X0) = (X1))
% 5.63/5.83           | ((sk_B) = (k2_relat_1 @ sk_B))
% 5.63/5.83           | ((sk_B) = (k2_relat_1 @ sk_B))))
% 5.63/5.83         <= ((((sk_B) = (k1_xboole_0))))),
% 5.63/5.83      inference('sup+', [status(thm)], ['101', '102'])).
% 5.63/5.83  thf('104', plain,
% 5.63/5.83      ((![X0 : $i, X1 : $i]: (((sk_B) = (k2_relat_1 @ sk_B)) | ((X0) = (X1))))
% 5.63/5.83         <= ((((sk_B) = (k1_xboole_0))))),
% 5.63/5.83      inference('simplify', [status(thm)], ['103'])).
% 5.63/5.83  thf('105', plain,
% 5.63/5.83      ((((sk_B) = (k2_relat_1 @ sk_B))) <= ((((sk_B) = (k1_xboole_0))))),
% 5.63/5.83      inference('condensation', [status(thm)], ['104'])).
% 5.63/5.83  thf('106', plain,
% 5.63/5.83      (![X16 : $i]:
% 5.63/5.83         (~ (r1_tarski @ (k2_relat_1 @ X16) @ sk_A)
% 5.63/5.83          | ((sk_B) != (k1_relat_1 @ X16))
% 5.63/5.83          | ~ (v1_funct_1 @ X16)
% 5.63/5.83          | ~ (v1_relat_1 @ X16))),
% 5.63/5.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.63/5.83  thf('107', plain,
% 5.63/5.83      (((~ (r1_tarski @ sk_B @ sk_A)
% 5.63/5.83         | ~ (v1_relat_1 @ sk_B)
% 5.63/5.83         | ~ (v1_funct_1 @ sk_B)
% 5.63/5.83         | ((sk_B) != (k1_relat_1 @ sk_B)))) <= ((((sk_B) = (k1_xboole_0))))),
% 5.63/5.83      inference('sup-', [status(thm)], ['105', '106'])).
% 5.63/5.83  thf('108', plain,
% 5.63/5.83      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 5.63/5.83      inference('split', [status(esa)], ['70'])).
% 5.63/5.83  thf('109', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 5.63/5.83      inference('cnf', [status(esa)], [t2_xboole_1])).
% 5.63/5.83  thf('110', plain,
% 5.63/5.83      ((![X0 : $i]: (r1_tarski @ sk_B @ X0)) <= ((((sk_B) = (k1_xboole_0))))),
% 5.63/5.83      inference('sup+', [status(thm)], ['108', '109'])).
% 5.63/5.83  thf('111', plain, (((v1_relat_1 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 5.63/5.83      inference('sup+', [status(thm)], ['84', '85'])).
% 5.63/5.83  thf('112', plain, (((v1_funct_1 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 5.63/5.83      inference('sup+', [status(thm)], ['87', '88'])).
% 5.63/5.83  thf('113', plain,
% 5.63/5.83      ((((k1_relat_1 @ sk_B) = (sk_B))) <= ((((sk_B) = (k1_xboole_0))))),
% 5.63/5.83      inference('demod', [status(thm)], ['79', '80'])).
% 5.63/5.83  thf('114', plain, ((((sk_B) != (sk_B))) <= ((((sk_B) = (k1_xboole_0))))),
% 5.63/5.83      inference('demod', [status(thm)], ['107', '110', '111', '112', '113'])).
% 5.63/5.83  thf('115', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 5.63/5.83      inference('simplify', [status(thm)], ['114'])).
% 5.63/5.83  thf('116', plain,
% 5.63/5.83      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B) = (k1_xboole_0)))),
% 5.63/5.83      inference('split', [status(esa)], ['70'])).
% 5.63/5.83  thf('117', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 5.63/5.83      inference('sat_resolution*', [status(thm)], ['115', '116'])).
% 5.63/5.83  thf('118', plain, (((sk_A) != (k1_xboole_0))),
% 5.63/5.83      inference('simpl_trail', [status(thm)], ['71', '117'])).
% 5.63/5.83  thf('119', plain, ($false),
% 5.63/5.83      inference('simplify_reflect-', [status(thm)], ['69', '118'])).
% 5.63/5.83  
% 5.63/5.83  % SZS output end Refutation
% 5.63/5.83  
% 5.63/5.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
