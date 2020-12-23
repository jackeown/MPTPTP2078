%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5oTQ6dq23g

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:44 EST 2020

% Result     : Theorem 8.52s
% Output     : Refutation 8.52s
% Verified   : 
% Statistics : Number of formulae       :  144 ( 817 expanded)
%              Number of leaves         :   21 ( 236 expanded)
%              Depth                    :   25
%              Number of atoms          : 1237 (8921 expanded)
%              Number of equality atoms :  159 (1523 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
       != k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
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

thf('16',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['5','6'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('17',plain,(
    ! [X5: $i] :
      ( ( ( k1_relat_1 @ X5 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X5 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('18',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['10','11'])).

thf('20',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['9','12','15','21'])).

thf('23',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X13 @ X14 ) @ X15 )
        = X13 )
      | ~ ( r2_hidden @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X1 @ k1_xboole_0 ) @ ( sk_D @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X1: $i] :
      ( ( sk_C_2 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_D @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( X2 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ k1_xboole_0 ) @ X2 )
      | ( X2 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X2 @ k1_xboole_0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X2 @ k1_xboole_0 ) @ X2 )
      | ( X2 = k1_xboole_0 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['29'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('31',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('32',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ( X9
       != ( k2_relat_1 @ X7 ) )
      | ( X10
        = ( k1_funct_1 @ X7 @ ( sk_D_1 @ X10 @ X7 ) ) )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('33',plain,(
    ! [X7: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k2_relat_1 @ X7 ) )
      | ( X10
        = ( k1_funct_1 @ X7 @ ( sk_D_1 @ X10 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('36',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('37',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ( X9
       != ( k2_relat_1 @ X7 ) )
      | ( r2_hidden @ ( sk_D_1 @ X10 @ X7 ) @ ( k1_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('38',plain,(
    ! [X7: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k2_relat_1 @ X7 ) )
      | ( r2_hidden @ ( sk_D_1 @ X10 @ X7 ) @ ( k1_relat_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X13 @ X14 ) @ X15 )
        = X13 )
      | ~ ( r2_hidden @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X2 @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) @ ( sk_D_1 @ ( sk_C @ X3 @ ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) ) @ ( sk_C_2 @ X2 @ X0 ) ) )
        = X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) @ X3 )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['35','41'])).

thf('43',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('44',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) @ ( sk_D_1 @ ( sk_C @ X3 @ ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) ) @ ( sk_C_2 @ X2 @ X0 ) ) )
        = X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) @ X3 ) ) ),
    inference(demod,[status(thm)],['42','43','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
        = X1 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['34','45'])).

thf('47',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('48',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
        = X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) @ X2 )
      | ( ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) ) @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) ) @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( sk_C_2 @ ( sk_C_1 @ X0 @ k1_xboole_0 ) @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','53'])).

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

thf('55',plain,(
    ! [X16: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X16 ) @ sk_A )
      | ( sk_B
       != ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) )
      | ( sk_B
       != ( k1_relat_1 @ ( sk_C_2 @ ( sk_C_1 @ sk_A @ k1_xboole_0 ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('58',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('59',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( sk_B != X0 ) ) ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( sk_A != k1_xboole_0 )
   <= ( sk_A != k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('64',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('65',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('69',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('70',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('71',plain,(
    ! [X4: $i] :
      ( ( ( k1_relat_1 @ X4 )
       != k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('72',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ X0 )
         != sk_B )
        | ~ ( v1_relat_1 @ X0 )
        | ( X0 = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('74',plain,
    ( ! [X0: $i] :
        ( ( ( k1_relat_1 @ X0 )
         != sk_B )
        | ~ ( v1_relat_1 @ X0 )
        | ( X0 = sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( X0 != sk_B )
        | ( ( sk_C_2 @ X1 @ X0 )
          = sk_B )
        | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','74'])).

thf('76',plain,
    ( ! [X1: $i] :
        ( ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ sk_B ) )
        | ( ( sk_C_2 @ X1 @ sk_B )
          = sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['75'])).

thf('77',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('78',plain,
    ( ! [X1: $i] :
        ( ( sk_C_2 @ X1 @ sk_B )
        = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('80',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X5: $i] :
      ( ( ( k1_relat_1 @ X5 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X5 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('82',plain,
    ( ( ( sk_B != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('84',plain,
    ( ! [X1: $i] :
        ( ( sk_C_2 @ X1 @ sk_B )
        = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('85',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('86',plain,
    ( ( v1_relat_1 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('88',plain,
    ( ( ( sk_B != sk_B )
      | ( ( k2_relat_1 @ sk_B )
        = sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['82','83','86','87'])).

thf('89',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X7: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k2_relat_1 @ X7 ) )
      | ( r2_hidden @ ( sk_D_1 @ X10 @ X7 ) @ ( k1_relat_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('91',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B ) @ ( k1_relat_1 @ sk_B ) )
        | ~ ( v1_funct_1 @ sk_B )
        | ~ ( v1_relat_1 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('93',plain,
    ( ! [X1: $i] :
        ( ( sk_C_2 @ X1 @ sk_B )
        = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('94',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('95',plain,
    ( ( v1_funct_1 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( v1_relat_1 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('97',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( r2_hidden @ ( sk_D_1 @ X0 @ sk_B ) @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['91','92','95','96'])).

thf('98',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) @ sk_B ) @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','97'])).

thf('99',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X13 @ X14 ) @ X15 )
        = X13 )
      | ~ ( r2_hidden @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('100',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( ( k1_funct_1 @ ( sk_C_2 @ X1 @ sk_B ) @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) @ sk_B ) )
          = X1 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,
    ( ! [X1: $i] :
        ( ( sk_C_2 @ X1 @ sk_B )
        = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['76','77'])).

thf('102',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( ( k1_funct_1 @ sk_B @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) @ sk_B ) )
          = X1 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,
    ( ! [X0: $i,X1: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( ( k1_funct_1 @ sk_B @ ( sk_D_1 @ ( sk_C @ X0 @ sk_B ) @ sk_B ) )
          = X1 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('104',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( X0 = X1 )
        | ( r1_tarski @ sk_B @ X2 )
        | ( r1_tarski @ sk_B @ X2 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['102','103'])).

thf('105',plain,
    ( ! [X0: $i,X1: $i,X2: $i] :
        ( ( r1_tarski @ sk_B @ X2 )
        | ( X0 = X1 ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['88'])).

thf('107',plain,(
    ! [X16: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X16 ) @ sk_A )
      | ( sk_B
       != ( k1_relat_1 @ X16 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_A )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ( sk_B
       != ( k1_relat_1 @ sk_B ) ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( v1_relat_1 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['84','85'])).

thf('110',plain,
    ( ( v1_funct_1 @ sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['93','94'])).

thf('111',plain,
    ( ( ( k1_relat_1 @ sk_B )
      = sk_B )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['78','79'])).

thf('112',plain,
    ( ( ~ ( r1_tarski @ sk_B @ sk_A )
      | ( sk_B != sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['108','109','110','111'])).

thf('113',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,
    ( ! [X0: $i,X1: $i] : ( X0 = X1 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['105','113'])).

thf('115',plain,
    ( ~ ( r1_tarski @ sk_B @ sk_A )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['112'])).

thf('116',plain,
    ( ! [X0: $i] :
        ~ ( r1_tarski @ sk_B @ X0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    sk_B != k1_xboole_0 ),
    inference('sup-',[status(thm)],['67','116'])).

thf('118',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['62'])).

thf('119',plain,(
    sk_A != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['117','118'])).

thf('120',plain,(
    sk_A != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['63','119'])).

thf('121',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['61','120'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.5oTQ6dq23g
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:13:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 8.52/8.74  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 8.52/8.74  % Solved by: fo/fo7.sh
% 8.52/8.74  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.52/8.74  % done 4099 iterations in 8.273s
% 8.52/8.74  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 8.52/8.74  % SZS output start Refutation
% 8.52/8.74  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 8.52/8.74  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 8.52/8.74  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 8.52/8.74  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 8.52/8.74  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 8.52/8.74  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 8.52/8.74  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.52/8.74  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 8.52/8.74  thf(sk_B_type, type, sk_B: $i).
% 8.52/8.74  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 8.52/8.74  thf(sk_A_type, type, sk_A: $i).
% 8.52/8.74  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.52/8.74  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 8.52/8.74  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 8.52/8.74  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 8.52/8.74  thf(s3_funct_1__e2_24__funct_1, axiom,
% 8.52/8.74    (![A:$i,B:$i]:
% 8.52/8.74     ( ?[C:$i]:
% 8.52/8.74       ( ( ![D:$i]:
% 8.52/8.74           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 8.52/8.74         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 8.52/8.74         ( v1_relat_1 @ C ) ) ))).
% 8.52/8.74  thf('0', plain,
% 8.52/8.74      (![X13 : $i, X14 : $i]: ((k1_relat_1 @ (sk_C_2 @ X13 @ X14)) = (X14))),
% 8.52/8.74      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 8.52/8.74  thf(t64_relat_1, axiom,
% 8.52/8.74    (![A:$i]:
% 8.52/8.74     ( ( v1_relat_1 @ A ) =>
% 8.52/8.74       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 8.52/8.74           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 8.52/8.74         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 8.52/8.74  thf('1', plain,
% 8.52/8.74      (![X4 : $i]:
% 8.52/8.74         (((k1_relat_1 @ X4) != (k1_xboole_0))
% 8.52/8.74          | ((X4) = (k1_xboole_0))
% 8.52/8.74          | ~ (v1_relat_1 @ X4))),
% 8.52/8.74      inference('cnf', [status(esa)], [t64_relat_1])).
% 8.52/8.74  thf('2', plain,
% 8.52/8.74      (![X0 : $i, X1 : $i]:
% 8.52/8.74         (((X0) != (k1_xboole_0))
% 8.52/8.74          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0))
% 8.52/8.74          | ((sk_C_2 @ X1 @ X0) = (k1_xboole_0)))),
% 8.52/8.74      inference('sup-', [status(thm)], ['0', '1'])).
% 8.52/8.74  thf('3', plain,
% 8.52/8.74      (![X1 : $i]:
% 8.52/8.74         (((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))
% 8.52/8.74          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ k1_xboole_0)))),
% 8.52/8.74      inference('simplify', [status(thm)], ['2'])).
% 8.52/8.74  thf('4', plain, (![X13 : $i, X14 : $i]: (v1_relat_1 @ (sk_C_2 @ X13 @ X14))),
% 8.52/8.74      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 8.52/8.74  thf('5', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 8.52/8.74      inference('demod', [status(thm)], ['3', '4'])).
% 8.52/8.74  thf('6', plain,
% 8.52/8.74      (![X13 : $i, X14 : $i]: ((k1_relat_1 @ (sk_C_2 @ X13 @ X14)) = (X14))),
% 8.52/8.74      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 8.52/8.74  thf('7', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 8.52/8.74      inference('sup+', [status(thm)], ['5', '6'])).
% 8.52/8.74  thf(d5_funct_1, axiom,
% 8.52/8.74    (![A:$i]:
% 8.52/8.74     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 8.52/8.74       ( ![B:$i]:
% 8.52/8.74         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 8.52/8.74           ( ![C:$i]:
% 8.52/8.74             ( ( r2_hidden @ C @ B ) <=>
% 8.52/8.74               ( ?[D:$i]:
% 8.52/8.74                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 8.52/8.74                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 8.52/8.74  thf('8', plain,
% 8.52/8.74      (![X6 : $i, X7 : $i]:
% 8.52/8.74         ((r2_hidden @ (sk_C_1 @ X6 @ X7) @ X6)
% 8.52/8.74          | (r2_hidden @ (sk_D @ X6 @ X7) @ (k1_relat_1 @ X7))
% 8.52/8.74          | ((X6) = (k2_relat_1 @ X7))
% 8.52/8.74          | ~ (v1_funct_1 @ X7)
% 8.52/8.74          | ~ (v1_relat_1 @ X7))),
% 8.52/8.74      inference('cnf', [status(esa)], [d5_funct_1])).
% 8.52/8.74  thf('9', plain,
% 8.52/8.74      (![X0 : $i]:
% 8.52/8.74         ((r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 8.52/8.74          | ~ (v1_relat_1 @ k1_xboole_0)
% 8.52/8.74          | ~ (v1_funct_1 @ k1_xboole_0)
% 8.52/8.74          | ((X0) = (k2_relat_1 @ k1_xboole_0))
% 8.52/8.74          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 8.52/8.74      inference('sup+', [status(thm)], ['7', '8'])).
% 8.52/8.74  thf('10', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 8.52/8.74      inference('demod', [status(thm)], ['3', '4'])).
% 8.52/8.74  thf('11', plain,
% 8.52/8.74      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (sk_C_2 @ X13 @ X14))),
% 8.52/8.74      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 8.52/8.74  thf('12', plain, ((v1_relat_1 @ k1_xboole_0)),
% 8.52/8.74      inference('sup+', [status(thm)], ['10', '11'])).
% 8.52/8.74  thf('13', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 8.52/8.74      inference('demod', [status(thm)], ['3', '4'])).
% 8.52/8.74  thf('14', plain,
% 8.52/8.74      (![X13 : $i, X14 : $i]: (v1_funct_1 @ (sk_C_2 @ X13 @ X14))),
% 8.52/8.74      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 8.52/8.74  thf('15', plain, ((v1_funct_1 @ k1_xboole_0)),
% 8.52/8.74      inference('sup+', [status(thm)], ['13', '14'])).
% 8.52/8.74  thf('16', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 8.52/8.74      inference('sup+', [status(thm)], ['5', '6'])).
% 8.52/8.74  thf(t65_relat_1, axiom,
% 8.52/8.74    (![A:$i]:
% 8.52/8.74     ( ( v1_relat_1 @ A ) =>
% 8.52/8.74       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 8.52/8.74         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 8.52/8.74  thf('17', plain,
% 8.52/8.74      (![X5 : $i]:
% 8.52/8.74         (((k1_relat_1 @ X5) != (k1_xboole_0))
% 8.52/8.74          | ((k2_relat_1 @ X5) = (k1_xboole_0))
% 8.52/8.74          | ~ (v1_relat_1 @ X5))),
% 8.52/8.74      inference('cnf', [status(esa)], [t65_relat_1])).
% 8.52/8.74  thf('18', plain,
% 8.52/8.74      ((((k1_xboole_0) != (k1_xboole_0))
% 8.52/8.74        | ~ (v1_relat_1 @ k1_xboole_0)
% 8.52/8.74        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 8.52/8.74      inference('sup-', [status(thm)], ['16', '17'])).
% 8.52/8.74  thf('19', plain, ((v1_relat_1 @ k1_xboole_0)),
% 8.52/8.74      inference('sup+', [status(thm)], ['10', '11'])).
% 8.52/8.74  thf('20', plain,
% 8.52/8.74      ((((k1_xboole_0) != (k1_xboole_0))
% 8.52/8.74        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 8.52/8.74      inference('demod', [status(thm)], ['18', '19'])).
% 8.52/8.74  thf('21', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 8.52/8.74      inference('simplify', [status(thm)], ['20'])).
% 8.52/8.74  thf('22', plain,
% 8.52/8.74      (![X0 : $i]:
% 8.52/8.74         ((r2_hidden @ (sk_D @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 8.52/8.74          | ((X0) = (k1_xboole_0))
% 8.52/8.74          | (r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0))),
% 8.52/8.74      inference('demod', [status(thm)], ['9', '12', '15', '21'])).
% 8.52/8.74  thf('23', plain,
% 8.52/8.74      (![X13 : $i, X14 : $i, X15 : $i]:
% 8.52/8.74         (((k1_funct_1 @ (sk_C_2 @ X13 @ X14) @ X15) = (X13))
% 8.52/8.74          | ~ (r2_hidden @ X15 @ X14))),
% 8.52/8.74      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 8.52/8.74  thf('24', plain,
% 8.52/8.74      (![X0 : $i, X1 : $i]:
% 8.52/8.74         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 8.52/8.74          | ((X0) = (k1_xboole_0))
% 8.52/8.74          | ((k1_funct_1 @ (sk_C_2 @ X1 @ k1_xboole_0) @ 
% 8.52/8.74              (sk_D @ X0 @ k1_xboole_0)) = (X1)))),
% 8.52/8.74      inference('sup-', [status(thm)], ['22', '23'])).
% 8.52/8.74  thf('25', plain, (![X1 : $i]: ((sk_C_2 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 8.52/8.74      inference('demod', [status(thm)], ['3', '4'])).
% 8.52/8.74  thf('26', plain,
% 8.52/8.74      (![X0 : $i, X1 : $i]:
% 8.52/8.74         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 8.52/8.74          | ((X0) = (k1_xboole_0))
% 8.52/8.74          | ((k1_funct_1 @ k1_xboole_0 @ (sk_D @ X0 @ k1_xboole_0)) = (X1)))),
% 8.52/8.74      inference('demod', [status(thm)], ['24', '25'])).
% 8.52/8.74  thf('27', plain,
% 8.52/8.74      (![X0 : $i, X1 : $i]:
% 8.52/8.74         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 8.52/8.74          | ((X0) = (k1_xboole_0))
% 8.52/8.74          | ((k1_funct_1 @ k1_xboole_0 @ (sk_D @ X0 @ k1_xboole_0)) = (X1)))),
% 8.52/8.74      inference('demod', [status(thm)], ['24', '25'])).
% 8.52/8.74  thf('28', plain,
% 8.52/8.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.52/8.74         (((X0) = (X1))
% 8.52/8.74          | ((X2) = (k1_xboole_0))
% 8.52/8.74          | (r2_hidden @ (sk_C_1 @ X2 @ k1_xboole_0) @ X2)
% 8.52/8.74          | ((X2) = (k1_xboole_0))
% 8.52/8.74          | (r2_hidden @ (sk_C_1 @ X2 @ k1_xboole_0) @ X2))),
% 8.52/8.74      inference('sup+', [status(thm)], ['26', '27'])).
% 8.52/8.74  thf('29', plain,
% 8.52/8.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.52/8.74         ((r2_hidden @ (sk_C_1 @ X2 @ k1_xboole_0) @ X2)
% 8.52/8.74          | ((X2) = (k1_xboole_0))
% 8.52/8.74          | ((X0) = (X1)))),
% 8.52/8.74      inference('simplify', [status(thm)], ['28'])).
% 8.52/8.74  thf('30', plain,
% 8.52/8.74      (![X0 : $i]:
% 8.52/8.74         ((r2_hidden @ (sk_C_1 @ X0 @ k1_xboole_0) @ X0)
% 8.52/8.74          | ((X0) = (k1_xboole_0)))),
% 8.52/8.74      inference('condensation', [status(thm)], ['29'])).
% 8.52/8.74  thf(d3_tarski, axiom,
% 8.52/8.74    (![A:$i,B:$i]:
% 8.52/8.74     ( ( r1_tarski @ A @ B ) <=>
% 8.52/8.74       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 8.52/8.74  thf('31', plain,
% 8.52/8.74      (![X1 : $i, X3 : $i]:
% 8.52/8.74         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 8.52/8.74      inference('cnf', [status(esa)], [d3_tarski])).
% 8.52/8.74  thf('32', plain,
% 8.52/8.74      (![X7 : $i, X9 : $i, X10 : $i]:
% 8.52/8.74         (((X9) != (k2_relat_1 @ X7))
% 8.52/8.74          | ((X10) = (k1_funct_1 @ X7 @ (sk_D_1 @ X10 @ X7)))
% 8.52/8.74          | ~ (r2_hidden @ X10 @ X9)
% 8.52/8.74          | ~ (v1_funct_1 @ X7)
% 8.52/8.74          | ~ (v1_relat_1 @ X7))),
% 8.52/8.74      inference('cnf', [status(esa)], [d5_funct_1])).
% 8.52/8.74  thf('33', plain,
% 8.52/8.74      (![X7 : $i, X10 : $i]:
% 8.52/8.74         (~ (v1_relat_1 @ X7)
% 8.52/8.74          | ~ (v1_funct_1 @ X7)
% 8.52/8.74          | ~ (r2_hidden @ X10 @ (k2_relat_1 @ X7))
% 8.52/8.74          | ((X10) = (k1_funct_1 @ X7 @ (sk_D_1 @ X10 @ X7))))),
% 8.52/8.74      inference('simplify', [status(thm)], ['32'])).
% 8.52/8.74  thf('34', plain,
% 8.52/8.74      (![X0 : $i, X1 : $i]:
% 8.52/8.74         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 8.52/8.74          | ((sk_C @ X1 @ (k2_relat_1 @ X0))
% 8.52/8.74              = (k1_funct_1 @ X0 @ 
% 8.52/8.74                 (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)))
% 8.52/8.74          | ~ (v1_funct_1 @ X0)
% 8.52/8.74          | ~ (v1_relat_1 @ X0))),
% 8.52/8.74      inference('sup-', [status(thm)], ['31', '33'])).
% 8.52/8.74  thf('35', plain,
% 8.52/8.74      (![X13 : $i, X14 : $i]: ((k1_relat_1 @ (sk_C_2 @ X13 @ X14)) = (X14))),
% 8.52/8.74      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 8.52/8.74  thf('36', plain,
% 8.52/8.74      (![X1 : $i, X3 : $i]:
% 8.52/8.74         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 8.52/8.74      inference('cnf', [status(esa)], [d3_tarski])).
% 8.52/8.74  thf('37', plain,
% 8.52/8.74      (![X7 : $i, X9 : $i, X10 : $i]:
% 8.52/8.74         (((X9) != (k2_relat_1 @ X7))
% 8.52/8.74          | (r2_hidden @ (sk_D_1 @ X10 @ X7) @ (k1_relat_1 @ X7))
% 8.52/8.74          | ~ (r2_hidden @ X10 @ X9)
% 8.52/8.74          | ~ (v1_funct_1 @ X7)
% 8.52/8.74          | ~ (v1_relat_1 @ X7))),
% 8.52/8.74      inference('cnf', [status(esa)], [d5_funct_1])).
% 8.52/8.74  thf('38', plain,
% 8.52/8.74      (![X7 : $i, X10 : $i]:
% 8.52/8.74         (~ (v1_relat_1 @ X7)
% 8.52/8.74          | ~ (v1_funct_1 @ X7)
% 8.52/8.74          | ~ (r2_hidden @ X10 @ (k2_relat_1 @ X7))
% 8.52/8.74          | (r2_hidden @ (sk_D_1 @ X10 @ X7) @ (k1_relat_1 @ X7)))),
% 8.52/8.74      inference('simplify', [status(thm)], ['37'])).
% 8.52/8.74  thf('39', plain,
% 8.52/8.74      (![X0 : $i, X1 : $i]:
% 8.52/8.74         ((r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 8.52/8.74          | (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 8.52/8.74             (k1_relat_1 @ X0))
% 8.52/8.74          | ~ (v1_funct_1 @ X0)
% 8.52/8.74          | ~ (v1_relat_1 @ X0))),
% 8.52/8.74      inference('sup-', [status(thm)], ['36', '38'])).
% 8.52/8.74  thf('40', plain,
% 8.52/8.74      (![X13 : $i, X14 : $i, X15 : $i]:
% 8.52/8.74         (((k1_funct_1 @ (sk_C_2 @ X13 @ X14) @ X15) = (X13))
% 8.52/8.74          | ~ (r2_hidden @ X15 @ X14))),
% 8.52/8.74      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 8.52/8.74  thf('41', plain,
% 8.52/8.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.52/8.74         (~ (v1_relat_1 @ X0)
% 8.52/8.74          | ~ (v1_funct_1 @ X0)
% 8.52/8.74          | (r1_tarski @ (k2_relat_1 @ X0) @ X1)
% 8.52/8.74          | ((k1_funct_1 @ (sk_C_2 @ X2 @ (k1_relat_1 @ X0)) @ 
% 8.52/8.74              (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)) = (X2)))),
% 8.52/8.74      inference('sup-', [status(thm)], ['39', '40'])).
% 8.52/8.74  thf('42', plain,
% 8.52/8.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.52/8.74         (((k1_funct_1 @ (sk_C_2 @ X1 @ X0) @ 
% 8.52/8.74            (sk_D_1 @ (sk_C @ X3 @ (k2_relat_1 @ (sk_C_2 @ X2 @ X0))) @ 
% 8.52/8.74             (sk_C_2 @ X2 @ X0)))
% 8.52/8.74            = (X1))
% 8.52/8.74          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X2 @ X0)) @ X3)
% 8.52/8.74          | ~ (v1_funct_1 @ (sk_C_2 @ X2 @ X0))
% 8.52/8.74          | ~ (v1_relat_1 @ (sk_C_2 @ X2 @ X0)))),
% 8.52/8.74      inference('sup+', [status(thm)], ['35', '41'])).
% 8.52/8.74  thf('43', plain,
% 8.52/8.74      (![X13 : $i, X14 : $i]: (v1_funct_1 @ (sk_C_2 @ X13 @ X14))),
% 8.52/8.74      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 8.52/8.74  thf('44', plain,
% 8.52/8.74      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (sk_C_2 @ X13 @ X14))),
% 8.52/8.74      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 8.52/8.74  thf('45', plain,
% 8.52/8.74      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.52/8.74         (((k1_funct_1 @ (sk_C_2 @ X1 @ X0) @ 
% 8.52/8.74            (sk_D_1 @ (sk_C @ X3 @ (k2_relat_1 @ (sk_C_2 @ X2 @ X0))) @ 
% 8.52/8.74             (sk_C_2 @ X2 @ X0)))
% 8.52/8.74            = (X1))
% 8.52/8.74          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X2 @ X0)) @ X3))),
% 8.52/8.74      inference('demod', [status(thm)], ['42', '43', '44'])).
% 8.52/8.74  thf('46', plain,
% 8.52/8.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.52/8.74         (((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) = (X1))
% 8.52/8.74          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0))
% 8.52/8.74          | ~ (v1_funct_1 @ (sk_C_2 @ X1 @ X0))
% 8.52/8.74          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2)
% 8.52/8.74          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2))),
% 8.52/8.74      inference('sup+', [status(thm)], ['34', '45'])).
% 8.52/8.74  thf('47', plain,
% 8.52/8.74      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (sk_C_2 @ X13 @ X14))),
% 8.52/8.74      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 8.52/8.74  thf('48', plain,
% 8.52/8.74      (![X13 : $i, X14 : $i]: (v1_funct_1 @ (sk_C_2 @ X13 @ X14))),
% 8.52/8.74      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 8.52/8.74  thf('49', plain,
% 8.52/8.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.52/8.74         (((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) = (X1))
% 8.52/8.74          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2)
% 8.52/8.74          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2))),
% 8.52/8.74      inference('demod', [status(thm)], ['46', '47', '48'])).
% 8.52/8.74  thf('50', plain,
% 8.52/8.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.52/8.74         ((r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0)) @ X2)
% 8.52/8.74          | ((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) = (X1)))),
% 8.52/8.74      inference('simplify', [status(thm)], ['49'])).
% 8.52/8.74  thf('51', plain,
% 8.52/8.74      (![X1 : $i, X3 : $i]:
% 8.52/8.74         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 8.52/8.74      inference('cnf', [status(esa)], [d3_tarski])).
% 8.52/8.74  thf('52', plain,
% 8.52/8.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.52/8.74         (~ (r2_hidden @ X0 @ X1)
% 8.52/8.74          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X2)) @ X1)
% 8.52/8.74          | (r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X2)) @ X1))),
% 8.52/8.74      inference('sup-', [status(thm)], ['50', '51'])).
% 8.52/8.74  thf('53', plain,
% 8.52/8.74      (![X0 : $i, X1 : $i, X2 : $i]:
% 8.52/8.74         ((r1_tarski @ (k2_relat_1 @ (sk_C_2 @ X0 @ X2)) @ X1)
% 8.52/8.74          | ~ (r2_hidden @ X0 @ X1))),
% 8.52/8.74      inference('simplify', [status(thm)], ['52'])).
% 8.52/8.74  thf('54', plain,
% 8.52/8.74      (![X0 : $i, X1 : $i]:
% 8.52/8.74         (((X0) = (k1_xboole_0))
% 8.52/8.74          | (r1_tarski @ 
% 8.52/8.74             (k2_relat_1 @ (sk_C_2 @ (sk_C_1 @ X0 @ k1_xboole_0) @ X1)) @ X0))),
% 8.52/8.74      inference('sup-', [status(thm)], ['30', '53'])).
% 8.52/8.74  thf(t18_funct_1, conjecture,
% 8.52/8.74    (![A:$i,B:$i]:
% 8.52/8.74     ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 8.52/8.74          ( ![C:$i]:
% 8.52/8.74            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 8.52/8.74              ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 8.52/8.74                   ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ))).
% 8.52/8.74  thf(zf_stmt_0, negated_conjecture,
% 8.52/8.74    (~( ![A:$i,B:$i]:
% 8.52/8.74        ( ~( ( ~( ( ( A ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) ) & 
% 8.52/8.74             ( ![C:$i]:
% 8.52/8.74               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 8.52/8.74                 ( ~( ( ( B ) = ( k1_relat_1 @ C ) ) & 
% 8.52/8.74                      ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) ) ) ) ) ) ) )),
% 8.52/8.74    inference('cnf.neg', [status(esa)], [t18_funct_1])).
% 8.52/8.74  thf('55', plain,
% 8.52/8.74      (![X16 : $i]:
% 8.52/8.74         (~ (r1_tarski @ (k2_relat_1 @ X16) @ sk_A)
% 8.52/8.74          | ((sk_B) != (k1_relat_1 @ X16))
% 8.52/8.74          | ~ (v1_funct_1 @ X16)
% 8.52/8.74          | ~ (v1_relat_1 @ X16))),
% 8.52/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.52/8.74  thf('56', plain,
% 8.52/8.74      (![X0 : $i]:
% 8.52/8.74         (((sk_A) = (k1_xboole_0))
% 8.52/8.74          | ~ (v1_relat_1 @ (sk_C_2 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0))
% 8.52/8.74          | ~ (v1_funct_1 @ (sk_C_2 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0))
% 8.52/8.74          | ((sk_B)
% 8.52/8.74              != (k1_relat_1 @ (sk_C_2 @ (sk_C_1 @ sk_A @ k1_xboole_0) @ X0))))),
% 8.52/8.74      inference('sup-', [status(thm)], ['54', '55'])).
% 8.52/8.74  thf('57', plain,
% 8.52/8.74      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (sk_C_2 @ X13 @ X14))),
% 8.52/8.74      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 8.52/8.74  thf('58', plain,
% 8.52/8.74      (![X13 : $i, X14 : $i]: (v1_funct_1 @ (sk_C_2 @ X13 @ X14))),
% 8.52/8.74      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 8.52/8.74  thf('59', plain,
% 8.52/8.74      (![X13 : $i, X14 : $i]: ((k1_relat_1 @ (sk_C_2 @ X13 @ X14)) = (X14))),
% 8.52/8.74      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 8.52/8.74  thf('60', plain, (![X0 : $i]: (((sk_A) = (k1_xboole_0)) | ((sk_B) != (X0)))),
% 8.52/8.74      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 8.52/8.74  thf('61', plain, (((sk_A) = (k1_xboole_0))),
% 8.52/8.74      inference('simplify', [status(thm)], ['60'])).
% 8.52/8.74  thf('62', plain, ((((sk_A) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0)))),
% 8.52/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.52/8.74  thf('63', plain,
% 8.52/8.74      ((((sk_A) != (k1_xboole_0))) <= (~ (((sk_A) = (k1_xboole_0))))),
% 8.52/8.74      inference('split', [status(esa)], ['62'])).
% 8.52/8.74  thf('64', plain,
% 8.52/8.74      (![X1 : $i, X3 : $i]:
% 8.52/8.74         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 8.52/8.74      inference('cnf', [status(esa)], [d3_tarski])).
% 8.52/8.74  thf('65', plain,
% 8.52/8.74      (![X1 : $i, X3 : $i]:
% 8.52/8.74         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 8.52/8.74      inference('cnf', [status(esa)], [d3_tarski])).
% 8.52/8.74  thf('66', plain,
% 8.52/8.74      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 8.52/8.74      inference('sup-', [status(thm)], ['64', '65'])).
% 8.52/8.74  thf('67', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 8.52/8.74      inference('simplify', [status(thm)], ['66'])).
% 8.52/8.74  thf('68', plain,
% 8.52/8.74      (![X1 : $i, X3 : $i]:
% 8.52/8.74         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 8.52/8.74      inference('cnf', [status(esa)], [d3_tarski])).
% 8.52/8.74  thf('69', plain,
% 8.52/8.74      (![X13 : $i, X14 : $i]: ((k1_relat_1 @ (sk_C_2 @ X13 @ X14)) = (X14))),
% 8.52/8.74      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 8.52/8.74  thf('70', plain,
% 8.52/8.74      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('split', [status(esa)], ['62'])).
% 8.52/8.74  thf('71', plain,
% 8.52/8.74      (![X4 : $i]:
% 8.52/8.74         (((k1_relat_1 @ X4) != (k1_xboole_0))
% 8.52/8.74          | ((X4) = (k1_xboole_0))
% 8.52/8.74          | ~ (v1_relat_1 @ X4))),
% 8.52/8.74      inference('cnf', [status(esa)], [t64_relat_1])).
% 8.52/8.74  thf('72', plain,
% 8.52/8.74      ((![X0 : $i]:
% 8.52/8.74          (((k1_relat_1 @ X0) != (sk_B))
% 8.52/8.74           | ~ (v1_relat_1 @ X0)
% 8.52/8.74           | ((X0) = (k1_xboole_0))))
% 8.52/8.74         <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('sup-', [status(thm)], ['70', '71'])).
% 8.52/8.74  thf('73', plain,
% 8.52/8.74      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('split', [status(esa)], ['62'])).
% 8.52/8.74  thf('74', plain,
% 8.52/8.74      ((![X0 : $i]:
% 8.52/8.74          (((k1_relat_1 @ X0) != (sk_B))
% 8.52/8.74           | ~ (v1_relat_1 @ X0)
% 8.52/8.74           | ((X0) = (sk_B))))
% 8.52/8.74         <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('demod', [status(thm)], ['72', '73'])).
% 8.52/8.74  thf('75', plain,
% 8.52/8.74      ((![X0 : $i, X1 : $i]:
% 8.52/8.74          (((X0) != (sk_B))
% 8.52/8.74           | ((sk_C_2 @ X1 @ X0) = (sk_B))
% 8.52/8.74           | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0))))
% 8.52/8.74         <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('sup-', [status(thm)], ['69', '74'])).
% 8.52/8.74  thf('76', plain,
% 8.52/8.74      ((![X1 : $i]:
% 8.52/8.74          (~ (v1_relat_1 @ (sk_C_2 @ X1 @ sk_B))
% 8.52/8.74           | ((sk_C_2 @ X1 @ sk_B) = (sk_B))))
% 8.52/8.74         <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('simplify', [status(thm)], ['75'])).
% 8.52/8.74  thf('77', plain,
% 8.52/8.74      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (sk_C_2 @ X13 @ X14))),
% 8.52/8.74      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 8.52/8.74  thf('78', plain,
% 8.52/8.74      ((![X1 : $i]: ((sk_C_2 @ X1 @ sk_B) = (sk_B)))
% 8.52/8.74         <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('demod', [status(thm)], ['76', '77'])).
% 8.52/8.74  thf('79', plain,
% 8.52/8.74      (![X13 : $i, X14 : $i]: ((k1_relat_1 @ (sk_C_2 @ X13 @ X14)) = (X14))),
% 8.52/8.74      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 8.52/8.74  thf('80', plain,
% 8.52/8.74      ((((k1_relat_1 @ sk_B) = (sk_B))) <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('sup+', [status(thm)], ['78', '79'])).
% 8.52/8.74  thf('81', plain,
% 8.52/8.74      (![X5 : $i]:
% 8.52/8.74         (((k1_relat_1 @ X5) != (k1_xboole_0))
% 8.52/8.74          | ((k2_relat_1 @ X5) = (k1_xboole_0))
% 8.52/8.74          | ~ (v1_relat_1 @ X5))),
% 8.52/8.74      inference('cnf', [status(esa)], [t65_relat_1])).
% 8.52/8.74  thf('82', plain,
% 8.52/8.74      (((((sk_B) != (k1_xboole_0))
% 8.52/8.74         | ~ (v1_relat_1 @ sk_B)
% 8.52/8.74         | ((k2_relat_1 @ sk_B) = (k1_xboole_0))))
% 8.52/8.74         <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('sup-', [status(thm)], ['80', '81'])).
% 8.52/8.74  thf('83', plain,
% 8.52/8.74      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('split', [status(esa)], ['62'])).
% 8.52/8.74  thf('84', plain,
% 8.52/8.74      ((![X1 : $i]: ((sk_C_2 @ X1 @ sk_B) = (sk_B)))
% 8.52/8.74         <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('demod', [status(thm)], ['76', '77'])).
% 8.52/8.74  thf('85', plain,
% 8.52/8.74      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (sk_C_2 @ X13 @ X14))),
% 8.52/8.74      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 8.52/8.74  thf('86', plain, (((v1_relat_1 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('sup+', [status(thm)], ['84', '85'])).
% 8.52/8.74  thf('87', plain,
% 8.52/8.74      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('split', [status(esa)], ['62'])).
% 8.52/8.74  thf('88', plain,
% 8.52/8.74      (((((sk_B) != (sk_B)) | ((k2_relat_1 @ sk_B) = (sk_B))))
% 8.52/8.74         <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('demod', [status(thm)], ['82', '83', '86', '87'])).
% 8.52/8.74  thf('89', plain,
% 8.52/8.74      ((((k2_relat_1 @ sk_B) = (sk_B))) <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('simplify', [status(thm)], ['88'])).
% 8.52/8.74  thf('90', plain,
% 8.52/8.74      (![X7 : $i, X10 : $i]:
% 8.52/8.74         (~ (v1_relat_1 @ X7)
% 8.52/8.74          | ~ (v1_funct_1 @ X7)
% 8.52/8.74          | ~ (r2_hidden @ X10 @ (k2_relat_1 @ X7))
% 8.52/8.74          | (r2_hidden @ (sk_D_1 @ X10 @ X7) @ (k1_relat_1 @ X7)))),
% 8.52/8.74      inference('simplify', [status(thm)], ['37'])).
% 8.52/8.74  thf('91', plain,
% 8.52/8.74      ((![X0 : $i]:
% 8.52/8.74          (~ (r2_hidden @ X0 @ sk_B)
% 8.52/8.74           | (r2_hidden @ (sk_D_1 @ X0 @ sk_B) @ (k1_relat_1 @ sk_B))
% 8.52/8.74           | ~ (v1_funct_1 @ sk_B)
% 8.52/8.74           | ~ (v1_relat_1 @ sk_B)))
% 8.52/8.74         <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('sup-', [status(thm)], ['89', '90'])).
% 8.52/8.74  thf('92', plain,
% 8.52/8.74      ((((k1_relat_1 @ sk_B) = (sk_B))) <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('sup+', [status(thm)], ['78', '79'])).
% 8.52/8.74  thf('93', plain,
% 8.52/8.74      ((![X1 : $i]: ((sk_C_2 @ X1 @ sk_B) = (sk_B)))
% 8.52/8.74         <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('demod', [status(thm)], ['76', '77'])).
% 8.52/8.74  thf('94', plain,
% 8.52/8.74      (![X13 : $i, X14 : $i]: (v1_funct_1 @ (sk_C_2 @ X13 @ X14))),
% 8.52/8.74      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 8.52/8.74  thf('95', plain, (((v1_funct_1 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('sup+', [status(thm)], ['93', '94'])).
% 8.52/8.74  thf('96', plain, (((v1_relat_1 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('sup+', [status(thm)], ['84', '85'])).
% 8.52/8.74  thf('97', plain,
% 8.52/8.74      ((![X0 : $i]:
% 8.52/8.74          (~ (r2_hidden @ X0 @ sk_B)
% 8.52/8.74           | (r2_hidden @ (sk_D_1 @ X0 @ sk_B) @ sk_B)))
% 8.52/8.74         <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('demod', [status(thm)], ['91', '92', '95', '96'])).
% 8.52/8.74  thf('98', plain,
% 8.52/8.74      ((![X0 : $i]:
% 8.52/8.74          ((r1_tarski @ sk_B @ X0)
% 8.52/8.74           | (r2_hidden @ (sk_D_1 @ (sk_C @ X0 @ sk_B) @ sk_B) @ sk_B)))
% 8.52/8.74         <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('sup-', [status(thm)], ['68', '97'])).
% 8.52/8.74  thf('99', plain,
% 8.52/8.74      (![X13 : $i, X14 : $i, X15 : $i]:
% 8.52/8.74         (((k1_funct_1 @ (sk_C_2 @ X13 @ X14) @ X15) = (X13))
% 8.52/8.74          | ~ (r2_hidden @ X15 @ X14))),
% 8.52/8.74      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 8.52/8.74  thf('100', plain,
% 8.52/8.74      ((![X0 : $i, X1 : $i]:
% 8.52/8.74          ((r1_tarski @ sk_B @ X0)
% 8.52/8.74           | ((k1_funct_1 @ (sk_C_2 @ X1 @ sk_B) @ 
% 8.52/8.74               (sk_D_1 @ (sk_C @ X0 @ sk_B) @ sk_B)) = (X1))))
% 8.52/8.74         <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('sup-', [status(thm)], ['98', '99'])).
% 8.52/8.74  thf('101', plain,
% 8.52/8.74      ((![X1 : $i]: ((sk_C_2 @ X1 @ sk_B) = (sk_B)))
% 8.52/8.74         <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('demod', [status(thm)], ['76', '77'])).
% 8.52/8.74  thf('102', plain,
% 8.52/8.74      ((![X0 : $i, X1 : $i]:
% 8.52/8.74          ((r1_tarski @ sk_B @ X0)
% 8.52/8.74           | ((k1_funct_1 @ sk_B @ (sk_D_1 @ (sk_C @ X0 @ sk_B) @ sk_B)) = (X1))))
% 8.52/8.74         <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('demod', [status(thm)], ['100', '101'])).
% 8.52/8.74  thf('103', plain,
% 8.52/8.74      ((![X0 : $i, X1 : $i]:
% 8.52/8.74          ((r1_tarski @ sk_B @ X0)
% 8.52/8.74           | ((k1_funct_1 @ sk_B @ (sk_D_1 @ (sk_C @ X0 @ sk_B) @ sk_B)) = (X1))))
% 8.52/8.74         <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('demod', [status(thm)], ['100', '101'])).
% 8.52/8.74  thf('104', plain,
% 8.52/8.74      ((![X0 : $i, X1 : $i, X2 : $i]:
% 8.52/8.74          (((X0) = (X1)) | (r1_tarski @ sk_B @ X2) | (r1_tarski @ sk_B @ X2)))
% 8.52/8.74         <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('sup+', [status(thm)], ['102', '103'])).
% 8.52/8.74  thf('105', plain,
% 8.52/8.74      ((![X0 : $i, X1 : $i, X2 : $i]: ((r1_tarski @ sk_B @ X2) | ((X0) = (X1))))
% 8.52/8.74         <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('simplify', [status(thm)], ['104'])).
% 8.52/8.74  thf('106', plain,
% 8.52/8.74      ((((k2_relat_1 @ sk_B) = (sk_B))) <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('simplify', [status(thm)], ['88'])).
% 8.52/8.74  thf('107', plain,
% 8.52/8.74      (![X16 : $i]:
% 8.52/8.74         (~ (r1_tarski @ (k2_relat_1 @ X16) @ sk_A)
% 8.52/8.74          | ((sk_B) != (k1_relat_1 @ X16))
% 8.52/8.74          | ~ (v1_funct_1 @ X16)
% 8.52/8.74          | ~ (v1_relat_1 @ X16))),
% 8.52/8.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.52/8.74  thf('108', plain,
% 8.52/8.74      (((~ (r1_tarski @ sk_B @ sk_A)
% 8.52/8.74         | ~ (v1_relat_1 @ sk_B)
% 8.52/8.74         | ~ (v1_funct_1 @ sk_B)
% 8.52/8.74         | ((sk_B) != (k1_relat_1 @ sk_B)))) <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('sup-', [status(thm)], ['106', '107'])).
% 8.52/8.74  thf('109', plain, (((v1_relat_1 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('sup+', [status(thm)], ['84', '85'])).
% 8.52/8.74  thf('110', plain, (((v1_funct_1 @ sk_B)) <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('sup+', [status(thm)], ['93', '94'])).
% 8.52/8.74  thf('111', plain,
% 8.52/8.74      ((((k1_relat_1 @ sk_B) = (sk_B))) <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('sup+', [status(thm)], ['78', '79'])).
% 8.52/8.74  thf('112', plain,
% 8.52/8.74      (((~ (r1_tarski @ sk_B @ sk_A) | ((sk_B) != (sk_B))))
% 8.52/8.74         <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('demod', [status(thm)], ['108', '109', '110', '111'])).
% 8.52/8.74  thf('113', plain,
% 8.52/8.74      ((~ (r1_tarski @ sk_B @ sk_A)) <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('simplify', [status(thm)], ['112'])).
% 8.52/8.74  thf('114', plain,
% 8.52/8.74      ((![X0 : $i, X1 : $i]: ((X0) = (X1))) <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('sup-', [status(thm)], ['105', '113'])).
% 8.52/8.74  thf('115', plain,
% 8.52/8.74      ((~ (r1_tarski @ sk_B @ sk_A)) <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('simplify', [status(thm)], ['112'])).
% 8.52/8.74  thf('116', plain,
% 8.52/8.74      ((![X0 : $i]: ~ (r1_tarski @ sk_B @ X0)) <= ((((sk_B) = (k1_xboole_0))))),
% 8.52/8.74      inference('sup-', [status(thm)], ['114', '115'])).
% 8.52/8.74  thf('117', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 8.52/8.74      inference('sup-', [status(thm)], ['67', '116'])).
% 8.52/8.74  thf('118', plain,
% 8.52/8.74      (~ (((sk_A) = (k1_xboole_0))) | (((sk_B) = (k1_xboole_0)))),
% 8.52/8.74      inference('split', [status(esa)], ['62'])).
% 8.52/8.74  thf('119', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 8.52/8.74      inference('sat_resolution*', [status(thm)], ['117', '118'])).
% 8.52/8.74  thf('120', plain, (((sk_A) != (k1_xboole_0))),
% 8.52/8.74      inference('simpl_trail', [status(thm)], ['63', '119'])).
% 8.52/8.74  thf('121', plain, ($false),
% 8.52/8.74      inference('simplify_reflect-', [status(thm)], ['61', '120'])).
% 8.52/8.74  
% 8.52/8.74  % SZS output end Refutation
% 8.52/8.74  
% 8.52/8.75  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
