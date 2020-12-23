%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UrQ52tqhzz

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:33 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 336 expanded)
%              Number of leaves         :   16 ( 108 expanded)
%              Depth                    :   22
%              Number of atoms          :  760 (3907 expanded)
%              Number of equality atoms :  119 ( 592 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

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
    ! [X3: $i,X4: $i] :
      ( ( k1_relat_1 @ ( sk_C_1 @ X3 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf(s3_funct_1__e2_25__funct_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ B @ C )
            = k1_xboole_0 ) )
      & ( ( k1_relat_1 @ B )
        = A )
      & ( v1_funct_1 @ B )
      & ( v1_relat_1 @ B ) ) )).

thf('1',plain,(
    ! [X6: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf(t16_funct_1,conjecture,(
    ! [A: $i] :
      ( ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ( ( ( ( k1_relat_1 @ B )
                    = A )
                  & ( ( k1_relat_1 @ C )
                    = A ) )
               => ( B = C ) ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ! [C: $i] :
                ( ( ( v1_relat_1 @ C )
                  & ( v1_funct_1 @ C ) )
               => ( ( ( ( k1_relat_1 @ B )
                      = A )
                    & ( ( k1_relat_1 @ C )
                      = A ) )
                 => ( B = C ) ) ) )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t16_funct_1])).

thf('2',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v1_relat_1 @ X8 )
      | ~ ( v1_funct_1 @ X8 )
      | ( X9 = X8 )
      | ( ( k1_relat_1 @ X8 )
       != sk_A )
      | ( ( k1_relat_1 @ X9 )
       != sk_A )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ( X1
        = ( sk_B @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_B @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X6: $i] :
      ( v1_funct_1 @ ( sk_B @ X6 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('5',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( sk_B @ X6 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ( X1
        = ( sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ! [X1: $i] :
      ( ( X1
        = ( sk_B @ sk_A ) )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ( ( sk_C_1 @ X1 @ X0 )
        = ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( sk_C_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('10',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_funct_1 @ ( sk_C_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ( ( sk_C_1 @ X1 @ X0 )
        = ( sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ! [X1: $i] :
      ( ( sk_C_1 @ X1 @ sk_A )
      = ( sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k1_relat_1 @ ( sk_C_1 @ X3 @ X4 ) )
      = X4 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('14',plain,(
    ! [X2: $i] :
      ( ( ( k1_relat_1 @ X2 )
       != k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ( ( sk_C_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X3: $i,X4: $i] :
      ( v1_relat_1 @ ( sk_C_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_C_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X1: $i] :
      ( ( sk_C_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('20',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X3 @ X4 ) @ X5 )
        = X3 )
      | ~ ( r2_hidden @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ( ( k1_funct_1 @ ( sk_C_1 @ X2 @ X0 ) @ ( sk_C @ X0 @ X1 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ k1_xboole_0 @ X1 ) )
        = X0 )
      | ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X1 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ k1_xboole_0 @ X1 ) )
        = X0 )
      | ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X1 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X2 ) @ X2 )
      | ( X2 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X2 ) @ X2 )
      | ( X2 = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X2 ) @ X2 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference(condensation,[status(thm)],['25'])).

thf('27',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X3 @ X4 ) @ X5 )
        = X3 )
      | ~ ( r2_hidden @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( sk_C_1 @ X1 @ X0 ) @ ( sk_C @ k1_xboole_0 @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( sk_B @ sk_A ) @ ( sk_C @ k1_xboole_0 @ sk_A ) )
        = X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['12','28'])).

thf('30',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( k1_funct_1 @ ( sk_B @ sk_A ) @ ( sk_C @ k1_xboole_0 @ sk_A ) )
      = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X1: $i] :
      ( ( sk_C_1 @ X1 @ sk_A )
      = ( sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('33',plain,(
    ! [X6: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X6 ) )
      = X6 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('34',plain,(
    ! [X2: $i] :
      ( ( ( k1_relat_1 @ X2 )
       != k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X6: $i] :
      ( v1_relat_1 @ ( sk_B @ X6 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_B @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,
    ( ( sk_B @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('40',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k1_funct_1 @ ( sk_B @ X6 ) @ X7 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X1 )
      | ( X1 = X0 )
      | ( ( k1_funct_1 @ ( sk_B @ X0 ) @ ( sk_C @ X0 @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('43',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k1_funct_1 @ ( sk_B @ X6 ) @ X7 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( sk_B @ X0 ) @ ( sk_C @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X0 @ sk_A ) @ ( sk_C @ k1_xboole_0 @ sk_A ) )
        = k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ k1_xboole_0 @ sk_A ) )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['32','44'])).

thf('46',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X0 @ sk_A ) @ ( sk_C @ k1_xboole_0 @ sk_A ) )
        = k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ k1_xboole_0 @ sk_A ) )
        = k1_xboole_0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['38','41'])).

thf('49',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X3 @ X4 ) @ X5 )
        = X3 )
      | ~ ( r2_hidden @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( sk_C_1 @ X1 @ X0 ) @ ( sk_C @ k1_xboole_0 @ X0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ k1_xboole_0 @ sk_A ) )
        = k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ k1_xboole_0 @ sk_A ) )
        = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ k1_xboole_0 @ sk_A ) )
        = k1_xboole_0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ k1_xboole_0 @ sk_A ) )
        = k1_xboole_0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference('simplify_reflect-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ k1_xboole_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference(condensation,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ k1_xboole_0 @ X1 ) )
        = X0 )
      | ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ X1 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','21'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['55','56'])).

thf('58',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A ) ) ),
    inference('simplify_reflect-',[status(thm)],['57','58'])).

thf('60',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( sk_A != X0 )
      | ( r2_hidden @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    r2_hidden @ ( sk_C @ k1_xboole_0 @ sk_A ) @ sk_A ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k1_funct_1 @ ( sk_B @ X6 ) @ X7 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('64',plain,
    ( ( k1_funct_1 @ ( sk_B @ sk_A ) @ ( sk_C @ k1_xboole_0 @ sk_A ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] : ( k1_xboole_0 = X0 ) ),
    inference(demod,[status(thm)],['31','64'])).

thf('66',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    sk_A != k1_xboole_0 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] : ( k1_xboole_0 = X0 ) ),
    inference(demod,[status(thm)],['31','64'])).

thf('69',plain,(
    $false ),
    inference('simplify_reflect+',[status(thm)],['67','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UrQ52tqhzz
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:38:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 81 iterations in 0.050s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.50  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.19/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.50  thf(sk_B_type, type, sk_B: $i > $i).
% 0.19/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.50  thf(s3_funct_1__e2_24__funct_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ?[C:$i]:
% 0.19/0.50       ( ( ![D:$i]:
% 0.19/0.50           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 0.19/0.50         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.19/0.50         ( v1_relat_1 @ C ) ) ))).
% 0.19/0.50  thf('0', plain,
% 0.19/0.50      (![X3 : $i, X4 : $i]: ((k1_relat_1 @ (sk_C_1 @ X3 @ X4)) = (X4))),
% 0.19/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.19/0.50  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ?[B:$i]:
% 0.19/0.50       ( ( ![C:$i]:
% 0.19/0.50           ( ( r2_hidden @ C @ A ) =>
% 0.19/0.50             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.19/0.50         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.19/0.50         ( v1_relat_1 @ B ) ) ))).
% 0.19/0.50  thf('1', plain, (![X6 : $i]: ((k1_relat_1 @ (sk_B @ X6)) = (X6))),
% 0.19/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.19/0.50  thf(t16_funct_1, conjecture,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( ![B:$i]:
% 0.19/0.50         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.50           ( ![C:$i]:
% 0.19/0.50             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.50               ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.19/0.50                   ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.19/0.50                 ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.19/0.50       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i]:
% 0.19/0.50        ( ( ![B:$i]:
% 0.19/0.50            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.50              ( ![C:$i]:
% 0.19/0.50                ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.50                  ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.19/0.50                      ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.19/0.50                    ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.19/0.50          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t16_funct_1])).
% 0.19/0.50  thf('2', plain,
% 0.19/0.50      (![X8 : $i, X9 : $i]:
% 0.19/0.50         (~ (v1_relat_1 @ X8)
% 0.19/0.50          | ~ (v1_funct_1 @ X8)
% 0.19/0.50          | ((X9) = (X8))
% 0.19/0.50          | ((k1_relat_1 @ X8) != (sk_A))
% 0.19/0.50          | ((k1_relat_1 @ X9) != (sk_A))
% 0.19/0.50          | ~ (v1_funct_1 @ X9)
% 0.19/0.50          | ~ (v1_relat_1 @ X9))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('3', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (((X0) != (sk_A))
% 0.19/0.50          | ~ (v1_relat_1 @ X1)
% 0.19/0.50          | ~ (v1_funct_1 @ X1)
% 0.19/0.50          | ((k1_relat_1 @ X1) != (sk_A))
% 0.19/0.50          | ((X1) = (sk_B @ X0))
% 0.19/0.50          | ~ (v1_funct_1 @ (sk_B @ X0))
% 0.19/0.50          | ~ (v1_relat_1 @ (sk_B @ X0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.50  thf('4', plain, (![X6 : $i]: (v1_funct_1 @ (sk_B @ X6))),
% 0.19/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.19/0.50  thf('5', plain, (![X6 : $i]: (v1_relat_1 @ (sk_B @ X6))),
% 0.19/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.19/0.50  thf('6', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (((X0) != (sk_A))
% 0.19/0.50          | ~ (v1_relat_1 @ X1)
% 0.19/0.50          | ~ (v1_funct_1 @ X1)
% 0.19/0.50          | ((k1_relat_1 @ X1) != (sk_A))
% 0.19/0.50          | ((X1) = (sk_B @ X0)))),
% 0.19/0.50      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.19/0.50  thf('7', plain,
% 0.19/0.50      (![X1 : $i]:
% 0.19/0.50         (((X1) = (sk_B @ sk_A))
% 0.19/0.50          | ((k1_relat_1 @ X1) != (sk_A))
% 0.19/0.50          | ~ (v1_funct_1 @ X1)
% 0.19/0.50          | ~ (v1_relat_1 @ X1))),
% 0.19/0.50      inference('simplify', [status(thm)], ['6'])).
% 0.19/0.50  thf('8', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (((X0) != (sk_A))
% 0.19/0.50          | ~ (v1_relat_1 @ (sk_C_1 @ X1 @ X0))
% 0.19/0.50          | ~ (v1_funct_1 @ (sk_C_1 @ X1 @ X0))
% 0.19/0.50          | ((sk_C_1 @ X1 @ X0) = (sk_B @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['0', '7'])).
% 0.19/0.50  thf('9', plain, (![X3 : $i, X4 : $i]: (v1_relat_1 @ (sk_C_1 @ X3 @ X4))),
% 0.19/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.19/0.50  thf('10', plain, (![X3 : $i, X4 : $i]: (v1_funct_1 @ (sk_C_1 @ X3 @ X4))),
% 0.19/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.19/0.50  thf('11', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (((X0) != (sk_A)) | ((sk_C_1 @ X1 @ X0) = (sk_B @ sk_A)))),
% 0.19/0.50      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.19/0.50  thf('12', plain, (![X1 : $i]: ((sk_C_1 @ X1 @ sk_A) = (sk_B @ sk_A))),
% 0.19/0.50      inference('simplify', [status(thm)], ['11'])).
% 0.19/0.50  thf('13', plain,
% 0.19/0.50      (![X3 : $i, X4 : $i]: ((k1_relat_1 @ (sk_C_1 @ X3 @ X4)) = (X4))),
% 0.19/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.19/0.50  thf(t64_relat_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ A ) =>
% 0.19/0.50       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.19/0.50           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.19/0.50         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.19/0.50  thf('14', plain,
% 0.19/0.50      (![X2 : $i]:
% 0.19/0.50         (((k1_relat_1 @ X2) != (k1_xboole_0))
% 0.19/0.50          | ((X2) = (k1_xboole_0))
% 0.19/0.50          | ~ (v1_relat_1 @ X2))),
% 0.19/0.50      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.19/0.50  thf('15', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (((X0) != (k1_xboole_0))
% 0.19/0.50          | ~ (v1_relat_1 @ (sk_C_1 @ X1 @ X0))
% 0.19/0.50          | ((sk_C_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.50  thf('16', plain, (![X3 : $i, X4 : $i]: (v1_relat_1 @ (sk_C_1 @ X3 @ X4))),
% 0.19/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.19/0.50  thf('17', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (((X0) != (k1_xboole_0)) | ((sk_C_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.19/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.19/0.50  thf('18', plain, (![X1 : $i]: ((sk_C_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.50      inference('simplify', [status(thm)], ['17'])).
% 0.19/0.50  thf(t2_tarski, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.19/0.50       ( ( A ) = ( B ) ) ))).
% 0.19/0.50  thf('19', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (((X1) = (X0))
% 0.19/0.50          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.19/0.50          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.19/0.50      inference('cnf', [status(esa)], [t2_tarski])).
% 0.19/0.50  thf('20', plain,
% 0.19/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.50         (((k1_funct_1 @ (sk_C_1 @ X3 @ X4) @ X5) = (X3))
% 0.19/0.50          | ~ (r2_hidden @ X5 @ X4))),
% 0.19/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.19/0.50  thf('21', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         ((r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.19/0.50          | ((X1) = (X0))
% 0.19/0.50          | ((k1_funct_1 @ (sk_C_1 @ X2 @ X0) @ (sk_C @ X0 @ X1)) = (X2)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.19/0.50  thf('22', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (((k1_funct_1 @ k1_xboole_0 @ (sk_C @ k1_xboole_0 @ X1)) = (X0))
% 0.19/0.50          | ((X1) = (k1_xboole_0))
% 0.19/0.50          | (r2_hidden @ (sk_C @ k1_xboole_0 @ X1) @ X1))),
% 0.19/0.50      inference('sup+', [status(thm)], ['18', '21'])).
% 0.19/0.50  thf('23', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (((k1_funct_1 @ k1_xboole_0 @ (sk_C @ k1_xboole_0 @ X1)) = (X0))
% 0.19/0.50          | ((X1) = (k1_xboole_0))
% 0.19/0.50          | (r2_hidden @ (sk_C @ k1_xboole_0 @ X1) @ X1))),
% 0.19/0.50      inference('sup+', [status(thm)], ['18', '21'])).
% 0.19/0.50  thf('24', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         (((X0) = (X1))
% 0.19/0.50          | (r2_hidden @ (sk_C @ k1_xboole_0 @ X2) @ X2)
% 0.19/0.50          | ((X2) = (k1_xboole_0))
% 0.19/0.50          | (r2_hidden @ (sk_C @ k1_xboole_0 @ X2) @ X2)
% 0.19/0.50          | ((X2) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['22', '23'])).
% 0.19/0.50  thf('25', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.50         (((X2) = (k1_xboole_0))
% 0.19/0.50          | (r2_hidden @ (sk_C @ k1_xboole_0 @ X2) @ X2)
% 0.19/0.50          | ((X0) = (X1)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['24'])).
% 0.19/0.50  thf('26', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0))),
% 0.19/0.50      inference('condensation', [status(thm)], ['25'])).
% 0.19/0.50  thf('27', plain,
% 0.19/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.50         (((k1_funct_1 @ (sk_C_1 @ X3 @ X4) @ X5) = (X3))
% 0.19/0.50          | ~ (r2_hidden @ X5 @ X4))),
% 0.19/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.19/0.50  thf('28', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (((X0) = (k1_xboole_0))
% 0.19/0.50          | ((k1_funct_1 @ (sk_C_1 @ X1 @ X0) @ (sk_C @ k1_xboole_0 @ X0))
% 0.19/0.50              = (X1)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.50  thf('29', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((k1_funct_1 @ (sk_B @ sk_A) @ (sk_C @ k1_xboole_0 @ sk_A)) = (X0))
% 0.19/0.50          | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['12', '28'])).
% 0.19/0.50  thf('30', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('31', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((k1_funct_1 @ (sk_B @ sk_A) @ (sk_C @ k1_xboole_0 @ sk_A)) = (X0))),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['29', '30'])).
% 0.19/0.50  thf('32', plain, (![X1 : $i]: ((sk_C_1 @ X1 @ sk_A) = (sk_B @ sk_A))),
% 0.19/0.50      inference('simplify', [status(thm)], ['11'])).
% 0.19/0.50  thf('33', plain, (![X6 : $i]: ((k1_relat_1 @ (sk_B @ X6)) = (X6))),
% 0.19/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.19/0.50  thf('34', plain,
% 0.19/0.50      (![X2 : $i]:
% 0.19/0.50         (((k1_relat_1 @ X2) != (k1_xboole_0))
% 0.19/0.50          | ((X2) = (k1_xboole_0))
% 0.19/0.50          | ~ (v1_relat_1 @ X2))),
% 0.19/0.50      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.19/0.50  thf('35', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((X0) != (k1_xboole_0))
% 0.19/0.50          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.19/0.50          | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['33', '34'])).
% 0.19/0.50  thf('36', plain, (![X6 : $i]: (v1_relat_1 @ (sk_B @ X6))),
% 0.19/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.19/0.50  thf('37', plain,
% 0.19/0.50      (![X0 : $i]: (((X0) != (k1_xboole_0)) | ((sk_B @ X0) = (k1_xboole_0)))),
% 0.19/0.50      inference('demod', [status(thm)], ['35', '36'])).
% 0.19/0.50  thf('38', plain, (((sk_B @ k1_xboole_0) = (k1_xboole_0))),
% 0.19/0.50      inference('simplify', [status(thm)], ['37'])).
% 0.19/0.50  thf('39', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (((X1) = (X0))
% 0.19/0.50          | (r2_hidden @ (sk_C @ X0 @ X1) @ X0)
% 0.19/0.50          | (r2_hidden @ (sk_C @ X0 @ X1) @ X1))),
% 0.19/0.50      inference('cnf', [status(esa)], [t2_tarski])).
% 0.19/0.50  thf('40', plain,
% 0.19/0.50      (![X6 : $i, X7 : $i]:
% 0.19/0.50         (((k1_funct_1 @ (sk_B @ X6) @ X7) = (k1_xboole_0))
% 0.19/0.50          | ~ (r2_hidden @ X7 @ X6))),
% 0.19/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.19/0.50  thf('41', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         ((r2_hidden @ (sk_C @ X0 @ X1) @ X1)
% 0.19/0.50          | ((X1) = (X0))
% 0.19/0.50          | ((k1_funct_1 @ (sk_B @ X0) @ (sk_C @ X0 @ X1)) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['39', '40'])).
% 0.19/0.50  thf('42', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((k1_funct_1 @ k1_xboole_0 @ (sk_C @ k1_xboole_0 @ X0))
% 0.19/0.50            = (k1_xboole_0))
% 0.19/0.50          | ((X0) = (k1_xboole_0))
% 0.19/0.50          | (r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0))),
% 0.19/0.50      inference('sup+', [status(thm)], ['38', '41'])).
% 0.19/0.50  thf('43', plain,
% 0.19/0.50      (![X6 : $i, X7 : $i]:
% 0.19/0.50         (((k1_funct_1 @ (sk_B @ X6) @ X7) = (k1_xboole_0))
% 0.19/0.50          | ~ (r2_hidden @ X7 @ X6))),
% 0.19/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.19/0.50  thf('44', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((X0) = (k1_xboole_0))
% 0.19/0.50          | ((k1_funct_1 @ k1_xboole_0 @ (sk_C @ k1_xboole_0 @ X0))
% 0.19/0.50              = (k1_xboole_0))
% 0.19/0.50          | ((k1_funct_1 @ (sk_B @ X0) @ (sk_C @ k1_xboole_0 @ X0))
% 0.19/0.50              = (k1_xboole_0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['42', '43'])).
% 0.19/0.50  thf('45', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((k1_funct_1 @ (sk_C_1 @ X0 @ sk_A) @ (sk_C @ k1_xboole_0 @ sk_A))
% 0.19/0.50            = (k1_xboole_0))
% 0.19/0.50          | ((k1_funct_1 @ k1_xboole_0 @ (sk_C @ k1_xboole_0 @ sk_A))
% 0.19/0.50              = (k1_xboole_0))
% 0.19/0.50          | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['32', '44'])).
% 0.19/0.50  thf('46', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('47', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((k1_funct_1 @ (sk_C_1 @ X0 @ sk_A) @ (sk_C @ k1_xboole_0 @ sk_A))
% 0.19/0.50            = (k1_xboole_0))
% 0.19/0.50          | ((k1_funct_1 @ k1_xboole_0 @ (sk_C @ k1_xboole_0 @ sk_A))
% 0.19/0.50              = (k1_xboole_0)))),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 0.19/0.50  thf('48', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((k1_funct_1 @ k1_xboole_0 @ (sk_C @ k1_xboole_0 @ X0))
% 0.19/0.50            = (k1_xboole_0))
% 0.19/0.50          | ((X0) = (k1_xboole_0))
% 0.19/0.50          | (r2_hidden @ (sk_C @ k1_xboole_0 @ X0) @ X0))),
% 0.19/0.50      inference('sup+', [status(thm)], ['38', '41'])).
% 0.19/0.50  thf('49', plain,
% 0.19/0.50      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.50         (((k1_funct_1 @ (sk_C_1 @ X3 @ X4) @ X5) = (X3))
% 0.19/0.50          | ~ (r2_hidden @ X5 @ X4))),
% 0.19/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.19/0.50  thf('50', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (((X0) = (k1_xboole_0))
% 0.19/0.50          | ((k1_funct_1 @ k1_xboole_0 @ (sk_C @ k1_xboole_0 @ X0))
% 0.19/0.50              = (k1_xboole_0))
% 0.19/0.50          | ((k1_funct_1 @ (sk_C_1 @ X1 @ X0) @ (sk_C @ k1_xboole_0 @ X0))
% 0.19/0.50              = (X1)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['48', '49'])).
% 0.19/0.50  thf('51', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((k1_xboole_0) = (X0))
% 0.19/0.50          | ((k1_funct_1 @ k1_xboole_0 @ (sk_C @ k1_xboole_0 @ sk_A))
% 0.19/0.50              = (k1_xboole_0))
% 0.19/0.50          | ((k1_funct_1 @ k1_xboole_0 @ (sk_C @ k1_xboole_0 @ sk_A))
% 0.19/0.50              = (k1_xboole_0))
% 0.19/0.50          | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['47', '50'])).
% 0.19/0.50  thf('52', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((sk_A) = (k1_xboole_0))
% 0.19/0.50          | ((k1_funct_1 @ k1_xboole_0 @ (sk_C @ k1_xboole_0 @ sk_A))
% 0.19/0.50              = (k1_xboole_0))
% 0.19/0.50          | ((k1_xboole_0) = (X0)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['51'])).
% 0.19/0.50  thf('53', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('54', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((k1_funct_1 @ k1_xboole_0 @ (sk_C @ k1_xboole_0 @ sk_A))
% 0.19/0.50            = (k1_xboole_0))
% 0.19/0.50          | ((k1_xboole_0) = (X0)))),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['52', '53'])).
% 0.19/0.50  thf('55', plain,
% 0.19/0.50      (((k1_funct_1 @ k1_xboole_0 @ (sk_C @ k1_xboole_0 @ sk_A))
% 0.19/0.50         = (k1_xboole_0))),
% 0.19/0.50      inference('condensation', [status(thm)], ['54'])).
% 0.19/0.50  thf('56', plain,
% 0.19/0.50      (![X0 : $i, X1 : $i]:
% 0.19/0.50         (((k1_funct_1 @ k1_xboole_0 @ (sk_C @ k1_xboole_0 @ X1)) = (X0))
% 0.19/0.50          | ((X1) = (k1_xboole_0))
% 0.19/0.50          | (r2_hidden @ (sk_C @ k1_xboole_0 @ X1) @ X1))),
% 0.19/0.50      inference('sup+', [status(thm)], ['18', '21'])).
% 0.19/0.50  thf('57', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((k1_xboole_0) = (X0))
% 0.19/0.50          | (r2_hidden @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A)
% 0.19/0.50          | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['55', '56'])).
% 0.19/0.50  thf('58', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('59', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((k1_xboole_0) = (X0))
% 0.19/0.50          | (r2_hidden @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A))),
% 0.19/0.50      inference('simplify_reflect-', [status(thm)], ['57', '58'])).
% 0.19/0.50  thf('60', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('61', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((sk_A) != (X0)) | (r2_hidden @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A))),
% 0.19/0.50      inference('sup-', [status(thm)], ['59', '60'])).
% 0.19/0.50  thf('62', plain, ((r2_hidden @ (sk_C @ k1_xboole_0 @ sk_A) @ sk_A)),
% 0.19/0.50      inference('simplify', [status(thm)], ['61'])).
% 0.19/0.50  thf('63', plain,
% 0.19/0.50      (![X6 : $i, X7 : $i]:
% 0.19/0.50         (((k1_funct_1 @ (sk_B @ X6) @ X7) = (k1_xboole_0))
% 0.19/0.50          | ~ (r2_hidden @ X7 @ X6))),
% 0.19/0.50      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.19/0.50  thf('64', plain,
% 0.19/0.50      (((k1_funct_1 @ (sk_B @ sk_A) @ (sk_C @ k1_xboole_0 @ sk_A))
% 0.19/0.50         = (k1_xboole_0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['62', '63'])).
% 0.19/0.50  thf('65', plain, (![X0 : $i]: ((k1_xboole_0) = (X0))),
% 0.19/0.50      inference('demod', [status(thm)], ['31', '64'])).
% 0.19/0.50  thf('66', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('67', plain, (((sk_A) != (k1_xboole_0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['65', '66'])).
% 0.19/0.50  thf('68', plain, (![X0 : $i]: ((k1_xboole_0) = (X0))),
% 0.19/0.50      inference('demod', [status(thm)], ['31', '64'])).
% 0.19/0.50  thf('69', plain, ($false),
% 0.19/0.50      inference('simplify_reflect+', [status(thm)], ['67', '68'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
