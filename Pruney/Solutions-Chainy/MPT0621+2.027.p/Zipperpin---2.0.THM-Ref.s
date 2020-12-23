%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.D5dtNzGpq1

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:31 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 305 expanded)
%              Number of leaves         :   20 ( 101 expanded)
%              Depth                    :   17
%              Number of atoms          :  557 (3335 expanded)
%              Number of equality atoms :   82 ( 458 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(np__1_type,type,(
    np__1: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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

thf('0',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ! [X8: $i,X9: $i] :
      ( ( k1_relat_1 @ ( sk_C_1 @ X8 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf(s3_funct_1__e7_25__funct_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ B @ C )
            = np__1 ) )
      & ( ( k1_relat_1 @ B )
        = A )
      & ( v1_funct_1 @ B )
      & ( v1_relat_1 @ B ) ) )).

thf('2',plain,(
    ! [X11: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('3',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ( X14 = X13 )
      | ( ( k1_relat_1 @ X13 )
       != sk_A )
      | ( ( k1_relat_1 @ X14 )
       != sk_A )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
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
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X11: $i] :
      ( v1_funct_1 @ ( sk_B @ X11 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('6',plain,(
    ! [X11: $i] :
      ( v1_relat_1 @ ( sk_B @ X11 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ( X1
        = ( sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    ! [X1: $i] :
      ( ( X1
        = ( sk_B @ sk_A ) )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ( ( sk_C_1 @ X1 @ X0 )
        = ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['1','8'])).

thf('10',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( sk_C_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('11',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_funct_1 @ ( sk_C_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ( ( sk_C_1 @ X1 @ X0 )
        = ( sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ! [X1: $i] :
      ( ( sk_C_1 @ X1 @ sk_A )
      = ( sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('14',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('15',plain,(
    ! [X2: $i,X5: $i] :
      ( ( X5
        = ( k1_relat_1 @ X2 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X5 @ X2 ) @ ( sk_D @ X5 @ X2 ) ) @ X2 )
      | ( r2_hidden @ ( sk_C @ X5 @ X2 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ X2 )
      | ( r2_hidden @ X0 @ X3 )
      | ( X3
       != ( k1_relat_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X0 @ ( k1_relat_1 @ X2 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X1 ) @ X2 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( X0
        = ( k1_relat_1 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','18'])).

thf('20',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X8 @ X9 ) @ X10 )
        = X8 )
      | ~ ( r2_hidden @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( sk_C_1 @ X1 @ k1_xboole_0 ) @ ( sk_C @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X8: $i,X9: $i] :
      ( ( k1_relat_1 @ ( sk_C_1 @ X8 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('25',plain,(
    ! [X7: $i] :
      ( ( ( k1_relat_1 @ X7 )
       != k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ( ( sk_C_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( sk_C_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != k1_xboole_0 )
      | ( ( sk_C_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X1: $i] :
      ( ( sk_C_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['23','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ k1_xboole_0 @ ( sk_C @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference(demod,[status(thm)],['23','29'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 = X1 )
      | ( X2 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X2 @ k1_xboole_0 ) @ X2 )
      | ( X2 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X2 @ k1_xboole_0 ) @ X2 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ X2 @ k1_xboole_0 ) @ X2 )
      | ( X2 = k1_xboole_0 )
      | ( X0 = X1 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['33'])).

thf('35',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k1_funct_1 @ ( sk_B @ X11 ) @ X12 )
        = np__1 )
      | ~ ( r2_hidden @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e7_25__funct_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( sk_B @ X0 ) @ ( sk_C @ X0 @ k1_xboole_0 ) )
        = np__1 ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X0 @ sk_A ) @ ( sk_C @ sk_A @ k1_xboole_0 ) )
        = np__1 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['13','36'])).

thf('38',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( k1_funct_1 @ ( sk_C_1 @ X0 @ sk_A ) @ ( sk_C @ sk_A @ k1_xboole_0 ) )
      = np__1 ) ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ k1_xboole_0 ) @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(condensation,[status(thm)],['33'])).

thf('41',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X8 @ X9 ) @ X10 )
        = X8 )
      | ~ ( r2_hidden @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( sk_C_1 @ X1 @ X0 ) @ ( sk_C @ X0 @ k1_xboole_0 ) )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( np__1 = X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['39','42'])).

thf('44',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] : ( np__1 = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] : ( np__1 = X0 ) ),
    inference('simplify_reflect-',[status(thm)],['43','44'])).

thf('47',plain,(
    np__1 != np__1 ),
    inference(demod,[status(thm)],['0','45','46'])).

thf('48',plain,(
    $false ),
    inference(simplify,[status(thm)],['47'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.D5dtNzGpq1
% 0.15/0.37  % Computer   : n024.cluster.edu
% 0.15/0.37  % Model      : x86_64 x86_64
% 0.15/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.37  % Memory     : 8042.1875MB
% 0.15/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.37  % CPULimit   : 60
% 0.15/0.37  % DateTime   : Tue Dec  1 10:03:21 EST 2020
% 0.15/0.37  % CPUTime    : 
% 0.15/0.37  % Running portfolio for 600 s
% 0.15/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.37  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.24/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.55  % Solved by: fo/fo7.sh
% 0.24/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.55  % done 76 iterations in 0.062s
% 0.24/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.55  % SZS output start Refutation
% 0.24/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.24/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.24/0.55  thf(sk_B_type, type, sk_B: $i > $i).
% 0.24/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.24/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.24/0.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.24/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.24/0.55  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.24/0.55  thf(np__1_type, type, np__1: $i).
% 0.24/0.55  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.24/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.24/0.55  thf(t16_funct_1, conjecture,
% 0.24/0.55    (![A:$i]:
% 0.24/0.55     ( ( ![B:$i]:
% 0.24/0.55         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.24/0.55           ( ![C:$i]:
% 0.24/0.55             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.24/0.55               ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.24/0.55                   ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.24/0.55                 ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.24/0.55       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.24/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.55    (~( ![A:$i]:
% 0.24/0.55        ( ( ![B:$i]:
% 0.24/0.55            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.24/0.55              ( ![C:$i]:
% 0.24/0.55                ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.24/0.55                  ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.24/0.55                      ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.24/0.55                    ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.24/0.55          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.24/0.55    inference('cnf.neg', [status(esa)], [t16_funct_1])).
% 0.24/0.55  thf('0', plain, (((sk_A) != (k1_xboole_0))),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf(s3_funct_1__e2_24__funct_1, axiom,
% 0.24/0.55    (![A:$i,B:$i]:
% 0.24/0.55     ( ?[C:$i]:
% 0.24/0.55       ( ( ![D:$i]:
% 0.24/0.55           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 0.24/0.55         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.24/0.55         ( v1_relat_1 @ C ) ) ))).
% 0.24/0.55  thf('1', plain,
% 0.24/0.55      (![X8 : $i, X9 : $i]: ((k1_relat_1 @ (sk_C_1 @ X8 @ X9)) = (X9))),
% 0.24/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.24/0.55  thf(s3_funct_1__e7_25__funct_1, axiom,
% 0.24/0.55    (![A:$i]:
% 0.24/0.55     ( ?[B:$i]:
% 0.24/0.55       ( ( ![C:$i]:
% 0.24/0.55           ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( np__1 ) ) ) ) & 
% 0.24/0.55         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.24/0.55         ( v1_relat_1 @ B ) ) ))).
% 0.24/0.55  thf('2', plain, (![X11 : $i]: ((k1_relat_1 @ (sk_B @ X11)) = (X11))),
% 0.24/0.55      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.24/0.55  thf('3', plain,
% 0.24/0.55      (![X13 : $i, X14 : $i]:
% 0.24/0.55         (~ (v1_relat_1 @ X13)
% 0.24/0.55          | ~ (v1_funct_1 @ X13)
% 0.24/0.55          | ((X14) = (X13))
% 0.24/0.55          | ((k1_relat_1 @ X13) != (sk_A))
% 0.24/0.55          | ((k1_relat_1 @ X14) != (sk_A))
% 0.24/0.55          | ~ (v1_funct_1 @ X14)
% 0.24/0.55          | ~ (v1_relat_1 @ X14))),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf('4', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i]:
% 0.24/0.55         (((X0) != (sk_A))
% 0.24/0.55          | ~ (v1_relat_1 @ X1)
% 0.24/0.55          | ~ (v1_funct_1 @ X1)
% 0.24/0.55          | ((k1_relat_1 @ X1) != (sk_A))
% 0.24/0.55          | ((X1) = (sk_B @ X0))
% 0.24/0.55          | ~ (v1_funct_1 @ (sk_B @ X0))
% 0.24/0.55          | ~ (v1_relat_1 @ (sk_B @ X0)))),
% 0.24/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.24/0.55  thf('5', plain, (![X11 : $i]: (v1_funct_1 @ (sk_B @ X11))),
% 0.24/0.55      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.24/0.55  thf('6', plain, (![X11 : $i]: (v1_relat_1 @ (sk_B @ X11))),
% 0.24/0.55      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.24/0.55  thf('7', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i]:
% 0.24/0.55         (((X0) != (sk_A))
% 0.24/0.55          | ~ (v1_relat_1 @ X1)
% 0.24/0.55          | ~ (v1_funct_1 @ X1)
% 0.24/0.55          | ((k1_relat_1 @ X1) != (sk_A))
% 0.24/0.55          | ((X1) = (sk_B @ X0)))),
% 0.24/0.55      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.24/0.55  thf('8', plain,
% 0.24/0.55      (![X1 : $i]:
% 0.24/0.55         (((X1) = (sk_B @ sk_A))
% 0.24/0.55          | ((k1_relat_1 @ X1) != (sk_A))
% 0.24/0.55          | ~ (v1_funct_1 @ X1)
% 0.24/0.55          | ~ (v1_relat_1 @ X1))),
% 0.24/0.55      inference('simplify', [status(thm)], ['7'])).
% 0.24/0.55  thf('9', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i]:
% 0.24/0.55         (((X0) != (sk_A))
% 0.24/0.55          | ~ (v1_relat_1 @ (sk_C_1 @ X1 @ X0))
% 0.24/0.55          | ~ (v1_funct_1 @ (sk_C_1 @ X1 @ X0))
% 0.24/0.55          | ((sk_C_1 @ X1 @ X0) = (sk_B @ sk_A)))),
% 0.24/0.55      inference('sup-', [status(thm)], ['1', '8'])).
% 0.24/0.55  thf('10', plain, (![X8 : $i, X9 : $i]: (v1_relat_1 @ (sk_C_1 @ X8 @ X9))),
% 0.24/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.24/0.55  thf('11', plain, (![X8 : $i, X9 : $i]: (v1_funct_1 @ (sk_C_1 @ X8 @ X9))),
% 0.24/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.24/0.55  thf('12', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i]:
% 0.24/0.55         (((X0) != (sk_A)) | ((sk_C_1 @ X1 @ X0) = (sk_B @ sk_A)))),
% 0.24/0.55      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.24/0.55  thf('13', plain, (![X1 : $i]: ((sk_C_1 @ X1 @ sk_A) = (sk_B @ sk_A))),
% 0.24/0.55      inference('simplify', [status(thm)], ['12'])).
% 0.24/0.55  thf(t60_relat_1, axiom,
% 0.24/0.55    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.24/0.55     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.24/0.55  thf('14', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.24/0.55      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.24/0.55  thf(d4_relat_1, axiom,
% 0.24/0.55    (![A:$i,B:$i]:
% 0.24/0.55     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.24/0.55       ( ![C:$i]:
% 0.24/0.55         ( ( r2_hidden @ C @ B ) <=>
% 0.24/0.55           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.24/0.55  thf('15', plain,
% 0.24/0.55      (![X2 : $i, X5 : $i]:
% 0.24/0.55         (((X5) = (k1_relat_1 @ X2))
% 0.24/0.55          | (r2_hidden @ (k4_tarski @ (sk_C @ X5 @ X2) @ (sk_D @ X5 @ X2)) @ X2)
% 0.24/0.55          | (r2_hidden @ (sk_C @ X5 @ X2) @ X5))),
% 0.24/0.55      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.24/0.55  thf('16', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.24/0.55         (~ (r2_hidden @ (k4_tarski @ X0 @ X1) @ X2)
% 0.24/0.55          | (r2_hidden @ X0 @ X3)
% 0.24/0.55          | ((X3) != (k1_relat_1 @ X2)))),
% 0.24/0.55      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.24/0.55  thf('17', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.55         ((r2_hidden @ X0 @ (k1_relat_1 @ X2))
% 0.24/0.55          | ~ (r2_hidden @ (k4_tarski @ X0 @ X1) @ X2))),
% 0.24/0.55      inference('simplify', [status(thm)], ['16'])).
% 0.24/0.55  thf('18', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i]:
% 0.24/0.55         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.24/0.55          | ((X1) = (k1_relat_1 @ X0))
% 0.24/0.55          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.24/0.55      inference('sup-', [status(thm)], ['15', '17'])).
% 0.24/0.55  thf('19', plain,
% 0.24/0.55      (![X0 : $i]:
% 0.24/0.55         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.24/0.55          | ((X0) = (k1_relat_1 @ k1_xboole_0))
% 0.24/0.55          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0))),
% 0.24/0.55      inference('sup+', [status(thm)], ['14', '18'])).
% 0.24/0.55  thf('20', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.24/0.55      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.24/0.55  thf('21', plain,
% 0.24/0.55      (![X0 : $i]:
% 0.24/0.55         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ k1_xboole_0)
% 0.24/0.55          | ((X0) = (k1_xboole_0))
% 0.24/0.55          | (r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0))),
% 0.24/0.55      inference('demod', [status(thm)], ['19', '20'])).
% 0.24/0.55  thf('22', plain,
% 0.24/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.24/0.55         (((k1_funct_1 @ (sk_C_1 @ X8 @ X9) @ X10) = (X8))
% 0.24/0.55          | ~ (r2_hidden @ X10 @ X9))),
% 0.24/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.24/0.55  thf('23', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i]:
% 0.24/0.55         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.24/0.55          | ((X0) = (k1_xboole_0))
% 0.24/0.55          | ((k1_funct_1 @ (sk_C_1 @ X1 @ k1_xboole_0) @ 
% 0.24/0.55              (sk_C @ X0 @ k1_xboole_0)) = (X1)))),
% 0.24/0.55      inference('sup-', [status(thm)], ['21', '22'])).
% 0.24/0.55  thf('24', plain,
% 0.24/0.55      (![X8 : $i, X9 : $i]: ((k1_relat_1 @ (sk_C_1 @ X8 @ X9)) = (X9))),
% 0.24/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.24/0.55  thf(t64_relat_1, axiom,
% 0.24/0.55    (![A:$i]:
% 0.24/0.55     ( ( v1_relat_1 @ A ) =>
% 0.24/0.55       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.24/0.55           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.24/0.55         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.24/0.55  thf('25', plain,
% 0.24/0.55      (![X7 : $i]:
% 0.24/0.55         (((k1_relat_1 @ X7) != (k1_xboole_0))
% 0.24/0.55          | ((X7) = (k1_xboole_0))
% 0.24/0.55          | ~ (v1_relat_1 @ X7))),
% 0.24/0.55      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.24/0.55  thf('26', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i]:
% 0.24/0.55         (((X0) != (k1_xboole_0))
% 0.24/0.55          | ~ (v1_relat_1 @ (sk_C_1 @ X1 @ X0))
% 0.24/0.55          | ((sk_C_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.24/0.55      inference('sup-', [status(thm)], ['24', '25'])).
% 0.24/0.55  thf('27', plain, (![X8 : $i, X9 : $i]: (v1_relat_1 @ (sk_C_1 @ X8 @ X9))),
% 0.24/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.24/0.55  thf('28', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i]:
% 0.24/0.55         (((X0) != (k1_xboole_0)) | ((sk_C_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.24/0.55      inference('demod', [status(thm)], ['26', '27'])).
% 0.24/0.55  thf('29', plain, (![X1 : $i]: ((sk_C_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.24/0.55      inference('simplify', [status(thm)], ['28'])).
% 0.24/0.55  thf('30', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i]:
% 0.24/0.55         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.24/0.55          | ((X0) = (k1_xboole_0))
% 0.24/0.55          | ((k1_funct_1 @ k1_xboole_0 @ (sk_C @ X0 @ k1_xboole_0)) = (X1)))),
% 0.24/0.55      inference('demod', [status(thm)], ['23', '29'])).
% 0.24/0.55  thf('31', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i]:
% 0.24/0.55         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0)
% 0.24/0.55          | ((X0) = (k1_xboole_0))
% 0.24/0.55          | ((k1_funct_1 @ k1_xboole_0 @ (sk_C @ X0 @ k1_xboole_0)) = (X1)))),
% 0.24/0.55      inference('demod', [status(thm)], ['23', '29'])).
% 0.24/0.55  thf('32', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.55         (((X0) = (X1))
% 0.24/0.55          | ((X2) = (k1_xboole_0))
% 0.24/0.55          | (r2_hidden @ (sk_C @ X2 @ k1_xboole_0) @ X2)
% 0.24/0.55          | ((X2) = (k1_xboole_0))
% 0.24/0.55          | (r2_hidden @ (sk_C @ X2 @ k1_xboole_0) @ X2))),
% 0.24/0.55      inference('sup+', [status(thm)], ['30', '31'])).
% 0.24/0.55  thf('33', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.24/0.55         ((r2_hidden @ (sk_C @ X2 @ k1_xboole_0) @ X2)
% 0.24/0.55          | ((X2) = (k1_xboole_0))
% 0.24/0.55          | ((X0) = (X1)))),
% 0.24/0.55      inference('simplify', [status(thm)], ['32'])).
% 0.24/0.55  thf('34', plain,
% 0.24/0.55      (![X0 : $i]:
% 0.24/0.55         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.24/0.55      inference('condensation', [status(thm)], ['33'])).
% 0.24/0.55  thf('35', plain,
% 0.24/0.55      (![X11 : $i, X12 : $i]:
% 0.24/0.55         (((k1_funct_1 @ (sk_B @ X11) @ X12) = (np__1))
% 0.24/0.55          | ~ (r2_hidden @ X12 @ X11))),
% 0.24/0.55      inference('cnf', [status(esa)], [s3_funct_1__e7_25__funct_1])).
% 0.24/0.55  thf('36', plain,
% 0.24/0.55      (![X0 : $i]:
% 0.24/0.55         (((X0) = (k1_xboole_0))
% 0.24/0.55          | ((k1_funct_1 @ (sk_B @ X0) @ (sk_C @ X0 @ k1_xboole_0)) = (np__1)))),
% 0.24/0.55      inference('sup-', [status(thm)], ['34', '35'])).
% 0.24/0.55  thf('37', plain,
% 0.24/0.55      (![X0 : $i]:
% 0.24/0.55         (((k1_funct_1 @ (sk_C_1 @ X0 @ sk_A) @ (sk_C @ sk_A @ k1_xboole_0))
% 0.24/0.55            = (np__1))
% 0.24/0.55          | ((sk_A) = (k1_xboole_0)))),
% 0.24/0.55      inference('sup+', [status(thm)], ['13', '36'])).
% 0.24/0.55  thf('38', plain, (((sk_A) != (k1_xboole_0))),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf('39', plain,
% 0.24/0.55      (![X0 : $i]:
% 0.24/0.55         ((k1_funct_1 @ (sk_C_1 @ X0 @ sk_A) @ (sk_C @ sk_A @ k1_xboole_0))
% 0.24/0.55           = (np__1))),
% 0.24/0.55      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.24/0.55  thf('40', plain,
% 0.24/0.55      (![X0 : $i]:
% 0.24/0.55         ((r2_hidden @ (sk_C @ X0 @ k1_xboole_0) @ X0) | ((X0) = (k1_xboole_0)))),
% 0.24/0.55      inference('condensation', [status(thm)], ['33'])).
% 0.24/0.55  thf('41', plain,
% 0.24/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.24/0.55         (((k1_funct_1 @ (sk_C_1 @ X8 @ X9) @ X10) = (X8))
% 0.24/0.55          | ~ (r2_hidden @ X10 @ X9))),
% 0.24/0.55      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.24/0.55  thf('42', plain,
% 0.24/0.55      (![X0 : $i, X1 : $i]:
% 0.24/0.55         (((X0) = (k1_xboole_0))
% 0.24/0.55          | ((k1_funct_1 @ (sk_C_1 @ X1 @ X0) @ (sk_C @ X0 @ k1_xboole_0))
% 0.24/0.55              = (X1)))),
% 0.24/0.55      inference('sup-', [status(thm)], ['40', '41'])).
% 0.24/0.55  thf('43', plain, (![X0 : $i]: (((np__1) = (X0)) | ((sk_A) = (k1_xboole_0)))),
% 0.24/0.55      inference('sup+', [status(thm)], ['39', '42'])).
% 0.24/0.55  thf('44', plain, (((sk_A) != (k1_xboole_0))),
% 0.24/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.55  thf('45', plain, (![X0 : $i]: ((np__1) = (X0))),
% 0.24/0.55      inference('simplify_reflect-', [status(thm)], ['43', '44'])).
% 0.24/0.55  thf('46', plain, (![X0 : $i]: ((np__1) = (X0))),
% 0.24/0.55      inference('simplify_reflect-', [status(thm)], ['43', '44'])).
% 0.24/0.55  thf('47', plain, (((np__1) != (np__1))),
% 0.24/0.55      inference('demod', [status(thm)], ['0', '45', '46'])).
% 0.24/0.55  thf('48', plain, ($false), inference('simplify', [status(thm)], ['47'])).
% 0.24/0.55  
% 0.24/0.55  % SZS output end Refutation
% 0.24/0.55  
% 0.24/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
