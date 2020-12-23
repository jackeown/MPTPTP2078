%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NKLloMS9zb

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:27 EST 2020

% Result     : Theorem 7.10s
% Output     : Refutation 7.10s
% Verified   : 
% Statistics : Number of formulae       :   62 (  77 expanded)
%              Number of leaves         :   19 (  33 expanded)
%              Depth                    :   21
%              Number of atoms          :  655 ( 893 expanded)
%              Number of equality atoms :   89 ( 123 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('0',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(l44_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 )
      | ( X3
        = ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

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

thf('2',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ( X9
       != ( k2_relat_1 @ X7 ) )
      | ( X10
        = ( k1_funct_1 @ X7 @ ( sk_D_1 @ X10 @ X7 ) ) )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('3',plain,(
    ! [X7: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k2_relat_1 @ X7 ) )
      | ( X10
        = ( k1_funct_1 @ X7 @ ( sk_D_1 @ X10 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

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

thf('5',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('6',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 )
      | ( X3
        = ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('7',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ( X9
       != ( k2_relat_1 @ X7 ) )
      | ( r2_hidden @ ( sk_D_1 @ X10 @ X7 ) @ ( k1_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('8',plain,(
    ! [X7: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k2_relat_1 @ X7 ) )
      | ( r2_hidden @ ( sk_D_1 @ X10 @ X7 ) @ ( k1_relat_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf('10',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X13 @ X14 ) @ X15 )
        = X13 )
      | ~ ( r2_hidden @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X2 @ ( k1_relat_1 @ X0 ) ) @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) @ ( sk_D_1 @ ( sk_C @ X3 @ ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) ) @ ( sk_C_2 @ X2 @ X0 ) ) )
        = X1 )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) )
        = ( k1_tarski @ X3 ) )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['5','11'])).

thf('13',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) @ ( sk_D_1 @ ( sk_C @ X3 @ ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) ) ) @ ( sk_C_2 @ X2 @ X0 ) ) )
        = X1 )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) )
        = ( k1_tarski @ X3 ) )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X2 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
        = X1 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
        = ( k1_tarski @ X2 ) )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
        = ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['4','15'])).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('18',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
        = X1 )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
        = ( k1_tarski @ X2 ) )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
        = ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
        = ( k1_tarski @ X2 ) )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ( ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( ( sk_C @ X4 @ X3 )
       != X4 )
      | ( X3
        = ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != X1 )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) )
        = ( k1_tarski @ X1 ) )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) )
        = ( k1_tarski @ X1 ) )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X0 @ X2 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X2 ) )
        = ( k1_tarski @ X1 ) )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X2 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

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

thf('24',plain,(
    ! [X16: $i] :
      ( ( ( k2_relat_1 @ X16 )
       != ( k1_tarski @ sk_B ) )
      | ( ( k1_relat_1 @ X16 )
       != sk_A )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_B ) )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X0 @ X1 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ ( sk_C_2 @ X0 @ X1 ) )
       != sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('28',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_B ) )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X0 @ X1 ) )
        = k1_xboole_0 )
      | ( X1 != sk_A ) ) ),
    inference(demod,[status(thm)],['25','26','27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_2 @ X0 @ sk_A ) )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ( k2_relat_1 @ ( sk_C_2 @ sk_B @ sk_A ) )
    = k1_xboole_0 ),
    inference(eq_res,[status(thm)],['30'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('32',plain,(
    ! [X5: $i] :
      ( ( ( k2_relat_1 @ X5 )
       != k1_xboole_0 )
      | ( X5 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('33',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( sk_C_2 @ sk_B @ sk_A ) )
    | ( ( sk_C_2 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('35',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( sk_C_2 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_C_2 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('38',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = sk_A ),
    inference('sup+',[status(thm)],['36','37'])).

thf('39',plain,(
    k1_xboole_0 = sk_A ),
    inference('sup+',[status(thm)],['0','38'])).

thf('40',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.NKLloMS9zb
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:28:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 7.10/7.28  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 7.10/7.28  % Solved by: fo/fo7.sh
% 7.10/7.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.10/7.28  % done 4131 iterations in 6.822s
% 7.10/7.28  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 7.10/7.28  % SZS output start Refutation
% 7.10/7.28  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 7.10/7.28  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 7.10/7.28  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 7.10/7.28  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 7.10/7.28  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 7.10/7.28  thf(sk_A_type, type, sk_A: $i).
% 7.10/7.28  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 7.10/7.28  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 7.10/7.28  thf(sk_B_type, type, sk_B: $i).
% 7.10/7.28  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 7.10/7.28  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 7.10/7.28  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 7.10/7.28  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.10/7.28  thf(t60_relat_1, axiom,
% 7.10/7.28    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 7.10/7.28     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 7.10/7.28  thf('0', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 7.10/7.28      inference('cnf', [status(esa)], [t60_relat_1])).
% 7.10/7.28  thf(l44_zfmisc_1, axiom,
% 7.10/7.28    (![A:$i,B:$i]:
% 7.10/7.28     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 7.10/7.28          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 7.10/7.28  thf('1', plain,
% 7.10/7.28      (![X3 : $i, X4 : $i]:
% 7.10/7.28         (((X3) = (k1_xboole_0))
% 7.10/7.28          | (r2_hidden @ (sk_C @ X4 @ X3) @ X3)
% 7.10/7.28          | ((X3) = (k1_tarski @ X4)))),
% 7.10/7.28      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 7.10/7.28  thf(d5_funct_1, axiom,
% 7.10/7.28    (![A:$i]:
% 7.10/7.28     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 7.10/7.28       ( ![B:$i]:
% 7.10/7.28         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 7.10/7.28           ( ![C:$i]:
% 7.10/7.28             ( ( r2_hidden @ C @ B ) <=>
% 7.10/7.28               ( ?[D:$i]:
% 7.10/7.28                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 7.10/7.28                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 7.10/7.28  thf('2', plain,
% 7.10/7.28      (![X7 : $i, X9 : $i, X10 : $i]:
% 7.10/7.28         (((X9) != (k2_relat_1 @ X7))
% 7.10/7.28          | ((X10) = (k1_funct_1 @ X7 @ (sk_D_1 @ X10 @ X7)))
% 7.10/7.28          | ~ (r2_hidden @ X10 @ X9)
% 7.10/7.28          | ~ (v1_funct_1 @ X7)
% 7.10/7.28          | ~ (v1_relat_1 @ X7))),
% 7.10/7.28      inference('cnf', [status(esa)], [d5_funct_1])).
% 7.10/7.28  thf('3', plain,
% 7.10/7.28      (![X7 : $i, X10 : $i]:
% 7.10/7.28         (~ (v1_relat_1 @ X7)
% 7.10/7.28          | ~ (v1_funct_1 @ X7)
% 7.10/7.28          | ~ (r2_hidden @ X10 @ (k2_relat_1 @ X7))
% 7.10/7.28          | ((X10) = (k1_funct_1 @ X7 @ (sk_D_1 @ X10 @ X7))))),
% 7.10/7.28      inference('simplify', [status(thm)], ['2'])).
% 7.10/7.28  thf('4', plain,
% 7.10/7.28      (![X0 : $i, X1 : $i]:
% 7.10/7.28         (((k2_relat_1 @ X0) = (k1_tarski @ X1))
% 7.10/7.28          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 7.10/7.28          | ((sk_C @ X1 @ (k2_relat_1 @ X0))
% 7.10/7.28              = (k1_funct_1 @ X0 @ 
% 7.10/7.28                 (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)))
% 7.10/7.28          | ~ (v1_funct_1 @ X0)
% 7.10/7.28          | ~ (v1_relat_1 @ X0))),
% 7.10/7.28      inference('sup-', [status(thm)], ['1', '3'])).
% 7.10/7.28  thf(s3_funct_1__e2_24__funct_1, axiom,
% 7.10/7.28    (![A:$i,B:$i]:
% 7.10/7.28     ( ?[C:$i]:
% 7.10/7.28       ( ( ![D:$i]:
% 7.10/7.28           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 7.10/7.28         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 7.10/7.28         ( v1_relat_1 @ C ) ) ))).
% 7.10/7.28  thf('5', plain,
% 7.10/7.28      (![X13 : $i, X14 : $i]: ((k1_relat_1 @ (sk_C_2 @ X13 @ X14)) = (X14))),
% 7.10/7.28      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 7.10/7.28  thf('6', plain,
% 7.10/7.28      (![X3 : $i, X4 : $i]:
% 7.10/7.28         (((X3) = (k1_xboole_0))
% 7.10/7.28          | (r2_hidden @ (sk_C @ X4 @ X3) @ X3)
% 7.10/7.28          | ((X3) = (k1_tarski @ X4)))),
% 7.10/7.28      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 7.10/7.28  thf('7', plain,
% 7.10/7.28      (![X7 : $i, X9 : $i, X10 : $i]:
% 7.10/7.28         (((X9) != (k2_relat_1 @ X7))
% 7.10/7.28          | (r2_hidden @ (sk_D_1 @ X10 @ X7) @ (k1_relat_1 @ X7))
% 7.10/7.28          | ~ (r2_hidden @ X10 @ X9)
% 7.10/7.28          | ~ (v1_funct_1 @ X7)
% 7.10/7.28          | ~ (v1_relat_1 @ X7))),
% 7.10/7.28      inference('cnf', [status(esa)], [d5_funct_1])).
% 7.10/7.28  thf('8', plain,
% 7.10/7.28      (![X7 : $i, X10 : $i]:
% 7.10/7.28         (~ (v1_relat_1 @ X7)
% 7.10/7.28          | ~ (v1_funct_1 @ X7)
% 7.10/7.28          | ~ (r2_hidden @ X10 @ (k2_relat_1 @ X7))
% 7.10/7.28          | (r2_hidden @ (sk_D_1 @ X10 @ X7) @ (k1_relat_1 @ X7)))),
% 7.10/7.28      inference('simplify', [status(thm)], ['7'])).
% 7.10/7.28  thf('9', plain,
% 7.10/7.28      (![X0 : $i, X1 : $i]:
% 7.10/7.28         (((k2_relat_1 @ X0) = (k1_tarski @ X1))
% 7.10/7.28          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 7.10/7.28          | (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 7.10/7.28             (k1_relat_1 @ X0))
% 7.10/7.28          | ~ (v1_funct_1 @ X0)
% 7.10/7.28          | ~ (v1_relat_1 @ X0))),
% 7.10/7.28      inference('sup-', [status(thm)], ['6', '8'])).
% 7.10/7.28  thf('10', plain,
% 7.10/7.28      (![X13 : $i, X14 : $i, X15 : $i]:
% 7.10/7.28         (((k1_funct_1 @ (sk_C_2 @ X13 @ X14) @ X15) = (X13))
% 7.10/7.28          | ~ (r2_hidden @ X15 @ X14))),
% 7.10/7.28      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 7.10/7.28  thf('11', plain,
% 7.10/7.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.10/7.28         (~ (v1_relat_1 @ X0)
% 7.10/7.28          | ~ (v1_funct_1 @ X0)
% 7.10/7.28          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 7.10/7.28          | ((k2_relat_1 @ X0) = (k1_tarski @ X1))
% 7.10/7.28          | ((k1_funct_1 @ (sk_C_2 @ X2 @ (k1_relat_1 @ X0)) @ 
% 7.10/7.28              (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)) = (X2)))),
% 7.10/7.28      inference('sup-', [status(thm)], ['9', '10'])).
% 7.10/7.28  thf('12', plain,
% 7.10/7.28      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.10/7.28         (((k1_funct_1 @ (sk_C_2 @ X1 @ X0) @ 
% 7.10/7.28            (sk_D_1 @ (sk_C @ X3 @ (k2_relat_1 @ (sk_C_2 @ X2 @ X0))) @ 
% 7.10/7.28             (sk_C_2 @ X2 @ X0)))
% 7.10/7.28            = (X1))
% 7.10/7.28          | ((k2_relat_1 @ (sk_C_2 @ X2 @ X0)) = (k1_tarski @ X3))
% 7.10/7.28          | ((k2_relat_1 @ (sk_C_2 @ X2 @ X0)) = (k1_xboole_0))
% 7.10/7.28          | ~ (v1_funct_1 @ (sk_C_2 @ X2 @ X0))
% 7.10/7.28          | ~ (v1_relat_1 @ (sk_C_2 @ X2 @ X0)))),
% 7.10/7.28      inference('sup+', [status(thm)], ['5', '11'])).
% 7.10/7.28  thf('13', plain,
% 7.10/7.28      (![X13 : $i, X14 : $i]: (v1_funct_1 @ (sk_C_2 @ X13 @ X14))),
% 7.10/7.28      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 7.10/7.28  thf('14', plain,
% 7.10/7.28      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (sk_C_2 @ X13 @ X14))),
% 7.10/7.28      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 7.10/7.28  thf('15', plain,
% 7.10/7.28      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.10/7.28         (((k1_funct_1 @ (sk_C_2 @ X1 @ X0) @ 
% 7.10/7.28            (sk_D_1 @ (sk_C @ X3 @ (k2_relat_1 @ (sk_C_2 @ X2 @ X0))) @ 
% 7.10/7.28             (sk_C_2 @ X2 @ X0)))
% 7.10/7.28            = (X1))
% 7.10/7.28          | ((k2_relat_1 @ (sk_C_2 @ X2 @ X0)) = (k1_tarski @ X3))
% 7.10/7.28          | ((k2_relat_1 @ (sk_C_2 @ X2 @ X0)) = (k1_xboole_0)))),
% 7.10/7.28      inference('demod', [status(thm)], ['12', '13', '14'])).
% 7.10/7.28  thf('16', plain,
% 7.10/7.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.10/7.28         (((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) = (X1))
% 7.10/7.28          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0))
% 7.10/7.28          | ~ (v1_funct_1 @ (sk_C_2 @ X1 @ X0))
% 7.10/7.28          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_xboole_0))
% 7.10/7.28          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_tarski @ X2))
% 7.10/7.28          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_xboole_0))
% 7.10/7.28          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_tarski @ X2)))),
% 7.10/7.28      inference('sup+', [status(thm)], ['4', '15'])).
% 7.10/7.28  thf('17', plain,
% 7.10/7.28      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (sk_C_2 @ X13 @ X14))),
% 7.10/7.28      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 7.10/7.28  thf('18', plain,
% 7.10/7.28      (![X13 : $i, X14 : $i]: (v1_funct_1 @ (sk_C_2 @ X13 @ X14))),
% 7.10/7.28      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 7.10/7.28  thf('19', plain,
% 7.10/7.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.10/7.28         (((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) = (X1))
% 7.10/7.28          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_xboole_0))
% 7.10/7.28          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_tarski @ X2))
% 7.10/7.28          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_xboole_0))
% 7.10/7.28          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_tarski @ X2)))),
% 7.10/7.28      inference('demod', [status(thm)], ['16', '17', '18'])).
% 7.10/7.28  thf('20', plain,
% 7.10/7.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.10/7.28         (((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_tarski @ X2))
% 7.10/7.28          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_xboole_0))
% 7.10/7.28          | ((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) = (X1)))),
% 7.10/7.28      inference('simplify', [status(thm)], ['19'])).
% 7.10/7.28  thf('21', plain,
% 7.10/7.28      (![X3 : $i, X4 : $i]:
% 7.10/7.28         (((X3) = (k1_xboole_0))
% 7.10/7.28          | ((sk_C @ X4 @ X3) != (X4))
% 7.10/7.28          | ((X3) = (k1_tarski @ X4)))),
% 7.10/7.28      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 7.10/7.28  thf('22', plain,
% 7.10/7.28      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.10/7.28         (((X0) != (X1))
% 7.10/7.28          | ((k2_relat_1 @ (sk_C_2 @ X0 @ X2)) = (k1_xboole_0))
% 7.10/7.28          | ((k2_relat_1 @ (sk_C_2 @ X0 @ X2)) = (k1_tarski @ X1))
% 7.10/7.28          | ((k2_relat_1 @ (sk_C_2 @ X0 @ X2)) = (k1_tarski @ X1))
% 7.10/7.28          | ((k2_relat_1 @ (sk_C_2 @ X0 @ X2)) = (k1_xboole_0)))),
% 7.10/7.28      inference('sup-', [status(thm)], ['20', '21'])).
% 7.10/7.28  thf('23', plain,
% 7.10/7.28      (![X1 : $i, X2 : $i]:
% 7.10/7.28         (((k2_relat_1 @ (sk_C_2 @ X1 @ X2)) = (k1_tarski @ X1))
% 7.10/7.28          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X2)) = (k1_xboole_0)))),
% 7.10/7.28      inference('simplify', [status(thm)], ['22'])).
% 7.10/7.28  thf(t15_funct_1, conjecture,
% 7.10/7.28    (![A:$i]:
% 7.10/7.28     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 7.10/7.28       ( ![B:$i]:
% 7.10/7.28         ( ?[C:$i]:
% 7.10/7.28           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 7.10/7.28             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 7.10/7.28             ( v1_relat_1 @ C ) ) ) ) ))).
% 7.10/7.28  thf(zf_stmt_0, negated_conjecture,
% 7.10/7.28    (~( ![A:$i]:
% 7.10/7.28        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 7.10/7.28          ( ![B:$i]:
% 7.10/7.28            ( ?[C:$i]:
% 7.10/7.28              ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 7.10/7.28                ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 7.10/7.28                ( v1_relat_1 @ C ) ) ) ) ) )),
% 7.10/7.28    inference('cnf.neg', [status(esa)], [t15_funct_1])).
% 7.10/7.28  thf('24', plain,
% 7.10/7.28      (![X16 : $i]:
% 7.10/7.28         (((k2_relat_1 @ X16) != (k1_tarski @ sk_B))
% 7.10/7.28          | ((k1_relat_1 @ X16) != (sk_A))
% 7.10/7.28          | ~ (v1_funct_1 @ X16)
% 7.10/7.28          | ~ (v1_relat_1 @ X16))),
% 7.10/7.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.10/7.28  thf('25', plain,
% 7.10/7.28      (![X0 : $i, X1 : $i]:
% 7.10/7.28         (((k1_tarski @ X0) != (k1_tarski @ sk_B))
% 7.10/7.28          | ((k2_relat_1 @ (sk_C_2 @ X0 @ X1)) = (k1_xboole_0))
% 7.10/7.28          | ~ (v1_relat_1 @ (sk_C_2 @ X0 @ X1))
% 7.10/7.28          | ~ (v1_funct_1 @ (sk_C_2 @ X0 @ X1))
% 7.10/7.28          | ((k1_relat_1 @ (sk_C_2 @ X0 @ X1)) != (sk_A)))),
% 7.10/7.28      inference('sup-', [status(thm)], ['23', '24'])).
% 7.10/7.28  thf('26', plain,
% 7.10/7.28      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (sk_C_2 @ X13 @ X14))),
% 7.10/7.28      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 7.10/7.28  thf('27', plain,
% 7.10/7.28      (![X13 : $i, X14 : $i]: (v1_funct_1 @ (sk_C_2 @ X13 @ X14))),
% 7.10/7.28      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 7.10/7.28  thf('28', plain,
% 7.10/7.28      (![X13 : $i, X14 : $i]: ((k1_relat_1 @ (sk_C_2 @ X13 @ X14)) = (X14))),
% 7.10/7.28      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 7.10/7.28  thf('29', plain,
% 7.10/7.28      (![X0 : $i, X1 : $i]:
% 7.10/7.28         (((k1_tarski @ X0) != (k1_tarski @ sk_B))
% 7.10/7.28          | ((k2_relat_1 @ (sk_C_2 @ X0 @ X1)) = (k1_xboole_0))
% 7.10/7.28          | ((X1) != (sk_A)))),
% 7.10/7.28      inference('demod', [status(thm)], ['25', '26', '27', '28'])).
% 7.10/7.28  thf('30', plain,
% 7.10/7.28      (![X0 : $i]:
% 7.10/7.28         (((k2_relat_1 @ (sk_C_2 @ X0 @ sk_A)) = (k1_xboole_0))
% 7.10/7.28          | ((k1_tarski @ X0) != (k1_tarski @ sk_B)))),
% 7.10/7.28      inference('simplify', [status(thm)], ['29'])).
% 7.10/7.28  thf('31', plain, (((k2_relat_1 @ (sk_C_2 @ sk_B @ sk_A)) = (k1_xboole_0))),
% 7.10/7.28      inference('eq_res', [status(thm)], ['30'])).
% 7.10/7.28  thf(t64_relat_1, axiom,
% 7.10/7.28    (![A:$i]:
% 7.10/7.28     ( ( v1_relat_1 @ A ) =>
% 7.10/7.28       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 7.10/7.28           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 7.10/7.28         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 7.10/7.28  thf('32', plain,
% 7.10/7.28      (![X5 : $i]:
% 7.10/7.28         (((k2_relat_1 @ X5) != (k1_xboole_0))
% 7.10/7.28          | ((X5) = (k1_xboole_0))
% 7.10/7.28          | ~ (v1_relat_1 @ X5))),
% 7.10/7.28      inference('cnf', [status(esa)], [t64_relat_1])).
% 7.10/7.28  thf('33', plain,
% 7.10/7.28      ((((k1_xboole_0) != (k1_xboole_0))
% 7.10/7.28        | ~ (v1_relat_1 @ (sk_C_2 @ sk_B @ sk_A))
% 7.10/7.28        | ((sk_C_2 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 7.10/7.28      inference('sup-', [status(thm)], ['31', '32'])).
% 7.10/7.28  thf('34', plain,
% 7.10/7.28      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (sk_C_2 @ X13 @ X14))),
% 7.10/7.28      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 7.10/7.28  thf('35', plain,
% 7.10/7.28      ((((k1_xboole_0) != (k1_xboole_0))
% 7.10/7.28        | ((sk_C_2 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 7.10/7.28      inference('demod', [status(thm)], ['33', '34'])).
% 7.10/7.28  thf('36', plain, (((sk_C_2 @ sk_B @ sk_A) = (k1_xboole_0))),
% 7.10/7.28      inference('simplify', [status(thm)], ['35'])).
% 7.10/7.28  thf('37', plain,
% 7.10/7.28      (![X13 : $i, X14 : $i]: ((k1_relat_1 @ (sk_C_2 @ X13 @ X14)) = (X14))),
% 7.10/7.28      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 7.10/7.28  thf('38', plain, (((k1_relat_1 @ k1_xboole_0) = (sk_A))),
% 7.10/7.28      inference('sup+', [status(thm)], ['36', '37'])).
% 7.10/7.28  thf('39', plain, (((k1_xboole_0) = (sk_A))),
% 7.10/7.28      inference('sup+', [status(thm)], ['0', '38'])).
% 7.10/7.28  thf('40', plain, (((sk_A) != (k1_xboole_0))),
% 7.10/7.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.10/7.28  thf('41', plain, ($false),
% 7.10/7.28      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 7.10/7.28  
% 7.10/7.28  % SZS output end Refutation
% 7.10/7.28  
% 7.13/7.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
