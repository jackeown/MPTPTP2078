%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vQGjbpT2zf

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:28 EST 2020

% Result     : Theorem 19.09s
% Output     : Refutation 19.09s
% Verified   : 
% Statistics : Number of formulae       :   58 (  73 expanded)
%              Number of leaves         :   18 (  32 expanded)
%              Depth                    :   19
%              Number of atoms          :  626 ( 864 expanded)
%              Number of equality atoms :   81 ( 115 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

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

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t41_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('0',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 )
      | ( X3
        = ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

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
    ! [X7: $i,X9: $i,X10: $i] :
      ( ( X9
       != ( k2_relat_1 @ X7 ) )
      | ( X10
        = ( k1_funct_1 @ X7 @ ( sk_D_1 @ X10 @ X7 ) ) )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('2',plain,(
    ! [X7: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k2_relat_1 @ X7 ) )
      | ( X10
        = ( k1_funct_1 @ X7 @ ( sk_D_1 @ X10 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) )
        = ( k1_funct_1 @ X0 @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

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

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 )
      | ( X3
        = ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('6',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ( X9
       != ( k2_relat_1 @ X7 ) )
      | ( r2_hidden @ ( sk_D_1 @ X10 @ X7 ) @ ( k1_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('7',plain,(
    ! [X7: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k2_relat_1 @ X7 ) )
      | ( r2_hidden @ ( sk_D_1 @ X10 @ X7 ) @ ( k1_relat_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ X1 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X1 @ ( k2_relat_1 @ X0 ) ) @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) ) @ ( sk_C_2 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X1 @ X0 ) )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
        = ( k1_tarski @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('11',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D_1 @ ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) ) @ ( sk_C_2 @ X1 @ X0 ) ) @ X0 )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
        = ( k1_tarski @ X2 ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X13 @ X14 ) @ X15 )
        = X13 )
      | ~ ( r2_hidden @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
        = ( k1_tarski @ X2 ) )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( sk_C_2 @ X3 @ X0 ) @ ( sk_D_1 @ ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) ) @ ( sk_C_2 @ X1 @ X0 ) ) )
        = X3 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
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
    inference('sup+',[status(thm)],['3','14'])).

thf('16',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('18',plain,(
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
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
        = ( k1_tarski @ X2 ) )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) )
        = k1_xboole_0 )
      | ( ( sk_C @ X2 @ ( k2_relat_1 @ ( sk_C_2 @ X1 @ X0 ) ) )
        = X1 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( ( sk_C @ X4 @ X3 )
       != X4 )
      | ( X3
        = ( k1_tarski @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[t41_zfmisc_1])).

thf('21',plain,(
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
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X2 ) )
        = ( k1_tarski @ X1 ) )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X1 @ X2 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

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

thf('23',plain,(
    ! [X16: $i] :
      ( ( ( k2_relat_1 @ X16 )
       != ( k1_tarski @ sk_B ) )
      | ( ( k1_relat_1 @ X16 )
       != sk_A )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_B ) )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X0 @ X1 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( sk_C_2 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ ( sk_C_2 @ X0 @ X1 ) )
      | ( ( k1_relat_1 @ ( sk_C_2 @ X0 @ X1 ) )
       != sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('26',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_B ) )
      | ( ( k2_relat_1 @ ( sk_C_2 @ X0 @ X1 ) )
        = k1_xboole_0 )
      | ( X1 != sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( sk_C_2 @ X0 @ sk_A ) )
        = k1_xboole_0 )
      | ( ( k1_tarski @ X0 )
       != ( k1_tarski @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( k2_relat_1 @ ( sk_C_2 @ sk_B @ sk_A ) )
    = k1_xboole_0 ),
    inference(eq_res,[status(thm)],['29'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('31',plain,(
    ! [X5: $i] :
      ( ( ( k2_relat_1 @ X5 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X5 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('32',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( sk_C_2 @ sk_B @ sk_A ) )
    | ( ( k1_relat_1 @ ( sk_C_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X13 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('35',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
    sk_A = k1_xboole_0 ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['36','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vQGjbpT2zf
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:48:39 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 19.09/19.34  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 19.09/19.34  % Solved by: fo/fo7.sh
% 19.09/19.34  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 19.09/19.34  % done 4599 iterations in 18.896s
% 19.09/19.34  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 19.09/19.34  % SZS output start Refutation
% 19.09/19.34  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 19.09/19.34  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 19.09/19.34  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 19.09/19.34  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 19.09/19.34  thf(sk_A_type, type, sk_A: $i).
% 19.09/19.34  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 19.09/19.34  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 19.09/19.34  thf(sk_B_type, type, sk_B: $i).
% 19.09/19.34  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 19.09/19.34  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 19.09/19.34  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 19.09/19.34  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 19.09/19.34  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 19.09/19.34  thf(t41_zfmisc_1, axiom,
% 19.09/19.34    (![A:$i,B:$i]:
% 19.09/19.34     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 19.09/19.34          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 19.09/19.34  thf('0', plain,
% 19.09/19.34      (![X3 : $i, X4 : $i]:
% 19.09/19.34         (((X3) = (k1_xboole_0))
% 19.09/19.34          | (r2_hidden @ (sk_C @ X4 @ X3) @ X3)
% 19.09/19.34          | ((X3) = (k1_tarski @ X4)))),
% 19.09/19.34      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 19.09/19.34  thf(d5_funct_1, axiom,
% 19.09/19.34    (![A:$i]:
% 19.09/19.34     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 19.09/19.34       ( ![B:$i]:
% 19.09/19.34         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 19.09/19.34           ( ![C:$i]:
% 19.09/19.34             ( ( r2_hidden @ C @ B ) <=>
% 19.09/19.34               ( ?[D:$i]:
% 19.09/19.34                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 19.09/19.34                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 19.09/19.34  thf('1', plain,
% 19.09/19.34      (![X7 : $i, X9 : $i, X10 : $i]:
% 19.09/19.34         (((X9) != (k2_relat_1 @ X7))
% 19.09/19.34          | ((X10) = (k1_funct_1 @ X7 @ (sk_D_1 @ X10 @ X7)))
% 19.09/19.34          | ~ (r2_hidden @ X10 @ X9)
% 19.09/19.34          | ~ (v1_funct_1 @ X7)
% 19.09/19.34          | ~ (v1_relat_1 @ X7))),
% 19.09/19.34      inference('cnf', [status(esa)], [d5_funct_1])).
% 19.09/19.34  thf('2', plain,
% 19.09/19.34      (![X7 : $i, X10 : $i]:
% 19.09/19.34         (~ (v1_relat_1 @ X7)
% 19.09/19.34          | ~ (v1_funct_1 @ X7)
% 19.09/19.34          | ~ (r2_hidden @ X10 @ (k2_relat_1 @ X7))
% 19.09/19.34          | ((X10) = (k1_funct_1 @ X7 @ (sk_D_1 @ X10 @ X7))))),
% 19.09/19.34      inference('simplify', [status(thm)], ['1'])).
% 19.09/19.34  thf('3', plain,
% 19.09/19.34      (![X0 : $i, X1 : $i]:
% 19.09/19.34         (((k2_relat_1 @ X0) = (k1_tarski @ X1))
% 19.09/19.34          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 19.09/19.34          | ((sk_C @ X1 @ (k2_relat_1 @ X0))
% 19.09/19.34              = (k1_funct_1 @ X0 @ 
% 19.09/19.34                 (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)))
% 19.09/19.34          | ~ (v1_funct_1 @ X0)
% 19.09/19.34          | ~ (v1_relat_1 @ X0))),
% 19.09/19.34      inference('sup-', [status(thm)], ['0', '2'])).
% 19.09/19.34  thf(s3_funct_1__e2_24__funct_1, axiom,
% 19.09/19.34    (![A:$i,B:$i]:
% 19.09/19.34     ( ?[C:$i]:
% 19.09/19.34       ( ( ![D:$i]:
% 19.09/19.34           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 19.09/19.34         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 19.09/19.34         ( v1_relat_1 @ C ) ) ))).
% 19.09/19.34  thf('4', plain,
% 19.09/19.34      (![X13 : $i, X14 : $i]: ((k1_relat_1 @ (sk_C_2 @ X13 @ X14)) = (X14))),
% 19.09/19.34      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 19.09/19.34  thf('5', plain,
% 19.09/19.34      (![X3 : $i, X4 : $i]:
% 19.09/19.34         (((X3) = (k1_xboole_0))
% 19.09/19.34          | (r2_hidden @ (sk_C @ X4 @ X3) @ X3)
% 19.09/19.34          | ((X3) = (k1_tarski @ X4)))),
% 19.09/19.34      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 19.09/19.34  thf('6', plain,
% 19.09/19.34      (![X7 : $i, X9 : $i, X10 : $i]:
% 19.09/19.34         (((X9) != (k2_relat_1 @ X7))
% 19.09/19.34          | (r2_hidden @ (sk_D_1 @ X10 @ X7) @ (k1_relat_1 @ X7))
% 19.09/19.34          | ~ (r2_hidden @ X10 @ X9)
% 19.09/19.34          | ~ (v1_funct_1 @ X7)
% 19.09/19.34          | ~ (v1_relat_1 @ X7))),
% 19.09/19.34      inference('cnf', [status(esa)], [d5_funct_1])).
% 19.09/19.34  thf('7', plain,
% 19.09/19.34      (![X7 : $i, X10 : $i]:
% 19.09/19.34         (~ (v1_relat_1 @ X7)
% 19.09/19.34          | ~ (v1_funct_1 @ X7)
% 19.09/19.34          | ~ (r2_hidden @ X10 @ (k2_relat_1 @ X7))
% 19.09/19.34          | (r2_hidden @ (sk_D_1 @ X10 @ X7) @ (k1_relat_1 @ X7)))),
% 19.09/19.34      inference('simplify', [status(thm)], ['6'])).
% 19.09/19.34  thf('8', plain,
% 19.09/19.34      (![X0 : $i, X1 : $i]:
% 19.09/19.34         (((k2_relat_1 @ X0) = (k1_tarski @ X1))
% 19.09/19.34          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 19.09/19.34          | (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 19.09/19.34             (k1_relat_1 @ X0))
% 19.09/19.34          | ~ (v1_funct_1 @ X0)
% 19.09/19.34          | ~ (v1_relat_1 @ X0))),
% 19.09/19.34      inference('sup-', [status(thm)], ['5', '7'])).
% 19.09/19.34  thf('9', plain,
% 19.09/19.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.09/19.34         ((r2_hidden @ 
% 19.09/19.34           (sk_D_1 @ (sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) @ 
% 19.09/19.34            (sk_C_2 @ X1 @ X0)) @ 
% 19.09/19.34           X0)
% 19.09/19.34          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0))
% 19.09/19.34          | ~ (v1_funct_1 @ (sk_C_2 @ X1 @ X0))
% 19.09/19.34          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_xboole_0))
% 19.09/19.34          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_tarski @ X2)))),
% 19.09/19.34      inference('sup+', [status(thm)], ['4', '8'])).
% 19.09/19.34  thf('10', plain,
% 19.09/19.34      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (sk_C_2 @ X13 @ X14))),
% 19.09/19.34      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 19.09/19.34  thf('11', plain,
% 19.09/19.34      (![X13 : $i, X14 : $i]: (v1_funct_1 @ (sk_C_2 @ X13 @ X14))),
% 19.09/19.34      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 19.09/19.34  thf('12', plain,
% 19.09/19.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.09/19.34         ((r2_hidden @ 
% 19.09/19.34           (sk_D_1 @ (sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) @ 
% 19.09/19.34            (sk_C_2 @ X1 @ X0)) @ 
% 19.09/19.34           X0)
% 19.09/19.34          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_xboole_0))
% 19.09/19.34          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_tarski @ X2)))),
% 19.09/19.34      inference('demod', [status(thm)], ['9', '10', '11'])).
% 19.09/19.34  thf('13', plain,
% 19.09/19.34      (![X13 : $i, X14 : $i, X15 : $i]:
% 19.09/19.34         (((k1_funct_1 @ (sk_C_2 @ X13 @ X14) @ X15) = (X13))
% 19.09/19.34          | ~ (r2_hidden @ X15 @ X14))),
% 19.09/19.34      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 19.09/19.34  thf('14', plain,
% 19.09/19.34      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 19.09/19.34         (((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_tarski @ X2))
% 19.09/19.34          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_xboole_0))
% 19.09/19.34          | ((k1_funct_1 @ (sk_C_2 @ X3 @ X0) @ 
% 19.09/19.34              (sk_D_1 @ (sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) @ 
% 19.09/19.34               (sk_C_2 @ X1 @ X0)))
% 19.09/19.34              = (X3)))),
% 19.09/19.34      inference('sup-', [status(thm)], ['12', '13'])).
% 19.09/19.34  thf('15', plain,
% 19.09/19.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.09/19.34         (((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) = (X1))
% 19.09/19.34          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0))
% 19.09/19.34          | ~ (v1_funct_1 @ (sk_C_2 @ X1 @ X0))
% 19.09/19.34          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_xboole_0))
% 19.09/19.34          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_tarski @ X2))
% 19.09/19.34          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_xboole_0))
% 19.09/19.34          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_tarski @ X2)))),
% 19.09/19.34      inference('sup+', [status(thm)], ['3', '14'])).
% 19.09/19.34  thf('16', plain,
% 19.09/19.34      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (sk_C_2 @ X13 @ X14))),
% 19.09/19.34      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 19.09/19.34  thf('17', plain,
% 19.09/19.34      (![X13 : $i, X14 : $i]: (v1_funct_1 @ (sk_C_2 @ X13 @ X14))),
% 19.09/19.34      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 19.09/19.34  thf('18', plain,
% 19.09/19.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.09/19.34         (((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) = (X1))
% 19.09/19.34          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_xboole_0))
% 19.09/19.34          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_tarski @ X2))
% 19.09/19.34          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_xboole_0))
% 19.09/19.34          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_tarski @ X2)))),
% 19.09/19.34      inference('demod', [status(thm)], ['15', '16', '17'])).
% 19.09/19.34  thf('19', plain,
% 19.09/19.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.09/19.34         (((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_tarski @ X2))
% 19.09/19.34          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_xboole_0))
% 19.09/19.34          | ((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) = (X1)))),
% 19.09/19.34      inference('simplify', [status(thm)], ['18'])).
% 19.09/19.34  thf('20', plain,
% 19.09/19.34      (![X3 : $i, X4 : $i]:
% 19.09/19.34         (((X3) = (k1_xboole_0))
% 19.09/19.34          | ((sk_C @ X4 @ X3) != (X4))
% 19.09/19.34          | ((X3) = (k1_tarski @ X4)))),
% 19.09/19.34      inference('cnf', [status(esa)], [t41_zfmisc_1])).
% 19.09/19.34  thf('21', plain,
% 19.09/19.34      (![X0 : $i, X1 : $i, X2 : $i]:
% 19.09/19.34         (((X0) != (X1))
% 19.09/19.34          | ((k2_relat_1 @ (sk_C_2 @ X0 @ X2)) = (k1_xboole_0))
% 19.09/19.34          | ((k2_relat_1 @ (sk_C_2 @ X0 @ X2)) = (k1_tarski @ X1))
% 19.09/19.34          | ((k2_relat_1 @ (sk_C_2 @ X0 @ X2)) = (k1_tarski @ X1))
% 19.09/19.34          | ((k2_relat_1 @ (sk_C_2 @ X0 @ X2)) = (k1_xboole_0)))),
% 19.09/19.34      inference('sup-', [status(thm)], ['19', '20'])).
% 19.09/19.34  thf('22', plain,
% 19.09/19.34      (![X1 : $i, X2 : $i]:
% 19.09/19.34         (((k2_relat_1 @ (sk_C_2 @ X1 @ X2)) = (k1_tarski @ X1))
% 19.09/19.34          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X2)) = (k1_xboole_0)))),
% 19.09/19.34      inference('simplify', [status(thm)], ['21'])).
% 19.09/19.34  thf(t15_funct_1, conjecture,
% 19.09/19.34    (![A:$i]:
% 19.09/19.34     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 19.09/19.34       ( ![B:$i]:
% 19.09/19.34         ( ?[C:$i]:
% 19.09/19.34           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 19.09/19.34             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 19.09/19.34             ( v1_relat_1 @ C ) ) ) ) ))).
% 19.09/19.34  thf(zf_stmt_0, negated_conjecture,
% 19.09/19.34    (~( ![A:$i]:
% 19.09/19.34        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 19.09/19.34          ( ![B:$i]:
% 19.09/19.34            ( ?[C:$i]:
% 19.09/19.34              ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 19.09/19.34                ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 19.09/19.34                ( v1_relat_1 @ C ) ) ) ) ) )),
% 19.09/19.34    inference('cnf.neg', [status(esa)], [t15_funct_1])).
% 19.09/19.34  thf('23', plain,
% 19.09/19.34      (![X16 : $i]:
% 19.09/19.34         (((k2_relat_1 @ X16) != (k1_tarski @ sk_B))
% 19.09/19.34          | ((k1_relat_1 @ X16) != (sk_A))
% 19.09/19.34          | ~ (v1_funct_1 @ X16)
% 19.09/19.34          | ~ (v1_relat_1 @ X16))),
% 19.09/19.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.09/19.34  thf('24', plain,
% 19.09/19.34      (![X0 : $i, X1 : $i]:
% 19.09/19.34         (((k1_tarski @ X0) != (k1_tarski @ sk_B))
% 19.09/19.34          | ((k2_relat_1 @ (sk_C_2 @ X0 @ X1)) = (k1_xboole_0))
% 19.09/19.34          | ~ (v1_relat_1 @ (sk_C_2 @ X0 @ X1))
% 19.09/19.34          | ~ (v1_funct_1 @ (sk_C_2 @ X0 @ X1))
% 19.09/19.34          | ((k1_relat_1 @ (sk_C_2 @ X0 @ X1)) != (sk_A)))),
% 19.09/19.34      inference('sup-', [status(thm)], ['22', '23'])).
% 19.09/19.34  thf('25', plain,
% 19.09/19.34      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (sk_C_2 @ X13 @ X14))),
% 19.09/19.34      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 19.09/19.34  thf('26', plain,
% 19.09/19.34      (![X13 : $i, X14 : $i]: (v1_funct_1 @ (sk_C_2 @ X13 @ X14))),
% 19.09/19.34      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 19.09/19.34  thf('27', plain,
% 19.09/19.34      (![X13 : $i, X14 : $i]: ((k1_relat_1 @ (sk_C_2 @ X13 @ X14)) = (X14))),
% 19.09/19.34      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 19.09/19.34  thf('28', plain,
% 19.09/19.34      (![X0 : $i, X1 : $i]:
% 19.09/19.34         (((k1_tarski @ X0) != (k1_tarski @ sk_B))
% 19.09/19.34          | ((k2_relat_1 @ (sk_C_2 @ X0 @ X1)) = (k1_xboole_0))
% 19.09/19.34          | ((X1) != (sk_A)))),
% 19.09/19.34      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 19.09/19.34  thf('29', plain,
% 19.09/19.34      (![X0 : $i]:
% 19.09/19.34         (((k2_relat_1 @ (sk_C_2 @ X0 @ sk_A)) = (k1_xboole_0))
% 19.09/19.34          | ((k1_tarski @ X0) != (k1_tarski @ sk_B)))),
% 19.09/19.34      inference('simplify', [status(thm)], ['28'])).
% 19.09/19.34  thf('30', plain, (((k2_relat_1 @ (sk_C_2 @ sk_B @ sk_A)) = (k1_xboole_0))),
% 19.09/19.34      inference('eq_res', [status(thm)], ['29'])).
% 19.09/19.34  thf(t65_relat_1, axiom,
% 19.09/19.34    (![A:$i]:
% 19.09/19.34     ( ( v1_relat_1 @ A ) =>
% 19.09/19.34       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 19.09/19.34         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 19.09/19.34  thf('31', plain,
% 19.09/19.34      (![X5 : $i]:
% 19.09/19.34         (((k2_relat_1 @ X5) != (k1_xboole_0))
% 19.09/19.34          | ((k1_relat_1 @ X5) = (k1_xboole_0))
% 19.09/19.34          | ~ (v1_relat_1 @ X5))),
% 19.09/19.34      inference('cnf', [status(esa)], [t65_relat_1])).
% 19.09/19.34  thf('32', plain,
% 19.09/19.34      ((((k1_xboole_0) != (k1_xboole_0))
% 19.09/19.34        | ~ (v1_relat_1 @ (sk_C_2 @ sk_B @ sk_A))
% 19.09/19.34        | ((k1_relat_1 @ (sk_C_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 19.09/19.34      inference('sup-', [status(thm)], ['30', '31'])).
% 19.09/19.34  thf('33', plain,
% 19.09/19.34      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (sk_C_2 @ X13 @ X14))),
% 19.09/19.34      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 19.09/19.34  thf('34', plain,
% 19.09/19.34      (![X13 : $i, X14 : $i]: ((k1_relat_1 @ (sk_C_2 @ X13 @ X14)) = (X14))),
% 19.09/19.34      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 19.09/19.34  thf('35', plain,
% 19.09/19.34      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 19.09/19.34      inference('demod', [status(thm)], ['32', '33', '34'])).
% 19.09/19.34  thf('36', plain, (((sk_A) = (k1_xboole_0))),
% 19.09/19.34      inference('simplify', [status(thm)], ['35'])).
% 19.09/19.34  thf('37', plain, (((sk_A) != (k1_xboole_0))),
% 19.09/19.34      inference('cnf', [status(esa)], [zf_stmt_0])).
% 19.09/19.34  thf('38', plain, ($false),
% 19.09/19.34      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 19.09/19.34  
% 19.09/19.34  % SZS output end Refutation
% 19.09/19.34  
% 19.09/19.35  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
