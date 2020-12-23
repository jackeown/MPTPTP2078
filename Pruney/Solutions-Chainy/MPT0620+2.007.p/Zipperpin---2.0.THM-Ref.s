%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.b7cG0x2BPA

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:27 EST 2020

% Result     : Theorem 16.21s
% Output     : Refutation 16.21s
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

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(l44_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ X1 )
      | ( X1
        = ( k1_tarski @ X2 ) ) ) ),
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

thf('1',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( X7
       != ( k2_relat_1 @ X5 ) )
      | ( X8
        = ( k1_funct_1 @ X5 @ ( sk_D_1 @ X8 @ X5 ) ) )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('2',plain,(
    ! [X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X5 ) )
      | ( X8
        = ( k1_funct_1 @ X5 @ ( sk_D_1 @ X8 @ X5 ) ) ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('5',plain,(
    ! [X1: $i,X2: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ X1 )
      | ( X1
        = ( k1_tarski @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('6',plain,(
    ! [X5: $i,X7: $i,X8: $i] :
      ( ( X7
       != ( k2_relat_1 @ X5 ) )
      | ( r2_hidden @ ( sk_D_1 @ X8 @ X5 ) @ ( k1_relat_1 @ X5 ) )
      | ~ ( r2_hidden @ X8 @ X7 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('7',plain,(
    ! [X5: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( r2_hidden @ X8 @ ( k2_relat_1 @ X5 ) )
      | ( r2_hidden @ ( sk_D_1 @ X8 @ X5 ) @ ( k1_relat_1 @ X5 ) ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('11',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
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
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_2 @ X11 @ X12 ) @ X13 )
        = X11 )
      | ~ ( r2_hidden @ X13 @ X12 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('17',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
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
    ! [X1: $i,X2: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( ( sk_C @ X2 @ X1 )
       != X2 )
      | ( X1
        = ( k1_tarski @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

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
    ! [X14: $i] :
      ( ( ( k2_relat_1 @ X14 )
       != ( k1_tarski @ sk_B ) )
      | ( ( k1_relat_1 @ X14 )
       != sk_A )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('26',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_funct_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('27',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) )
      = X12 ) ),
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
    ! [X3: $i] :
      ( ( ( k2_relat_1 @ X3 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X3 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('32',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( sk_C_2 @ sk_B @ sk_A ) )
    | ( ( k1_relat_1 @ ( sk_C_2 @ sk_B @ sk_A ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('34',plain,(
    ! [X11: $i,X12: $i] :
      ( ( k1_relat_1 @ ( sk_C_2 @ X11 @ X12 ) )
      = X12 ) ),
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
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.b7cG0x2BPA
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:52:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 16.21/16.41  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 16.21/16.41  % Solved by: fo/fo7.sh
% 16.21/16.41  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 16.21/16.41  % done 3839 iterations in 15.955s
% 16.21/16.41  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 16.21/16.41  % SZS output start Refutation
% 16.21/16.41  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 16.21/16.41  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 16.21/16.41  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 16.21/16.41  thf(sk_B_type, type, sk_B: $i).
% 16.21/16.41  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 16.21/16.41  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 16.21/16.41  thf(sk_A_type, type, sk_A: $i).
% 16.21/16.41  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 16.21/16.41  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 16.21/16.41  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 16.21/16.41  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 16.21/16.41  thf(sk_C_2_type, type, sk_C_2: $i > $i > $i).
% 16.21/16.41  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 16.21/16.41  thf(l44_zfmisc_1, axiom,
% 16.21/16.41    (![A:$i,B:$i]:
% 16.21/16.41     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 16.21/16.41          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 16.21/16.41  thf('0', plain,
% 16.21/16.41      (![X1 : $i, X2 : $i]:
% 16.21/16.41         (((X1) = (k1_xboole_0))
% 16.21/16.41          | (r2_hidden @ (sk_C @ X2 @ X1) @ X1)
% 16.21/16.41          | ((X1) = (k1_tarski @ X2)))),
% 16.21/16.41      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 16.21/16.41  thf(d5_funct_1, axiom,
% 16.21/16.41    (![A:$i]:
% 16.21/16.41     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 16.21/16.41       ( ![B:$i]:
% 16.21/16.41         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 16.21/16.41           ( ![C:$i]:
% 16.21/16.41             ( ( r2_hidden @ C @ B ) <=>
% 16.21/16.41               ( ?[D:$i]:
% 16.21/16.41                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 16.21/16.41                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 16.21/16.41  thf('1', plain,
% 16.21/16.41      (![X5 : $i, X7 : $i, X8 : $i]:
% 16.21/16.41         (((X7) != (k2_relat_1 @ X5))
% 16.21/16.41          | ((X8) = (k1_funct_1 @ X5 @ (sk_D_1 @ X8 @ X5)))
% 16.21/16.41          | ~ (r2_hidden @ X8 @ X7)
% 16.21/16.41          | ~ (v1_funct_1 @ X5)
% 16.21/16.41          | ~ (v1_relat_1 @ X5))),
% 16.21/16.41      inference('cnf', [status(esa)], [d5_funct_1])).
% 16.21/16.41  thf('2', plain,
% 16.21/16.41      (![X5 : $i, X8 : $i]:
% 16.21/16.41         (~ (v1_relat_1 @ X5)
% 16.21/16.41          | ~ (v1_funct_1 @ X5)
% 16.21/16.41          | ~ (r2_hidden @ X8 @ (k2_relat_1 @ X5))
% 16.21/16.41          | ((X8) = (k1_funct_1 @ X5 @ (sk_D_1 @ X8 @ X5))))),
% 16.21/16.41      inference('simplify', [status(thm)], ['1'])).
% 16.21/16.41  thf('3', plain,
% 16.21/16.41      (![X0 : $i, X1 : $i]:
% 16.21/16.41         (((k2_relat_1 @ X0) = (k1_tarski @ X1))
% 16.21/16.41          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 16.21/16.41          | ((sk_C @ X1 @ (k2_relat_1 @ X0))
% 16.21/16.41              = (k1_funct_1 @ X0 @ 
% 16.21/16.41                 (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0)))
% 16.21/16.41          | ~ (v1_funct_1 @ X0)
% 16.21/16.41          | ~ (v1_relat_1 @ X0))),
% 16.21/16.41      inference('sup-', [status(thm)], ['0', '2'])).
% 16.21/16.41  thf(s3_funct_1__e2_24__funct_1, axiom,
% 16.21/16.41    (![A:$i,B:$i]:
% 16.21/16.41     ( ?[C:$i]:
% 16.21/16.41       ( ( ![D:$i]:
% 16.21/16.41           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 16.21/16.41         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 16.21/16.41         ( v1_relat_1 @ C ) ) ))).
% 16.21/16.41  thf('4', plain,
% 16.21/16.41      (![X11 : $i, X12 : $i]: ((k1_relat_1 @ (sk_C_2 @ X11 @ X12)) = (X12))),
% 16.21/16.41      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 16.21/16.41  thf('5', plain,
% 16.21/16.41      (![X1 : $i, X2 : $i]:
% 16.21/16.41         (((X1) = (k1_xboole_0))
% 16.21/16.41          | (r2_hidden @ (sk_C @ X2 @ X1) @ X1)
% 16.21/16.41          | ((X1) = (k1_tarski @ X2)))),
% 16.21/16.41      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 16.21/16.41  thf('6', plain,
% 16.21/16.41      (![X5 : $i, X7 : $i, X8 : $i]:
% 16.21/16.41         (((X7) != (k2_relat_1 @ X5))
% 16.21/16.41          | (r2_hidden @ (sk_D_1 @ X8 @ X5) @ (k1_relat_1 @ X5))
% 16.21/16.41          | ~ (r2_hidden @ X8 @ X7)
% 16.21/16.41          | ~ (v1_funct_1 @ X5)
% 16.21/16.41          | ~ (v1_relat_1 @ X5))),
% 16.21/16.41      inference('cnf', [status(esa)], [d5_funct_1])).
% 16.21/16.41  thf('7', plain,
% 16.21/16.41      (![X5 : $i, X8 : $i]:
% 16.21/16.41         (~ (v1_relat_1 @ X5)
% 16.21/16.41          | ~ (v1_funct_1 @ X5)
% 16.21/16.41          | ~ (r2_hidden @ X8 @ (k2_relat_1 @ X5))
% 16.21/16.41          | (r2_hidden @ (sk_D_1 @ X8 @ X5) @ (k1_relat_1 @ X5)))),
% 16.21/16.41      inference('simplify', [status(thm)], ['6'])).
% 16.21/16.41  thf('8', plain,
% 16.21/16.41      (![X0 : $i, X1 : $i]:
% 16.21/16.41         (((k2_relat_1 @ X0) = (k1_tarski @ X1))
% 16.21/16.41          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 16.21/16.41          | (r2_hidden @ (sk_D_1 @ (sk_C @ X1 @ (k2_relat_1 @ X0)) @ X0) @ 
% 16.21/16.41             (k1_relat_1 @ X0))
% 16.21/16.41          | ~ (v1_funct_1 @ X0)
% 16.21/16.41          | ~ (v1_relat_1 @ X0))),
% 16.21/16.41      inference('sup-', [status(thm)], ['5', '7'])).
% 16.21/16.41  thf('9', plain,
% 16.21/16.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.21/16.41         ((r2_hidden @ 
% 16.21/16.41           (sk_D_1 @ (sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) @ 
% 16.21/16.41            (sk_C_2 @ X1 @ X0)) @ 
% 16.21/16.41           X0)
% 16.21/16.41          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0))
% 16.21/16.41          | ~ (v1_funct_1 @ (sk_C_2 @ X1 @ X0))
% 16.21/16.41          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_xboole_0))
% 16.21/16.41          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_tarski @ X2)))),
% 16.21/16.41      inference('sup+', [status(thm)], ['4', '8'])).
% 16.21/16.41  thf('10', plain,
% 16.21/16.41      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (sk_C_2 @ X11 @ X12))),
% 16.21/16.41      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 16.21/16.41  thf('11', plain,
% 16.21/16.41      (![X11 : $i, X12 : $i]: (v1_funct_1 @ (sk_C_2 @ X11 @ X12))),
% 16.21/16.41      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 16.21/16.41  thf('12', plain,
% 16.21/16.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.21/16.41         ((r2_hidden @ 
% 16.21/16.41           (sk_D_1 @ (sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) @ 
% 16.21/16.41            (sk_C_2 @ X1 @ X0)) @ 
% 16.21/16.41           X0)
% 16.21/16.41          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_xboole_0))
% 16.21/16.41          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_tarski @ X2)))),
% 16.21/16.41      inference('demod', [status(thm)], ['9', '10', '11'])).
% 16.21/16.41  thf('13', plain,
% 16.21/16.41      (![X11 : $i, X12 : $i, X13 : $i]:
% 16.21/16.41         (((k1_funct_1 @ (sk_C_2 @ X11 @ X12) @ X13) = (X11))
% 16.21/16.41          | ~ (r2_hidden @ X13 @ X12))),
% 16.21/16.41      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 16.21/16.41  thf('14', plain,
% 16.21/16.41      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 16.21/16.41         (((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_tarski @ X2))
% 16.21/16.41          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_xboole_0))
% 16.21/16.41          | ((k1_funct_1 @ (sk_C_2 @ X3 @ X0) @ 
% 16.21/16.41              (sk_D_1 @ (sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) @ 
% 16.21/16.41               (sk_C_2 @ X1 @ X0)))
% 16.21/16.41              = (X3)))),
% 16.21/16.41      inference('sup-', [status(thm)], ['12', '13'])).
% 16.21/16.41  thf('15', plain,
% 16.21/16.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.21/16.41         (((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) = (X1))
% 16.21/16.41          | ~ (v1_relat_1 @ (sk_C_2 @ X1 @ X0))
% 16.21/16.41          | ~ (v1_funct_1 @ (sk_C_2 @ X1 @ X0))
% 16.21/16.41          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_xboole_0))
% 16.21/16.41          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_tarski @ X2))
% 16.21/16.41          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_xboole_0))
% 16.21/16.41          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_tarski @ X2)))),
% 16.21/16.41      inference('sup+', [status(thm)], ['3', '14'])).
% 16.21/16.41  thf('16', plain,
% 16.21/16.41      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (sk_C_2 @ X11 @ X12))),
% 16.21/16.41      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 16.21/16.41  thf('17', plain,
% 16.21/16.41      (![X11 : $i, X12 : $i]: (v1_funct_1 @ (sk_C_2 @ X11 @ X12))),
% 16.21/16.41      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 16.21/16.41  thf('18', plain,
% 16.21/16.41      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.21/16.41         (((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) = (X1))
% 16.21/16.41          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_xboole_0))
% 16.21/16.41          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_tarski @ X2))
% 16.21/16.41          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_xboole_0))
% 16.21/16.41          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_tarski @ X2)))),
% 16.21/16.41      inference('demod', [status(thm)], ['15', '16', '17'])).
% 16.21/16.42  thf('19', plain,
% 16.21/16.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.21/16.42         (((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_tarski @ X2))
% 16.21/16.42          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X0)) = (k1_xboole_0))
% 16.21/16.42          | ((sk_C @ X2 @ (k2_relat_1 @ (sk_C_2 @ X1 @ X0))) = (X1)))),
% 16.21/16.42      inference('simplify', [status(thm)], ['18'])).
% 16.21/16.42  thf('20', plain,
% 16.21/16.42      (![X1 : $i, X2 : $i]:
% 16.21/16.42         (((X1) = (k1_xboole_0))
% 16.21/16.42          | ((sk_C @ X2 @ X1) != (X2))
% 16.21/16.42          | ((X1) = (k1_tarski @ X2)))),
% 16.21/16.42      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 16.21/16.42  thf('21', plain,
% 16.21/16.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 16.21/16.42         (((X0) != (X1))
% 16.21/16.42          | ((k2_relat_1 @ (sk_C_2 @ X0 @ X2)) = (k1_xboole_0))
% 16.21/16.42          | ((k2_relat_1 @ (sk_C_2 @ X0 @ X2)) = (k1_tarski @ X1))
% 16.21/16.42          | ((k2_relat_1 @ (sk_C_2 @ X0 @ X2)) = (k1_tarski @ X1))
% 16.21/16.42          | ((k2_relat_1 @ (sk_C_2 @ X0 @ X2)) = (k1_xboole_0)))),
% 16.21/16.42      inference('sup-', [status(thm)], ['19', '20'])).
% 16.21/16.42  thf('22', plain,
% 16.21/16.42      (![X1 : $i, X2 : $i]:
% 16.21/16.42         (((k2_relat_1 @ (sk_C_2 @ X1 @ X2)) = (k1_tarski @ X1))
% 16.21/16.42          | ((k2_relat_1 @ (sk_C_2 @ X1 @ X2)) = (k1_xboole_0)))),
% 16.21/16.42      inference('simplify', [status(thm)], ['21'])).
% 16.21/16.42  thf(t15_funct_1, conjecture,
% 16.21/16.42    (![A:$i]:
% 16.21/16.42     ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 16.21/16.42       ( ![B:$i]:
% 16.21/16.42         ( ?[C:$i]:
% 16.21/16.42           ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 16.21/16.42             ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 16.21/16.42             ( v1_relat_1 @ C ) ) ) ) ))).
% 16.21/16.42  thf(zf_stmt_0, negated_conjecture,
% 16.21/16.42    (~( ![A:$i]:
% 16.21/16.42        ( ( ( A ) != ( k1_xboole_0 ) ) =>
% 16.21/16.42          ( ![B:$i]:
% 16.21/16.42            ( ?[C:$i]:
% 16.21/16.42              ( ( ( k2_relat_1 @ C ) = ( k1_tarski @ B ) ) & 
% 16.21/16.42                ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 16.21/16.42                ( v1_relat_1 @ C ) ) ) ) ) )),
% 16.21/16.42    inference('cnf.neg', [status(esa)], [t15_funct_1])).
% 16.21/16.42  thf('23', plain,
% 16.21/16.42      (![X14 : $i]:
% 16.21/16.42         (((k2_relat_1 @ X14) != (k1_tarski @ sk_B))
% 16.21/16.42          | ((k1_relat_1 @ X14) != (sk_A))
% 16.21/16.42          | ~ (v1_funct_1 @ X14)
% 16.21/16.42          | ~ (v1_relat_1 @ X14))),
% 16.21/16.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.21/16.42  thf('24', plain,
% 16.21/16.42      (![X0 : $i, X1 : $i]:
% 16.21/16.42         (((k1_tarski @ X0) != (k1_tarski @ sk_B))
% 16.21/16.42          | ((k2_relat_1 @ (sk_C_2 @ X0 @ X1)) = (k1_xboole_0))
% 16.21/16.42          | ~ (v1_relat_1 @ (sk_C_2 @ X0 @ X1))
% 16.21/16.42          | ~ (v1_funct_1 @ (sk_C_2 @ X0 @ X1))
% 16.21/16.42          | ((k1_relat_1 @ (sk_C_2 @ X0 @ X1)) != (sk_A)))),
% 16.21/16.42      inference('sup-', [status(thm)], ['22', '23'])).
% 16.21/16.42  thf('25', plain,
% 16.21/16.42      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (sk_C_2 @ X11 @ X12))),
% 16.21/16.42      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 16.21/16.42  thf('26', plain,
% 16.21/16.42      (![X11 : $i, X12 : $i]: (v1_funct_1 @ (sk_C_2 @ X11 @ X12))),
% 16.21/16.42      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 16.21/16.42  thf('27', plain,
% 16.21/16.42      (![X11 : $i, X12 : $i]: ((k1_relat_1 @ (sk_C_2 @ X11 @ X12)) = (X12))),
% 16.21/16.42      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 16.21/16.42  thf('28', plain,
% 16.21/16.42      (![X0 : $i, X1 : $i]:
% 16.21/16.42         (((k1_tarski @ X0) != (k1_tarski @ sk_B))
% 16.21/16.42          | ((k2_relat_1 @ (sk_C_2 @ X0 @ X1)) = (k1_xboole_0))
% 16.21/16.42          | ((X1) != (sk_A)))),
% 16.21/16.42      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 16.21/16.42  thf('29', plain,
% 16.21/16.42      (![X0 : $i]:
% 16.21/16.42         (((k2_relat_1 @ (sk_C_2 @ X0 @ sk_A)) = (k1_xboole_0))
% 16.21/16.42          | ((k1_tarski @ X0) != (k1_tarski @ sk_B)))),
% 16.21/16.42      inference('simplify', [status(thm)], ['28'])).
% 16.21/16.42  thf('30', plain, (((k2_relat_1 @ (sk_C_2 @ sk_B @ sk_A)) = (k1_xboole_0))),
% 16.21/16.42      inference('eq_res', [status(thm)], ['29'])).
% 16.21/16.42  thf(t65_relat_1, axiom,
% 16.21/16.42    (![A:$i]:
% 16.21/16.42     ( ( v1_relat_1 @ A ) =>
% 16.21/16.42       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 16.21/16.42         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 16.21/16.42  thf('31', plain,
% 16.21/16.42      (![X3 : $i]:
% 16.21/16.42         (((k2_relat_1 @ X3) != (k1_xboole_0))
% 16.21/16.42          | ((k1_relat_1 @ X3) = (k1_xboole_0))
% 16.21/16.42          | ~ (v1_relat_1 @ X3))),
% 16.21/16.42      inference('cnf', [status(esa)], [t65_relat_1])).
% 16.21/16.42  thf('32', plain,
% 16.21/16.42      ((((k1_xboole_0) != (k1_xboole_0))
% 16.21/16.42        | ~ (v1_relat_1 @ (sk_C_2 @ sk_B @ sk_A))
% 16.21/16.42        | ((k1_relat_1 @ (sk_C_2 @ sk_B @ sk_A)) = (k1_xboole_0)))),
% 16.21/16.42      inference('sup-', [status(thm)], ['30', '31'])).
% 16.21/16.42  thf('33', plain,
% 16.21/16.42      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (sk_C_2 @ X11 @ X12))),
% 16.21/16.42      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 16.21/16.42  thf('34', plain,
% 16.21/16.42      (![X11 : $i, X12 : $i]: ((k1_relat_1 @ (sk_C_2 @ X11 @ X12)) = (X12))),
% 16.21/16.42      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 16.21/16.42  thf('35', plain,
% 16.21/16.42      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 16.21/16.42      inference('demod', [status(thm)], ['32', '33', '34'])).
% 16.21/16.42  thf('36', plain, (((sk_A) = (k1_xboole_0))),
% 16.21/16.42      inference('simplify', [status(thm)], ['35'])).
% 16.21/16.42  thf('37', plain, (((sk_A) != (k1_xboole_0))),
% 16.21/16.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 16.21/16.42  thf('38', plain, ($false),
% 16.21/16.42      inference('simplify_reflect-', [status(thm)], ['36', '37'])).
% 16.21/16.42  
% 16.21/16.42  % SZS output end Refutation
% 16.21/16.42  
% 16.21/16.42  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
