%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FdFWIzqwMD

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:00 EST 2020

% Result     : Theorem 5.77s
% Output     : Refutation 5.84s
% Verified   : 
% Statistics : Number of formulae       :   72 (  81 expanded)
%              Number of leaves         :   32 (  37 expanded)
%              Depth                    :   14
%              Number of atoms          :  601 ( 742 expanded)
%              Number of equality atoms :   59 (  70 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(l44_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A
         != ( k1_tarski @ B ) )
        & ( A != k1_xboole_0 )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( C != B ) ) ) )).

thf('0',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_C_1 @ X11 @ X10 ) @ X10 )
      | ( X10
        = ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf(t204_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ) )).

thf('1',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X30 @ ( k11_relat_1 @ X31 @ X32 ) )
      | ( r2_hidden @ ( k4_tarski @ X32 @ X30 ) @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t204_relat_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_C_1 @ X2 @ ( k11_relat_1 @ X1 @ X0 ) ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X33 @ X35 ) @ X34 )
      | ( X35
        = ( k1_funct_1 @ X34 @ X33 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = ( k1_tarski @ X2 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( sk_C_1 @ X2 @ ( k11_relat_1 @ X0 @ X1 ) )
        = ( k1_funct_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( sk_C_1 @ X2 @ ( k11_relat_1 @ X0 @ X1 ) )
        = ( k1_funct_1 @ X0 @ X1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = ( k1_tarski @ X2 ) )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X10 = k1_xboole_0 )
      | ( ( sk_C_1 @ X11 @ X10 )
       != X11 )
      | ( X10
        = ( k1_tarski @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[l44_zfmisc_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_funct_1 @ X1 @ X0 )
       != X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ X2 ) )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X1 @ X0 ) ) )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf(t117_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
         => ( ( k11_relat_1 @ B @ A )
            = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t117_funct_1])).

thf('9',plain,(
    ( k11_relat_1 @ sk_B @ sk_A )
 != ( k1_tarski @ ( k1_funct_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != ( k11_relat_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( ( k11_relat_1 @ sk_B @ sk_A )
     != ( k11_relat_1 @ sk_B @ sk_A ) )
    | ( ( k11_relat_1 @ sk_B @ sk_A )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,
    ( ( k11_relat_1 @ sk_B @ sk_A )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['13'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('15',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k11_relat_1 @ X26 @ X27 )
        = ( k9_relat_1 @ X26 @ ( k1_tarski @ X27 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('16',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k9_relat_1 @ X28 @ X29 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X28 ) @ X29 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X1 ) @ ( k1_tarski @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ ( k1_tarski @ sk_A ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_B ) @ X0 )
      | ~ ( r2_hidden @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ~ ( r2_hidden @ sk_A @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('27',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('28',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('29',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( k2_enumset1 @ X7 @ X7 @ X8 @ X9 )
      = ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf(d2_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( ( F != D )
              & ( F != C )
              & ( F != B )
              & ( F != A ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ D @ C @ B @ A )
    <=> ( ( F != A )
        & ( F != B )
        & ( F != C )
        & ( F != D ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( E
        = ( k2_enumset1 @ A @ B @ C @ D ) )
    <=> ! [F: $i] :
          ( ( r2_hidden @ F @ E )
        <=> ~ ( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) )).

thf('30',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 @ X22 )
      | ( r2_hidden @ X18 @ X23 )
      | ( X23
       != ( k2_enumset1 @ X22 @ X21 @ X20 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('31',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( r2_hidden @ X18 @ ( k2_enumset1 @ X22 @ X21 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X3 @ ( k1_enumset1 @ X2 @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2 ) ) ),
    inference('sup+',[status(thm)],['29','31'])).

thf('33',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X13 != X12 )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('34',plain,(
    ! [X12: $i,X14: $i,X15: $i,X16: $i] :
      ~ ( zip_tseitin_0 @ X12 @ X14 @ X15 @ X16 @ X12 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r2_hidden @ X0 @ ( k1_enumset1 @ X0 @ X1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X1 @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['28','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','36'])).

thf('38',plain,(
    $false ),
    inference(demod,[status(thm)],['26','37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FdFWIzqwMD
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:27:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 5.77/6.00  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 5.77/6.00  % Solved by: fo/fo7.sh
% 5.77/6.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 5.77/6.00  % done 6805 iterations in 5.540s
% 5.77/6.00  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 5.77/6.00  % SZS output start Refutation
% 5.77/6.00  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 5.77/6.00  thf(sk_A_type, type, sk_A: $i).
% 5.77/6.00  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 5.77/6.00  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 5.77/6.00  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 5.77/6.00  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 5.77/6.00  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 5.77/6.00  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 5.77/6.00  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 5.77/6.00  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 5.77/6.00  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 5.77/6.00  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 5.77/6.00  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 5.77/6.00  thf(sk_B_type, type, sk_B: $i).
% 5.77/6.00  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 5.77/6.00  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 5.77/6.00  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 5.77/6.00  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 5.77/6.00  thf(l44_zfmisc_1, axiom,
% 5.77/6.00    (![A:$i,B:$i]:
% 5.77/6.00     ( ~( ( ( A ) != ( k1_tarski @ B ) ) & ( ( A ) != ( k1_xboole_0 ) ) & 
% 5.77/6.00          ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( ( C ) != ( B ) ) ) ) ) ) ))).
% 5.77/6.00  thf('0', plain,
% 5.77/6.00      (![X10 : $i, X11 : $i]:
% 5.77/6.00         (((X10) = (k1_xboole_0))
% 5.77/6.00          | (r2_hidden @ (sk_C_1 @ X11 @ X10) @ X10)
% 5.77/6.00          | ((X10) = (k1_tarski @ X11)))),
% 5.77/6.00      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 5.77/6.00  thf(t204_relat_1, axiom,
% 5.77/6.00    (![A:$i,B:$i,C:$i]:
% 5.77/6.00     ( ( v1_relat_1 @ C ) =>
% 5.77/6.00       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 5.77/6.00         ( r2_hidden @ B @ ( k11_relat_1 @ C @ A ) ) ) ))).
% 5.77/6.00  thf('1', plain,
% 5.77/6.00      (![X30 : $i, X31 : $i, X32 : $i]:
% 5.77/6.00         (~ (r2_hidden @ X30 @ (k11_relat_1 @ X31 @ X32))
% 5.77/6.00          | (r2_hidden @ (k4_tarski @ X32 @ X30) @ X31)
% 5.77/6.00          | ~ (v1_relat_1 @ X31))),
% 5.77/6.00      inference('cnf', [status(esa)], [t204_relat_1])).
% 5.77/6.00  thf('2', plain,
% 5.77/6.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.77/6.00         (((k11_relat_1 @ X1 @ X0) = (k1_tarski @ X2))
% 5.77/6.00          | ((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 5.77/6.00          | ~ (v1_relat_1 @ X1)
% 5.77/6.00          | (r2_hidden @ 
% 5.77/6.00             (k4_tarski @ X0 @ (sk_C_1 @ X2 @ (k11_relat_1 @ X1 @ X0))) @ X1))),
% 5.77/6.00      inference('sup-', [status(thm)], ['0', '1'])).
% 5.77/6.00  thf(t8_funct_1, axiom,
% 5.77/6.00    (![A:$i,B:$i,C:$i]:
% 5.77/6.00     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 5.77/6.00       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 5.77/6.00         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 5.77/6.00           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 5.77/6.00  thf('3', plain,
% 5.77/6.00      (![X33 : $i, X34 : $i, X35 : $i]:
% 5.77/6.00         (~ (r2_hidden @ (k4_tarski @ X33 @ X35) @ X34)
% 5.77/6.00          | ((X35) = (k1_funct_1 @ X34 @ X33))
% 5.77/6.00          | ~ (v1_funct_1 @ X34)
% 5.77/6.00          | ~ (v1_relat_1 @ X34))),
% 5.77/6.00      inference('cnf', [status(esa)], [t8_funct_1])).
% 5.77/6.00  thf('4', plain,
% 5.77/6.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.77/6.00         (~ (v1_relat_1 @ X0)
% 5.77/6.00          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 5.77/6.00          | ((k11_relat_1 @ X0 @ X1) = (k1_tarski @ X2))
% 5.77/6.00          | ~ (v1_relat_1 @ X0)
% 5.77/6.00          | ~ (v1_funct_1 @ X0)
% 5.77/6.00          | ((sk_C_1 @ X2 @ (k11_relat_1 @ X0 @ X1)) = (k1_funct_1 @ X0 @ X1)))),
% 5.77/6.00      inference('sup-', [status(thm)], ['2', '3'])).
% 5.77/6.00  thf('5', plain,
% 5.77/6.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.77/6.00         (((sk_C_1 @ X2 @ (k11_relat_1 @ X0 @ X1)) = (k1_funct_1 @ X0 @ X1))
% 5.77/6.00          | ~ (v1_funct_1 @ X0)
% 5.77/6.00          | ((k11_relat_1 @ X0 @ X1) = (k1_tarski @ X2))
% 5.77/6.00          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 5.77/6.00          | ~ (v1_relat_1 @ X0))),
% 5.77/6.00      inference('simplify', [status(thm)], ['4'])).
% 5.77/6.00  thf('6', plain,
% 5.77/6.00      (![X10 : $i, X11 : $i]:
% 5.77/6.00         (((X10) = (k1_xboole_0))
% 5.77/6.00          | ((sk_C_1 @ X11 @ X10) != (X11))
% 5.77/6.00          | ((X10) = (k1_tarski @ X11)))),
% 5.77/6.00      inference('cnf', [status(esa)], [l44_zfmisc_1])).
% 5.77/6.00  thf('7', plain,
% 5.77/6.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.77/6.00         (((k1_funct_1 @ X1 @ X0) != (X2))
% 5.77/6.00          | ~ (v1_relat_1 @ X1)
% 5.77/6.00          | ((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 5.77/6.00          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ X2))
% 5.77/6.00          | ~ (v1_funct_1 @ X1)
% 5.77/6.00          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ X2))
% 5.77/6.00          | ((k11_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 5.77/6.00      inference('sup-', [status(thm)], ['5', '6'])).
% 5.77/6.00  thf('8', plain,
% 5.77/6.00      (![X0 : $i, X1 : $i]:
% 5.77/6.00         (~ (v1_funct_1 @ X1)
% 5.77/6.00          | ((k11_relat_1 @ X1 @ X0) = (k1_tarski @ (k1_funct_1 @ X1 @ X0)))
% 5.77/6.00          | ((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 5.77/6.00          | ~ (v1_relat_1 @ X1))),
% 5.77/6.00      inference('simplify', [status(thm)], ['7'])).
% 5.77/6.00  thf(t117_funct_1, conjecture,
% 5.77/6.00    (![A:$i,B:$i]:
% 5.77/6.00     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 5.77/6.00       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 5.77/6.00         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 5.77/6.00  thf(zf_stmt_0, negated_conjecture,
% 5.77/6.00    (~( ![A:$i,B:$i]:
% 5.77/6.00        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 5.77/6.00          ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 5.77/6.00            ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )),
% 5.77/6.00    inference('cnf.neg', [status(esa)], [t117_funct_1])).
% 5.77/6.00  thf('9', plain,
% 5.77/6.00      (((k11_relat_1 @ sk_B @ sk_A) != (k1_tarski @ (k1_funct_1 @ sk_B @ sk_A)))),
% 5.77/6.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.77/6.00  thf('10', plain,
% 5.77/6.00      ((((k11_relat_1 @ sk_B @ sk_A) != (k11_relat_1 @ sk_B @ sk_A))
% 5.77/6.00        | ~ (v1_relat_1 @ sk_B)
% 5.77/6.00        | ((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))
% 5.77/6.00        | ~ (v1_funct_1 @ sk_B))),
% 5.77/6.00      inference('sup-', [status(thm)], ['8', '9'])).
% 5.77/6.00  thf('11', plain, ((v1_relat_1 @ sk_B)),
% 5.77/6.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.77/6.00  thf('12', plain, ((v1_funct_1 @ sk_B)),
% 5.77/6.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.77/6.00  thf('13', plain,
% 5.77/6.00      ((((k11_relat_1 @ sk_B @ sk_A) != (k11_relat_1 @ sk_B @ sk_A))
% 5.77/6.00        | ((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0)))),
% 5.77/6.00      inference('demod', [status(thm)], ['10', '11', '12'])).
% 5.77/6.00  thf('14', plain, (((k11_relat_1 @ sk_B @ sk_A) = (k1_xboole_0))),
% 5.77/6.00      inference('simplify', [status(thm)], ['13'])).
% 5.77/6.00  thf(d16_relat_1, axiom,
% 5.77/6.00    (![A:$i]:
% 5.77/6.00     ( ( v1_relat_1 @ A ) =>
% 5.77/6.00       ( ![B:$i]:
% 5.77/6.00         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 5.77/6.00  thf('15', plain,
% 5.77/6.00      (![X26 : $i, X27 : $i]:
% 5.77/6.00         (((k11_relat_1 @ X26 @ X27) = (k9_relat_1 @ X26 @ (k1_tarski @ X27)))
% 5.77/6.00          | ~ (v1_relat_1 @ X26))),
% 5.77/6.00      inference('cnf', [status(esa)], [d16_relat_1])).
% 5.77/6.00  thf(t151_relat_1, axiom,
% 5.77/6.00    (![A:$i,B:$i]:
% 5.77/6.00     ( ( v1_relat_1 @ B ) =>
% 5.77/6.00       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 5.77/6.00         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 5.77/6.00  thf('16', plain,
% 5.77/6.00      (![X28 : $i, X29 : $i]:
% 5.77/6.00         (((k9_relat_1 @ X28 @ X29) != (k1_xboole_0))
% 5.77/6.00          | (r1_xboole_0 @ (k1_relat_1 @ X28) @ X29)
% 5.77/6.00          | ~ (v1_relat_1 @ X28))),
% 5.77/6.00      inference('cnf', [status(esa)], [t151_relat_1])).
% 5.77/6.00  thf('17', plain,
% 5.77/6.00      (![X0 : $i, X1 : $i]:
% 5.77/6.00         (((k11_relat_1 @ X1 @ X0) != (k1_xboole_0))
% 5.77/6.00          | ~ (v1_relat_1 @ X1)
% 5.77/6.00          | ~ (v1_relat_1 @ X1)
% 5.77/6.00          | (r1_xboole_0 @ (k1_relat_1 @ X1) @ (k1_tarski @ X0)))),
% 5.77/6.00      inference('sup-', [status(thm)], ['15', '16'])).
% 5.77/6.00  thf('18', plain,
% 5.77/6.00      (![X0 : $i, X1 : $i]:
% 5.77/6.00         ((r1_xboole_0 @ (k1_relat_1 @ X1) @ (k1_tarski @ X0))
% 5.77/6.00          | ~ (v1_relat_1 @ X1)
% 5.77/6.00          | ((k11_relat_1 @ X1 @ X0) != (k1_xboole_0)))),
% 5.77/6.00      inference('simplify', [status(thm)], ['17'])).
% 5.77/6.00  thf('19', plain,
% 5.77/6.00      ((((k1_xboole_0) != (k1_xboole_0))
% 5.77/6.00        | ~ (v1_relat_1 @ sk_B)
% 5.77/6.00        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A)))),
% 5.77/6.00      inference('sup-', [status(thm)], ['14', '18'])).
% 5.77/6.00  thf('20', plain, ((v1_relat_1 @ sk_B)),
% 5.77/6.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.77/6.00  thf('21', plain,
% 5.77/6.00      ((((k1_xboole_0) != (k1_xboole_0))
% 5.77/6.00        | (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A)))),
% 5.77/6.00      inference('demod', [status(thm)], ['19', '20'])).
% 5.77/6.00  thf('22', plain, ((r1_xboole_0 @ (k1_relat_1 @ sk_B) @ (k1_tarski @ sk_A))),
% 5.77/6.00      inference('simplify', [status(thm)], ['21'])).
% 5.77/6.00  thf('23', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_B))),
% 5.77/6.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 5.77/6.00  thf(t3_xboole_0, axiom,
% 5.77/6.00    (![A:$i,B:$i]:
% 5.77/6.00     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 5.77/6.00            ( r1_xboole_0 @ A @ B ) ) ) & 
% 5.77/6.00       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 5.77/6.00            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 5.77/6.00  thf('24', plain,
% 5.77/6.00      (![X0 : $i, X2 : $i, X3 : $i]:
% 5.77/6.00         (~ (r2_hidden @ X2 @ X0)
% 5.77/6.00          | ~ (r2_hidden @ X2 @ X3)
% 5.77/6.00          | ~ (r1_xboole_0 @ X0 @ X3))),
% 5.77/6.00      inference('cnf', [status(esa)], [t3_xboole_0])).
% 5.77/6.00  thf('25', plain,
% 5.77/6.00      (![X0 : $i]:
% 5.77/6.00         (~ (r1_xboole_0 @ (k1_relat_1 @ sk_B) @ X0)
% 5.77/6.00          | ~ (r2_hidden @ sk_A @ X0))),
% 5.77/6.00      inference('sup-', [status(thm)], ['23', '24'])).
% 5.77/6.00  thf('26', plain, (~ (r2_hidden @ sk_A @ (k1_tarski @ sk_A))),
% 5.77/6.00      inference('sup-', [status(thm)], ['22', '25'])).
% 5.77/6.00  thf(t69_enumset1, axiom,
% 5.77/6.00    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 5.77/6.00  thf('27', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 5.77/6.00      inference('cnf', [status(esa)], [t69_enumset1])).
% 5.77/6.00  thf(t70_enumset1, axiom,
% 5.77/6.00    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 5.77/6.00  thf('28', plain,
% 5.77/6.00      (![X5 : $i, X6 : $i]:
% 5.77/6.00         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 5.84/6.00      inference('cnf', [status(esa)], [t70_enumset1])).
% 5.84/6.00  thf(t71_enumset1, axiom,
% 5.84/6.00    (![A:$i,B:$i,C:$i]:
% 5.84/6.00     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 5.84/6.00  thf('29', plain,
% 5.84/6.00      (![X7 : $i, X8 : $i, X9 : $i]:
% 5.84/6.00         ((k2_enumset1 @ X7 @ X7 @ X8 @ X9) = (k1_enumset1 @ X7 @ X8 @ X9))),
% 5.84/6.00      inference('cnf', [status(esa)], [t71_enumset1])).
% 5.84/6.00  thf(d2_enumset1, axiom,
% 5.84/6.00    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 5.84/6.00     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 5.84/6.00       ( ![F:$i]:
% 5.84/6.00         ( ( r2_hidden @ F @ E ) <=>
% 5.84/6.00           ( ~( ( ( F ) != ( D ) ) & ( ( F ) != ( C ) ) & ( ( F ) != ( B ) ) & 
% 5.84/6.00                ( ( F ) != ( A ) ) ) ) ) ) ))).
% 5.84/6.00  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 5.84/6.00  thf(zf_stmt_2, axiom,
% 5.84/6.00    (![F:$i,D:$i,C:$i,B:$i,A:$i]:
% 5.84/6.00     ( ( zip_tseitin_0 @ F @ D @ C @ B @ A ) <=>
% 5.84/6.00       ( ( ( F ) != ( A ) ) & ( ( F ) != ( B ) ) & ( ( F ) != ( C ) ) & 
% 5.84/6.00         ( ( F ) != ( D ) ) ) ))).
% 5.84/6.00  thf(zf_stmt_3, axiom,
% 5.84/6.00    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 5.84/6.00     ( ( ( E ) = ( k2_enumset1 @ A @ B @ C @ D ) ) <=>
% 5.84/6.00       ( ![F:$i]:
% 5.84/6.00         ( ( r2_hidden @ F @ E ) <=> ( ~( zip_tseitin_0 @ F @ D @ C @ B @ A ) ) ) ) ))).
% 5.84/6.00  thf('30', plain,
% 5.84/6.00      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 5.84/6.00         ((zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 @ X22)
% 5.84/6.00          | (r2_hidden @ X18 @ X23)
% 5.84/6.00          | ((X23) != (k2_enumset1 @ X22 @ X21 @ X20 @ X19)))),
% 5.84/6.00      inference('cnf', [status(esa)], [zf_stmt_3])).
% 5.84/6.00  thf('31', plain,
% 5.84/6.00      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 5.84/6.00         ((r2_hidden @ X18 @ (k2_enumset1 @ X22 @ X21 @ X20 @ X19))
% 5.84/6.00          | (zip_tseitin_0 @ X18 @ X19 @ X20 @ X21 @ X22))),
% 5.84/6.00      inference('simplify', [status(thm)], ['30'])).
% 5.84/6.00  thf('32', plain,
% 5.84/6.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 5.84/6.00         ((r2_hidden @ X3 @ (k1_enumset1 @ X2 @ X1 @ X0))
% 5.84/6.00          | (zip_tseitin_0 @ X3 @ X0 @ X1 @ X2 @ X2))),
% 5.84/6.00      inference('sup+', [status(thm)], ['29', '31'])).
% 5.84/6.00  thf('33', plain,
% 5.84/6.00      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 5.84/6.00         (((X13) != (X12)) | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X16 @ X12))),
% 5.84/6.00      inference('cnf', [status(esa)], [zf_stmt_2])).
% 5.84/6.00  thf('34', plain,
% 5.84/6.00      (![X12 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 5.84/6.00         ~ (zip_tseitin_0 @ X12 @ X14 @ X15 @ X16 @ X12)),
% 5.84/6.00      inference('simplify', [status(thm)], ['33'])).
% 5.84/6.00  thf('35', plain,
% 5.84/6.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 5.84/6.00         (r2_hidden @ X0 @ (k1_enumset1 @ X0 @ X1 @ X2))),
% 5.84/6.00      inference('sup-', [status(thm)], ['32', '34'])).
% 5.84/6.00  thf('36', plain,
% 5.84/6.00      (![X0 : $i, X1 : $i]: (r2_hidden @ X1 @ (k2_tarski @ X1 @ X0))),
% 5.84/6.00      inference('sup+', [status(thm)], ['28', '35'])).
% 5.84/6.00  thf('37', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 5.84/6.00      inference('sup+', [status(thm)], ['27', '36'])).
% 5.84/6.00  thf('38', plain, ($false), inference('demod', [status(thm)], ['26', '37'])).
% 5.84/6.00  
% 5.84/6.00  % SZS output end Refutation
% 5.84/6.00  
% 5.84/6.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
