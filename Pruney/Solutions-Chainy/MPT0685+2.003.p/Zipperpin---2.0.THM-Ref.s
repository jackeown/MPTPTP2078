%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xg6qvH7Mzb

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   64 (  73 expanded)
%              Number of leaves         :   25 (  33 expanded)
%              Depth                    :   16
%              Number of atoms          :  588 ( 723 expanded)
%              Number of equality atoms :   45 (  60 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(t182_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) )).

thf('0',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) )
        = ( k10_relat_1 @ X13 @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf(s3_funct_1__e9_44_1__funct_1,axiom,(
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
    ! [X21: $i] :
      ( ( k1_relat_1 @ ( sk_B_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

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

thf('2',plain,(
    ! [X19: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf(t198_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( ( k1_relat_1 @ A )
                  = ( k1_relat_1 @ B ) )
               => ( ( k1_relat_1 @ ( k5_relat_1 @ C @ A ) )
                  = ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( ( k1_relat_1 @ X15 )
       != ( k1_relat_1 @ X14 ) )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X16 @ X15 ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X16 @ X14 ) ) )
      | ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t198_relat_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X2 @ ( sk_B @ X0 ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( sk_B @ X19 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
       != ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X2 @ ( sk_B @ X0 ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X2 @ ( sk_B @ ( k1_relat_1 @ X1 ) ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X2 @ X1 ) ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( sk_B @ X0 ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( sk_B_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( sk_B_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['1','7'])).

thf('9',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( sk_B_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( sk_B @ X0 ) ) )
        = ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( sk_B_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( sk_B @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ ( k1_relat_1 @ ( sk_B_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( sk_B_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','10'])).

thf('12',plain,(
    ! [X21: $i] :
      ( ( k1_relat_1 @ ( sk_B_1 @ X21 ) )
      = X21 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('13',plain,(
    ! [X21: $i] :
      ( v1_relat_1 @ ( sk_B_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e9_44_1__funct_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( sk_B @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X1 @ ( sk_B @ X0 ) ) )
        = ( k10_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t112_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A )
            = ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) )).

thf('16',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ( ( k7_relat_1 @ ( k5_relat_1 @ X10 @ X9 ) @ X11 )
        = ( k5_relat_1 @ ( k7_relat_1 @ X10 @ X11 ) @ X9 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t112_relat_1])).

thf(dt_k5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_relat_1 @ B ) )
     => ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 )
      | ( v1_relat_1 @ ( k5_relat_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_relat_1])).

thf('18',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ X13 @ X12 ) )
        = ( k10_relat_1 @ X13 @ ( k1_relat_1 @ X12 ) ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t182_relat_1])).

thf(t90_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('19',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ X17 @ X18 ) )
        = ( k3_xboole_0 @ ( k1_relat_1 @ X17 ) @ X18 ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t90_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k7_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ X2 ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X1 @ ( k1_relat_1 @ X0 ) ) @ X2 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X2 @ ( k1_relat_1 @ X0 ) ) @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['16','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 )
      | ( ( k1_relat_1 @ ( k5_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X2 @ ( k1_relat_1 @ X0 ) ) @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X2 @ ( k1_relat_1 @ ( sk_B @ X0 ) ) ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['15','24'])).

thf('26',plain,(
    ! [X19: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X19 ) )
      = X19 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('27',plain,(
    ! [X19: $i] :
      ( v1_relat_1 @ ( sk_B @ X19 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X2 @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('29',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X2 @ X0 ) @ X1 ) ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf(commutativity_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ B )
      = ( k3_xboole_0 @ B @ A ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k3_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ ( k10_relat_1 @ X2 @ X0 ) )
        = ( k10_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(t139_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
        = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t139_funct_1])).

thf('33',plain,(
    ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B_2 )
 != ( k3_xboole_0 @ sk_A @ ( k10_relat_1 @ sk_C @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B_2 )
     != ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B_2 ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B_2 )
 != ( k10_relat_1 @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_B_2 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    $false ),
    inference(simplify,[status(thm)],['36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.xg6qvH7Mzb
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:15:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.21/0.52  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.52  % Solved by: fo/fo7.sh
% 0.21/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.52  % done 92 iterations in 0.071s
% 0.21/0.52  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.52  % SZS output start Refutation
% 0.21/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.52  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.21/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.21/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.52  thf(sk_B_1_type, type, sk_B_1: $i > $i).
% 0.21/0.52  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.52  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.21/0.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.52  thf(t182_relat_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( v1_relat_1 @ B ) =>
% 0.21/0.52           ( ( k1_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.21/0.52             ( k10_relat_1 @ A @ ( k1_relat_1 @ B ) ) ) ) ) ))).
% 0.21/0.52  thf('0', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X12)
% 0.21/0.52          | ((k1_relat_1 @ (k5_relat_1 @ X13 @ X12))
% 0.21/0.52              = (k10_relat_1 @ X13 @ (k1_relat_1 @ X12)))
% 0.21/0.52          | ~ (v1_relat_1 @ X13))),
% 0.21/0.52      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.21/0.52  thf(s3_funct_1__e9_44_1__funct_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ?[B:$i]:
% 0.21/0.52       ( ( ![C:$i]:
% 0.21/0.52           ( ( r2_hidden @ C @ A ) =>
% 0.21/0.52             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.52         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.21/0.52         ( v1_relat_1 @ B ) ) ))).
% 0.21/0.52  thf('1', plain, (![X21 : $i]: ((k1_relat_1 @ (sk_B_1 @ X21)) = (X21))),
% 0.21/0.52      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 0.21/0.52  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ?[B:$i]:
% 0.21/0.52       ( ( ![C:$i]:
% 0.21/0.52           ( ( r2_hidden @ C @ A ) =>
% 0.21/0.52             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.52         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.21/0.52         ( v1_relat_1 @ B ) ) ))).
% 0.21/0.52  thf('2', plain, (![X19 : $i]: ((k1_relat_1 @ (sk_B @ X19)) = (X19))),
% 0.21/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.52  thf(t198_relat_1, axiom,
% 0.21/0.52    (![A:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ A ) =>
% 0.21/0.52       ( ![B:$i]:
% 0.21/0.52         ( ( v1_relat_1 @ B ) =>
% 0.21/0.52           ( ![C:$i]:
% 0.21/0.52             ( ( v1_relat_1 @ C ) =>
% 0.21/0.52               ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) =>
% 0.21/0.52                 ( ( k1_relat_1 @ ( k5_relat_1 @ C @ A ) ) =
% 0.21/0.52                   ( k1_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) ) ) ))).
% 0.21/0.52  thf('3', plain,
% 0.21/0.52      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X14)
% 0.21/0.52          | ((k1_relat_1 @ X15) != (k1_relat_1 @ X14))
% 0.21/0.52          | ((k1_relat_1 @ (k5_relat_1 @ X16 @ X15))
% 0.21/0.52              = (k1_relat_1 @ (k5_relat_1 @ X16 @ X14)))
% 0.21/0.52          | ~ (v1_relat_1 @ X16)
% 0.21/0.52          | ~ (v1_relat_1 @ X15))),
% 0.21/0.52      inference('cnf', [status(esa)], [t198_relat_1])).
% 0.21/0.52  thf('4', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (((X0) != (k1_relat_1 @ X1))
% 0.21/0.52          | ~ (v1_relat_1 @ (sk_B @ X0))
% 0.21/0.52          | ~ (v1_relat_1 @ X2)
% 0.21/0.52          | ((k1_relat_1 @ (k5_relat_1 @ X2 @ (sk_B @ X0)))
% 0.21/0.52              = (k1_relat_1 @ (k5_relat_1 @ X2 @ X1)))
% 0.21/0.52          | ~ (v1_relat_1 @ X1))),
% 0.21/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.52  thf('5', plain, (![X19 : $i]: (v1_relat_1 @ (sk_B @ X19))),
% 0.21/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.52  thf('6', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (((X0) != (k1_relat_1 @ X1))
% 0.21/0.52          | ~ (v1_relat_1 @ X2)
% 0.21/0.52          | ((k1_relat_1 @ (k5_relat_1 @ X2 @ (sk_B @ X0)))
% 0.21/0.52              = (k1_relat_1 @ (k5_relat_1 @ X2 @ X1)))
% 0.21/0.52          | ~ (v1_relat_1 @ X1))),
% 0.21/0.52      inference('demod', [status(thm)], ['4', '5'])).
% 0.21/0.52  thf('7', plain,
% 0.21/0.52      (![X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X1)
% 0.21/0.52          | ((k1_relat_1 @ (k5_relat_1 @ X2 @ (sk_B @ (k1_relat_1 @ X1))))
% 0.21/0.52              = (k1_relat_1 @ (k5_relat_1 @ X2 @ X1)))
% 0.21/0.52          | ~ (v1_relat_1 @ X2))),
% 0.21/0.52      inference('simplify', [status(thm)], ['6'])).
% 0.21/0.52  thf('8', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (sk_B @ X0)))
% 0.21/0.52            = (k1_relat_1 @ (k5_relat_1 @ X1 @ (sk_B_1 @ X0))))
% 0.21/0.52          | ~ (v1_relat_1 @ X1)
% 0.21/0.52          | ~ (v1_relat_1 @ (sk_B_1 @ X0)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['1', '7'])).
% 0.21/0.52  thf('9', plain, (![X21 : $i]: (v1_relat_1 @ (sk_B_1 @ X21))),
% 0.21/0.52      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 0.21/0.52  thf('10', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (sk_B @ X0)))
% 0.21/0.52            = (k1_relat_1 @ (k5_relat_1 @ X1 @ (sk_B_1 @ X0))))
% 0.21/0.52          | ~ (v1_relat_1 @ X1))),
% 0.21/0.52      inference('demod', [status(thm)], ['8', '9'])).
% 0.21/0.52  thf('11', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (sk_B @ X0)))
% 0.21/0.52            = (k10_relat_1 @ X1 @ (k1_relat_1 @ (sk_B_1 @ X0))))
% 0.21/0.52          | ~ (v1_relat_1 @ X1)
% 0.21/0.52          | ~ (v1_relat_1 @ (sk_B_1 @ X0))
% 0.21/0.52          | ~ (v1_relat_1 @ X1))),
% 0.21/0.52      inference('sup+', [status(thm)], ['0', '10'])).
% 0.21/0.52  thf('12', plain, (![X21 : $i]: ((k1_relat_1 @ (sk_B_1 @ X21)) = (X21))),
% 0.21/0.52      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 0.21/0.52  thf('13', plain, (![X21 : $i]: (v1_relat_1 @ (sk_B_1 @ X21))),
% 0.21/0.52      inference('cnf', [status(esa)], [s3_funct_1__e9_44_1__funct_1])).
% 0.21/0.52  thf('14', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (((k1_relat_1 @ (k5_relat_1 @ X1 @ (sk_B @ X0)))
% 0.21/0.52            = (k10_relat_1 @ X1 @ X0))
% 0.21/0.52          | ~ (v1_relat_1 @ X1)
% 0.21/0.52          | ~ (v1_relat_1 @ X1))),
% 0.21/0.52      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.21/0.52  thf('15', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X1)
% 0.21/0.52          | ((k1_relat_1 @ (k5_relat_1 @ X1 @ (sk_B @ X0)))
% 0.21/0.52              = (k10_relat_1 @ X1 @ X0)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['14'])).
% 0.21/0.52  thf(t112_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ![C:$i]:
% 0.21/0.52         ( ( v1_relat_1 @ C ) =>
% 0.21/0.52           ( ( k7_relat_1 @ ( k5_relat_1 @ B @ C ) @ A ) =
% 0.21/0.52             ( k5_relat_1 @ ( k7_relat_1 @ B @ A ) @ C ) ) ) ) ))).
% 0.21/0.52  thf('16', plain,
% 0.21/0.52      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X9)
% 0.21/0.52          | ((k7_relat_1 @ (k5_relat_1 @ X10 @ X9) @ X11)
% 0.21/0.52              = (k5_relat_1 @ (k7_relat_1 @ X10 @ X11) @ X9))
% 0.21/0.52          | ~ (v1_relat_1 @ X10))),
% 0.21/0.52      inference('cnf', [status(esa)], [t112_relat_1])).
% 0.21/0.52  thf(dt_k5_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( ( v1_relat_1 @ A ) & ( v1_relat_1 @ B ) ) =>
% 0.21/0.52       ( v1_relat_1 @ ( k5_relat_1 @ A @ B ) ) ))).
% 0.21/0.52  thf('17', plain,
% 0.21/0.52      (![X5 : $i, X6 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X5)
% 0.21/0.52          | ~ (v1_relat_1 @ X6)
% 0.21/0.52          | (v1_relat_1 @ (k5_relat_1 @ X5 @ X6)))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k5_relat_1])).
% 0.21/0.52  thf('18', plain,
% 0.21/0.52      (![X12 : $i, X13 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X12)
% 0.21/0.52          | ((k1_relat_1 @ (k5_relat_1 @ X13 @ X12))
% 0.21/0.52              = (k10_relat_1 @ X13 @ (k1_relat_1 @ X12)))
% 0.21/0.52          | ~ (v1_relat_1 @ X13))),
% 0.21/0.52      inference('cnf', [status(esa)], [t182_relat_1])).
% 0.21/0.52  thf(t90_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ B ) =>
% 0.21/0.52       ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) =
% 0.21/0.52         ( k3_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.52  thf('19', plain,
% 0.21/0.52      (![X17 : $i, X18 : $i]:
% 0.21/0.52         (((k1_relat_1 @ (k7_relat_1 @ X17 @ X18))
% 0.21/0.52            = (k3_xboole_0 @ (k1_relat_1 @ X17) @ X18))
% 0.21/0.52          | ~ (v1_relat_1 @ X17))),
% 0.21/0.52      inference('cnf', [status(esa)], [t90_relat_1])).
% 0.21/0.52  thf('20', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (((k1_relat_1 @ (k7_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2))
% 0.21/0.52            = (k3_xboole_0 @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ X2))
% 0.21/0.52          | ~ (v1_relat_1 @ X1)
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['18', '19'])).
% 0.21/0.52  thf('21', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ X1)
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ X1)
% 0.21/0.52          | ((k1_relat_1 @ (k7_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2))
% 0.21/0.52              = (k3_xboole_0 @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ X2)))),
% 0.21/0.52      inference('sup-', [status(thm)], ['17', '20'])).
% 0.21/0.52  thf('22', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (((k1_relat_1 @ (k7_relat_1 @ (k5_relat_1 @ X1 @ X0) @ X2))
% 0.21/0.52            = (k3_xboole_0 @ (k10_relat_1 @ X1 @ (k1_relat_1 @ X0)) @ X2))
% 0.21/0.52          | ~ (v1_relat_1 @ X1)
% 0.21/0.52          | ~ (v1_relat_1 @ X0))),
% 0.21/0.52      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.52  thf('23', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 0.21/0.52            = (k3_xboole_0 @ (k10_relat_1 @ X2 @ (k1_relat_1 @ X0)) @ X1))
% 0.21/0.52          | ~ (v1_relat_1 @ X2)
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ X2))),
% 0.21/0.52      inference('sup+', [status(thm)], ['16', '22'])).
% 0.21/0.52  thf('24', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X0)
% 0.21/0.52          | ~ (v1_relat_1 @ X2)
% 0.21/0.52          | ((k1_relat_1 @ (k5_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 0.21/0.52              = (k3_xboole_0 @ (k10_relat_1 @ X2 @ (k1_relat_1 @ X0)) @ X1)))),
% 0.21/0.52      inference('simplify', [status(thm)], ['23'])).
% 0.21/0.52  thf('25', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (((k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)
% 0.21/0.52            = (k3_xboole_0 @ (k10_relat_1 @ X2 @ (k1_relat_1 @ (sk_B @ X0))) @ 
% 0.21/0.52               X1))
% 0.21/0.52          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X1))
% 0.21/0.52          | ~ (v1_relat_1 @ X2)
% 0.21/0.52          | ~ (v1_relat_1 @ (sk_B @ X0)))),
% 0.21/0.52      inference('sup+', [status(thm)], ['15', '24'])).
% 0.21/0.52  thf('26', plain, (![X19 : $i]: ((k1_relat_1 @ (sk_B @ X19)) = (X19))),
% 0.21/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.52  thf('27', plain, (![X19 : $i]: (v1_relat_1 @ (sk_B @ X19))),
% 0.21/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.21/0.52  thf('28', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (((k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)
% 0.21/0.52            = (k3_xboole_0 @ (k10_relat_1 @ X2 @ X0) @ X1))
% 0.21/0.52          | ~ (v1_relat_1 @ (k7_relat_1 @ X2 @ X1))
% 0.21/0.52          | ~ (v1_relat_1 @ X2))),
% 0.21/0.52      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.21/0.52  thf(dt_k7_relat_1, axiom,
% 0.21/0.52    (![A:$i,B:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.21/0.52  thf('29', plain,
% 0.21/0.52      (![X7 : $i, X8 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X7) | (v1_relat_1 @ (k7_relat_1 @ X7 @ X8)))),
% 0.21/0.52      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.21/0.52  thf('30', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (~ (v1_relat_1 @ X2)
% 0.21/0.52          | ((k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0)
% 0.21/0.52              = (k3_xboole_0 @ (k10_relat_1 @ X2 @ X0) @ X1)))),
% 0.21/0.52      inference('clc', [status(thm)], ['28', '29'])).
% 0.21/0.52  thf(commutativity_k3_xboole_0, axiom,
% 0.21/0.52    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ B ) = ( k3_xboole_0 @ B @ A ) ))).
% 0.21/0.52  thf('31', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i]: ((k3_xboole_0 @ X1 @ X0) = (k3_xboole_0 @ X0 @ X1))),
% 0.21/0.52      inference('cnf', [status(esa)], [commutativity_k3_xboole_0])).
% 0.21/0.52  thf('32', plain,
% 0.21/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.52         (((k3_xboole_0 @ X1 @ (k10_relat_1 @ X2 @ X0))
% 0.21/0.52            = (k10_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0))
% 0.21/0.52          | ~ (v1_relat_1 @ X2))),
% 0.21/0.52      inference('sup+', [status(thm)], ['30', '31'])).
% 0.21/0.52  thf(t139_funct_1, conjecture,
% 0.21/0.52    (![A:$i,B:$i,C:$i]:
% 0.21/0.52     ( ( v1_relat_1 @ C ) =>
% 0.21/0.52       ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.21/0.52         ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.21/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.52        ( ( v1_relat_1 @ C ) =>
% 0.21/0.52          ( ( k10_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) =
% 0.21/0.52            ( k3_xboole_0 @ A @ ( k10_relat_1 @ C @ B ) ) ) ) )),
% 0.21/0.52    inference('cnf.neg', [status(esa)], [t139_funct_1])).
% 0.21/0.52  thf('33', plain,
% 0.21/0.52      (((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B_2)
% 0.21/0.52         != (k3_xboole_0 @ sk_A @ (k10_relat_1 @ sk_C @ sk_B_2)))),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('34', plain,
% 0.21/0.52      ((((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B_2)
% 0.21/0.52          != (k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B_2))
% 0.21/0.52        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.21/0.52  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.52  thf('36', plain,
% 0.21/0.52      (((k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B_2)
% 0.21/0.52         != (k10_relat_1 @ (k7_relat_1 @ sk_C @ sk_A) @ sk_B_2))),
% 0.21/0.52      inference('demod', [status(thm)], ['34', '35'])).
% 0.21/0.52  thf('37', plain, ($false), inference('simplify', [status(thm)], ['36'])).
% 0.21/0.52  
% 0.21/0.52  % SZS output end Refutation
% 0.21/0.52  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
