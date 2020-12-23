%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.U4SZkFqojo

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:09 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 (  88 expanded)
%              Number of leaves         :   20 (  36 expanded)
%              Depth                    :   14
%              Number of atoms          :  492 ( 787 expanded)
%              Number of equality atoms :   21 (  31 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(t137_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('0',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k10_relat_1 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X12 @ X13 ) @ ( k10_relat_1 @ X12 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t137_funct_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ( k3_xboole_0 @ X7 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

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

thf('5',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t166_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ A @ D ) @ C )
            & ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('6',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k10_relat_1 @ X11 @ X9 ) )
      | ( r2_hidden @ ( sk_D @ X11 @ X9 @ X10 ) @ X9 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t166_relat_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('9',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X0 @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X1 @ X0 @ ( sk_C @ X2 @ ( k10_relat_1 @ X1 @ X0 ) ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ ( k10_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k10_relat_1 @ X0 @ k1_xboole_0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k3_xboole_0 @ ( k10_relat_1 @ X1 @ k1_xboole_0 ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ ( k3_xboole_0 @ k1_xboole_0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('19',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('20',plain,(
    ! [X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X5 @ X3 )
      | ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( r1_xboole_0 @ X3 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','26'])).

thf('28',plain,(
    ! [X1: $i] :
      ( ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf(t141_funct_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( r1_xboole_0 @ B @ C )
         => ( r1_xboole_0 @ ( k10_relat_1 @ A @ B ) @ ( k10_relat_1 @ A @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ! [B: $i,C: $i] :
            ( ( r1_xboole_0 @ B @ C )
           => ( r1_xboole_0 @ ( k10_relat_1 @ A @ B ) @ ( k10_relat_1 @ A @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t141_funct_1])).

thf('29',plain,(
    r1_xboole_0 @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('31',plain,
    ( ( k3_xboole_0 @ sk_B @ sk_C_1 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k10_relat_1 @ X12 @ ( k3_xboole_0 @ X13 @ X14 ) )
        = ( k3_xboole_0 @ ( k10_relat_1 @ X12 @ X13 ) @ ( k10_relat_1 @ X12 @ X14 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t137_funct_1])).

thf('33',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X2 )
      | ( ( k3_xboole_0 @ X0 @ X2 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k10_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ( r1_xboole_0 @ ( k10_relat_1 @ X2 @ X1 ) @ ( k10_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ k1_xboole_0 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k10_relat_1 @ X0 @ sk_B ) @ ( k10_relat_1 @ X0 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_xboole_0 @ ( k10_relat_1 @ X0 @ sk_B ) @ ( k10_relat_1 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['28','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k10_relat_1 @ X0 @ sk_B ) @ ( k10_relat_1 @ X0 @ sk_C_1 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ~ ( r1_xboole_0 @ ( k10_relat_1 @ sk_A @ sk_B ) @ ( k10_relat_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    $false ),
    inference(demod,[status(thm)],['39','40','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.U4SZkFqojo
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:58:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 57 iterations in 0.023s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.49  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.49  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.49  thf(t137_funct_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.49       ( ( k10_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 0.20/0.49         ( k3_xboole_0 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.20/0.49  thf('0', plain,
% 0.20/0.49      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.49         (((k10_relat_1 @ X12 @ (k3_xboole_0 @ X13 @ X14))
% 0.20/0.49            = (k3_xboole_0 @ (k10_relat_1 @ X12 @ X13) @ 
% 0.20/0.49               (k10_relat_1 @ X12 @ X14)))
% 0.20/0.49          | ~ (v1_funct_1 @ X12)
% 0.20/0.49          | ~ (v1_relat_1 @ X12))),
% 0.20/0.49      inference('cnf', [status(esa)], [t137_funct_1])).
% 0.20/0.49  thf(t2_boole, axiom,
% 0.20/0.49    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      (![X7 : $i]: ((k3_xboole_0 @ X7 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.49      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.49  thf(d7_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.20/0.49       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X0 : $i, X2 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k1_xboole_0) != (k1_xboole_0)) | (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf('4', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.20/0.49      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.49  thf(t3_xboole_0, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.20/0.49            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.49       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.49            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.49  thf(t166_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ C ) =>
% 0.20/0.49       ( ( r2_hidden @ A @ ( k10_relat_1 @ C @ B ) ) <=>
% 0.20/0.49         ( ?[D:$i]:
% 0.20/0.49           ( ( r2_hidden @ D @ B ) & 
% 0.20/0.49             ( r2_hidden @ ( k4_tarski @ A @ D ) @ C ) & 
% 0.20/0.49             ( r2_hidden @ D @ ( k2_relat_1 @ C ) ) ) ) ) ))).
% 0.20/0.49  thf('6', plain,
% 0.20/0.49      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X10 @ (k10_relat_1 @ X11 @ X9))
% 0.20/0.49          | (r2_hidden @ (sk_D @ X11 @ X9 @ X10) @ X9)
% 0.20/0.49          | ~ (v1_relat_1 @ X11))),
% 0.20/0.49      inference('cnf', [status(esa)], [t166_relat_1])).
% 0.20/0.49  thf('7', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ (k10_relat_1 @ X1 @ X0) @ X2)
% 0.20/0.49          | ~ (v1_relat_1 @ X1)
% 0.20/0.49          | (r2_hidden @ 
% 0.20/0.49             (sk_D @ X1 @ X0 @ (sk_C @ X2 @ (k10_relat_1 @ X1 @ X0))) @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf('8', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ (k10_relat_1 @ X1 @ X0) @ X2)
% 0.20/0.49          | ~ (v1_relat_1 @ X1)
% 0.20/0.49          | (r2_hidden @ 
% 0.20/0.49             (sk_D @ X1 @ X0 @ (sk_C @ X2 @ (k10_relat_1 @ X1 @ X0))) @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X5 @ X3)
% 0.20/0.49          | ~ (r2_hidden @ X5 @ X6)
% 0.20/0.49          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X1)
% 0.20/0.49          | (r1_xboole_0 @ (k10_relat_1 @ X1 @ X0) @ X2)
% 0.20/0.49          | ~ (r1_xboole_0 @ X0 @ X3)
% 0.20/0.49          | ~ (r2_hidden @ 
% 0.20/0.49               (sk_D @ X1 @ X0 @ (sk_C @ X2 @ (k10_relat_1 @ X1 @ X0))) @ X3))),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X1)
% 0.20/0.49          | (r1_xboole_0 @ (k10_relat_1 @ X1 @ X0) @ X2)
% 0.20/0.49          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.20/0.49          | (r1_xboole_0 @ (k10_relat_1 @ X1 @ X0) @ X2)
% 0.20/0.49          | ~ (v1_relat_1 @ X1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['7', '10'])).
% 0.20/0.49  thf('12', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (r1_xboole_0 @ X0 @ X0)
% 0.20/0.49          | (r1_xboole_0 @ (k10_relat_1 @ X1 @ X0) @ X2)
% 0.20/0.49          | ~ (v1_relat_1 @ X1))),
% 0.20/0.49      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X0)
% 0.20/0.49          | (r1_xboole_0 @ (k10_relat_1 @ X0 @ k1_xboole_0) @ X1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '12'])).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.49  thf('15', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (v1_relat_1 @ X1)
% 0.20/0.49          | ((k3_xboole_0 @ (k10_relat_1 @ X1 @ k1_xboole_0) @ X0)
% 0.20/0.49              = (k1_xboole_0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((k10_relat_1 @ X1 @ (k3_xboole_0 @ k1_xboole_0 @ X0))
% 0.20/0.49            = (k1_xboole_0))
% 0.20/0.49          | ~ (v1_relat_1 @ X1)
% 0.20/0.49          | ~ (v1_funct_1 @ X1)
% 0.20/0.49          | ~ (v1_relat_1 @ X1))),
% 0.20/0.49      inference('sup+', [status(thm)], ['0', '15'])).
% 0.20/0.49  thf('17', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.20/0.49      inference('simplify', [status(thm)], ['3'])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X3 : $i, X4 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.49  thf('20', plain,
% 0.20/0.49      (![X3 : $i, X5 : $i, X6 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X5 @ X3)
% 0.20/0.49          | ~ (r2_hidden @ X5 @ X6)
% 0.20/0.49          | ~ (r1_xboole_0 @ X3 @ X6))),
% 0.20/0.49      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.20/0.49  thf('21', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X0 @ X1)
% 0.20/0.49          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.20/0.49          | ~ (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.20/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X0 @ X1)
% 0.20/0.49          | ~ (r1_xboole_0 @ X0 @ X0)
% 0.20/0.49          | (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.49      inference('sup-', [status(thm)], ['18', '21'])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (~ (r1_xboole_0 @ X0 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.49      inference('simplify', [status(thm)], ['22'])).
% 0.20/0.49  thf('24', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 0.20/0.49      inference('sup-', [status(thm)], ['17', '23'])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X0 : $i]: ((k3_xboole_0 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      (![X1 : $i]:
% 0.20/0.49         (((k10_relat_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))
% 0.20/0.49          | ~ (v1_relat_1 @ X1)
% 0.20/0.49          | ~ (v1_funct_1 @ X1)
% 0.20/0.49          | ~ (v1_relat_1 @ X1))),
% 0.20/0.49      inference('demod', [status(thm)], ['16', '26'])).
% 0.20/0.49  thf('28', plain,
% 0.20/0.49      (![X1 : $i]:
% 0.20/0.49         (~ (v1_funct_1 @ X1)
% 0.20/0.49          | ~ (v1_relat_1 @ X1)
% 0.20/0.49          | ((k10_relat_1 @ X1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.20/0.49      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.49  thf(t141_funct_1, conjecture,
% 0.20/0.49    (![A:$i]:
% 0.20/0.49     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.49       ( ![B:$i,C:$i]:
% 0.20/0.49         ( ( r1_xboole_0 @ B @ C ) =>
% 0.20/0.49           ( r1_xboole_0 @ ( k10_relat_1 @ A @ B ) @ ( k10_relat_1 @ A @ C ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i]:
% 0.20/0.49        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.49          ( ![B:$i,C:$i]:
% 0.20/0.49            ( ( r1_xboole_0 @ B @ C ) =>
% 0.20/0.49              ( r1_xboole_0 @ ( k10_relat_1 @ A @ B ) @ ( k10_relat_1 @ A @ C ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t141_funct_1])).
% 0.20/0.49  thf('29', plain, ((r1_xboole_0 @ sk_B @ sk_C_1)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('30', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i]:
% 0.20/0.49         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.20/0.49      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.49  thf('31', plain, (((k3_xboole_0 @ sk_B @ sk_C_1) = (k1_xboole_0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.49         (((k10_relat_1 @ X12 @ (k3_xboole_0 @ X13 @ X14))
% 0.20/0.49            = (k3_xboole_0 @ (k10_relat_1 @ X12 @ X13) @ 
% 0.20/0.49               (k10_relat_1 @ X12 @ X14)))
% 0.20/0.49          | ~ (v1_funct_1 @ X12)
% 0.20/0.49          | ~ (v1_relat_1 @ X12))),
% 0.20/0.49      inference('cnf', [status(esa)], [t137_funct_1])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (![X0 : $i, X2 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ X0 @ X2) | ((k3_xboole_0 @ X0 @ X2) != (k1_xboole_0)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.20/0.49  thf('34', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (((k10_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) != (k1_xboole_0))
% 0.20/0.49          | ~ (v1_relat_1 @ X2)
% 0.20/0.49          | ~ (v1_funct_1 @ X2)
% 0.20/0.49          | (r1_xboole_0 @ (k10_relat_1 @ X2 @ X1) @ (k10_relat_1 @ X2 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['32', '33'])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k10_relat_1 @ X0 @ k1_xboole_0) != (k1_xboole_0))
% 0.20/0.49          | (r1_xboole_0 @ (k10_relat_1 @ X0 @ sk_B) @ 
% 0.20/0.49             (k10_relat_1 @ X0 @ sk_C_1))
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0))),
% 0.20/0.49      inference('sup-', [status(thm)], ['31', '34'])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.49          | ~ (v1_relat_1 @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0)
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | (r1_xboole_0 @ (k10_relat_1 @ X0 @ sk_B) @ 
% 0.20/0.49             (k10_relat_1 @ X0 @ sk_C_1)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['28', '35'])).
% 0.20/0.49  thf('37', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r1_xboole_0 @ (k10_relat_1 @ X0 @ sk_B) @ 
% 0.20/0.49           (k10_relat_1 @ X0 @ sk_C_1))
% 0.20/0.49          | ~ (v1_funct_1 @ X0)
% 0.20/0.49          | ~ (v1_relat_1 @ X0))),
% 0.20/0.49      inference('simplify', [status(thm)], ['36'])).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (~ (r1_xboole_0 @ (k10_relat_1 @ sk_A @ sk_B) @ 
% 0.20/0.49          (k10_relat_1 @ sk_A @ sk_C_1))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('39', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_funct_1 @ sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.49  thf('40', plain, ((v1_relat_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('41', plain, ((v1_funct_1 @ sk_A)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('42', plain, ($false),
% 0.20/0.49      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
