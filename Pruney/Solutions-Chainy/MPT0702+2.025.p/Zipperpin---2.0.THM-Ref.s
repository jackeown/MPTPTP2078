%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UMCiVySRZa

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:45 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 (  95 expanded)
%              Number of leaves         :   25 (  39 expanded)
%              Depth                    :   15
%              Number of atoms          :  468 ( 803 expanded)
%              Number of equality atoms :   29 (  37 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(t157_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
          & ( v2_funct_1 @ C ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) )
            & ( r1_tarski @ A @ ( k1_relat_1 @ C ) )
            & ( v2_funct_1 @ C ) )
         => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t157_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ ( k9_relat_1 @ sk_C_1 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k4_xboole_0 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k6_subset_1 @ X21 @ X22 )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k6_subset_1 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,
    ( ( k6_subset_1 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ ( k9_relat_1 @ sk_C_1 @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t123_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( v2_funct_1 @ C )
       => ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
          = ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v2_funct_1 @ X25 )
      | ( ( k9_relat_1 @ X25 @ ( k6_subset_1 @ X26 @ X27 ) )
        = ( k6_subset_1 @ ( k9_relat_1 @ X25 @ X26 ) @ ( k9_relat_1 @ X25 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t123_funct_1])).

thf('7',plain,
    ( ( ( k9_relat_1 @ sk_C_1 @ ( k6_subset_1 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k9_relat_1 @ sk_C_1 @ ( k6_subset_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['7','8','9','10'])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('12',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k9_relat_1 @ X23 @ X24 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X23 ) @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('13',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ ( k6_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ ( k6_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) @ ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['15'])).

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

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('19',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ X3 )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    r1_xboole_0 @ ( k6_subset_1 @ sk_A @ sk_B ) @ ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ X4 @ X5 )
      | ( X4 != X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,(
    ! [X5: $i] :
      ( r1_tarski @ X5 @ X5 ) ),
    inference(simplify,[status(thm)],['25'])).

thf(t64_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ C @ D )
        & ( r1_xboole_0 @ B @ D ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('27',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ( r1_xboole_0 @ X14 @ X15 )
      | ~ ( r1_tarski @ X14 @ X16 )
      | ~ ( r1_tarski @ X15 @ X17 )
      | ~ ( r1_xboole_0 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t64_xboole_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X2 @ X1 )
      | ( r1_xboole_0 @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ X0 @ sk_A )
      | ~ ( r1_xboole_0 @ X0 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf('30',plain,(
    r1_xboole_0 @ ( k6_subset_1 @ sk_A @ sk_B ) @ sk_A ),
    inference('sup-',[status(thm)],['23','29'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('31',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k4_xboole_0 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('32',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k6_subset_1 @ X21 @ X22 )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('33',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k6_subset_1 @ X18 @ X19 )
        = X18 )
      | ~ ( r1_xboole_0 @ X18 @ X19 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k6_subset_1 @ ( k6_subset_1 @ sk_A @ sk_B ) @ sk_A )
    = ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('35',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf('36',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k6_subset_1 @ X21 @ X22 )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('37',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X12 @ X13 ) @ X12 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X7: $i,X9: $i] :
      ( ( ( k6_subset_1 @ X7 @ X9 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ ( k6_subset_1 @ X0 @ X1 ) @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( k1_xboole_0
    = ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference(demod,[status(thm)],['34','39'])).

thf('41',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( ( k4_xboole_0 @ X7 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('42',plain,(
    ! [X21: $i,X22: $i] :
      ( ( k6_subset_1 @ X21 @ X22 )
      = ( k4_xboole_0 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('43',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( ( k6_subset_1 @ X7 @ X8 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['40','43'])).

thf('45',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    $false ),
    inference(demod,[status(thm)],['0','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UMCiVySRZa
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:48:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 101 iterations in 0.035s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.48  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.48  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.48  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.48  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.21/0.48  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.21/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.48  thf(t157_funct_1, conjecture,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.48       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.21/0.48           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.21/0.48         ( r1_tarski @ A @ B ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.48        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.48          ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.21/0.48              ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.21/0.48            ( r1_tarski @ A @ B ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t157_funct_1])).
% 0.21/0.48  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      ((r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ (k9_relat_1 @ sk_C_1 @ sk_B))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(l32_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X7 : $i, X9 : $i]:
% 0.21/0.48         (((k4_xboole_0 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.21/0.48      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.48  thf(redefinition_k6_subset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (![X21 : $i, X22 : $i]:
% 0.21/0.48         ((k6_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.48  thf('4', plain,
% 0.21/0.48      (![X7 : $i, X9 : $i]:
% 0.21/0.48         (((k6_subset_1 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.21/0.48      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.48  thf('5', plain,
% 0.21/0.48      (((k6_subset_1 @ (k9_relat_1 @ sk_C_1 @ sk_A) @ 
% 0.21/0.48         (k9_relat_1 @ sk_C_1 @ sk_B)) = (k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '4'])).
% 0.21/0.48  thf(t123_funct_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.48       ( ( v2_funct_1 @ C ) =>
% 0.21/0.48         ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 0.21/0.48           ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 0.21/0.48  thf('6', plain,
% 0.21/0.48      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.48         (~ (v2_funct_1 @ X25)
% 0.21/0.48          | ((k9_relat_1 @ X25 @ (k6_subset_1 @ X26 @ X27))
% 0.21/0.48              = (k6_subset_1 @ (k9_relat_1 @ X25 @ X26) @ 
% 0.21/0.48                 (k9_relat_1 @ X25 @ X27)))
% 0.21/0.48          | ~ (v1_funct_1 @ X25)
% 0.21/0.48          | ~ (v1_relat_1 @ X25))),
% 0.21/0.48      inference('cnf', [status(esa)], [t123_funct_1])).
% 0.21/0.48  thf('7', plain,
% 0.21/0.48      ((((k9_relat_1 @ sk_C_1 @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.21/0.48        | ~ (v1_relat_1 @ sk_C_1)
% 0.21/0.48        | ~ (v1_funct_1 @ sk_C_1)
% 0.21/0.48        | ~ (v2_funct_1 @ sk_C_1))),
% 0.21/0.48      inference('sup+', [status(thm)], ['5', '6'])).
% 0.21/0.48  thf('8', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('9', plain, ((v1_funct_1 @ sk_C_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('10', plain, ((v2_funct_1 @ sk_C_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      (((k9_relat_1 @ sk_C_1 @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.21/0.48      inference('demod', [status(thm)], ['7', '8', '9', '10'])).
% 0.21/0.48  thf(t151_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ B ) =>
% 0.21/0.48       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.21/0.48         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X23 : $i, X24 : $i]:
% 0.21/0.48         (((k9_relat_1 @ X23 @ X24) != (k1_xboole_0))
% 0.21/0.48          | (r1_xboole_0 @ (k1_relat_1 @ X23) @ X24)
% 0.21/0.48          | ~ (v1_relat_1 @ X23))),
% 0.21/0.48      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.48        | ~ (v1_relat_1 @ sk_C_1)
% 0.21/0.48        | (r1_xboole_0 @ (k1_relat_1 @ sk_C_1) @ (k6_subset_1 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.48  thf('14', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('15', plain,
% 0.21/0.48      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.48        | (r1_xboole_0 @ (k1_relat_1 @ sk_C_1) @ (k6_subset_1 @ sk_A @ sk_B)))),
% 0.21/0.48      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      ((r1_xboole_0 @ (k1_relat_1 @ sk_C_1) @ (k6_subset_1 @ sk_A @ sk_B))),
% 0.21/0.48      inference('simplify', [status(thm)], ['15'])).
% 0.21/0.48  thf(t3_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.21/0.48            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.21/0.48       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.21/0.48            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.21/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.48  thf('18', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.48  thf('19', plain,
% 0.21/0.48      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X2 @ X0)
% 0.21/0.48          | ~ (r2_hidden @ X2 @ X3)
% 0.21/0.48          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.21/0.48      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ X1 @ X0)
% 0.21/0.48          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.21/0.48          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.21/0.48      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ X0 @ X1)
% 0.21/0.48          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.21/0.48          | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['17', '20'])).
% 0.21/0.48  thf('22', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.21/0.48      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      ((r1_xboole_0 @ (k6_subset_1 @ sk_A @ sk_B) @ (k1_relat_1 @ sk_C_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['16', '22'])).
% 0.21/0.48  thf('24', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C_1))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(d10_xboole_0, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.48  thf('25', plain,
% 0.21/0.48      (![X4 : $i, X5 : $i]: ((r1_tarski @ X4 @ X5) | ((X4) != (X5)))),
% 0.21/0.48      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.48  thf('26', plain, (![X5 : $i]: (r1_tarski @ X5 @ X5)),
% 0.21/0.48      inference('simplify', [status(thm)], ['25'])).
% 0.21/0.48  thf(t64_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.48     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ C @ D ) & 
% 0.21/0.48         ( r1_xboole_0 @ B @ D ) ) =>
% 0.21/0.48       ( r1_xboole_0 @ A @ C ) ))).
% 0.21/0.48  thf('27', plain,
% 0.21/0.48      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ X14 @ X15)
% 0.21/0.48          | ~ (r1_tarski @ X14 @ X16)
% 0.21/0.48          | ~ (r1_tarski @ X15 @ X17)
% 0.21/0.48          | ~ (r1_xboole_0 @ X16 @ X17))),
% 0.21/0.48      inference('cnf', [status(esa)], [t64_xboole_1])).
% 0.21/0.48  thf('28', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.48         (~ (r1_xboole_0 @ X0 @ X1)
% 0.21/0.48          | ~ (r1_tarski @ X2 @ X1)
% 0.21/0.48          | (r1_xboole_0 @ X0 @ X2))),
% 0.21/0.48      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      (![X0 : $i]:
% 0.21/0.48         ((r1_xboole_0 @ X0 @ sk_A)
% 0.21/0.48          | ~ (r1_xboole_0 @ X0 @ (k1_relat_1 @ sk_C_1)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['24', '28'])).
% 0.21/0.48  thf('30', plain, ((r1_xboole_0 @ (k6_subset_1 @ sk_A @ sk_B) @ sk_A)),
% 0.21/0.48      inference('sup-', [status(thm)], ['23', '29'])).
% 0.21/0.48  thf(t83_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      (![X18 : $i, X19 : $i]:
% 0.21/0.48         (((k4_xboole_0 @ X18 @ X19) = (X18)) | ~ (r1_xboole_0 @ X18 @ X19))),
% 0.21/0.48      inference('cnf', [status(esa)], [t83_xboole_1])).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      (![X21 : $i, X22 : $i]:
% 0.21/0.48         ((k6_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      (![X18 : $i, X19 : $i]:
% 0.21/0.48         (((k6_subset_1 @ X18 @ X19) = (X18)) | ~ (r1_xboole_0 @ X18 @ X19))),
% 0.21/0.48      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.48  thf('34', plain,
% 0.21/0.48      (((k6_subset_1 @ (k6_subset_1 @ sk_A @ sk_B) @ sk_A)
% 0.21/0.48         = (k6_subset_1 @ sk_A @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['30', '33'])).
% 0.21/0.48  thf(t36_xboole_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 0.21/0.48      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      (![X21 : $i, X22 : $i]:
% 0.21/0.48         ((k6_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      (![X12 : $i, X13 : $i]: (r1_tarski @ (k6_subset_1 @ X12 @ X13) @ X12)),
% 0.21/0.48      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.48  thf('38', plain,
% 0.21/0.48      (![X7 : $i, X9 : $i]:
% 0.21/0.48         (((k6_subset_1 @ X7 @ X9) = (k1_xboole_0)) | ~ (r1_tarski @ X7 @ X9))),
% 0.21/0.48      inference('demod', [status(thm)], ['2', '3'])).
% 0.21/0.48  thf('39', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]:
% 0.21/0.48         ((k6_subset_1 @ (k6_subset_1 @ X0 @ X1) @ X0) = (k1_xboole_0))),
% 0.21/0.48      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.48  thf('40', plain, (((k1_xboole_0) = (k6_subset_1 @ sk_A @ sk_B))),
% 0.21/0.48      inference('demod', [status(thm)], ['34', '39'])).
% 0.21/0.48  thf('41', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i]:
% 0.21/0.48         ((r1_tarski @ X7 @ X8) | ((k4_xboole_0 @ X7 @ X8) != (k1_xboole_0)))),
% 0.21/0.48      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.21/0.48  thf('42', plain,
% 0.21/0.48      (![X21 : $i, X22 : $i]:
% 0.21/0.48         ((k6_subset_1 @ X21 @ X22) = (k4_xboole_0 @ X21 @ X22))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.21/0.48  thf('43', plain,
% 0.21/0.48      (![X7 : $i, X8 : $i]:
% 0.21/0.48         ((r1_tarski @ X7 @ X8) | ((k6_subset_1 @ X7 @ X8) != (k1_xboole_0)))),
% 0.21/0.48      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.48  thf('44', plain,
% 0.21/0.48      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.21/0.48      inference('sup-', [status(thm)], ['40', '43'])).
% 0.21/0.48  thf('45', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.21/0.48      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.48  thf('46', plain, ($false), inference('demod', [status(thm)], ['0', '45'])).
% 0.21/0.48  
% 0.21/0.48  % SZS output end Refutation
% 0.21/0.48  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
