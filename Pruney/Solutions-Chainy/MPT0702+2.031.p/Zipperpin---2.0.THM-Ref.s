%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.w7nDoKYQnu

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:46 EST 2020

% Result     : Theorem 0.53s
% Output     : Refutation 0.53s
% Verified   : 
% Statistics : Number of formulae       :   68 (  94 expanded)
%              Number of leaves         :   23 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :  458 ( 849 expanded)
%              Number of equality atoms :   28 (  37 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('3',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t138_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('5',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k10_relat_1 @ X24 @ ( k6_subset_1 @ X25 @ X26 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X24 @ X25 ) @ ( k10_relat_1 @ X24 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('7',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('8',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k10_relat_1 @ X24 @ ( k4_xboole_0 @ X25 @ X26 ) )
        = ( k4_xboole_0 @ ( k10_relat_1 @ X24 @ X25 ) @ ( k10_relat_1 @ X24 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['4','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('11',plain,(
    ! [X1: $i] :
      ( ( ( k10_relat_1 @ X1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('14',plain,
    ( ( k4_xboole_0 @ ( k9_relat_1 @ sk_C @ sk_A ) @ ( k9_relat_1 @ sk_C @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t123_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( v2_funct_1 @ C )
       => ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
          = ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) )).

thf('15',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k9_relat_1 @ X21 @ ( k6_subset_1 @ X22 @ X23 ) )
        = ( k6_subset_1 @ ( k9_relat_1 @ X21 @ X22 ) @ ( k9_relat_1 @ X21 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t123_funct_1])).

thf('16',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('17',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('18',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k9_relat_1 @ X21 @ ( k4_xboole_0 @ X22 @ X23 ) )
        = ( k4_xboole_0 @ ( k9_relat_1 @ X21 @ X22 ) @ ( k9_relat_1 @ X21 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ( ( k9_relat_1 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['14','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( k9_relat_1 @ sk_C @ ( k4_xboole_0 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['19','20','21','22'])).

thf('24',plain,(
    r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('25',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X13 @ X14 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('26',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('29',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ X27 @ ( k1_relat_1 @ X28 ) )
      | ( r1_tarski @ X27 @ ( k10_relat_1 @ X28 @ ( k9_relat_1 @ X28 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k10_relat_1 @ sk_C @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','32'])).

thf('34',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['11','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['34','35','36'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('38',plain,(
    ! [X15: $i] :
      ( ( X15 = k1_xboole_0 )
      | ~ ( r1_tarski @ X15 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('39',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('41',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    $false ),
    inference(demod,[status(thm)],['0','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.w7nDoKYQnu
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:38:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.53/0.77  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.53/0.77  % Solved by: fo/fo7.sh
% 0.53/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.53/0.77  % done 670 iterations in 0.311s
% 0.53/0.77  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.53/0.77  % SZS output start Refutation
% 0.53/0.77  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.53/0.77  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.53/0.77  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.53/0.77  thf(sk_B_type, type, sk_B: $i).
% 0.53/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.53/0.77  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.53/0.77  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.53/0.77  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.53/0.77  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.53/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.53/0.77  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.53/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.53/0.77  thf(sk_C_type, type, sk_C: $i).
% 0.53/0.77  thf(t157_funct_1, conjecture,
% 0.53/0.77    (![A:$i,B:$i,C:$i]:
% 0.53/0.77     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.53/0.77       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.53/0.77           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.53/0.77         ( r1_tarski @ A @ B ) ) ))).
% 0.53/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.53/0.77    (~( ![A:$i,B:$i,C:$i]:
% 0.53/0.77        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.53/0.77          ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.53/0.77              ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.53/0.77            ( r1_tarski @ A @ B ) ) ) )),
% 0.53/0.77    inference('cnf.neg', [status(esa)], [t157_funct_1])).
% 0.53/0.77  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf(d10_xboole_0, axiom,
% 0.53/0.77    (![A:$i,B:$i]:
% 0.53/0.77     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.53/0.77  thf('1', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.53/0.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.53/0.77  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.53/0.77      inference('simplify', [status(thm)], ['1'])).
% 0.53/0.77  thf(l32_xboole_1, axiom,
% 0.53/0.77    (![A:$i,B:$i]:
% 0.53/0.77     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.53/0.77  thf('3', plain,
% 0.53/0.77      (![X3 : $i, X5 : $i]:
% 0.53/0.77         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.53/0.77      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.53/0.77  thf('4', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.53/0.77      inference('sup-', [status(thm)], ['2', '3'])).
% 0.53/0.77  thf(t138_funct_1, axiom,
% 0.53/0.77    (![A:$i,B:$i,C:$i]:
% 0.53/0.77     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.53/0.77       ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 0.53/0.77         ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.53/0.77  thf('5', plain,
% 0.53/0.77      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.53/0.77         (((k10_relat_1 @ X24 @ (k6_subset_1 @ X25 @ X26))
% 0.53/0.77            = (k6_subset_1 @ (k10_relat_1 @ X24 @ X25) @ 
% 0.53/0.77               (k10_relat_1 @ X24 @ X26)))
% 0.53/0.77          | ~ (v1_funct_1 @ X24)
% 0.53/0.77          | ~ (v1_relat_1 @ X24))),
% 0.53/0.77      inference('cnf', [status(esa)], [t138_funct_1])).
% 0.53/0.77  thf(redefinition_k6_subset_1, axiom,
% 0.53/0.77    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.53/0.77  thf('6', plain,
% 0.53/0.77      (![X19 : $i, X20 : $i]:
% 0.53/0.77         ((k6_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))),
% 0.53/0.77      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.53/0.77  thf('7', plain,
% 0.53/0.77      (![X19 : $i, X20 : $i]:
% 0.53/0.77         ((k6_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))),
% 0.53/0.77      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.53/0.77  thf('8', plain,
% 0.53/0.77      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.53/0.77         (((k10_relat_1 @ X24 @ (k4_xboole_0 @ X25 @ X26))
% 0.53/0.77            = (k4_xboole_0 @ (k10_relat_1 @ X24 @ X25) @ 
% 0.53/0.77               (k10_relat_1 @ X24 @ X26)))
% 0.53/0.77          | ~ (v1_funct_1 @ X24)
% 0.53/0.77          | ~ (v1_relat_1 @ X24))),
% 0.53/0.77      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.53/0.77  thf('9', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i]:
% 0.53/0.77         (((k10_relat_1 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0))
% 0.53/0.77          | ~ (v1_relat_1 @ X1)
% 0.53/0.77          | ~ (v1_funct_1 @ X1))),
% 0.53/0.77      inference('sup+', [status(thm)], ['4', '8'])).
% 0.53/0.77  thf('10', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.53/0.77      inference('sup-', [status(thm)], ['2', '3'])).
% 0.53/0.77  thf('11', plain,
% 0.53/0.77      (![X1 : $i]:
% 0.53/0.77         (((k10_relat_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))
% 0.53/0.77          | ~ (v1_relat_1 @ X1)
% 0.53/0.77          | ~ (v1_funct_1 @ X1))),
% 0.53/0.77      inference('demod', [status(thm)], ['9', '10'])).
% 0.53/0.77  thf('12', plain,
% 0.53/0.77      ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('13', plain,
% 0.53/0.77      (![X3 : $i, X5 : $i]:
% 0.53/0.77         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.53/0.77      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.53/0.77  thf('14', plain,
% 0.53/0.77      (((k4_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))
% 0.53/0.77         = (k1_xboole_0))),
% 0.53/0.77      inference('sup-', [status(thm)], ['12', '13'])).
% 0.53/0.77  thf(t123_funct_1, axiom,
% 0.53/0.77    (![A:$i,B:$i,C:$i]:
% 0.53/0.77     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.53/0.77       ( ( v2_funct_1 @ C ) =>
% 0.53/0.77         ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 0.53/0.77           ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 0.53/0.77  thf('15', plain,
% 0.53/0.77      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.53/0.77         (~ (v2_funct_1 @ X21)
% 0.53/0.77          | ((k9_relat_1 @ X21 @ (k6_subset_1 @ X22 @ X23))
% 0.53/0.77              = (k6_subset_1 @ (k9_relat_1 @ X21 @ X22) @ 
% 0.53/0.77                 (k9_relat_1 @ X21 @ X23)))
% 0.53/0.77          | ~ (v1_funct_1 @ X21)
% 0.53/0.77          | ~ (v1_relat_1 @ X21))),
% 0.53/0.77      inference('cnf', [status(esa)], [t123_funct_1])).
% 0.53/0.77  thf('16', plain,
% 0.53/0.77      (![X19 : $i, X20 : $i]:
% 0.53/0.77         ((k6_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))),
% 0.53/0.77      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.53/0.77  thf('17', plain,
% 0.53/0.77      (![X19 : $i, X20 : $i]:
% 0.53/0.77         ((k6_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))),
% 0.53/0.77      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.53/0.77  thf('18', plain,
% 0.53/0.77      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.53/0.77         (~ (v2_funct_1 @ X21)
% 0.53/0.77          | ((k9_relat_1 @ X21 @ (k4_xboole_0 @ X22 @ X23))
% 0.53/0.77              = (k4_xboole_0 @ (k9_relat_1 @ X21 @ X22) @ 
% 0.53/0.77                 (k9_relat_1 @ X21 @ X23)))
% 0.53/0.77          | ~ (v1_funct_1 @ X21)
% 0.53/0.77          | ~ (v1_relat_1 @ X21))),
% 0.53/0.77      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.53/0.77  thf('19', plain,
% 0.53/0.77      ((((k9_relat_1 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.53/0.77        | ~ (v1_relat_1 @ sk_C)
% 0.53/0.77        | ~ (v1_funct_1 @ sk_C)
% 0.53/0.77        | ~ (v2_funct_1 @ sk_C))),
% 0.53/0.77      inference('sup+', [status(thm)], ['14', '18'])).
% 0.53/0.77  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('22', plain, ((v2_funct_1 @ sk_C)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('23', plain,
% 0.53/0.77      (((k9_relat_1 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.53/0.77      inference('demod', [status(thm)], ['19', '20', '21', '22'])).
% 0.53/0.77  thf('24', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf(t36_xboole_1, axiom,
% 0.53/0.77    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.53/0.77  thf('25', plain,
% 0.53/0.77      (![X13 : $i, X14 : $i]: (r1_tarski @ (k4_xboole_0 @ X13 @ X14) @ X13)),
% 0.53/0.77      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.53/0.77  thf(t1_xboole_1, axiom,
% 0.53/0.77    (![A:$i,B:$i,C:$i]:
% 0.53/0.77     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.53/0.77       ( r1_tarski @ A @ C ) ))).
% 0.53/0.77  thf('26', plain,
% 0.53/0.77      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.53/0.77         (~ (r1_tarski @ X9 @ X10)
% 0.53/0.77          | ~ (r1_tarski @ X10 @ X11)
% 0.53/0.77          | (r1_tarski @ X9 @ X11))),
% 0.53/0.77      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.53/0.77  thf('27', plain,
% 0.53/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.53/0.77         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.53/0.77      inference('sup-', [status(thm)], ['25', '26'])).
% 0.53/0.77  thf('28', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ (k1_relat_1 @ sk_C))),
% 0.53/0.77      inference('sup-', [status(thm)], ['24', '27'])).
% 0.53/0.77  thf(t146_funct_1, axiom,
% 0.53/0.77    (![A:$i,B:$i]:
% 0.53/0.77     ( ( v1_relat_1 @ B ) =>
% 0.53/0.77       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.53/0.77         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.53/0.77  thf('29', plain,
% 0.53/0.77      (![X27 : $i, X28 : $i]:
% 0.53/0.77         (~ (r1_tarski @ X27 @ (k1_relat_1 @ X28))
% 0.53/0.77          | (r1_tarski @ X27 @ (k10_relat_1 @ X28 @ (k9_relat_1 @ X28 @ X27)))
% 0.53/0.77          | ~ (v1_relat_1 @ X28))),
% 0.53/0.77      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.53/0.77  thf('30', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         (~ (v1_relat_1 @ sk_C)
% 0.53/0.77          | (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ 
% 0.53/0.77             (k10_relat_1 @ sk_C @ 
% 0.53/0.77              (k9_relat_1 @ sk_C @ (k4_xboole_0 @ sk_A @ X0)))))),
% 0.53/0.77      inference('sup-', [status(thm)], ['28', '29'])).
% 0.53/0.77  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('32', plain,
% 0.53/0.77      (![X0 : $i]:
% 0.53/0.77         (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ 
% 0.53/0.77          (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ (k4_xboole_0 @ sk_A @ X0))))),
% 0.53/0.77      inference('demod', [status(thm)], ['30', '31'])).
% 0.53/0.77  thf('33', plain,
% 0.53/0.77      ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.53/0.77        (k10_relat_1 @ sk_C @ k1_xboole_0))),
% 0.53/0.77      inference('sup+', [status(thm)], ['23', '32'])).
% 0.53/0.77  thf('34', plain,
% 0.53/0.77      (((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0)
% 0.53/0.77        | ~ (v1_funct_1 @ sk_C)
% 0.53/0.77        | ~ (v1_relat_1 @ sk_C))),
% 0.53/0.77      inference('sup+', [status(thm)], ['11', '33'])).
% 0.53/0.77  thf('35', plain, ((v1_funct_1 @ sk_C)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('36', plain, ((v1_relat_1 @ sk_C)),
% 0.53/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.53/0.77  thf('37', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0)),
% 0.53/0.77      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.53/0.77  thf(t3_xboole_1, axiom,
% 0.53/0.77    (![A:$i]:
% 0.53/0.77     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.53/0.77  thf('38', plain,
% 0.53/0.77      (![X15 : $i]:
% 0.53/0.77         (((X15) = (k1_xboole_0)) | ~ (r1_tarski @ X15 @ k1_xboole_0))),
% 0.53/0.77      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.53/0.77  thf('39', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.53/0.77      inference('sup-', [status(thm)], ['37', '38'])).
% 0.53/0.77  thf('40', plain,
% 0.53/0.77      (![X3 : $i, X4 : $i]:
% 0.53/0.77         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.53/0.77      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.53/0.77  thf('41', plain,
% 0.53/0.77      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.53/0.77      inference('sup-', [status(thm)], ['39', '40'])).
% 0.53/0.77  thf('42', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.53/0.77      inference('simplify', [status(thm)], ['41'])).
% 0.53/0.77  thf('43', plain, ($false), inference('demod', [status(thm)], ['0', '42'])).
% 0.53/0.77  
% 0.53/0.77  % SZS output end Refutation
% 0.53/0.77  
% 0.61/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
