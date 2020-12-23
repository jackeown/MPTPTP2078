%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZVM4kCfPUR

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:46 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 101 expanded)
%              Number of leaves         :   25 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :  488 ( 888 expanded)
%              Number of equality atoms :   31 (  41 expanded)
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

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

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
    ! [X12: $i,X13: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X12 @ X13 ) @ X12 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('26',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_xboole_0 @ X10 @ X9 )
        = X9 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('28',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( r1_tarski @ ( k4_xboole_0 @ X0 @ X2 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['24','29'])).

thf(t146_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ) )).

thf('31',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ X27 @ ( k1_relat_1 @ X28 ) )
      | ( r1_tarski @ X27 @ ( k10_relat_1 @ X28 @ ( k9_relat_1 @ X28 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t146_funct_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ X0 ) @ ( k10_relat_1 @ sk_C @ ( k9_relat_1 @ sk_C @ ( k4_xboole_0 @ sk_A @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ ( k10_relat_1 @ sk_C @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['23','34'])).

thf('36',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['11','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['36','37','38'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('40',plain,(
    ! [X11: $i] :
      ( r1_tarski @ k1_xboole_0 @ X11 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('41',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['39','42'])).

thf('44',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('45',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_tarski @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['0','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZVM4kCfPUR
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:09:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.47/0.66  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.66  % Solved by: fo/fo7.sh
% 0.47/0.66  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.66  % done 461 iterations in 0.202s
% 0.47/0.66  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.66  % SZS output start Refutation
% 0.47/0.66  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.47/0.66  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.66  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.47/0.66  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.66  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.66  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.47/0.66  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.47/0.66  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.66  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.66  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.66  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.47/0.66  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.47/0.66  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.66  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.66  thf(t157_funct_1, conjecture,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.47/0.66       ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.47/0.66           ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.47/0.66         ( r1_tarski @ A @ B ) ) ))).
% 0.47/0.66  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.66    (~( ![A:$i,B:$i,C:$i]:
% 0.47/0.66        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.47/0.66          ( ( ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) & 
% 0.47/0.66              ( r1_tarski @ A @ ( k1_relat_1 @ C ) ) & ( v2_funct_1 @ C ) ) =>
% 0.47/0.66            ( r1_tarski @ A @ B ) ) ) )),
% 0.47/0.66    inference('cnf.neg', [status(esa)], [t157_funct_1])).
% 0.47/0.66  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(d10_xboole_0, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.66  thf('1', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.47/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.66  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.47/0.66      inference('simplify', [status(thm)], ['1'])).
% 0.47/0.66  thf(l32_xboole_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.47/0.66  thf('3', plain,
% 0.47/0.66      (![X3 : $i, X5 : $i]:
% 0.47/0.66         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.47/0.66      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.47/0.66  thf('4', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['2', '3'])).
% 0.47/0.66  thf(t138_funct_1, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.47/0.66       ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 0.47/0.66         ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.47/0.66  thf('5', plain,
% 0.47/0.66      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.47/0.66         (((k10_relat_1 @ X24 @ (k6_subset_1 @ X25 @ X26))
% 0.47/0.66            = (k6_subset_1 @ (k10_relat_1 @ X24 @ X25) @ 
% 0.47/0.66               (k10_relat_1 @ X24 @ X26)))
% 0.47/0.66          | ~ (v1_funct_1 @ X24)
% 0.47/0.66          | ~ (v1_relat_1 @ X24))),
% 0.47/0.66      inference('cnf', [status(esa)], [t138_funct_1])).
% 0.47/0.66  thf(redefinition_k6_subset_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.47/0.66  thf('6', plain,
% 0.47/0.66      (![X19 : $i, X20 : $i]:
% 0.47/0.66         ((k6_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))),
% 0.47/0.66      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.47/0.66  thf('7', plain,
% 0.47/0.66      (![X19 : $i, X20 : $i]:
% 0.47/0.66         ((k6_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))),
% 0.47/0.66      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.47/0.66  thf('8', plain,
% 0.47/0.66      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.47/0.66         (((k10_relat_1 @ X24 @ (k4_xboole_0 @ X25 @ X26))
% 0.47/0.66            = (k4_xboole_0 @ (k10_relat_1 @ X24 @ X25) @ 
% 0.47/0.66               (k10_relat_1 @ X24 @ X26)))
% 0.47/0.66          | ~ (v1_funct_1 @ X24)
% 0.47/0.66          | ~ (v1_relat_1 @ X24))),
% 0.47/0.66      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.47/0.66  thf('9', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         (((k10_relat_1 @ X1 @ (k4_xboole_0 @ X0 @ X0)) = (k1_xboole_0))
% 0.47/0.66          | ~ (v1_relat_1 @ X1)
% 0.47/0.66          | ~ (v1_funct_1 @ X1))),
% 0.47/0.66      inference('sup+', [status(thm)], ['4', '8'])).
% 0.47/0.66  thf('10', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['2', '3'])).
% 0.47/0.66  thf('11', plain,
% 0.47/0.66      (![X1 : $i]:
% 0.47/0.66         (((k10_relat_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))
% 0.47/0.66          | ~ (v1_relat_1 @ X1)
% 0.47/0.66          | ~ (v1_funct_1 @ X1))),
% 0.47/0.66      inference('demod', [status(thm)], ['9', '10'])).
% 0.47/0.66  thf('12', plain,
% 0.47/0.66      ((r1_tarski @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('13', plain,
% 0.47/0.66      (![X3 : $i, X5 : $i]:
% 0.47/0.66         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 0.47/0.66      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.47/0.66  thf('14', plain,
% 0.47/0.66      (((k4_xboole_0 @ (k9_relat_1 @ sk_C @ sk_A) @ (k9_relat_1 @ sk_C @ sk_B))
% 0.47/0.66         = (k1_xboole_0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['12', '13'])).
% 0.47/0.66  thf(t123_funct_1, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.47/0.66       ( ( v2_funct_1 @ C ) =>
% 0.47/0.66         ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 0.47/0.66           ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 0.47/0.66  thf('15', plain,
% 0.47/0.66      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.47/0.66         (~ (v2_funct_1 @ X21)
% 0.47/0.66          | ((k9_relat_1 @ X21 @ (k6_subset_1 @ X22 @ X23))
% 0.47/0.66              = (k6_subset_1 @ (k9_relat_1 @ X21 @ X22) @ 
% 0.47/0.66                 (k9_relat_1 @ X21 @ X23)))
% 0.47/0.66          | ~ (v1_funct_1 @ X21)
% 0.47/0.66          | ~ (v1_relat_1 @ X21))),
% 0.47/0.66      inference('cnf', [status(esa)], [t123_funct_1])).
% 0.47/0.66  thf('16', plain,
% 0.47/0.66      (![X19 : $i, X20 : $i]:
% 0.47/0.66         ((k6_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))),
% 0.47/0.66      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.47/0.66  thf('17', plain,
% 0.47/0.66      (![X19 : $i, X20 : $i]:
% 0.47/0.66         ((k6_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))),
% 0.47/0.66      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.47/0.66  thf('18', plain,
% 0.47/0.66      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.47/0.66         (~ (v2_funct_1 @ X21)
% 0.47/0.66          | ((k9_relat_1 @ X21 @ (k4_xboole_0 @ X22 @ X23))
% 0.47/0.66              = (k4_xboole_0 @ (k9_relat_1 @ X21 @ X22) @ 
% 0.47/0.66                 (k9_relat_1 @ X21 @ X23)))
% 0.47/0.66          | ~ (v1_funct_1 @ X21)
% 0.47/0.66          | ~ (v1_relat_1 @ X21))),
% 0.47/0.66      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.47/0.66  thf('19', plain,
% 0.47/0.66      ((((k9_relat_1 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.47/0.66        | ~ (v1_relat_1 @ sk_C)
% 0.47/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.66        | ~ (v2_funct_1 @ sk_C))),
% 0.47/0.66      inference('sup+', [status(thm)], ['14', '18'])).
% 0.47/0.66  thf('20', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('22', plain, ((v2_funct_1 @ sk_C)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('23', plain,
% 0.47/0.66      (((k9_relat_1 @ sk_C @ (k4_xboole_0 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.47/0.66      inference('demod', [status(thm)], ['19', '20', '21', '22'])).
% 0.47/0.66  thf('24', plain, ((r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf(t36_xboole_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.47/0.66  thf('25', plain,
% 0.47/0.66      (![X12 : $i, X13 : $i]: (r1_tarski @ (k4_xboole_0 @ X12 @ X13) @ X12)),
% 0.47/0.66      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.47/0.66  thf(t12_xboole_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.47/0.66  thf('26', plain,
% 0.47/0.66      (![X9 : $i, X10 : $i]:
% 0.47/0.66         (((k2_xboole_0 @ X10 @ X9) = (X9)) | ~ (r1_tarski @ X10 @ X9))),
% 0.47/0.66      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.47/0.66  thf('27', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i]:
% 0.47/0.66         ((k2_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X0) = (X0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['25', '26'])).
% 0.47/0.66  thf(t11_xboole_1, axiom,
% 0.47/0.66    (![A:$i,B:$i,C:$i]:
% 0.47/0.66     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.47/0.66  thf('28', plain,
% 0.47/0.66      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.47/0.66         ((r1_tarski @ X6 @ X7) | ~ (r1_tarski @ (k2_xboole_0 @ X6 @ X8) @ X7))),
% 0.47/0.66      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.47/0.66  thf('29', plain,
% 0.47/0.66      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.66         (~ (r1_tarski @ X0 @ X1) | (r1_tarski @ (k4_xboole_0 @ X0 @ X2) @ X1))),
% 0.47/0.66      inference('sup-', [status(thm)], ['27', '28'])).
% 0.47/0.66  thf('30', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ (k1_relat_1 @ sk_C))),
% 0.47/0.66      inference('sup-', [status(thm)], ['24', '29'])).
% 0.47/0.66  thf(t146_funct_1, axiom,
% 0.47/0.66    (![A:$i,B:$i]:
% 0.47/0.66     ( ( v1_relat_1 @ B ) =>
% 0.47/0.66       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.47/0.66         ( r1_tarski @ A @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) ) ) ))).
% 0.47/0.66  thf('31', plain,
% 0.47/0.66      (![X27 : $i, X28 : $i]:
% 0.47/0.66         (~ (r1_tarski @ X27 @ (k1_relat_1 @ X28))
% 0.47/0.66          | (r1_tarski @ X27 @ (k10_relat_1 @ X28 @ (k9_relat_1 @ X28 @ X27)))
% 0.47/0.66          | ~ (v1_relat_1 @ X28))),
% 0.47/0.66      inference('cnf', [status(esa)], [t146_funct_1])).
% 0.47/0.66  thf('32', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (~ (v1_relat_1 @ sk_C)
% 0.47/0.66          | (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ 
% 0.47/0.66             (k10_relat_1 @ sk_C @ 
% 0.47/0.66              (k9_relat_1 @ sk_C @ (k4_xboole_0 @ sk_A @ X0)))))),
% 0.47/0.66      inference('sup-', [status(thm)], ['30', '31'])).
% 0.47/0.66  thf('33', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('34', plain,
% 0.47/0.66      (![X0 : $i]:
% 0.47/0.66         (r1_tarski @ (k4_xboole_0 @ sk_A @ X0) @ 
% 0.47/0.66          (k10_relat_1 @ sk_C @ (k9_relat_1 @ sk_C @ (k4_xboole_0 @ sk_A @ X0))))),
% 0.47/0.66      inference('demod', [status(thm)], ['32', '33'])).
% 0.47/0.66  thf('35', plain,
% 0.47/0.66      ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ 
% 0.47/0.66        (k10_relat_1 @ sk_C @ k1_xboole_0))),
% 0.47/0.66      inference('sup+', [status(thm)], ['23', '34'])).
% 0.47/0.66  thf('36', plain,
% 0.47/0.66      (((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0)
% 0.47/0.66        | ~ (v1_funct_1 @ sk_C)
% 0.47/0.66        | ~ (v1_relat_1 @ sk_C))),
% 0.47/0.66      inference('sup+', [status(thm)], ['11', '35'])).
% 0.47/0.66  thf('37', plain, ((v1_funct_1 @ sk_C)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 0.47/0.66      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.66  thf('39', plain, ((r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ k1_xboole_0)),
% 0.47/0.66      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.47/0.66  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.47/0.66  thf('40', plain, (![X11 : $i]: (r1_tarski @ k1_xboole_0 @ X11)),
% 0.47/0.66      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.47/0.66  thf('41', plain,
% 0.47/0.66      (![X0 : $i, X2 : $i]:
% 0.47/0.66         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.47/0.66      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.66  thf('42', plain,
% 0.47/0.66      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.47/0.66      inference('sup-', [status(thm)], ['40', '41'])).
% 0.47/0.66  thf('43', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.47/0.66      inference('sup-', [status(thm)], ['39', '42'])).
% 0.47/0.66  thf('44', plain,
% 0.47/0.66      (![X3 : $i, X4 : $i]:
% 0.47/0.66         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 0.47/0.66      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.47/0.66  thf('45', plain,
% 0.47/0.66      ((((k1_xboole_0) != (k1_xboole_0)) | (r1_tarski @ sk_A @ sk_B))),
% 0.47/0.66      inference('sup-', [status(thm)], ['43', '44'])).
% 0.47/0.66  thf('46', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.47/0.66      inference('simplify', [status(thm)], ['45'])).
% 0.47/0.66  thf('47', plain, ($false), inference('demod', [status(thm)], ['0', '46'])).
% 0.47/0.66  
% 0.47/0.66  % SZS output end Refutation
% 0.47/0.66  
% 0.47/0.67  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
