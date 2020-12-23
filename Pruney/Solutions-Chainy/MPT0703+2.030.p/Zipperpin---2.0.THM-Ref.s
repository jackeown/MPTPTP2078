%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tJlKAMJrXQ

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:53 EST 2020

% Result     : Theorem 0.64s
% Output     : Refutation 0.64s
% Verified   : 
% Statistics : Number of formulae       :   73 (  94 expanded)
%              Number of leaves         :   26 (  38 expanded)
%              Depth                    :   15
%              Number of atoms          :  479 ( 742 expanded)
%              Number of equality atoms :   25 (  33 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t158_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) )
          & ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) )
       => ( r1_tarski @ A @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) )
            & ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) )
         => ( r1_tarski @ A @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t158_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t138_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ) )).

thf('1',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k10_relat_1 @ X33 @ ( k6_subset_1 @ X34 @ X35 ) )
        = ( k6_subset_1 @ ( k10_relat_1 @ X33 @ X34 ) @ ( k10_relat_1 @ X33 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t138_funct_1])).

thf('2',plain,(
    r1_tarski @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t12_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( ( k2_xboole_0 @ A @ B )
        = B ) ) )).

thf('3',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_xboole_0 @ X7 @ X6 )
        = X6 )
      | ~ ( r1_tarski @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t12_xboole_1])).

thf('4',plain,
    ( ( k2_xboole_0 @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = ( k10_relat_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('5',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_tarski @ X27 @ ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X3 @ X5 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ X2 @ ( k2_xboole_0 @ ( k2_xboole_0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X15 @ X16 ) @ X17 )
      | ~ ( r1_tarski @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('9',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k6_subset_1 @ X29 @ X30 )
      = ( k4_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('10',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X15 @ X16 ) @ X17 )
      | ~ ( r1_tarski @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X2 @ ( k2_xboole_0 @ X2 @ X1 ) ) @ X0 ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X27: $i,X28: $i] :
      ( r1_tarski @ X27 @ ( k2_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('13',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ X15 @ X16 ) @ X17 )
      | ~ ( r1_tarski @ X15 @ ( k2_xboole_0 @ X16 @ X17 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k6_subset_1 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t38_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) )
     => ( A = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13 = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ ( k4_xboole_0 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t38_xboole_1])).

thf('16',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k6_subset_1 @ X29 @ X30 )
      = ( k4_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('17',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13 = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ ( k6_subset_1 @ X14 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k6_subset_1 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13 = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ ( k6_subset_1 @ X14 @ X13 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k6_subset_1 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','20'])).

thf('22',plain,
    ( ( k6_subset_1 @ ( k10_relat_1 @ sk_C @ sk_A ) @ ( k10_relat_1 @ sk_C @ sk_B ) )
    = k1_xboole_0 ),
    inference('sup+',[status(thm)],['4','21'])).

thf('23',plain,
    ( ( ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['1','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k10_relat_1 @ sk_C @ ( k6_subset_1 @ sk_A @ sk_B ) )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['23','24','25'])).

thf(t173_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k10_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('27',plain,(
    ! [X31: $i,X32: $i] :
      ( ( ( k10_relat_1 @ X31 @ X32 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k2_relat_1 @ X31 ) @ X32 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('28',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_C ) @ ( k6_subset_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k2_relat_1 @ sk_C ) @ ( k6_subset_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    r1_xboole_0 @ ( k2_relat_1 @ sk_C ) @ ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t63_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_xboole_0 @ B @ C ) )
     => ( r1_xboole_0 @ A @ C ) ) )).

thf('33',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ X21 @ X22 )
      | ~ ( r1_xboole_0 @ X22 @ X23 )
      | ( r1_xboole_0 @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t63_xboole_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ sk_A @ X0 )
      | ~ ( r1_xboole_0 @ ( k2_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    r1_xboole_0 @ sk_A @ ( k6_subset_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['36'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('38',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_tarski @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X18 @ X19 ) @ X20 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('39',plain,(
    ! [X29: $i,X30: $i] :
      ( ( k6_subset_1 @ X29 @ X30 )
      = ( k4_xboole_0 @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('40',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r1_tarski @ X18 @ ( k2_xboole_0 @ X19 @ X20 ) )
      | ~ ( r1_tarski @ ( k6_subset_1 @ X18 @ X19 ) @ X20 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k6_subset_1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf(t73_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('42',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( r1_tarski @ X24 @ X25 )
      | ~ ( r1_tarski @ X24 @ ( k2_xboole_0 @ X25 @ X26 ) )
      | ~ ( r1_xboole_0 @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ ( k6_subset_1 @ X1 @ X0 ) )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference('sup-',[status(thm)],['35','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['0','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tJlKAMJrXQ
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:24:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.64/0.85  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.64/0.85  % Solved by: fo/fo7.sh
% 0.64/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.64/0.85  % done 931 iterations in 0.400s
% 0.64/0.85  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.64/0.85  % SZS output start Refutation
% 0.64/0.85  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.64/0.85  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.64/0.85  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.64/0.85  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.64/0.85  thf(sk_C_type, type, sk_C: $i).
% 0.64/0.85  thf(sk_B_type, type, sk_B: $i).
% 0.64/0.85  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.64/0.85  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.64/0.85  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.64/0.85  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.64/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.64/0.85  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.64/0.85  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.64/0.85  thf(t158_funct_1, conjecture,
% 0.64/0.85    (![A:$i,B:$i,C:$i]:
% 0.64/0.85     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.64/0.85       ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.64/0.85           ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.64/0.85         ( r1_tarski @ A @ B ) ) ))).
% 0.64/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.64/0.85    (~( ![A:$i,B:$i,C:$i]:
% 0.64/0.85        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.64/0.85          ( ( ( r1_tarski @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) & 
% 0.64/0.85              ( r1_tarski @ A @ ( k2_relat_1 @ C ) ) ) =>
% 0.64/0.85            ( r1_tarski @ A @ B ) ) ) )),
% 0.64/0.85    inference('cnf.neg', [status(esa)], [t158_funct_1])).
% 0.64/0.85  thf('0', plain, (~ (r1_tarski @ sk_A @ sk_B)),
% 0.64/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.85  thf(t138_funct_1, axiom,
% 0.64/0.85    (![A:$i,B:$i,C:$i]:
% 0.64/0.85     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.64/0.85       ( ( k10_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 0.64/0.85         ( k6_subset_1 @ ( k10_relat_1 @ C @ A ) @ ( k10_relat_1 @ C @ B ) ) ) ))).
% 0.64/0.85  thf('1', plain,
% 0.64/0.85      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.64/0.85         (((k10_relat_1 @ X33 @ (k6_subset_1 @ X34 @ X35))
% 0.64/0.85            = (k6_subset_1 @ (k10_relat_1 @ X33 @ X34) @ 
% 0.64/0.85               (k10_relat_1 @ X33 @ X35)))
% 0.64/0.85          | ~ (v1_funct_1 @ X33)
% 0.64/0.85          | ~ (v1_relat_1 @ X33))),
% 0.64/0.85      inference('cnf', [status(esa)], [t138_funct_1])).
% 0.64/0.85  thf('2', plain,
% 0.64/0.85      ((r1_tarski @ (k10_relat_1 @ sk_C @ sk_A) @ (k10_relat_1 @ sk_C @ sk_B))),
% 0.64/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.85  thf(t12_xboole_1, axiom,
% 0.64/0.85    (![A:$i,B:$i]:
% 0.64/0.85     ( ( r1_tarski @ A @ B ) => ( ( k2_xboole_0 @ A @ B ) = ( B ) ) ))).
% 0.64/0.85  thf('3', plain,
% 0.64/0.85      (![X6 : $i, X7 : $i]:
% 0.64/0.85         (((k2_xboole_0 @ X7 @ X6) = (X6)) | ~ (r1_tarski @ X7 @ X6))),
% 0.64/0.85      inference('cnf', [status(esa)], [t12_xboole_1])).
% 0.64/0.85  thf('4', plain,
% 0.64/0.85      (((k2_xboole_0 @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 0.64/0.85         (k10_relat_1 @ sk_C @ sk_B)) = (k10_relat_1 @ sk_C @ sk_B))),
% 0.64/0.85      inference('sup-', [status(thm)], ['2', '3'])).
% 0.64/0.85  thf(t7_xboole_1, axiom,
% 0.64/0.85    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.64/0.85  thf('5', plain,
% 0.64/0.85      (![X27 : $i, X28 : $i]: (r1_tarski @ X27 @ (k2_xboole_0 @ X27 @ X28))),
% 0.64/0.85      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.64/0.85  thf(t11_xboole_1, axiom,
% 0.64/0.85    (![A:$i,B:$i,C:$i]:
% 0.64/0.85     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 0.64/0.85  thf('6', plain,
% 0.64/0.85      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.64/0.85         ((r1_tarski @ X3 @ X4) | ~ (r1_tarski @ (k2_xboole_0 @ X3 @ X5) @ X4))),
% 0.64/0.85      inference('cnf', [status(esa)], [t11_xboole_1])).
% 0.64/0.85  thf('7', plain,
% 0.64/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.85         (r1_tarski @ X2 @ (k2_xboole_0 @ (k2_xboole_0 @ X2 @ X1) @ X0))),
% 0.64/0.85      inference('sup-', [status(thm)], ['5', '6'])).
% 0.64/0.85  thf(t43_xboole_1, axiom,
% 0.64/0.85    (![A:$i,B:$i,C:$i]:
% 0.64/0.85     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.64/0.85       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.64/0.85  thf('8', plain,
% 0.64/0.85      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.64/0.85         ((r1_tarski @ (k4_xboole_0 @ X15 @ X16) @ X17)
% 0.64/0.85          | ~ (r1_tarski @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 0.64/0.85      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.64/0.85  thf(redefinition_k6_subset_1, axiom,
% 0.64/0.85    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.64/0.85  thf('9', plain,
% 0.64/0.85      (![X29 : $i, X30 : $i]:
% 0.64/0.85         ((k6_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))),
% 0.64/0.85      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.64/0.85  thf('10', plain,
% 0.64/0.85      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.64/0.85         ((r1_tarski @ (k6_subset_1 @ X15 @ X16) @ X17)
% 0.64/0.85          | ~ (r1_tarski @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 0.64/0.85      inference('demod', [status(thm)], ['8', '9'])).
% 0.64/0.85  thf('11', plain,
% 0.64/0.85      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.64/0.85         (r1_tarski @ (k6_subset_1 @ X2 @ (k2_xboole_0 @ X2 @ X1)) @ X0)),
% 0.64/0.85      inference('sup-', [status(thm)], ['7', '10'])).
% 0.64/0.85  thf('12', plain,
% 0.64/0.85      (![X27 : $i, X28 : $i]: (r1_tarski @ X27 @ (k2_xboole_0 @ X27 @ X28))),
% 0.64/0.85      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.64/0.85  thf('13', plain,
% 0.64/0.85      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.64/0.85         ((r1_tarski @ (k6_subset_1 @ X15 @ X16) @ X17)
% 0.64/0.85          | ~ (r1_tarski @ X15 @ (k2_xboole_0 @ X16 @ X17)))),
% 0.64/0.85      inference('demod', [status(thm)], ['8', '9'])).
% 0.64/0.85  thf('14', plain,
% 0.64/0.85      (![X0 : $i, X1 : $i]: (r1_tarski @ (k6_subset_1 @ X1 @ X1) @ X0)),
% 0.64/0.85      inference('sup-', [status(thm)], ['12', '13'])).
% 0.64/0.85  thf(t38_xboole_1, axiom,
% 0.64/0.85    (![A:$i,B:$i]:
% 0.64/0.85     ( ( r1_tarski @ A @ ( k4_xboole_0 @ B @ A ) ) =>
% 0.64/0.85       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.64/0.85  thf('15', plain,
% 0.64/0.85      (![X13 : $i, X14 : $i]:
% 0.64/0.85         (((X13) = (k1_xboole_0))
% 0.64/0.85          | ~ (r1_tarski @ X13 @ (k4_xboole_0 @ X14 @ X13)))),
% 0.64/0.85      inference('cnf', [status(esa)], [t38_xboole_1])).
% 0.64/0.85  thf('16', plain,
% 0.64/0.85      (![X29 : $i, X30 : $i]:
% 0.64/0.85         ((k6_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))),
% 0.64/0.85      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.64/0.85  thf('17', plain,
% 0.64/0.85      (![X13 : $i, X14 : $i]:
% 0.64/0.85         (((X13) = (k1_xboole_0))
% 0.64/0.85          | ~ (r1_tarski @ X13 @ (k6_subset_1 @ X14 @ X13)))),
% 0.64/0.85      inference('demod', [status(thm)], ['15', '16'])).
% 0.64/0.85  thf('18', plain, (![X0 : $i]: ((k6_subset_1 @ X0 @ X0) = (k1_xboole_0))),
% 0.64/0.85      inference('sup-', [status(thm)], ['14', '17'])).
% 0.64/0.85  thf('19', plain,
% 0.64/0.85      (![X13 : $i, X14 : $i]:
% 0.64/0.85         (((X13) = (k1_xboole_0))
% 0.64/0.85          | ~ (r1_tarski @ X13 @ (k6_subset_1 @ X14 @ X13)))),
% 0.64/0.85      inference('demod', [status(thm)], ['15', '16'])).
% 0.64/0.85  thf('20', plain,
% 0.64/0.85      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.64/0.85      inference('sup-', [status(thm)], ['18', '19'])).
% 0.64/0.85  thf('21', plain,
% 0.64/0.85      (![X0 : $i, X1 : $i]:
% 0.64/0.85         ((k6_subset_1 @ X1 @ (k2_xboole_0 @ X1 @ X0)) = (k1_xboole_0))),
% 0.64/0.85      inference('sup-', [status(thm)], ['11', '20'])).
% 0.64/0.85  thf('22', plain,
% 0.64/0.85      (((k6_subset_1 @ (k10_relat_1 @ sk_C @ sk_A) @ 
% 0.64/0.85         (k10_relat_1 @ sk_C @ sk_B)) = (k1_xboole_0))),
% 0.64/0.85      inference('sup+', [status(thm)], ['4', '21'])).
% 0.64/0.85  thf('23', plain,
% 0.64/0.85      ((((k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))
% 0.64/0.85        | ~ (v1_relat_1 @ sk_C)
% 0.64/0.85        | ~ (v1_funct_1 @ sk_C))),
% 0.64/0.85      inference('sup+', [status(thm)], ['1', '22'])).
% 0.64/0.85  thf('24', plain, ((v1_relat_1 @ sk_C)),
% 0.64/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.85  thf('25', plain, ((v1_funct_1 @ sk_C)),
% 0.64/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.85  thf('26', plain,
% 0.64/0.85      (((k10_relat_1 @ sk_C @ (k6_subset_1 @ sk_A @ sk_B)) = (k1_xboole_0))),
% 0.64/0.85      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.64/0.85  thf(t173_relat_1, axiom,
% 0.64/0.85    (![A:$i,B:$i]:
% 0.64/0.85     ( ( v1_relat_1 @ B ) =>
% 0.64/0.85       ( ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.64/0.85         ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.64/0.85  thf('27', plain,
% 0.64/0.85      (![X31 : $i, X32 : $i]:
% 0.64/0.85         (((k10_relat_1 @ X31 @ X32) != (k1_xboole_0))
% 0.64/0.85          | (r1_xboole_0 @ (k2_relat_1 @ X31) @ X32)
% 0.64/0.85          | ~ (v1_relat_1 @ X31))),
% 0.64/0.85      inference('cnf', [status(esa)], [t173_relat_1])).
% 0.64/0.85  thf('28', plain,
% 0.64/0.85      ((((k1_xboole_0) != (k1_xboole_0))
% 0.64/0.85        | ~ (v1_relat_1 @ sk_C)
% 0.64/0.85        | (r1_xboole_0 @ (k2_relat_1 @ sk_C) @ (k6_subset_1 @ sk_A @ sk_B)))),
% 0.64/0.85      inference('sup-', [status(thm)], ['26', '27'])).
% 0.64/0.85  thf('29', plain, ((v1_relat_1 @ sk_C)),
% 0.64/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.85  thf('30', plain,
% 0.64/0.85      ((((k1_xboole_0) != (k1_xboole_0))
% 0.64/0.85        | (r1_xboole_0 @ (k2_relat_1 @ sk_C) @ (k6_subset_1 @ sk_A @ sk_B)))),
% 0.64/0.85      inference('demod', [status(thm)], ['28', '29'])).
% 0.64/0.85  thf('31', plain,
% 0.64/0.85      ((r1_xboole_0 @ (k2_relat_1 @ sk_C) @ (k6_subset_1 @ sk_A @ sk_B))),
% 0.64/0.85      inference('simplify', [status(thm)], ['30'])).
% 0.64/0.85  thf('32', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_C))),
% 0.64/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.85  thf(t63_xboole_1, axiom,
% 0.64/0.85    (![A:$i,B:$i,C:$i]:
% 0.64/0.85     ( ( ( r1_tarski @ A @ B ) & ( r1_xboole_0 @ B @ C ) ) =>
% 0.64/0.85       ( r1_xboole_0 @ A @ C ) ))).
% 0.64/0.85  thf('33', plain,
% 0.64/0.85      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.64/0.85         (~ (r1_tarski @ X21 @ X22)
% 0.64/0.85          | ~ (r1_xboole_0 @ X22 @ X23)
% 0.64/0.85          | (r1_xboole_0 @ X21 @ X23))),
% 0.64/0.85      inference('cnf', [status(esa)], [t63_xboole_1])).
% 0.64/0.85  thf('34', plain,
% 0.64/0.85      (![X0 : $i]:
% 0.64/0.85         ((r1_xboole_0 @ sk_A @ X0)
% 0.64/0.85          | ~ (r1_xboole_0 @ (k2_relat_1 @ sk_C) @ X0))),
% 0.64/0.85      inference('sup-', [status(thm)], ['32', '33'])).
% 0.64/0.85  thf('35', plain, ((r1_xboole_0 @ sk_A @ (k6_subset_1 @ sk_A @ sk_B))),
% 0.64/0.85      inference('sup-', [status(thm)], ['31', '34'])).
% 0.64/0.85  thf(d10_xboole_0, axiom,
% 0.64/0.85    (![A:$i,B:$i]:
% 0.64/0.85     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.64/0.85  thf('36', plain,
% 0.64/0.85      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.64/0.85      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.64/0.85  thf('37', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.64/0.85      inference('simplify', [status(thm)], ['36'])).
% 0.64/0.85  thf(t44_xboole_1, axiom,
% 0.64/0.85    (![A:$i,B:$i,C:$i]:
% 0.64/0.85     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.64/0.85       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.64/0.85  thf('38', plain,
% 0.64/0.85      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.64/0.85         ((r1_tarski @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 0.64/0.85          | ~ (r1_tarski @ (k4_xboole_0 @ X18 @ X19) @ X20))),
% 0.64/0.85      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.64/0.85  thf('39', plain,
% 0.64/0.85      (![X29 : $i, X30 : $i]:
% 0.64/0.85         ((k6_subset_1 @ X29 @ X30) = (k4_xboole_0 @ X29 @ X30))),
% 0.64/0.85      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.64/0.85  thf('40', plain,
% 0.64/0.85      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.64/0.85         ((r1_tarski @ X18 @ (k2_xboole_0 @ X19 @ X20))
% 0.64/0.85          | ~ (r1_tarski @ (k6_subset_1 @ X18 @ X19) @ X20))),
% 0.64/0.85      inference('demod', [status(thm)], ['38', '39'])).
% 0.64/0.85  thf('41', plain,
% 0.64/0.85      (![X0 : $i, X1 : $i]:
% 0.64/0.85         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k6_subset_1 @ X1 @ X0)))),
% 0.64/0.85      inference('sup-', [status(thm)], ['37', '40'])).
% 0.64/0.85  thf(t73_xboole_1, axiom,
% 0.64/0.85    (![A:$i,B:$i,C:$i]:
% 0.64/0.85     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 0.64/0.85       ( r1_tarski @ A @ B ) ))).
% 0.64/0.85  thf('42', plain,
% 0.64/0.85      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.64/0.85         ((r1_tarski @ X24 @ X25)
% 0.64/0.85          | ~ (r1_tarski @ X24 @ (k2_xboole_0 @ X25 @ X26))
% 0.64/0.85          | ~ (r1_xboole_0 @ X24 @ X26))),
% 0.64/0.85      inference('cnf', [status(esa)], [t73_xboole_1])).
% 0.64/0.85  thf('43', plain,
% 0.64/0.85      (![X0 : $i, X1 : $i]:
% 0.64/0.85         (~ (r1_xboole_0 @ X1 @ (k6_subset_1 @ X1 @ X0))
% 0.64/0.85          | (r1_tarski @ X1 @ X0))),
% 0.64/0.85      inference('sup-', [status(thm)], ['41', '42'])).
% 0.64/0.85  thf('44', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.64/0.85      inference('sup-', [status(thm)], ['35', '43'])).
% 0.64/0.85  thf('45', plain, ($false), inference('demod', [status(thm)], ['0', '44'])).
% 0.64/0.85  
% 0.64/0.85  % SZS output end Refutation
% 0.64/0.85  
% 0.64/0.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
