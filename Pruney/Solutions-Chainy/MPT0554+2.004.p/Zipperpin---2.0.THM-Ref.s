%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4Ji7RoBDDg

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:42:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 109 expanded)
%              Number of leaves         :   23 (  43 expanded)
%              Depth                    :   17
%              Number of atoms          :  529 ( 767 expanded)
%              Number of equality atoms :   22 (  31 expanded)
%              Maximal formula depth    :   11 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t153_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( k9_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf('0',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k9_relat_1 @ X26 @ ( k2_xboole_0 @ X27 @ X28 ) )
        = ( k2_xboole_0 @ ( k9_relat_1 @ X26 @ X27 ) @ ( k9_relat_1 @ X26 @ X28 ) ) )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t153_relat_1])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t156_relat_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_tarski @ A @ B )
       => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( v1_relat_1 @ C )
       => ( ( r1_tarski @ A @ B )
         => ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t156_relat_1])).

thf('2',plain,(
    r1_tarski @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf(t7_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ) )).

thf('6',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('7',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X2 @ X3 )
      | ( r2_hidden @ X2 @ X4 )
      | ~ ( r1_tarski @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k2_xboole_0 @ sk_B @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r1_tarski @ X3 @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X5 @ X3 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) )
      | ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_A @ ( k2_xboole_0 @ sk_B @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('13',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      | ~ ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ sk_A @ sk_B ) @ X0 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('16',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      | ~ ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t3_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('18',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X1 @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('20',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('21',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['17','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k4_xboole_0 @ X0 @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k4_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','25'])).

thf(t155_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( r1_tarski @ ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) @ ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ) )).

thf('27',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k6_subset_1 @ ( k9_relat_1 @ X29 @ X30 ) @ ( k9_relat_1 @ X29 @ X31 ) ) @ ( k9_relat_1 @ X29 @ ( k6_subset_1 @ X30 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t155_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('28',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k6_subset_1 @ X24 @ X25 )
      = ( k4_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('29',plain,(
    ! [X24: $i,X25: $i] :
      ( ( k6_subset_1 @ X24 @ X25 )
      = ( k4_xboole_0 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('30',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k9_relat_1 @ X29 @ X30 ) @ ( k9_relat_1 @ X29 @ X31 ) ) @ ( k9_relat_1 @ X29 @ ( k4_xboole_0 @ X30 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) ) @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['26','30'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('32',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r1_tarski @ X19 @ ( k2_xboole_0 @ X20 @ X21 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X19 @ X20 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k2_xboole_0 @ ( k9_relat_1 @ X0 @ sk_B ) @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(commutativity_k2_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ B )
      = ( k2_xboole_0 @ B @ A ) ) )).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k2_xboole_0 @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) @ ( k9_relat_1 @ X0 @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ sk_B ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['0','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ ( k2_xboole_0 @ k1_xboole_0 @ sk_B ) ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X15: $i] :
      ( ( k4_xboole_0 @ X15 @ k1_xboole_0 )
      = X15 ) ),
    inference(cnf,[status(esa)],[t3_boole])).

thf('39',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ( X12 != X13 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('40',plain,(
    ! [X13: $i] :
      ( r1_tarski @ X13 @ X13 ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X16 @ X17 ) @ X18 )
      | ~ ( r1_tarski @ X16 @ ( k2_xboole_0 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ k1_xboole_0 @ X0 ) @ X0 ) ),
    inference('sup+',[status(thm)],['38','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_xboole_0 @ X1 @ X0 )
      = ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[commutativity_k2_xboole_0])).

thf('45',plain,(
    ! [X22: $i,X23: $i] :
      ( r1_tarski @ X22 @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_1])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X12: $i,X14: $i] :
      ( ( X12 = X14 )
      | ~ ( r1_tarski @ X14 @ X12 )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_xboole_0 @ X1 @ X0 ) @ X0 )
      | ( ( k2_xboole_0 @ X1 @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_xboole_0 @ k1_xboole_0 @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['37','49'])).

thf('51',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ ( k9_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    $false ),
    inference(demod,[status(thm)],['52','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4Ji7RoBDDg
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:25:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 270 iterations in 0.082s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.20/0.53  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.20/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.53  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(t153_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ C ) =>
% 0.20/0.53       ( ( k9_relat_1 @ C @ ( k2_xboole_0 @ A @ B ) ) =
% 0.20/0.53         ( k2_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.53         (((k9_relat_1 @ X26 @ (k2_xboole_0 @ X27 @ X28))
% 0.20/0.53            = (k2_xboole_0 @ (k9_relat_1 @ X26 @ X27) @ 
% 0.20/0.53               (k9_relat_1 @ X26 @ X28)))
% 0.20/0.53          | ~ (v1_relat_1 @ X26))),
% 0.20/0.53      inference('cnf', [status(esa)], [t153_relat_1])).
% 0.20/0.53  thf(d3_tarski, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      (![X3 : $i, X5 : $i]:
% 0.20/0.53         ((r1_tarski @ X3 @ X5) | (r2_hidden @ (sk_C @ X5 @ X3) @ X3))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf(t156_relat_1, conjecture,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ C ) =>
% 0.20/0.53       ( ( r1_tarski @ A @ B ) =>
% 0.20/0.53         ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.53        ( ( v1_relat_1 @ C ) =>
% 0.20/0.53          ( ( r1_tarski @ A @ B ) =>
% 0.20/0.53            ( r1_tarski @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t156_relat_1])).
% 0.20/0.53  thf('2', plain, ((r1_tarski @ sk_A @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('3', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X2 @ X3)
% 0.20/0.53          | (r2_hidden @ X2 @ X4)
% 0.20/0.53          | ~ (r1_tarski @ X3 @ X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X0 : $i]: ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r1_tarski @ sk_A @ X0) | (r2_hidden @ (sk_C @ X0 @ sk_A) @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '4'])).
% 0.20/0.53  thf(t7_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( r1_tarski @ A @ ( k2_xboole_0 @ A @ B ) ))).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 0.20/0.53      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X2 @ X3)
% 0.20/0.53          | (r2_hidden @ X2 @ X4)
% 0.20/0.53          | ~ (r1_tarski @ X3 @ X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf('8', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         ((r2_hidden @ X2 @ (k2_xboole_0 @ X1 @ X0)) | ~ (r2_hidden @ X2 @ X1))),
% 0.20/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((r1_tarski @ sk_A @ X0)
% 0.20/0.53          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k2_xboole_0 @ sk_B @ X1)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['5', '8'])).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X3 : $i, X5 : $i]:
% 0.20/0.53         ((r1_tarski @ X3 @ X5) | ~ (r2_hidden @ (sk_C @ X5 @ X3) @ X5))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ X0))
% 0.20/0.53          | (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X0 : $i]: (r1_tarski @ sk_A @ (k2_xboole_0 @ sk_B @ X0))),
% 0.20/0.53      inference('simplify', [status(thm)], ['11'])).
% 0.20/0.53  thf(t43_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.20/0.53       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.53         ((r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.20/0.53          | ~ (r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X0 : $i]: (r1_tarski @ (k4_xboole_0 @ sk_A @ sk_B) @ X0)),
% 0.20/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 0.20/0.53      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.53         ((r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.20/0.53          | ~ (r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf(t3_boole, axiom,
% 0.20/0.53    (![A:$i]: ( ( k4_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.20/0.53  thf('18', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (r1_tarski @ (k4_xboole_0 @ X1 @ X1) @ X0)),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf('20', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.20/0.53      inference('sup+', [status(thm)], ['18', '19'])).
% 0.20/0.53  thf(d10_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X12 : $i, X14 : $i]:
% 0.20/0.53         (((X12) = (X14))
% 0.20/0.53          | ~ (r1_tarski @ X14 @ X12)
% 0.20/0.53          | ~ (r1_tarski @ X12 @ X14))),
% 0.20/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('23', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['17', '22'])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (r1_tarski @ X1 @ (k4_xboole_0 @ X0 @ X0)) | ((X1) = (k1_xboole_0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.53  thf('26', plain, (((k4_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['14', '25'])).
% 0.20/0.53  thf(t155_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ C ) =>
% 0.20/0.53       ( r1_tarski @
% 0.20/0.53         ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) @ 
% 0.20/0.53         ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) ) ))).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.53         ((r1_tarski @ 
% 0.20/0.53           (k6_subset_1 @ (k9_relat_1 @ X29 @ X30) @ (k9_relat_1 @ X29 @ X31)) @ 
% 0.20/0.53           (k9_relat_1 @ X29 @ (k6_subset_1 @ X30 @ X31)))
% 0.20/0.53          | ~ (v1_relat_1 @ X29))),
% 0.20/0.53      inference('cnf', [status(esa)], [t155_relat_1])).
% 0.20/0.53  thf(redefinition_k6_subset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (![X24 : $i, X25 : $i]:
% 0.20/0.53         ((k6_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (![X24 : $i, X25 : $i]:
% 0.20/0.53         ((k6_subset_1 @ X24 @ X25) = (k4_xboole_0 @ X24 @ X25))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.53         ((r1_tarski @ 
% 0.20/0.53           (k4_xboole_0 @ (k9_relat_1 @ X29 @ X30) @ (k9_relat_1 @ X29 @ X31)) @ 
% 0.20/0.53           (k9_relat_1 @ X29 @ (k4_xboole_0 @ X30 @ X31)))
% 0.20/0.53          | ~ (v1_relat_1 @ X29))),
% 0.20/0.53      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r1_tarski @ 
% 0.20/0.53           (k4_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B)) @ 
% 0.20/0.53           (k9_relat_1 @ X0 @ k1_xboole_0))
% 0.20/0.53          | ~ (v1_relat_1 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['26', '30'])).
% 0.20/0.53  thf(t44_xboole_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.20/0.53       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.53         ((r1_tarski @ X19 @ (k2_xboole_0 @ X20 @ X21))
% 0.20/0.53          | ~ (r1_tarski @ (k4_xboole_0 @ X19 @ X20) @ X21))),
% 0.20/0.53      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | (r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ 
% 0.20/0.53             (k2_xboole_0 @ (k9_relat_1 @ X0 @ sk_B) @ 
% 0.20/0.53              (k9_relat_1 @ X0 @ k1_xboole_0))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.53  thf(commutativity_k2_xboole_0, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ( k2_xboole_0 @ A @ B ) = ( k2_xboole_0 @ B @ A ) ))).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | (r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ 
% 0.20/0.53             (k2_xboole_0 @ (k9_relat_1 @ X0 @ k1_xboole_0) @ 
% 0.20/0.53              (k9_relat_1 @ X0 @ sk_B))))),
% 0.20/0.53      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ 
% 0.20/0.53           (k9_relat_1 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ sk_B)))
% 0.20/0.53          | ~ (v1_relat_1 @ X0)
% 0.20/0.53          | ~ (v1_relat_1 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['0', '35'])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | (r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ 
% 0.20/0.53             (k9_relat_1 @ X0 @ (k2_xboole_0 @ k1_xboole_0 @ sk_B))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['36'])).
% 0.20/0.53  thf('38', plain, (![X15 : $i]: ((k4_xboole_0 @ X15 @ k1_xboole_0) = (X15))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_boole])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      (![X12 : $i, X13 : $i]: ((r1_tarski @ X12 @ X13) | ((X12) != (X13)))),
% 0.20/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.53  thf('40', plain, (![X13 : $i]: (r1_tarski @ X13 @ X13)),
% 0.20/0.53      inference('simplify', [status(thm)], ['39'])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.53         ((r1_tarski @ (k4_xboole_0 @ X16 @ X17) @ X18)
% 0.20/0.53          | ~ (r1_tarski @ X16 @ (k2_xboole_0 @ X17 @ X18)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 0.20/0.53      inference('sup-', [status(thm)], ['40', '41'])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      (![X0 : $i]: (r1_tarski @ (k2_xboole_0 @ k1_xboole_0 @ X0) @ X0)),
% 0.20/0.53      inference('sup+', [status(thm)], ['38', '42'])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: ((k2_xboole_0 @ X1 @ X0) = (k2_xboole_0 @ X0 @ X1))),
% 0.20/0.53      inference('cnf', [status(esa)], [commutativity_k2_xboole_0])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i]: (r1_tarski @ X22 @ (k2_xboole_0 @ X22 @ X23))),
% 0.20/0.53      inference('cnf', [status(esa)], [t7_xboole_1])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]: (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ X0))),
% 0.20/0.53      inference('sup+', [status(thm)], ['44', '45'])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (![X12 : $i, X14 : $i]:
% 0.20/0.53         (((X12) = (X14))
% 0.20/0.53          | ~ (r1_tarski @ X14 @ X12)
% 0.20/0.53          | ~ (r1_tarski @ X12 @ X14))),
% 0.20/0.53      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         (~ (r1_tarski @ (k2_xboole_0 @ X1 @ X0) @ X0)
% 0.20/0.53          | ((k2_xboole_0 @ X1 @ X0) = (X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['46', '47'])).
% 0.20/0.53  thf('49', plain, (![X0 : $i]: ((k2_xboole_0 @ k1_xboole_0 @ X0) = (X0))),
% 0.20/0.53      inference('sup-', [status(thm)], ['43', '48'])).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         (~ (v1_relat_1 @ X0)
% 0.20/0.53          | (r1_tarski @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B)))),
% 0.20/0.53      inference('demod', [status(thm)], ['37', '49'])).
% 0.20/0.53  thf('51', plain,
% 0.20/0.53      (~ (r1_tarski @ (k9_relat_1 @ sk_C_1 @ sk_A) @ 
% 0.20/0.53          (k9_relat_1 @ sk_C_1 @ sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('52', plain, (~ (v1_relat_1 @ sk_C_1)),
% 0.20/0.53      inference('sup-', [status(thm)], ['50', '51'])).
% 0.20/0.53  thf('53', plain, ((v1_relat_1 @ sk_C_1)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('54', plain, ($false), inference('demod', [status(thm)], ['52', '53'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
