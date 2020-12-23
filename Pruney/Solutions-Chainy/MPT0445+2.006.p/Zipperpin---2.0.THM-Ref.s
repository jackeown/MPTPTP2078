%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9s8dybRvHL

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:50 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 126 expanded)
%              Number of leaves         :   16 (  45 expanded)
%              Depth                    :   17
%              Number of atoms          :  564 (1113 expanded)
%              Number of equality atoms :   21 (  52 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(fc2_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( v1_relat_1 @ X29 )
      | ( v1_relat_1 @ ( k4_xboole_0 @ X29 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[fc2_relat_1])).

thf(t26_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k2_xboole_0 @ A @ B ) )
            = ( k2_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ( ( k2_relat_1 @ ( k2_xboole_0 @ X32 @ X31 ) )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X32 ) @ ( k2_relat_1 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t26_relat_1])).

thf(t39_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) )
      = ( k2_xboole_0 @ A @ B ) ) )).

thf('2',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('4',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('5',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X1 @ ( k2_xboole_0 @ X0 @ X1 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X1 ) ) @ ( k2_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','9'])).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('12',plain,(
    ! [X31: $i,X32: $i] :
      ( ~ ( v1_relat_1 @ X31 )
      | ( ( k2_relat_1 @ ( k2_xboole_0 @ X32 @ X31 ) )
        = ( k2_xboole_0 @ ( k2_relat_1 @ X32 ) @ ( k2_relat_1 @ X31 ) ) )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t26_relat_1])).

thf(t43_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      | ~ ( r1_tarski @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_relat_1 @ X1 ) ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_relat_1 @ ( k2_xboole_0 @ X1 @ X0 ) ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ ( k2_relat_1 @ X1 ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k4_xboole_0 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X1 ) ) @ ( k2_relat_1 @ X1 ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','15'])).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','8'])).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r1_tarski @ X8 @ ( k2_xboole_0 @ X9 @ X10 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ X0 @ ( k2_xboole_0 @ X1 @ ( k2_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('22',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      | ~ ( r1_tarski @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ X2 @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 ) @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
        = ( k4_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X3: $i,X4: $i] :
      ( ( k2_xboole_0 @ X3 @ ( k4_xboole_0 @ X4 @ X3 ) )
      = ( k2_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t39_xboole_1])).

thf('28',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['3'])).

thf('29',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X7 )
      | ~ ( r1_tarski @ X5 @ ( k2_xboole_0 @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t43_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ X0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 ) @ ( k4_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X1 @ X0 ) @ X1 )
      = ( k4_xboole_0 @ ( k4_xboole_0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k2_xboole_0 @ X0 @ X1 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k4_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 )
      = ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X1 ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['16','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ X1 ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) ) )
      | ~ ( v1_relat_1 @ ( k4_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['0','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf(t28_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t28_relat_1])).

thf('40',plain,(
    ~ ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ sk_A @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('41',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k6_subset_1 @ X27 @ X28 )
      = ( k4_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('42',plain,(
    ! [X27: $i,X28: $i] :
      ( ( k6_subset_1 @ X27 @ X28 )
      = ( k4_xboole_0 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('43',plain,(
    ~ ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['44','45','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9s8dybRvHL
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:46:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.65  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.65  % Solved by: fo/fo7.sh
% 0.45/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.65  % done 321 iterations in 0.199s
% 0.45/0.65  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.65  % SZS output start Refutation
% 0.45/0.65  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.45/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.65  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.65  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.65  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.45/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.65  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.45/0.65  thf(fc2_relat_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k4_xboole_0 @ A @ B ) ) ))).
% 0.45/0.65  thf('0', plain,
% 0.45/0.65      (![X29 : $i, X30 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X29) | (v1_relat_1 @ (k4_xboole_0 @ X29 @ X30)))),
% 0.45/0.65      inference('cnf', [status(esa)], [fc2_relat_1])).
% 0.45/0.65  thf(t26_relat_1, axiom,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( v1_relat_1 @ A ) =>
% 0.45/0.65       ( ![B:$i]:
% 0.45/0.65         ( ( v1_relat_1 @ B ) =>
% 0.45/0.65           ( ( k2_relat_1 @ ( k2_xboole_0 @ A @ B ) ) =
% 0.45/0.65             ( k2_xboole_0 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 0.45/0.65  thf('1', plain,
% 0.45/0.65      (![X31 : $i, X32 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X31)
% 0.45/0.65          | ((k2_relat_1 @ (k2_xboole_0 @ X32 @ X31))
% 0.45/0.65              = (k2_xboole_0 @ (k2_relat_1 @ X32) @ (k2_relat_1 @ X31)))
% 0.45/0.65          | ~ (v1_relat_1 @ X32))),
% 0.45/0.65      inference('cnf', [status(esa)], [t26_relat_1])).
% 0.45/0.65  thf(t39_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( k2_xboole_0 @ A @ ( k4_xboole_0 @ B @ A ) ) = ( k2_xboole_0 @ A @ B ) ))).
% 0.45/0.65  thf('2', plain,
% 0.45/0.65      (![X3 : $i, X4 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3))
% 0.45/0.65           = (k2_xboole_0 @ X3 @ X4))),
% 0.45/0.65      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.45/0.65  thf(d10_xboole_0, axiom,
% 0.45/0.65    (![A:$i,B:$i]:
% 0.45/0.65     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.65  thf('3', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.45/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.65  thf('4', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.45/0.65      inference('simplify', [status(thm)], ['3'])).
% 0.45/0.65  thf(t44_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.45/0.65       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.45/0.65  thf('5', plain,
% 0.45/0.65      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.65         ((r1_tarski @ X8 @ (k2_xboole_0 @ X9 @ X10))
% 0.45/0.65          | ~ (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X10))),
% 0.45/0.65      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.45/0.65  thf('6', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.65  thf('7', plain,
% 0.45/0.65      (![X3 : $i, X4 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3))
% 0.45/0.65           = (k2_xboole_0 @ X3 @ X4))),
% 0.45/0.65      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.45/0.65  thf('8', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]: (r1_tarski @ X1 @ (k2_xboole_0 @ X0 @ X1))),
% 0.45/0.65      inference('demod', [status(thm)], ['6', '7'])).
% 0.45/0.65  thf('9', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['2', '8'])).
% 0.45/0.65  thf('10', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((r1_tarski @ (k4_xboole_0 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X1)) @ 
% 0.45/0.65           (k2_relat_1 @ (k2_xboole_0 @ X1 @ X0)))
% 0.45/0.65          | ~ (v1_relat_1 @ X1)
% 0.45/0.65          | ~ (v1_relat_1 @ X0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['1', '9'])).
% 0.45/0.65  thf('11', plain,
% 0.45/0.65      (![X3 : $i, X4 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3))
% 0.45/0.65           = (k2_xboole_0 @ X3 @ X4))),
% 0.45/0.65      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.45/0.65  thf('12', plain,
% 0.45/0.65      (![X31 : $i, X32 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X31)
% 0.45/0.65          | ((k2_relat_1 @ (k2_xboole_0 @ X32 @ X31))
% 0.45/0.65              = (k2_xboole_0 @ (k2_relat_1 @ X32) @ (k2_relat_1 @ X31)))
% 0.45/0.65          | ~ (v1_relat_1 @ X32))),
% 0.45/0.65      inference('cnf', [status(esa)], [t26_relat_1])).
% 0.45/0.65  thf(t43_xboole_1, axiom,
% 0.45/0.65    (![A:$i,B:$i,C:$i]:
% 0.45/0.65     ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) =>
% 0.45/0.65       ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) ))).
% 0.45/0.65  thf('13', plain,
% 0.45/0.65      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.65         ((r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.45/0.65          | ~ (r1_tarski @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.45/0.65  thf('14', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65         (~ (r1_tarski @ X2 @ (k2_relat_1 @ (k2_xboole_0 @ X1 @ X0)))
% 0.45/0.65          | ~ (v1_relat_1 @ X1)
% 0.45/0.65          | ~ (v1_relat_1 @ X0)
% 0.45/0.65          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_relat_1 @ X1)) @ 
% 0.45/0.65             (k2_relat_1 @ X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['12', '13'])).
% 0.45/0.65  thf('15', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65         (~ (r1_tarski @ X2 @ (k2_relat_1 @ (k2_xboole_0 @ X1 @ X0)))
% 0.45/0.65          | (r1_tarski @ (k4_xboole_0 @ X2 @ (k2_relat_1 @ X1)) @ 
% 0.45/0.65             (k2_relat_1 @ (k4_xboole_0 @ X0 @ X1)))
% 0.45/0.65          | ~ (v1_relat_1 @ (k4_xboole_0 @ X0 @ X1))
% 0.45/0.65          | ~ (v1_relat_1 @ X1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['11', '14'])).
% 0.45/0.65  thf('16', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X0)
% 0.45/0.65          | ~ (v1_relat_1 @ X1)
% 0.45/0.65          | ~ (v1_relat_1 @ X1)
% 0.45/0.65          | ~ (v1_relat_1 @ (k4_xboole_0 @ X0 @ X1))
% 0.45/0.65          | (r1_tarski @ 
% 0.45/0.65             (k4_xboole_0 @ 
% 0.45/0.65              (k4_xboole_0 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X1)) @ 
% 0.45/0.65              (k2_relat_1 @ X1)) @ 
% 0.45/0.65             (k2_relat_1 @ (k4_xboole_0 @ X0 @ X1))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['10', '15'])).
% 0.45/0.65  thf('17', plain,
% 0.45/0.65      (![X3 : $i, X4 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3))
% 0.45/0.65           = (k2_xboole_0 @ X3 @ X4))),
% 0.45/0.65      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.45/0.65  thf('18', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['2', '8'])).
% 0.45/0.65  thf('19', plain,
% 0.45/0.65      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.45/0.65         ((r1_tarski @ X8 @ (k2_xboole_0 @ X9 @ X10))
% 0.45/0.65          | ~ (r1_tarski @ (k4_xboole_0 @ X8 @ X9) @ X10))),
% 0.45/0.65      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.45/0.65  thf('20', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (r1_tarski @ X0 @ (k2_xboole_0 @ X1 @ (k2_xboole_0 @ X1 @ X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['18', '19'])).
% 0.45/0.65  thf('21', plain,
% 0.45/0.65      (![X3 : $i, X4 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3))
% 0.45/0.65           = (k2_xboole_0 @ X3 @ X4))),
% 0.45/0.65      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.45/0.65  thf('22', plain,
% 0.45/0.65      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.65         ((r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.45/0.65          | ~ (r1_tarski @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.45/0.65  thf('23', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.65         (~ (r1_tarski @ X2 @ (k2_xboole_0 @ X1 @ X0))
% 0.45/0.65          | (r1_tarski @ (k4_xboole_0 @ X2 @ X1) @ (k4_xboole_0 @ X0 @ X1)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['21', '22'])).
% 0.45/0.65  thf('24', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ 
% 0.45/0.65          (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1))),
% 0.45/0.65      inference('sup-', [status(thm)], ['20', '23'])).
% 0.45/0.65  thf('25', plain,
% 0.45/0.65      (![X0 : $i, X2 : $i]:
% 0.45/0.65         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.45/0.65      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.45/0.65  thf('26', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0) @ 
% 0.45/0.65             (k4_xboole_0 @ X1 @ X0))
% 0.45/0.65          | ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 0.45/0.65              = (k4_xboole_0 @ X1 @ X0)))),
% 0.45/0.65      inference('sup-', [status(thm)], ['24', '25'])).
% 0.45/0.65  thf('27', plain,
% 0.45/0.65      (![X3 : $i, X4 : $i]:
% 0.45/0.65         ((k2_xboole_0 @ X3 @ (k4_xboole_0 @ X4 @ X3))
% 0.45/0.65           = (k2_xboole_0 @ X3 @ X4))),
% 0.45/0.65      inference('cnf', [status(esa)], [t39_xboole_1])).
% 0.45/0.65  thf('28', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.45/0.65      inference('simplify', [status(thm)], ['3'])).
% 0.45/0.65  thf('29', plain,
% 0.45/0.65      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.65         ((r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X7)
% 0.45/0.65          | ~ (r1_tarski @ X5 @ (k2_xboole_0 @ X6 @ X7)))),
% 0.45/0.65      inference('cnf', [status(esa)], [t43_xboole_1])).
% 0.45/0.65  thf('30', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ X0)),
% 0.45/0.65      inference('sup-', [status(thm)], ['28', '29'])).
% 0.45/0.65  thf('31', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (r1_tarski @ (k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1) @ 
% 0.45/0.65          (k4_xboole_0 @ X0 @ X1))),
% 0.45/0.65      inference('sup+', [status(thm)], ['27', '30'])).
% 0.45/0.65  thf('32', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 0.45/0.65           = (k4_xboole_0 @ X1 @ X0))),
% 0.45/0.65      inference('demod', [status(thm)], ['26', '31'])).
% 0.45/0.65  thf('33', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X1 @ X0) @ X1)
% 0.45/0.65           = (k4_xboole_0 @ (k4_xboole_0 @ X0 @ X1) @ X1))),
% 0.45/0.65      inference('sup+', [status(thm)], ['17', '32'])).
% 0.45/0.65  thf('34', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((k4_xboole_0 @ (k2_xboole_0 @ X0 @ X1) @ X0)
% 0.45/0.65           = (k4_xboole_0 @ X1 @ X0))),
% 0.45/0.65      inference('demod', [status(thm)], ['26', '31'])).
% 0.45/0.65  thf('35', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((k4_xboole_0 @ (k4_xboole_0 @ X1 @ X0) @ X0)
% 0.45/0.65           = (k4_xboole_0 @ X1 @ X0))),
% 0.45/0.65      inference('sup+', [status(thm)], ['33', '34'])).
% 0.45/0.65  thf('36', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X0)
% 0.45/0.65          | ~ (v1_relat_1 @ X1)
% 0.45/0.65          | ~ (v1_relat_1 @ X1)
% 0.45/0.65          | ~ (v1_relat_1 @ (k4_xboole_0 @ X0 @ X1))
% 0.45/0.65          | (r1_tarski @ 
% 0.45/0.65             (k4_xboole_0 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X1)) @ 
% 0.45/0.65             (k2_relat_1 @ (k4_xboole_0 @ X0 @ X1))))),
% 0.45/0.65      inference('demod', [status(thm)], ['16', '35'])).
% 0.45/0.65  thf('37', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((r1_tarski @ (k4_xboole_0 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ X1)) @ 
% 0.45/0.65           (k2_relat_1 @ (k4_xboole_0 @ X0 @ X1)))
% 0.45/0.65          | ~ (v1_relat_1 @ (k4_xboole_0 @ X0 @ X1))
% 0.45/0.65          | ~ (v1_relat_1 @ X1)
% 0.45/0.65          | ~ (v1_relat_1 @ X0))),
% 0.45/0.65      inference('simplify', [status(thm)], ['36'])).
% 0.45/0.65  thf('38', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         (~ (v1_relat_1 @ X1)
% 0.45/0.65          | ~ (v1_relat_1 @ X1)
% 0.45/0.65          | ~ (v1_relat_1 @ X0)
% 0.45/0.65          | (r1_tarski @ 
% 0.45/0.65             (k4_xboole_0 @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0)) @ 
% 0.45/0.65             (k2_relat_1 @ (k4_xboole_0 @ X1 @ X0))))),
% 0.45/0.65      inference('sup-', [status(thm)], ['0', '37'])).
% 0.45/0.65  thf('39', plain,
% 0.45/0.65      (![X0 : $i, X1 : $i]:
% 0.45/0.65         ((r1_tarski @ (k4_xboole_0 @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0)) @ 
% 0.45/0.65           (k2_relat_1 @ (k4_xboole_0 @ X1 @ X0)))
% 0.45/0.65          | ~ (v1_relat_1 @ X0)
% 0.45/0.65          | ~ (v1_relat_1 @ X1))),
% 0.45/0.65      inference('simplify', [status(thm)], ['38'])).
% 0.45/0.65  thf(t28_relat_1, conjecture,
% 0.45/0.65    (![A:$i]:
% 0.45/0.65     ( ( v1_relat_1 @ A ) =>
% 0.45/0.65       ( ![B:$i]:
% 0.45/0.65         ( ( v1_relat_1 @ B ) =>
% 0.45/0.65           ( r1_tarski @
% 0.45/0.65             ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ 
% 0.45/0.65             ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.45/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.65    (~( ![A:$i]:
% 0.45/0.65        ( ( v1_relat_1 @ A ) =>
% 0.45/0.65          ( ![B:$i]:
% 0.45/0.65            ( ( v1_relat_1 @ B ) =>
% 0.45/0.65              ( r1_tarski @
% 0.45/0.65                ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ 
% 0.45/0.65                ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ) )),
% 0.45/0.65    inference('cnf.neg', [status(esa)], [t28_relat_1])).
% 0.45/0.65  thf('40', plain,
% 0.45/0.65      (~ (r1_tarski @ 
% 0.45/0.65          (k6_subset_1 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B)) @ 
% 0.45/0.65          (k2_relat_1 @ (k6_subset_1 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf(redefinition_k6_subset_1, axiom,
% 0.45/0.65    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.45/0.65  thf('41', plain,
% 0.45/0.65      (![X27 : $i, X28 : $i]:
% 0.45/0.65         ((k6_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))),
% 0.45/0.65      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.45/0.65  thf('42', plain,
% 0.45/0.65      (![X27 : $i, X28 : $i]:
% 0.45/0.65         ((k6_subset_1 @ X27 @ X28) = (k4_xboole_0 @ X27 @ X28))),
% 0.45/0.65      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.45/0.65  thf('43', plain,
% 0.45/0.65      (~ (r1_tarski @ 
% 0.45/0.65          (k4_xboole_0 @ (k2_relat_1 @ sk_A) @ (k2_relat_1 @ sk_B)) @ 
% 0.45/0.65          (k2_relat_1 @ (k4_xboole_0 @ sk_A @ sk_B)))),
% 0.45/0.65      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.45/0.65  thf('44', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 0.45/0.65      inference('sup-', [status(thm)], ['39', '43'])).
% 0.45/0.65  thf('45', plain, ((v1_relat_1 @ sk_A)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('46', plain, ((v1_relat_1 @ sk_B)),
% 0.45/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.65  thf('47', plain, ($false),
% 0.45/0.65      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.45/0.65  
% 0.45/0.65  % SZS output end Refutation
% 0.45/0.65  
% 0.49/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
