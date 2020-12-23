%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oIWkdoyAIf

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:02 EST 2020

% Result     : Theorem 2.40s
% Output     : Refutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   55 (  74 expanded)
%              Number of leaves         :   23 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :  370 ( 554 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   12 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k3_relat_1_type,type,(
    k3_relat_1: $i > $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('0',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('1',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['0'])).

thf(t85_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( r1_tarski @ X33 @ X34 )
      | ( r1_xboole_0 @ X33 @ ( k4_xboole_0 @ X35 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t85_xboole_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_xboole_0 @ X0 @ ( k4_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t31_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ ( k2_xboole_0 @ B @ C ) ) )).

thf('4',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( r1_tarski @ ( k2_xboole_0 @ ( k3_xboole_0 @ X21 @ X22 ) @ ( k3_xboole_0 @ X21 @ X23 ) ) @ ( k2_xboole_0 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t31_xboole_1])).

thf(t11_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ C ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( r1_tarski @ ( k2_xboole_0 @ X12 @ X14 ) @ X13 ) ) ),
    inference(cnf,[status(esa)],[t11_xboole_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ ( k2_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t73_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) )
        & ( r1_xboole_0 @ A @ C ) )
     => ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( r1_tarski @ X30 @ X31 )
      | ~ ( r1_tarski @ X30 @ ( k2_xboole_0 @ X31 @ X32 ) )
      | ~ ( r1_xboole_0 @ X30 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t73_xboole_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k3_xboole_0 @ X2 @ X1 ) @ X0 )
      | ( r1_tarski @ ( k3_xboole_0 @ X2 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf(t31_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf('10',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( v1_relat_1 @ X59 )
      | ( r1_tarski @ ( k3_relat_1 @ X60 ) @ ( k3_relat_1 @ X59 ) )
      | ~ ( r1_tarski @ X60 @ X59 )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('13',plain,(
    ! [X43: $i,X45: $i] :
      ( ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X45 ) )
      | ~ ( r1_tarski @ X43 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('15',plain,(
    ! [X51: $i,X52: $i] :
      ( ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X52 ) )
      | ( v1_relat_1 @ X51 )
      | ~ ( v1_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['11','16'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('18',plain,(
    ! [X15: $i,X16: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X15 @ X16 ) @ X15 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf('19',plain,(
    ! [X59: $i,X60: $i] :
      ( ~ ( v1_relat_1 @ X59 )
      | ( r1_tarski @ ( k3_relat_1 @ X60 ) @ ( k3_relat_1 @ X59 ) )
      | ~ ( r1_tarski @ X60 @ X59 )
      | ~ ( v1_relat_1 @ X60 ) ) ),
    inference(cnf,[status(esa)],[t31_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc1_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X53: $i,X54: $i] :
      ( ~ ( v1_relat_1 @ X53 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X53 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[fc1_relat_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_relat_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('23',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ X17 @ X18 )
      | ~ ( r1_tarski @ X17 @ X19 )
      | ( r1_tarski @ X17 @ ( k3_xboole_0 @ X18 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ X0 ) @ X2 ) )
      | ~ ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ X1 ) @ ( k3_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','24'])).

thf(t34_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_relat_1])).

thf('26',plain,(
    ~ ( r1_tarski @ ( k3_relat_1 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) @ ( k3_xboole_0 @ ( k3_relat_1 @ sk_A ) @ ( k3_relat_1 @ sk_B ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    $false ),
    inference(demod,[status(thm)],['27','28','29'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.oIWkdoyAIf
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:34:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 2.40/2.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.40/2.61  % Solved by: fo/fo7.sh
% 2.40/2.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.40/2.61  % done 4782 iterations in 2.166s
% 2.40/2.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.40/2.61  % SZS output start Refutation
% 2.40/2.61  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 2.40/2.61  thf(k3_relat_1_type, type, k3_relat_1: $i > $i).
% 2.40/2.61  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 2.40/2.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.40/2.61  thf(sk_B_type, type, sk_B: $i).
% 2.40/2.61  thf(sk_A_type, type, sk_A: $i).
% 2.40/2.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.40/2.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.40/2.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.40/2.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.40/2.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.40/2.61  thf(d10_xboole_0, axiom,
% 2.40/2.61    (![A:$i,B:$i]:
% 2.40/2.61     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.40/2.61  thf('0', plain,
% 2.40/2.61      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.40/2.61      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.40/2.61  thf('1', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.40/2.61      inference('simplify', [status(thm)], ['0'])).
% 2.40/2.61  thf(t85_xboole_1, axiom,
% 2.40/2.61    (![A:$i,B:$i,C:$i]:
% 2.40/2.61     ( ( r1_tarski @ A @ B ) => ( r1_xboole_0 @ A @ ( k4_xboole_0 @ C @ B ) ) ))).
% 2.40/2.61  thf('2', plain,
% 2.40/2.61      (![X33 : $i, X34 : $i, X35 : $i]:
% 2.40/2.61         (~ (r1_tarski @ X33 @ X34)
% 2.40/2.61          | (r1_xboole_0 @ X33 @ (k4_xboole_0 @ X35 @ X34)))),
% 2.40/2.61      inference('cnf', [status(esa)], [t85_xboole_1])).
% 2.40/2.61  thf('3', plain,
% 2.40/2.61      (![X0 : $i, X1 : $i]: (r1_xboole_0 @ X0 @ (k4_xboole_0 @ X1 @ X0))),
% 2.40/2.61      inference('sup-', [status(thm)], ['1', '2'])).
% 2.40/2.61  thf(t31_xboole_1, axiom,
% 2.40/2.61    (![A:$i,B:$i,C:$i]:
% 2.40/2.61     ( r1_tarski @
% 2.40/2.61       ( k2_xboole_0 @ ( k3_xboole_0 @ A @ B ) @ ( k3_xboole_0 @ A @ C ) ) @ 
% 2.40/2.61       ( k2_xboole_0 @ B @ C ) ))).
% 2.40/2.61  thf('4', plain,
% 2.40/2.61      (![X21 : $i, X22 : $i, X23 : $i]:
% 2.40/2.61         (r1_tarski @ 
% 2.40/2.61          (k2_xboole_0 @ (k3_xboole_0 @ X21 @ X22) @ (k3_xboole_0 @ X21 @ X23)) @ 
% 2.40/2.61          (k2_xboole_0 @ X22 @ X23))),
% 2.40/2.61      inference('cnf', [status(esa)], [t31_xboole_1])).
% 2.40/2.61  thf(t11_xboole_1, axiom,
% 2.40/2.61    (![A:$i,B:$i,C:$i]:
% 2.40/2.61     ( ( r1_tarski @ ( k2_xboole_0 @ A @ B ) @ C ) => ( r1_tarski @ A @ C ) ))).
% 2.40/2.61  thf('5', plain,
% 2.40/2.61      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.40/2.61         ((r1_tarski @ X12 @ X13)
% 2.40/2.61          | ~ (r1_tarski @ (k2_xboole_0 @ X12 @ X14) @ X13))),
% 2.40/2.61      inference('cnf', [status(esa)], [t11_xboole_1])).
% 2.40/2.61  thf('6', plain,
% 2.40/2.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.40/2.61         (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ (k2_xboole_0 @ X1 @ X0))),
% 2.40/2.61      inference('sup-', [status(thm)], ['4', '5'])).
% 2.40/2.61  thf(t73_xboole_1, axiom,
% 2.40/2.61    (![A:$i,B:$i,C:$i]:
% 2.40/2.61     ( ( ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) & ( r1_xboole_0 @ A @ C ) ) =>
% 2.40/2.61       ( r1_tarski @ A @ B ) ))).
% 2.40/2.61  thf('7', plain,
% 2.40/2.61      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.40/2.61         ((r1_tarski @ X30 @ X31)
% 2.40/2.61          | ~ (r1_tarski @ X30 @ (k2_xboole_0 @ X31 @ X32))
% 2.40/2.61          | ~ (r1_xboole_0 @ X30 @ X32))),
% 2.40/2.61      inference('cnf', [status(esa)], [t73_xboole_1])).
% 2.40/2.61  thf('8', plain,
% 2.40/2.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.40/2.61         (~ (r1_xboole_0 @ (k3_xboole_0 @ X2 @ X1) @ X0)
% 2.40/2.61          | (r1_tarski @ (k3_xboole_0 @ X2 @ X1) @ X1))),
% 2.40/2.61      inference('sup-', [status(thm)], ['6', '7'])).
% 2.40/2.61  thf('9', plain,
% 2.40/2.61      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 2.40/2.61      inference('sup-', [status(thm)], ['3', '8'])).
% 2.40/2.61  thf(t31_relat_1, axiom,
% 2.40/2.61    (![A:$i]:
% 2.40/2.61     ( ( v1_relat_1 @ A ) =>
% 2.40/2.61       ( ![B:$i]:
% 2.40/2.61         ( ( v1_relat_1 @ B ) =>
% 2.40/2.61           ( ( r1_tarski @ A @ B ) =>
% 2.40/2.61             ( r1_tarski @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 2.40/2.61  thf('10', plain,
% 2.40/2.61      (![X59 : $i, X60 : $i]:
% 2.40/2.61         (~ (v1_relat_1 @ X59)
% 2.40/2.61          | (r1_tarski @ (k3_relat_1 @ X60) @ (k3_relat_1 @ X59))
% 2.40/2.61          | ~ (r1_tarski @ X60 @ X59)
% 2.40/2.61          | ~ (v1_relat_1 @ X60))),
% 2.40/2.61      inference('cnf', [status(esa)], [t31_relat_1])).
% 2.40/2.61  thf('11', plain,
% 2.40/2.61      (![X0 : $i, X1 : $i]:
% 2.40/2.61         (~ (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0))
% 2.40/2.61          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 2.40/2.61             (k3_relat_1 @ X0))
% 2.40/2.61          | ~ (v1_relat_1 @ X0))),
% 2.40/2.61      inference('sup-', [status(thm)], ['9', '10'])).
% 2.40/2.61  thf('12', plain,
% 2.40/2.61      (![X0 : $i, X1 : $i]: (r1_tarski @ (k3_xboole_0 @ X1 @ X0) @ X0)),
% 2.40/2.61      inference('sup-', [status(thm)], ['3', '8'])).
% 2.40/2.61  thf(t3_subset, axiom,
% 2.40/2.61    (![A:$i,B:$i]:
% 2.40/2.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.40/2.61  thf('13', plain,
% 2.40/2.61      (![X43 : $i, X45 : $i]:
% 2.40/2.61         ((m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X45)) | ~ (r1_tarski @ X43 @ X45))),
% 2.40/2.61      inference('cnf', [status(esa)], [t3_subset])).
% 2.40/2.61  thf('14', plain,
% 2.40/2.61      (![X0 : $i, X1 : $i]:
% 2.40/2.61         (m1_subset_1 @ (k3_xboole_0 @ X1 @ X0) @ (k1_zfmisc_1 @ X0))),
% 2.40/2.61      inference('sup-', [status(thm)], ['12', '13'])).
% 2.40/2.61  thf(cc2_relat_1, axiom,
% 2.40/2.61    (![A:$i]:
% 2.40/2.61     ( ( v1_relat_1 @ A ) =>
% 2.40/2.61       ( ![B:$i]:
% 2.40/2.61         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.40/2.61  thf('15', plain,
% 2.40/2.61      (![X51 : $i, X52 : $i]:
% 2.40/2.61         (~ (m1_subset_1 @ X51 @ (k1_zfmisc_1 @ X52))
% 2.40/2.61          | (v1_relat_1 @ X51)
% 2.40/2.61          | ~ (v1_relat_1 @ X52))),
% 2.40/2.61      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.40/2.61  thf('16', plain,
% 2.40/2.61      (![X0 : $i, X1 : $i]:
% 2.40/2.61         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X1 @ X0)))),
% 2.40/2.61      inference('sup-', [status(thm)], ['14', '15'])).
% 2.40/2.61  thf('17', plain,
% 2.40/2.61      (![X0 : $i, X1 : $i]:
% 2.40/2.61         (~ (v1_relat_1 @ X0)
% 2.40/2.61          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 2.40/2.61             (k3_relat_1 @ X0)))),
% 2.40/2.61      inference('clc', [status(thm)], ['11', '16'])).
% 2.40/2.61  thf(t17_xboole_1, axiom,
% 2.40/2.61    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 2.40/2.61  thf('18', plain,
% 2.40/2.61      (![X15 : $i, X16 : $i]: (r1_tarski @ (k3_xboole_0 @ X15 @ X16) @ X15)),
% 2.40/2.61      inference('cnf', [status(esa)], [t17_xboole_1])).
% 2.40/2.61  thf('19', plain,
% 2.40/2.61      (![X59 : $i, X60 : $i]:
% 2.40/2.61         (~ (v1_relat_1 @ X59)
% 2.40/2.61          | (r1_tarski @ (k3_relat_1 @ X60) @ (k3_relat_1 @ X59))
% 2.40/2.61          | ~ (r1_tarski @ X60 @ X59)
% 2.40/2.61          | ~ (v1_relat_1 @ X60))),
% 2.40/2.61      inference('cnf', [status(esa)], [t31_relat_1])).
% 2.40/2.61  thf('20', plain,
% 2.40/2.61      (![X0 : $i, X1 : $i]:
% 2.40/2.61         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 2.40/2.61          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 2.40/2.61             (k3_relat_1 @ X0))
% 2.40/2.61          | ~ (v1_relat_1 @ X0))),
% 2.40/2.61      inference('sup-', [status(thm)], ['18', '19'])).
% 2.40/2.61  thf(fc1_relat_1, axiom,
% 2.40/2.61    (![A:$i,B:$i]:
% 2.40/2.61     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k3_xboole_0 @ A @ B ) ) ))).
% 2.40/2.61  thf('21', plain,
% 2.40/2.61      (![X53 : $i, X54 : $i]:
% 2.40/2.61         (~ (v1_relat_1 @ X53) | (v1_relat_1 @ (k3_xboole_0 @ X53 @ X54)))),
% 2.40/2.61      inference('cnf', [status(esa)], [fc1_relat_1])).
% 2.40/2.61  thf('22', plain,
% 2.40/2.61      (![X0 : $i, X1 : $i]:
% 2.40/2.61         (~ (v1_relat_1 @ X0)
% 2.40/2.61          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 2.40/2.61             (k3_relat_1 @ X0)))),
% 2.40/2.61      inference('clc', [status(thm)], ['20', '21'])).
% 2.40/2.61  thf(t19_xboole_1, axiom,
% 2.40/2.61    (![A:$i,B:$i,C:$i]:
% 2.40/2.61     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 2.40/2.61       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 2.40/2.61  thf('23', plain,
% 2.40/2.61      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.40/2.61         (~ (r1_tarski @ X17 @ X18)
% 2.40/2.61          | ~ (r1_tarski @ X17 @ X19)
% 2.40/2.61          | (r1_tarski @ X17 @ (k3_xboole_0 @ X18 @ X19)))),
% 2.40/2.61      inference('cnf', [status(esa)], [t19_xboole_1])).
% 2.40/2.61  thf('24', plain,
% 2.40/2.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.40/2.61         (~ (v1_relat_1 @ X0)
% 2.40/2.61          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 2.40/2.61             (k3_xboole_0 @ (k3_relat_1 @ X0) @ X2))
% 2.40/2.61          | ~ (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X0 @ X1)) @ X2))),
% 2.40/2.61      inference('sup-', [status(thm)], ['22', '23'])).
% 2.40/2.61  thf('25', plain,
% 2.40/2.61      (![X0 : $i, X1 : $i]:
% 2.40/2.61         (~ (v1_relat_1 @ X0)
% 2.40/2.61          | (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 2.40/2.61             (k3_xboole_0 @ (k3_relat_1 @ X1) @ (k3_relat_1 @ X0)))
% 2.40/2.61          | ~ (v1_relat_1 @ X1))),
% 2.40/2.61      inference('sup-', [status(thm)], ['17', '24'])).
% 2.40/2.61  thf(t34_relat_1, conjecture,
% 2.40/2.61    (![A:$i]:
% 2.40/2.61     ( ( v1_relat_1 @ A ) =>
% 2.40/2.61       ( ![B:$i]:
% 2.40/2.61         ( ( v1_relat_1 @ B ) =>
% 2.40/2.61           ( r1_tarski @
% 2.40/2.61             ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 2.40/2.61             ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ))).
% 2.40/2.61  thf(zf_stmt_0, negated_conjecture,
% 2.40/2.61    (~( ![A:$i]:
% 2.40/2.61        ( ( v1_relat_1 @ A ) =>
% 2.40/2.61          ( ![B:$i]:
% 2.40/2.61            ( ( v1_relat_1 @ B ) =>
% 2.40/2.61              ( r1_tarski @
% 2.40/2.61                ( k3_relat_1 @ ( k3_xboole_0 @ A @ B ) ) @ 
% 2.40/2.61                ( k3_xboole_0 @ ( k3_relat_1 @ A ) @ ( k3_relat_1 @ B ) ) ) ) ) ) )),
% 2.40/2.61    inference('cnf.neg', [status(esa)], [t34_relat_1])).
% 2.40/2.61  thf('26', plain,
% 2.40/2.61      (~ (r1_tarski @ (k3_relat_1 @ (k3_xboole_0 @ sk_A @ sk_B)) @ 
% 2.40/2.61          (k3_xboole_0 @ (k3_relat_1 @ sk_A) @ (k3_relat_1 @ sk_B)))),
% 2.40/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.61  thf('27', plain, ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_B))),
% 2.40/2.61      inference('sup-', [status(thm)], ['25', '26'])).
% 2.40/2.61  thf('28', plain, ((v1_relat_1 @ sk_A)),
% 2.40/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.61  thf('29', plain, ((v1_relat_1 @ sk_B)),
% 2.40/2.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.40/2.61  thf('30', plain, ($false),
% 2.40/2.61      inference('demod', [status(thm)], ['27', '28', '29'])).
% 2.40/2.61  
% 2.40/2.61  % SZS output end Refutation
% 2.40/2.61  
% 2.40/2.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
