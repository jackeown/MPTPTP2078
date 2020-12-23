%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.c936xlsTS2

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:38 EST 2020

% Result     : Theorem 14.99s
% Output     : Refutation 14.99s
% Verified   : 
% Statistics : Number of formulae       :   50 (  59 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :  405 ( 505 expanded)
%              Number of equality atoms :   26 (  29 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(t123_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( v2_funct_1 @ C )
       => ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) )
          = ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) )).

thf('0',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v2_funct_1 @ X31 )
      | ( ( k9_relat_1 @ X31 @ ( k6_subset_1 @ X32 @ X33 ) )
        = ( k6_subset_1 @ ( k9_relat_1 @ X31 @ X32 ) @ ( k9_relat_1 @ X31 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t123_funct_1])).

thf(t145_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ) )).

thf('1',plain,(
    ! [X37: $i,X38: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X37 @ ( k10_relat_1 @ X37 @ X38 ) ) @ X38 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t145_funct_1])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k4_xboole_0 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('4',plain,(
    ! [X3: $i,X5: $i] :
      ( ( ( k6_subset_1 @ X3 @ X5 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k6_subset_1 @ ( k9_relat_1 @ X1 @ ( k10_relat_1 @ X1 @ X0 ) ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X1 @ ( k6_subset_1 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 ) )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ X1 @ ( k6_subset_1 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t167_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X23: $i,X24: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X23 @ X24 ) @ ( k1_relat_1 @ X23 ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t167_relat_1])).

thf(t109_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ) )).

thf('9',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k4_xboole_0 @ X6 @ X8 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t109_xboole_1])).

thf('10',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('11',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r1_tarski @ X6 @ X7 )
      | ( r1_tarski @ ( k6_subset_1 @ X6 @ X8 ) @ X7 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k6_subset_1 @ ( k10_relat_1 @ X0 @ X1 ) @ X2 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf(t152_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( ( k9_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf('13',plain,(
    ! [X21: $i,X22: $i] :
      ( ( X21 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X22 )
      | ~ ( r1_tarski @ X21 @ ( k1_relat_1 @ X22 ) )
      | ( ( k9_relat_1 @ X22 @ X21 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t152_relat_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ ( k6_subset_1 @ ( k10_relat_1 @ X0 @ X2 ) @ X1 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k6_subset_1 @ ( k10_relat_1 @ X0 @ X2 ) @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k6_subset_1 @ ( k10_relat_1 @ X0 @ X2 ) @ X1 )
        = k1_xboole_0 )
      | ( ( k9_relat_1 @ X0 @ ( k6_subset_1 @ ( k10_relat_1 @ X0 @ X2 ) @ X1 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k6_subset_1 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k6_subset_1 @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 )
        = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('19',plain,(
    ! [X19: $i,X20: $i] :
      ( ( k6_subset_1 @ X19 @ X20 )
      = ( k4_xboole_0 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('20',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( ( k6_subset_1 @ X3 @ X4 )
       != k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v2_funct_1 @ X1 )
      | ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k10_relat_1 @ X1 @ ( k9_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t152_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( v2_funct_1 @ B )
       => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( v2_funct_1 @ B )
         => ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t152_funct_1])).

thf('23',plain,(
    ~ ( r1_tarski @ ( k10_relat_1 @ sk_B @ ( k9_relat_1 @ sk_B @ sk_A ) ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v2_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v2_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    $false ),
    inference(demod,[status(thm)],['24','25','26','27'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.c936xlsTS2
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:32:26 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.33  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 14.99/15.22  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 14.99/15.22  % Solved by: fo/fo7.sh
% 14.99/15.22  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 14.99/15.22  % done 12990 iterations in 14.778s
% 14.99/15.22  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 14.99/15.22  % SZS output start Refutation
% 14.99/15.22  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 14.99/15.22  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 14.99/15.22  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 14.99/15.22  thf(sk_A_type, type, sk_A: $i).
% 14.99/15.22  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 14.99/15.22  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 14.99/15.22  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 14.99/15.22  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 14.99/15.22  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 14.99/15.22  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 14.99/15.22  thf(sk_B_type, type, sk_B: $i).
% 14.99/15.22  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 14.99/15.22  thf(t123_funct_1, axiom,
% 14.99/15.22    (![A:$i,B:$i,C:$i]:
% 14.99/15.22     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 14.99/15.22       ( ( v2_funct_1 @ C ) =>
% 14.99/15.22         ( ( k9_relat_1 @ C @ ( k6_subset_1 @ A @ B ) ) =
% 14.99/15.22           ( k6_subset_1 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 14.99/15.22  thf('0', plain,
% 14.99/15.22      (![X31 : $i, X32 : $i, X33 : $i]:
% 14.99/15.22         (~ (v2_funct_1 @ X31)
% 14.99/15.22          | ((k9_relat_1 @ X31 @ (k6_subset_1 @ X32 @ X33))
% 14.99/15.22              = (k6_subset_1 @ (k9_relat_1 @ X31 @ X32) @ 
% 14.99/15.22                 (k9_relat_1 @ X31 @ X33)))
% 14.99/15.22          | ~ (v1_funct_1 @ X31)
% 14.99/15.22          | ~ (v1_relat_1 @ X31))),
% 14.99/15.22      inference('cnf', [status(esa)], [t123_funct_1])).
% 14.99/15.22  thf(t145_funct_1, axiom,
% 14.99/15.22    (![A:$i,B:$i]:
% 14.99/15.22     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 14.99/15.22       ( r1_tarski @ ( k9_relat_1 @ B @ ( k10_relat_1 @ B @ A ) ) @ A ) ))).
% 14.99/15.22  thf('1', plain,
% 14.99/15.22      (![X37 : $i, X38 : $i]:
% 14.99/15.22         ((r1_tarski @ (k9_relat_1 @ X37 @ (k10_relat_1 @ X37 @ X38)) @ X38)
% 14.99/15.22          | ~ (v1_funct_1 @ X37)
% 14.99/15.22          | ~ (v1_relat_1 @ X37))),
% 14.99/15.22      inference('cnf', [status(esa)], [t145_funct_1])).
% 14.99/15.22  thf(l32_xboole_1, axiom,
% 14.99/15.22    (![A:$i,B:$i]:
% 14.99/15.22     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 14.99/15.22  thf('2', plain,
% 14.99/15.22      (![X3 : $i, X5 : $i]:
% 14.99/15.22         (((k4_xboole_0 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 14.99/15.22      inference('cnf', [status(esa)], [l32_xboole_1])).
% 14.99/15.22  thf(redefinition_k6_subset_1, axiom,
% 14.99/15.22    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 14.99/15.22  thf('3', plain,
% 14.99/15.22      (![X19 : $i, X20 : $i]:
% 14.99/15.22         ((k6_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))),
% 14.99/15.22      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 14.99/15.22  thf('4', plain,
% 14.99/15.22      (![X3 : $i, X5 : $i]:
% 14.99/15.22         (((k6_subset_1 @ X3 @ X5) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ X5))),
% 14.99/15.22      inference('demod', [status(thm)], ['2', '3'])).
% 14.99/15.22  thf('5', plain,
% 14.99/15.22      (![X0 : $i, X1 : $i]:
% 14.99/15.22         (~ (v1_relat_1 @ X1)
% 14.99/15.22          | ~ (v1_funct_1 @ X1)
% 14.99/15.22          | ((k6_subset_1 @ (k9_relat_1 @ X1 @ (k10_relat_1 @ X1 @ X0)) @ X0)
% 14.99/15.22              = (k1_xboole_0)))),
% 14.99/15.22      inference('sup-', [status(thm)], ['1', '4'])).
% 14.99/15.22  thf('6', plain,
% 14.99/15.22      (![X0 : $i, X1 : $i]:
% 14.99/15.22         (((k9_relat_1 @ X1 @ 
% 14.99/15.22            (k6_subset_1 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0))
% 14.99/15.23            = (k1_xboole_0))
% 14.99/15.23          | ~ (v1_relat_1 @ X1)
% 14.99/15.23          | ~ (v1_funct_1 @ X1)
% 14.99/15.23          | ~ (v2_funct_1 @ X1)
% 14.99/15.23          | ~ (v1_funct_1 @ X1)
% 14.99/15.23          | ~ (v1_relat_1 @ X1))),
% 14.99/15.23      inference('sup+', [status(thm)], ['0', '5'])).
% 14.99/15.23  thf('7', plain,
% 14.99/15.23      (![X0 : $i, X1 : $i]:
% 14.99/15.23         (~ (v2_funct_1 @ X1)
% 14.99/15.23          | ~ (v1_funct_1 @ X1)
% 14.99/15.23          | ~ (v1_relat_1 @ X1)
% 14.99/15.23          | ((k9_relat_1 @ X1 @ 
% 14.99/15.23              (k6_subset_1 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0))
% 14.99/15.23              = (k1_xboole_0)))),
% 14.99/15.23      inference('simplify', [status(thm)], ['6'])).
% 14.99/15.23  thf(t167_relat_1, axiom,
% 14.99/15.23    (![A:$i,B:$i]:
% 14.99/15.23     ( ( v1_relat_1 @ B ) =>
% 14.99/15.23       ( r1_tarski @ ( k10_relat_1 @ B @ A ) @ ( k1_relat_1 @ B ) ) ))).
% 14.99/15.23  thf('8', plain,
% 14.99/15.23      (![X23 : $i, X24 : $i]:
% 14.99/15.23         ((r1_tarski @ (k10_relat_1 @ X23 @ X24) @ (k1_relat_1 @ X23))
% 14.99/15.23          | ~ (v1_relat_1 @ X23))),
% 14.99/15.23      inference('cnf', [status(esa)], [t167_relat_1])).
% 14.99/15.23  thf(t109_xboole_1, axiom,
% 14.99/15.23    (![A:$i,B:$i,C:$i]:
% 14.99/15.23     ( ( r1_tarski @ A @ B ) => ( r1_tarski @ ( k4_xboole_0 @ A @ C ) @ B ) ))).
% 14.99/15.23  thf('9', plain,
% 14.99/15.23      (![X6 : $i, X7 : $i, X8 : $i]:
% 14.99/15.23         (~ (r1_tarski @ X6 @ X7) | (r1_tarski @ (k4_xboole_0 @ X6 @ X8) @ X7))),
% 14.99/15.23      inference('cnf', [status(esa)], [t109_xboole_1])).
% 14.99/15.23  thf('10', plain,
% 14.99/15.23      (![X19 : $i, X20 : $i]:
% 14.99/15.23         ((k6_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))),
% 14.99/15.23      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 14.99/15.23  thf('11', plain,
% 14.99/15.23      (![X6 : $i, X7 : $i, X8 : $i]:
% 14.99/15.23         (~ (r1_tarski @ X6 @ X7) | (r1_tarski @ (k6_subset_1 @ X6 @ X8) @ X7))),
% 14.99/15.23      inference('demod', [status(thm)], ['9', '10'])).
% 14.99/15.23  thf('12', plain,
% 14.99/15.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.99/15.23         (~ (v1_relat_1 @ X0)
% 14.99/15.23          | (r1_tarski @ (k6_subset_1 @ (k10_relat_1 @ X0 @ X1) @ X2) @ 
% 14.99/15.23             (k1_relat_1 @ X0)))),
% 14.99/15.23      inference('sup-', [status(thm)], ['8', '11'])).
% 14.99/15.23  thf(t152_relat_1, axiom,
% 14.99/15.23    (![A:$i,B:$i]:
% 14.99/15.23     ( ( v1_relat_1 @ B ) =>
% 14.99/15.23       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 14.99/15.23            ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & 
% 14.99/15.23            ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 14.99/15.23  thf('13', plain,
% 14.99/15.23      (![X21 : $i, X22 : $i]:
% 14.99/15.23         (((X21) = (k1_xboole_0))
% 14.99/15.23          | ~ (v1_relat_1 @ X22)
% 14.99/15.23          | ~ (r1_tarski @ X21 @ (k1_relat_1 @ X22))
% 14.99/15.23          | ((k9_relat_1 @ X22 @ X21) != (k1_xboole_0)))),
% 14.99/15.23      inference('cnf', [status(esa)], [t152_relat_1])).
% 14.99/15.23  thf('14', plain,
% 14.99/15.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.99/15.23         (~ (v1_relat_1 @ X0)
% 14.99/15.23          | ((k9_relat_1 @ X0 @ (k6_subset_1 @ (k10_relat_1 @ X0 @ X2) @ X1))
% 14.99/15.23              != (k1_xboole_0))
% 14.99/15.23          | ~ (v1_relat_1 @ X0)
% 14.99/15.23          | ((k6_subset_1 @ (k10_relat_1 @ X0 @ X2) @ X1) = (k1_xboole_0)))),
% 14.99/15.23      inference('sup-', [status(thm)], ['12', '13'])).
% 14.99/15.23  thf('15', plain,
% 14.99/15.23      (![X0 : $i, X1 : $i, X2 : $i]:
% 14.99/15.23         (((k6_subset_1 @ (k10_relat_1 @ X0 @ X2) @ X1) = (k1_xboole_0))
% 14.99/15.23          | ((k9_relat_1 @ X0 @ (k6_subset_1 @ (k10_relat_1 @ X0 @ X2) @ X1))
% 14.99/15.23              != (k1_xboole_0))
% 14.99/15.23          | ~ (v1_relat_1 @ X0))),
% 14.99/15.23      inference('simplify', [status(thm)], ['14'])).
% 14.99/15.23  thf('16', plain,
% 14.99/15.23      (![X0 : $i, X1 : $i]:
% 14.99/15.23         (((k1_xboole_0) != (k1_xboole_0))
% 14.99/15.23          | ~ (v1_relat_1 @ X1)
% 14.99/15.23          | ~ (v1_funct_1 @ X1)
% 14.99/15.23          | ~ (v2_funct_1 @ X1)
% 14.99/15.23          | ~ (v1_relat_1 @ X1)
% 14.99/15.23          | ((k6_subset_1 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0)
% 14.99/15.23              = (k1_xboole_0)))),
% 14.99/15.23      inference('sup-', [status(thm)], ['7', '15'])).
% 14.99/15.23  thf('17', plain,
% 14.99/15.23      (![X0 : $i, X1 : $i]:
% 14.99/15.23         (((k6_subset_1 @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0)
% 14.99/15.23            = (k1_xboole_0))
% 14.99/15.23          | ~ (v2_funct_1 @ X1)
% 14.99/15.23          | ~ (v1_funct_1 @ X1)
% 14.99/15.23          | ~ (v1_relat_1 @ X1))),
% 14.99/15.23      inference('simplify', [status(thm)], ['16'])).
% 14.99/15.23  thf('18', plain,
% 14.99/15.23      (![X3 : $i, X4 : $i]:
% 14.99/15.23         ((r1_tarski @ X3 @ X4) | ((k4_xboole_0 @ X3 @ X4) != (k1_xboole_0)))),
% 14.99/15.23      inference('cnf', [status(esa)], [l32_xboole_1])).
% 14.99/15.23  thf('19', plain,
% 14.99/15.23      (![X19 : $i, X20 : $i]:
% 14.99/15.23         ((k6_subset_1 @ X19 @ X20) = (k4_xboole_0 @ X19 @ X20))),
% 14.99/15.23      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 14.99/15.23  thf('20', plain,
% 14.99/15.23      (![X3 : $i, X4 : $i]:
% 14.99/15.23         ((r1_tarski @ X3 @ X4) | ((k6_subset_1 @ X3 @ X4) != (k1_xboole_0)))),
% 14.99/15.23      inference('demod', [status(thm)], ['18', '19'])).
% 14.99/15.23  thf('21', plain,
% 14.99/15.23      (![X0 : $i, X1 : $i]:
% 14.99/15.23         (((k1_xboole_0) != (k1_xboole_0))
% 14.99/15.23          | ~ (v1_relat_1 @ X1)
% 14.99/15.23          | ~ (v1_funct_1 @ X1)
% 14.99/15.23          | ~ (v2_funct_1 @ X1)
% 14.99/15.23          | (r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0))),
% 14.99/15.23      inference('sup-', [status(thm)], ['17', '20'])).
% 14.99/15.23  thf('22', plain,
% 14.99/15.23      (![X0 : $i, X1 : $i]:
% 14.99/15.23         ((r1_tarski @ (k10_relat_1 @ X1 @ (k9_relat_1 @ X1 @ X0)) @ X0)
% 14.99/15.23          | ~ (v2_funct_1 @ X1)
% 14.99/15.23          | ~ (v1_funct_1 @ X1)
% 14.99/15.23          | ~ (v1_relat_1 @ X1))),
% 14.99/15.23      inference('simplify', [status(thm)], ['21'])).
% 14.99/15.23  thf(t152_funct_1, conjecture,
% 14.99/15.23    (![A:$i,B:$i]:
% 14.99/15.23     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 14.99/15.23       ( ( v2_funct_1 @ B ) =>
% 14.99/15.23         ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ))).
% 14.99/15.23  thf(zf_stmt_0, negated_conjecture,
% 14.99/15.23    (~( ![A:$i,B:$i]:
% 14.99/15.23        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 14.99/15.23          ( ( v2_funct_1 @ B ) =>
% 14.99/15.23            ( r1_tarski @ ( k10_relat_1 @ B @ ( k9_relat_1 @ B @ A ) ) @ A ) ) ) )),
% 14.99/15.23    inference('cnf.neg', [status(esa)], [t152_funct_1])).
% 14.99/15.23  thf('23', plain,
% 14.99/15.23      (~ (r1_tarski @ (k10_relat_1 @ sk_B @ (k9_relat_1 @ sk_B @ sk_A)) @ sk_A)),
% 14.99/15.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.99/15.23  thf('24', plain,
% 14.99/15.23      ((~ (v1_relat_1 @ sk_B) | ~ (v1_funct_1 @ sk_B) | ~ (v2_funct_1 @ sk_B))),
% 14.99/15.23      inference('sup-', [status(thm)], ['22', '23'])).
% 14.99/15.23  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 14.99/15.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.99/15.23  thf('26', plain, ((v1_funct_1 @ sk_B)),
% 14.99/15.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.99/15.23  thf('27', plain, ((v2_funct_1 @ sk_B)),
% 14.99/15.23      inference('cnf', [status(esa)], [zf_stmt_0])).
% 14.99/15.23  thf('28', plain, ($false),
% 14.99/15.23      inference('demod', [status(thm)], ['24', '25', '26', '27'])).
% 14.99/15.23  
% 14.99/15.23  % SZS output end Refutation
% 14.99/15.23  
% 14.99/15.23  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
