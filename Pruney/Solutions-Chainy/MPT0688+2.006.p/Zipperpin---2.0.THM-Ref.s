%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pQOT2LiJR0

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   40 (  46 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :   11
%              Number of atoms          :  225 ( 300 expanded)
%              Number of equality atoms :   12 (  17 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(t143_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ! [C: $i] :
            ~ ( ( r2_hidden @ C @ A )
              & ( ( k10_relat_1 @ B @ ( k1_tarski @ C ) )
                = k1_xboole_0 ) )
       => ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( v1_relat_1 @ B )
       => ( ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( ( k10_relat_1 @ B @ ( k1_tarski @ C ) )
                  = k1_xboole_0 ) )
         => ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t143_funct_1])).

thf('0',plain,(
    ~ ( r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('2',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l27_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( r2_hidden @ A @ B )
     => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ ( k1_tarski @ X9 ) @ X10 )
      | ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[l27_zfmisc_1])).

thf(symmetry_r1_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
     => ( r1_xboole_0 @ B @ A ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_xboole_0 @ X4 @ X5 )
      | ~ ( r1_xboole_0 @ X5 @ X4 ) ) ),
    inference(cnf,[status(esa)],[symmetry_r1_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ ( k1_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','5'])).

thf(t173_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k10_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_xboole_0 @ ( k2_relat_1 @ X11 ) @ X12 )
      | ( ( k10_relat_1 @ X11 @ X12 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t173_relat_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k10_relat_1 @ X1 @ ( k2_tarski @ X0 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('10',plain,(
    ! [X13: $i] :
      ( ~ ( r2_hidden @ X13 @ sk_A )
      | ( ( k10_relat_1 @ sk_B @ ( k1_tarski @ X13 ) )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ sk_B @ ( k2_tarski @ X0 @ X0 ) )
       != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_A ) @ ( k2_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['1','15'])).

thf('17',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,
    ( ( r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) )
    | ( r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    $false ),
    inference(demod,[status(thm)],['0','19'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.pQOT2LiJR0
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:22:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 27 iterations in 0.016s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.46  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.46  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.46  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.20/0.46  thf(t143_funct_1, conjecture,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ B ) =>
% 0.20/0.46       ( ( ![C:$i]:
% 0.20/0.46           ( ~( ( r2_hidden @ C @ A ) & 
% 0.20/0.46                ( ( k10_relat_1 @ B @ ( k1_tarski @ C ) ) = ( k1_xboole_0 ) ) ) ) ) =>
% 0.20/0.46         ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i]:
% 0.20/0.46        ( ( v1_relat_1 @ B ) =>
% 0.20/0.46          ( ( ![C:$i]:
% 0.20/0.46              ( ~( ( r2_hidden @ C @ A ) & 
% 0.20/0.46                   ( ( k10_relat_1 @ B @ ( k1_tarski @ C ) ) = ( k1_xboole_0 ) ) ) ) ) =>
% 0.20/0.46            ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t143_funct_1])).
% 0.20/0.46  thf('0', plain, (~ (r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(d3_tarski, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.46       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      (![X1 : $i, X3 : $i]:
% 0.20/0.46         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.46      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.46  thf(t69_enumset1, axiom,
% 0.20/0.46    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.46  thf('2', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.20/0.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.46  thf(l27_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ~( r2_hidden @ A @ B ) ) => ( r1_xboole_0 @ ( k1_tarski @ A ) @ B ) ))).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (![X9 : $i, X10 : $i]:
% 0.20/0.46         ((r1_xboole_0 @ (k1_tarski @ X9) @ X10) | (r2_hidden @ X9 @ X10))),
% 0.20/0.46      inference('cnf', [status(esa)], [l27_zfmisc_1])).
% 0.20/0.46  thf(symmetry_r1_xboole_0, axiom,
% 0.20/0.46    (![A:$i,B:$i]: ( ( r1_xboole_0 @ A @ B ) => ( r1_xboole_0 @ B @ A ) ))).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (![X4 : $i, X5 : $i]:
% 0.20/0.46         ((r1_xboole_0 @ X4 @ X5) | ~ (r1_xboole_0 @ X5 @ X4))),
% 0.20/0.46      inference('cnf', [status(esa)], [symmetry_r1_xboole_0])).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((r2_hidden @ X1 @ X0) | (r1_xboole_0 @ X0 @ (k1_tarski @ X1)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((r1_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0)) | (r2_hidden @ X0 @ X1))),
% 0.20/0.46      inference('sup+', [status(thm)], ['2', '5'])).
% 0.20/0.46  thf(t173_relat_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ B ) =>
% 0.20/0.46       ( ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.20/0.46         ( r1_xboole_0 @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (![X11 : $i, X12 : $i]:
% 0.20/0.46         (~ (r1_xboole_0 @ (k2_relat_1 @ X11) @ X12)
% 0.20/0.46          | ((k10_relat_1 @ X11 @ X12) = (k1_xboole_0))
% 0.20/0.46          | ~ (v1_relat_1 @ X11))),
% 0.20/0.46      inference('cnf', [status(esa)], [t173_relat_1])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((r2_hidden @ X0 @ (k2_relat_1 @ X1))
% 0.20/0.46          | ~ (v1_relat_1 @ X1)
% 0.20/0.46          | ((k10_relat_1 @ X1 @ (k2_tarski @ X0 @ X0)) = (k1_xboole_0)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.46  thf('9', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.20/0.46      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      (![X13 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X13 @ sk_A)
% 0.20/0.46          | ((k10_relat_1 @ sk_B @ (k1_tarski @ X13)) != (k1_xboole_0)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (((k10_relat_1 @ sk_B @ (k2_tarski @ X0 @ X0)) != (k1_xboole_0))
% 0.20/0.46          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.46          | ~ (v1_relat_1 @ sk_B)
% 0.20/0.46          | (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.20/0.46          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['8', '11'])).
% 0.20/0.46  thf('13', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('14', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (((k1_xboole_0) != (k1_xboole_0))
% 0.20/0.46          | (r2_hidden @ X0 @ (k2_relat_1 @ sk_B))
% 0.20/0.46          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['12', '13'])).
% 0.20/0.46  thf('15', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X0 @ sk_A) | (r2_hidden @ X0 @ (k2_relat_1 @ sk_B)))),
% 0.20/0.46      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.46  thf('16', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         ((r1_tarski @ sk_A @ X0)
% 0.20/0.46          | (r2_hidden @ (sk_C @ X0 @ sk_A) @ (k2_relat_1 @ sk_B)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['1', '15'])).
% 0.20/0.46  thf('17', plain,
% 0.20/0.46      (![X1 : $i, X3 : $i]:
% 0.20/0.46         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.20/0.46      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.46  thf('18', plain,
% 0.20/0.46      (((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))
% 0.20/0.46        | (r1_tarski @ sk_A @ (k2_relat_1 @ sk_B)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.46  thf('19', plain, ((r1_tarski @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.20/0.46      inference('simplify', [status(thm)], ['18'])).
% 0.20/0.46  thf('20', plain, ($false), inference('demod', [status(thm)], ['0', '19'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
