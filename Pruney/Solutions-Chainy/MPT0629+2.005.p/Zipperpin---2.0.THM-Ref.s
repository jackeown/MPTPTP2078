%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MH8PkH3AYp

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:48 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 100 expanded)
%              Number of leaves         :   19 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :  358 (1096 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(t25_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( r2_hidden @ A @ ( k2_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
           => ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v1_funct_1 @ C ) )
           => ( ( r2_hidden @ A @ ( k2_relat_1 @ ( k5_relat_1 @ C @ B ) ) )
             => ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_funct_1])).

thf('0',plain,(
    ~ ( r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t160_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) )
            = ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ( ( k2_relat_1 @ ( k5_relat_1 @ X5 @ X4 ) )
        = ( k9_relat_1 @ X4 @ ( k2_relat_1 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t160_relat_1])).

thf('2',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_A @ ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    r2_hidden @ sk_A @ ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('7',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k9_relat_1 @ X3 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X3 @ X1 @ X2 ) @ ( k1_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( sk_D @ sk_B @ ( k2_relat_1 @ sk_C ) @ sk_A ) @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    r2_hidden @ ( sk_D @ sk_B @ ( k2_relat_1 @ sk_C ) @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(t12_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X10 @ ( k1_relat_1 @ X11 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X11 @ X10 ) @ ( k2_relat_1 @ X11 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t12_funct_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ sk_C ) @ sk_A ) ) @ ( k2_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ sk_C ) @ sk_A ) ) @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    r2_hidden @ sk_A @ ( k9_relat_1 @ sk_B @ ( k2_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('17',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k9_relat_1 @ X3 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X1 @ X2 ) @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ ( k2_relat_1 @ sk_C ) @ sk_A ) @ sk_A ) @ sk_B ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ ( k2_relat_1 @ sk_C ) @ sk_A ) @ sk_A ) @ sk_B ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    r2_hidden @ ( sk_D @ sk_B @ ( k2_relat_1 @ sk_C ) @ sk_A ) @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(d4_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( ~ ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( C = k1_xboole_0 ) ) )
          & ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
           => ( ( C
                = ( k1_funct_1 @ A @ B ) )
            <=> ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) )).

thf('22',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ X7 ) )
      | ( X9
        = ( k1_funct_1 @ X7 @ X6 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X9 ) @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_funct_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ ( k2_relat_1 @ sk_C ) @ sk_A ) @ X0 ) @ sk_B )
      | ( X0
        = ( k1_funct_1 @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ sk_C ) @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_B @ ( k2_relat_1 @ sk_C ) @ sk_A ) @ X0 ) @ sk_B )
      | ( X0
        = ( k1_funct_1 @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ sk_C ) @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_B @ ( sk_D @ sk_B @ ( k2_relat_1 @ sk_C ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf('28',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['15','27'])).

thf('29',plain,(
    $false ),
    inference(demod,[status(thm)],['0','28'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MH8PkH3AYp
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:53:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 39 iterations in 0.041s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.50  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.50  thf(t25_funct_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.50       ( ![C:$i]:
% 0.20/0.50         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.50           ( ( r2_hidden @ A @ ( k2_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 0.20/0.50             ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i]:
% 0.20/0.50        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.50          ( ![C:$i]:
% 0.20/0.50            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.50              ( ( r2_hidden @ A @ ( k2_relat_1 @ ( k5_relat_1 @ C @ B ) ) ) =>
% 0.20/0.50                ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t25_funct_1])).
% 0.20/0.50  thf('0', plain, (~ (r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t160_relat_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ A ) =>
% 0.20/0.50       ( ![B:$i]:
% 0.20/0.50         ( ( v1_relat_1 @ B ) =>
% 0.20/0.50           ( ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) =
% 0.20/0.50             ( k9_relat_1 @ B @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X4 : $i, X5 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ X4)
% 0.20/0.50          | ((k2_relat_1 @ (k5_relat_1 @ X5 @ X4))
% 0.20/0.50              = (k9_relat_1 @ X4 @ (k2_relat_1 @ X5)))
% 0.20/0.50          | ~ (v1_relat_1 @ X5))),
% 0.20/0.50      inference('cnf', [status(esa)], [t160_relat_1])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      ((r2_hidden @ sk_A @ (k2_relat_1 @ (k5_relat_1 @ sk_C @ sk_B)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (((r2_hidden @ sk_A @ (k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_C)))
% 0.20/0.50        | ~ (v1_relat_1 @ sk_C)
% 0.20/0.50        | ~ (v1_relat_1 @ sk_B))),
% 0.20/0.50      inference('sup+', [status(thm)], ['1', '2'])).
% 0.20/0.50  thf('4', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('5', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      ((r2_hidden @ sk_A @ (k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_C)))),
% 0.20/0.50      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.20/0.50  thf(t143_relat_1, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( v1_relat_1 @ C ) =>
% 0.20/0.50       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.20/0.50         ( ?[D:$i]:
% 0.20/0.50           ( ( r2_hidden @ D @ B ) & 
% 0.20/0.50             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.20/0.50             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.20/0.50  thf('7', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X2 @ (k9_relat_1 @ X3 @ X1))
% 0.20/0.50          | (r2_hidden @ (sk_D @ X3 @ X1 @ X2) @ (k1_relat_1 @ X3))
% 0.20/0.50          | ~ (v1_relat_1 @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.50        | (r2_hidden @ (sk_D @ sk_B @ (k2_relat_1 @ sk_C) @ sk_A) @ 
% 0.20/0.50           (k1_relat_1 @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf('9', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      ((r2_hidden @ (sk_D @ sk_B @ (k2_relat_1 @ sk_C) @ sk_A) @ 
% 0.20/0.50        (k1_relat_1 @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf(t12_funct_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.50       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.50         ( r2_hidden @ ( k1_funct_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) ))).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X10 : $i, X11 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X10 @ (k1_relat_1 @ X11))
% 0.20/0.50          | (r2_hidden @ (k1_funct_1 @ X11 @ X10) @ (k2_relat_1 @ X11))
% 0.20/0.50          | ~ (v1_funct_1 @ X11)
% 0.20/0.50          | ~ (v1_relat_1 @ X11))),
% 0.20/0.50      inference('cnf', [status(esa)], [t12_funct_1])).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.50        | ~ (v1_funct_1 @ sk_B)
% 0.20/0.50        | (r2_hidden @ 
% 0.20/0.50           (k1_funct_1 @ sk_B @ (sk_D @ sk_B @ (k2_relat_1 @ sk_C) @ sk_A)) @ 
% 0.20/0.50           (k2_relat_1 @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.50  thf('13', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('14', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('15', plain,
% 0.20/0.50      ((r2_hidden @ 
% 0.20/0.50        (k1_funct_1 @ sk_B @ (sk_D @ sk_B @ (k2_relat_1 @ sk_C) @ sk_A)) @ 
% 0.20/0.50        (k2_relat_1 @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      ((r2_hidden @ sk_A @ (k9_relat_1 @ sk_B @ (k2_relat_1 @ sk_C)))),
% 0.20/0.50      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X2 @ (k9_relat_1 @ X3 @ X1))
% 0.20/0.50          | (r2_hidden @ (k4_tarski @ (sk_D @ X3 @ X1 @ X2) @ X2) @ X3)
% 0.20/0.50          | ~ (v1_relat_1 @ X3))),
% 0.20/0.50      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      ((~ (v1_relat_1 @ sk_B)
% 0.20/0.50        | (r2_hidden @ 
% 0.20/0.50           (k4_tarski @ (sk_D @ sk_B @ (k2_relat_1 @ sk_C) @ sk_A) @ sk_A) @ 
% 0.20/0.50           sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.50  thf('19', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      ((r2_hidden @ 
% 0.20/0.50        (k4_tarski @ (sk_D @ sk_B @ (k2_relat_1 @ sk_C) @ sk_A) @ sk_A) @ sk_B)),
% 0.20/0.50      inference('demod', [status(thm)], ['18', '19'])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      ((r2_hidden @ (sk_D @ sk_B @ (k2_relat_1 @ sk_C) @ sk_A) @ 
% 0.20/0.50        (k1_relat_1 @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['8', '9'])).
% 0.20/0.50  thf(d4_funct_1, axiom,
% 0.20/0.50    (![A:$i]:
% 0.20/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.50       ( ![B:$i,C:$i]:
% 0.20/0.50         ( ( ( ~( r2_hidden @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.20/0.50             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.20/0.50               ( ( C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.50           ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) =>
% 0.20/0.50             ( ( ( C ) = ( k1_funct_1 @ A @ B ) ) <=>
% 0.20/0.50               ( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) ) ) ))).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X6 : $i, X7 : $i, X9 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X6 @ (k1_relat_1 @ X7))
% 0.20/0.50          | ((X9) = (k1_funct_1 @ X7 @ X6))
% 0.20/0.50          | ~ (r2_hidden @ (k4_tarski @ X6 @ X9) @ X7)
% 0.20/0.50          | ~ (v1_funct_1 @ X7)
% 0.20/0.50          | ~ (v1_relat_1 @ X7))),
% 0.20/0.50      inference('cnf', [status(esa)], [d4_funct_1])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (v1_relat_1 @ sk_B)
% 0.20/0.50          | ~ (v1_funct_1 @ sk_B)
% 0.20/0.50          | ~ (r2_hidden @ 
% 0.20/0.50               (k4_tarski @ (sk_D @ sk_B @ (k2_relat_1 @ sk_C) @ sk_A) @ X0) @ 
% 0.20/0.50               sk_B)
% 0.20/0.50          | ((X0)
% 0.20/0.50              = (k1_funct_1 @ sk_B @ (sk_D @ sk_B @ (k2_relat_1 @ sk_C) @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('24', plain, ((v1_relat_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('25', plain, ((v1_funct_1 @ sk_B)),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r2_hidden @ 
% 0.20/0.50             (k4_tarski @ (sk_D @ sk_B @ (k2_relat_1 @ sk_C) @ sk_A) @ X0) @ 
% 0.20/0.50             sk_B)
% 0.20/0.50          | ((X0)
% 0.20/0.50              = (k1_funct_1 @ sk_B @ (sk_D @ sk_B @ (k2_relat_1 @ sk_C) @ sk_A))))),
% 0.20/0.50      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (((sk_A)
% 0.20/0.50         = (k1_funct_1 @ sk_B @ (sk_D @ sk_B @ (k2_relat_1 @ sk_C) @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['20', '26'])).
% 0.20/0.50  thf('28', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_B))),
% 0.20/0.50      inference('demod', [status(thm)], ['15', '27'])).
% 0.20/0.50  thf('29', plain, ($false), inference('demod', [status(thm)], ['0', '28'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
