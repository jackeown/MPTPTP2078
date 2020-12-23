%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GiGFVLzIw7

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   58 (  80 expanded)
%              Number of leaves         :   20 (  34 expanded)
%              Depth                    :   13
%              Number of atoms          :  453 ( 734 expanded)
%              Number of equality atoms :   14 (  19 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t125_funct_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r1_xboole_0 @ A @ B )
          & ( v2_funct_1 @ C ) )
       => ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( ( r1_xboole_0 @ A @ B )
            & ( v2_funct_1 @ C ) )
         => ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t125_funct_1])).

thf('0',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(idempotence_k3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( k3_xboole_0 @ A @ A )
      = A ) )).

thf('1',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ X0 )
      = X0 ) ),
    inference(cnf,[status(esa)],[idempotence_k3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('2',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ X0 ) @ X0 )
      | ( r1_xboole_0 @ X0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ X4 ) )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    r1_xboole_0 @ ( k3_xboole_0 @ sk_A @ sk_B ) @ ( k3_xboole_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('7',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X7 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('8',plain,
    ( ( k3_xboole_0 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t121_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( v2_funct_1 @ C )
       => ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
          = ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k9_relat_1 @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) )
        = ( k3_xboole_0 @ ( k9_relat_1 @ X14 @ X15 ) @ ( k9_relat_1 @ X14 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t121_funct_1])).

thf('10',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X2 )
      | ( r2_hidden @ ( sk_C @ X2 @ X1 ) @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k9_relat_1 @ X2 @ X0 ) @ ( k9_relat_1 @ X2 @ X1 ) ) @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v2_funct_1 @ X2 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k9_relat_1 @ X0 @ sk_B ) @ ( k9_relat_1 @ X0 @ sk_A ) ) @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('13',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('14',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X12 ) @ X13 )
      | ( ( k9_relat_1 @ X12 @ X13 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('18',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) @ ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X7: $i] :
      ( ( X7 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X7 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( v2_funct_1 @ X14 )
      | ( ( k9_relat_1 @ X14 @ ( k3_xboole_0 @ X15 @ X16 ) )
        = ( k3_xboole_0 @ ( k9_relat_1 @ X14 @ X15 ) @ ( k9_relat_1 @ X14 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t121_funct_1])).

thf('22',plain,(
    ! [X1: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_xboole_0 @ X1 @ X4 ) )
      | ~ ( r1_xboole_0 @ X1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v2_funct_1 @ X2 )
      | ~ ( r1_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k9_relat_1 @ X1 @ k1_xboole_0 ) )
      | ~ ( r1_xboole_0 @ ( k9_relat_1 @ X1 @ X0 ) @ ( k9_relat_1 @ X1 @ k1_xboole_0 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ X1 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['15','24'])).

thf('26',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('27',plain,(
    ! [X0: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X2: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k9_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ~ ( r1_xboole_0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ ( k9_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['32','33','34','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.GiGFVLzIw7
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:16:56 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.51  % Solved by: fo/fo7.sh
% 0.22/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.51  % done 96 iterations in 0.042s
% 0.22/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.51  % SZS output start Refutation
% 0.22/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.51  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.51  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.22/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.51  thf(t125_funct_1, conjecture,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.51       ( ( ( r1_xboole_0 @ A @ B ) & ( v2_funct_1 @ C ) ) =>
% 0.22/0.51         ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.22/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.51    (~( ![A:$i,B:$i,C:$i]:
% 0.22/0.51        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.51          ( ( ( r1_xboole_0 @ A @ B ) & ( v2_funct_1 @ C ) ) =>
% 0.22/0.51            ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 0.22/0.51    inference('cnf.neg', [status(esa)], [t125_funct_1])).
% 0.22/0.51  thf('0', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf(idempotence_k3_xboole_0, axiom,
% 0.22/0.51    (![A:$i,B:$i]: ( ( k3_xboole_0 @ A @ A ) = ( A ) ))).
% 0.22/0.51  thf('1', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ X0) = (X0))),
% 0.22/0.51      inference('cnf', [status(esa)], [idempotence_k3_xboole_0])).
% 0.22/0.51  thf(t4_xboole_0, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.51            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.51       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.51            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.22/0.51  thf('2', plain,
% 0.22/0.51      (![X1 : $i, X2 : $i]:
% 0.22/0.51         ((r1_xboole_0 @ X1 @ X2)
% 0.22/0.51          | (r2_hidden @ (sk_C @ X2 @ X1) @ (k3_xboole_0 @ X1 @ X2)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.51  thf('3', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((r2_hidden @ (sk_C @ X0 @ X0) @ X0) | (r1_xboole_0 @ X0 @ X0))),
% 0.22/0.51      inference('sup+', [status(thm)], ['1', '2'])).
% 0.22/0.51  thf('4', plain,
% 0.22/0.51      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X1 @ X4))
% 0.22/0.51          | ~ (r1_xboole_0 @ X1 @ X4))),
% 0.22/0.51      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.51  thf('5', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.22/0.51          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.51  thf('6', plain,
% 0.22/0.51      ((r1_xboole_0 @ (k3_xboole_0 @ sk_A @ sk_B) @ (k3_xboole_0 @ sk_A @ sk_B))),
% 0.22/0.51      inference('sup-', [status(thm)], ['0', '5'])).
% 0.22/0.51  thf(t66_xboole_1, axiom,
% 0.22/0.51    (![A:$i]:
% 0.22/0.51     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.22/0.51       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.22/0.51  thf('7', plain,
% 0.22/0.51      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X7 @ X7))),
% 0.22/0.51      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.22/0.51  thf('8', plain, (((k3_xboole_0 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.51  thf(t121_funct_1, axiom,
% 0.22/0.51    (![A:$i,B:$i,C:$i]:
% 0.22/0.51     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.51       ( ( v2_funct_1 @ C ) =>
% 0.22/0.51         ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 0.22/0.51           ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 0.22/0.51  thf('9', plain,
% 0.22/0.51      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.51         (~ (v2_funct_1 @ X14)
% 0.22/0.51          | ((k9_relat_1 @ X14 @ (k3_xboole_0 @ X15 @ X16))
% 0.22/0.51              = (k3_xboole_0 @ (k9_relat_1 @ X14 @ X15) @ 
% 0.22/0.51                 (k9_relat_1 @ X14 @ X16)))
% 0.22/0.51          | ~ (v1_funct_1 @ X14)
% 0.22/0.51          | ~ (v1_relat_1 @ X14))),
% 0.22/0.51      inference('cnf', [status(esa)], [t121_funct_1])).
% 0.22/0.51  thf('10', plain,
% 0.22/0.51      (![X1 : $i, X2 : $i]:
% 0.22/0.51         ((r1_xboole_0 @ X1 @ X2)
% 0.22/0.51          | (r2_hidden @ (sk_C @ X2 @ X1) @ (k3_xboole_0 @ X1 @ X2)))),
% 0.22/0.51      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.51  thf('11', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         ((r2_hidden @ 
% 0.22/0.51           (sk_C @ (k9_relat_1 @ X2 @ X0) @ (k9_relat_1 @ X2 @ X1)) @ 
% 0.22/0.51           (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.22/0.51          | ~ (v1_relat_1 @ X2)
% 0.22/0.51          | ~ (v1_funct_1 @ X2)
% 0.22/0.51          | ~ (v2_funct_1 @ X2)
% 0.22/0.51          | (r1_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ (k9_relat_1 @ X2 @ X0)))),
% 0.22/0.51      inference('sup+', [status(thm)], ['9', '10'])).
% 0.22/0.51  thf('12', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((r2_hidden @ 
% 0.22/0.51           (sk_C @ (k9_relat_1 @ X0 @ sk_B) @ (k9_relat_1 @ X0 @ sk_A)) @ 
% 0.22/0.51           (k9_relat_1 @ X0 @ k1_xboole_0))
% 0.22/0.51          | (r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.22/0.51          | ~ (v2_funct_1 @ X0)
% 0.22/0.51          | ~ (v1_funct_1 @ X0)
% 0.22/0.51          | ~ (v1_relat_1 @ X0))),
% 0.22/0.51      inference('sup+', [status(thm)], ['8', '11'])).
% 0.22/0.51  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.22/0.51  thf('13', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.22/0.51      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.22/0.51  thf(t151_relat_1, axiom,
% 0.22/0.51    (![A:$i,B:$i]:
% 0.22/0.51     ( ( v1_relat_1 @ B ) =>
% 0.22/0.51       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.51         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.51  thf('14', plain,
% 0.22/0.51      (![X12 : $i, X13 : $i]:
% 0.22/0.51         (~ (r1_xboole_0 @ (k1_relat_1 @ X12) @ X13)
% 0.22/0.51          | ((k9_relat_1 @ X12 @ X13) = (k1_xboole_0))
% 0.22/0.51          | ~ (v1_relat_1 @ X12))),
% 0.22/0.51      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.22/0.51  thf('15', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (v1_relat_1 @ X0)
% 0.22/0.51          | ((k9_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.51  thf('16', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.22/0.51      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.22/0.51  thf('17', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i]:
% 0.22/0.51         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0))
% 0.22/0.51          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.51  thf('18', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (r1_xboole_0 @ (k3_xboole_0 @ X0 @ k1_xboole_0) @ 
% 0.22/0.51          (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.51  thf('19', plain,
% 0.22/0.51      (![X7 : $i]: (((X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X7 @ X7))),
% 0.22/0.51      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.22/0.51  thf('20', plain,
% 0.22/0.51      (![X0 : $i]: ((k3_xboole_0 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.51  thf('21', plain,
% 0.22/0.51      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.51         (~ (v2_funct_1 @ X14)
% 0.22/0.51          | ((k9_relat_1 @ X14 @ (k3_xboole_0 @ X15 @ X16))
% 0.22/0.51              = (k3_xboole_0 @ (k9_relat_1 @ X14 @ X15) @ 
% 0.22/0.51                 (k9_relat_1 @ X14 @ X16)))
% 0.22/0.51          | ~ (v1_funct_1 @ X14)
% 0.22/0.51          | ~ (v1_relat_1 @ X14))),
% 0.22/0.51      inference('cnf', [status(esa)], [t121_funct_1])).
% 0.22/0.51  thf('22', plain,
% 0.22/0.51      (![X1 : $i, X3 : $i, X4 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X3 @ (k3_xboole_0 @ X1 @ X4))
% 0.22/0.51          | ~ (r1_xboole_0 @ X1 @ X4))),
% 0.22/0.51      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.22/0.51  thf('23', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X3 @ (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.22/0.51          | ~ (v1_relat_1 @ X2)
% 0.22/0.51          | ~ (v1_funct_1 @ X2)
% 0.22/0.51          | ~ (v2_funct_1 @ X2)
% 0.22/0.51          | ~ (r1_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ (k9_relat_1 @ X2 @ X0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.51  thf('24', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X2 @ (k9_relat_1 @ X1 @ k1_xboole_0))
% 0.22/0.51          | ~ (r1_xboole_0 @ (k9_relat_1 @ X1 @ X0) @ 
% 0.22/0.51               (k9_relat_1 @ X1 @ k1_xboole_0))
% 0.22/0.51          | ~ (v2_funct_1 @ X1)
% 0.22/0.51          | ~ (v1_funct_1 @ X1)
% 0.22/0.51          | ~ (v1_relat_1 @ X1))),
% 0.22/0.51      inference('sup-', [status(thm)], ['20', '23'])).
% 0.22/0.51  thf('25', plain,
% 0.22/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.51         (~ (r1_xboole_0 @ (k9_relat_1 @ X0 @ X1) @ k1_xboole_0)
% 0.22/0.51          | ~ (v1_relat_1 @ X0)
% 0.22/0.51          | ~ (v1_relat_1 @ X0)
% 0.22/0.51          | ~ (v1_funct_1 @ X0)
% 0.22/0.51          | ~ (v2_funct_1 @ X0)
% 0.22/0.51          | ~ (r2_hidden @ X2 @ (k9_relat_1 @ X0 @ k1_xboole_0)))),
% 0.22/0.51      inference('sup-', [status(thm)], ['15', '24'])).
% 0.22/0.51  thf('26', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.22/0.51      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.22/0.51  thf('27', plain,
% 0.22/0.51      (![X0 : $i, X2 : $i]:
% 0.22/0.51         (~ (v1_relat_1 @ X0)
% 0.22/0.51          | ~ (v1_relat_1 @ X0)
% 0.22/0.51          | ~ (v1_funct_1 @ X0)
% 0.22/0.51          | ~ (v2_funct_1 @ X0)
% 0.22/0.51          | ~ (r2_hidden @ X2 @ (k9_relat_1 @ X0 @ k1_xboole_0)))),
% 0.22/0.51      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.51  thf('28', plain,
% 0.22/0.51      (![X0 : $i, X2 : $i]:
% 0.22/0.51         (~ (r2_hidden @ X2 @ (k9_relat_1 @ X0 @ k1_xboole_0))
% 0.22/0.51          | ~ (v2_funct_1 @ X0)
% 0.22/0.51          | ~ (v1_funct_1 @ X0)
% 0.22/0.51          | ~ (v1_relat_1 @ X0))),
% 0.22/0.51      inference('simplify', [status(thm)], ['27'])).
% 0.22/0.51  thf('29', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         (~ (v1_relat_1 @ X0)
% 0.22/0.51          | ~ (v1_funct_1 @ X0)
% 0.22/0.51          | ~ (v2_funct_1 @ X0)
% 0.22/0.51          | (r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.22/0.51          | ~ (v1_relat_1 @ X0)
% 0.22/0.51          | ~ (v1_funct_1 @ X0)
% 0.22/0.51          | ~ (v2_funct_1 @ X0))),
% 0.22/0.51      inference('sup-', [status(thm)], ['12', '28'])).
% 0.22/0.51  thf('30', plain,
% 0.22/0.51      (![X0 : $i]:
% 0.22/0.51         ((r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.22/0.51          | ~ (v2_funct_1 @ X0)
% 0.22/0.51          | ~ (v1_funct_1 @ X0)
% 0.22/0.51          | ~ (v1_relat_1 @ X0))),
% 0.22/0.51      inference('simplify', [status(thm)], ['29'])).
% 0.22/0.51  thf('31', plain,
% 0.22/0.51      (~ (r1_xboole_0 @ (k9_relat_1 @ sk_C_1 @ sk_A) @ 
% 0.22/0.51          (k9_relat_1 @ sk_C_1 @ sk_B))),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('32', plain,
% 0.22/0.51      ((~ (v1_relat_1 @ sk_C_1)
% 0.22/0.51        | ~ (v1_funct_1 @ sk_C_1)
% 0.22/0.51        | ~ (v2_funct_1 @ sk_C_1))),
% 0.22/0.51      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.51  thf('33', plain, ((v1_relat_1 @ sk_C_1)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('34', plain, ((v1_funct_1 @ sk_C_1)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('35', plain, ((v2_funct_1 @ sk_C_1)),
% 0.22/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.51  thf('36', plain, ($false),
% 0.22/0.51      inference('demod', [status(thm)], ['32', '33', '34', '35'])).
% 0.22/0.51  
% 0.22/0.51  % SZS output end Refutation
% 0.22/0.51  
% 0.22/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
