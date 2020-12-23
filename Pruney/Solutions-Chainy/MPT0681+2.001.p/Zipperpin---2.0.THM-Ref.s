%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FXya4pB3iS

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:46:02 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   50 (  65 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :   12
%              Number of atoms          :  439 ( 679 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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

thf('1',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d12_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_funct_1 @ A )
        & ( v1_relat_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) )
                  & ( r2_hidden @ E @ B )
                  & ( D
                    = ( k1_funct_1 @ A @ E ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( D
          = ( k1_funct_1 @ A @ E ) )
        & ( r2_hidden @ E @ B )
        & ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) )).

thf('2',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ ( sk_D @ X13 @ X14 @ X15 ) @ X13 )
      | ( zip_tseitin_0 @ ( sk_E @ X13 @ X14 @ X15 ) @ ( sk_D @ X13 @ X14 @ X15 ) @ X14 @ X15 )
      | ( X13
        = ( k9_relat_1 @ X15 @ X14 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('3',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X9 @ X11 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X2
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('5',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ ( sk_E @ ( k3_xboole_0 @ X1 @ X0 ) @ X3 @ X2 ) @ X3 )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k9_relat_1 @ X2 @ X3 ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k3_xboole_0 @ sk_A @ sk_B )
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ ( k3_xboole_0 @ sk_A @ sk_B ) @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ sk_A @ sk_B )
        = ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k3_xboole_0 @ sk_A @ sk_B )
        = ( k9_relat_1 @ X0 @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['0','9'])).

thf(t121_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( v2_funct_1 @ C )
       => ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) )
          = ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ) )).

thf('11',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v2_funct_1 @ X21 )
      | ( ( k9_relat_1 @ X21 @ ( k3_xboole_0 @ X22 @ X23 ) )
        = ( k3_xboole_0 @ ( k9_relat_1 @ X21 @ X22 ) @ ( k9_relat_1 @ X21 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t121_funct_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k9_relat_1 @ X2 @ X0 ) @ ( k9_relat_1 @ X2 @ X1 ) ) @ ( k9_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X2 )
      | ~ ( v1_funct_1 @ X2 )
      | ~ ( v2_funct_1 @ X2 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X2 @ X1 ) @ ( k9_relat_1 @ X2 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ ( k9_relat_1 @ X0 @ sk_B ) @ ( k9_relat_1 @ X0 @ sk_A ) ) @ ( k3_xboole_0 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['10','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_C @ ( k9_relat_1 @ X0 @ sk_B ) @ ( k9_relat_1 @ X0 @ sk_A ) ) @ ( k3_xboole_0 @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( r1_xboole_0 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    r1_xboole_0 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k9_relat_1 @ X0 @ sk_A ) @ ( k9_relat_1 @ X0 @ sk_B ) )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( r1_xboole_0 @ ( k9_relat_1 @ sk_C_1 @ sk_A ) @ ( k9_relat_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v2_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    $false ),
    inference(demod,[status(thm)],['21','22','23','24'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FXya4pB3iS
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:42:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.36/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.59  % Solved by: fo/fo7.sh
% 0.36/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.59  % done 97 iterations in 0.126s
% 0.36/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.59  % SZS output start Refutation
% 0.36/0.59  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.36/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.59  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.36/0.59  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.36/0.59  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.36/0.59  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.36/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.59  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.36/0.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.36/0.59  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.36/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.59  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.36/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.36/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.59  thf(t125_funct_1, conjecture,
% 0.36/0.59    (![A:$i,B:$i,C:$i]:
% 0.36/0.59     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.36/0.59       ( ( ( r1_xboole_0 @ A @ B ) & ( v2_funct_1 @ C ) ) =>
% 0.36/0.59         ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ))).
% 0.36/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.59    (~( ![A:$i,B:$i,C:$i]:
% 0.36/0.59        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.36/0.59          ( ( ( r1_xboole_0 @ A @ B ) & ( v2_funct_1 @ C ) ) =>
% 0.36/0.59            ( r1_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) )),
% 0.36/0.59    inference('cnf.neg', [status(esa)], [t125_funct_1])).
% 0.36/0.59  thf('0', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('1', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(d12_funct_1, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.36/0.59       ( ![B:$i,C:$i]:
% 0.36/0.59         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.36/0.59           ( ![D:$i]:
% 0.36/0.59             ( ( r2_hidden @ D @ C ) <=>
% 0.36/0.59               ( ?[E:$i]:
% 0.36/0.59                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 0.36/0.59                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 0.36/0.59  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.36/0.59  thf(zf_stmt_2, axiom,
% 0.36/0.59    (![E:$i,D:$i,B:$i,A:$i]:
% 0.36/0.59     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.36/0.59       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 0.36/0.59         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 0.36/0.59  thf(zf_stmt_3, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.59       ( ![B:$i,C:$i]:
% 0.36/0.59         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.36/0.59           ( ![D:$i]:
% 0.36/0.59             ( ( r2_hidden @ D @ C ) <=>
% 0.36/0.59               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 0.36/0.59  thf('2', plain,
% 0.36/0.59      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.36/0.59         ((r2_hidden @ (sk_D @ X13 @ X14 @ X15) @ X13)
% 0.36/0.59          | (zip_tseitin_0 @ (sk_E @ X13 @ X14 @ X15) @ 
% 0.36/0.59             (sk_D @ X13 @ X14 @ X15) @ X14 @ X15)
% 0.36/0.59          | ((X13) = (k9_relat_1 @ X15 @ X14))
% 0.36/0.59          | ~ (v1_funct_1 @ X15)
% 0.36/0.59          | ~ (v1_relat_1 @ X15))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.36/0.59  thf('3', plain,
% 0.36/0.59      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.36/0.59         ((r2_hidden @ X9 @ X11) | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X8))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.36/0.59  thf('4', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.59         (~ (v1_relat_1 @ X0)
% 0.36/0.59          | ~ (v1_funct_1 @ X0)
% 0.36/0.59          | ((X2) = (k9_relat_1 @ X0 @ X1))
% 0.36/0.59          | (r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.36/0.59          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X1))),
% 0.36/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.59  thf(t4_xboole_0, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.36/0.59            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.36/0.59       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.36/0.59            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.36/0.59  thf('5', plain,
% 0.36/0.59      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.36/0.59         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.36/0.59          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.36/0.59      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.36/0.59  thf('6', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.59         ((r2_hidden @ (sk_E @ (k3_xboole_0 @ X1 @ X0) @ X3 @ X2) @ X3)
% 0.36/0.59          | ((k3_xboole_0 @ X1 @ X0) = (k9_relat_1 @ X2 @ X3))
% 0.36/0.59          | ~ (v1_funct_1 @ X2)
% 0.36/0.59          | ~ (v1_relat_1 @ X2)
% 0.36/0.59          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['4', '5'])).
% 0.36/0.59  thf('7', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         (~ (v1_relat_1 @ X0)
% 0.36/0.59          | ~ (v1_funct_1 @ X0)
% 0.36/0.59          | ((k3_xboole_0 @ sk_A @ sk_B) = (k9_relat_1 @ X0 @ X1))
% 0.36/0.59          | (r2_hidden @ (sk_E @ (k3_xboole_0 @ sk_A @ sk_B) @ X1 @ X0) @ X1))),
% 0.36/0.59      inference('sup-', [status(thm)], ['1', '6'])).
% 0.36/0.59  thf('8', plain,
% 0.36/0.59      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.36/0.59         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.36/0.59          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.36/0.59      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.36/0.59  thf('9', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.59         (((k3_xboole_0 @ sk_A @ sk_B)
% 0.36/0.59            = (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.36/0.59          | ~ (v1_funct_1 @ X2)
% 0.36/0.59          | ~ (v1_relat_1 @ X2)
% 0.36/0.59          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.59  thf('10', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (~ (v1_relat_1 @ X0)
% 0.36/0.59          | ~ (v1_funct_1 @ X0)
% 0.36/0.59          | ((k3_xboole_0 @ sk_A @ sk_B)
% 0.36/0.59              = (k9_relat_1 @ X0 @ (k3_xboole_0 @ sk_A @ sk_B))))),
% 0.36/0.59      inference('sup-', [status(thm)], ['0', '9'])).
% 0.36/0.59  thf(t121_funct_1, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i]:
% 0.36/0.59     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.36/0.59       ( ( v2_funct_1 @ C ) =>
% 0.36/0.59         ( ( k9_relat_1 @ C @ ( k3_xboole_0 @ A @ B ) ) =
% 0.36/0.59           ( k3_xboole_0 @ ( k9_relat_1 @ C @ A ) @ ( k9_relat_1 @ C @ B ) ) ) ) ))).
% 0.36/0.59  thf('11', plain,
% 0.36/0.59      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.36/0.59         (~ (v2_funct_1 @ X21)
% 0.36/0.59          | ((k9_relat_1 @ X21 @ (k3_xboole_0 @ X22 @ X23))
% 0.36/0.59              = (k3_xboole_0 @ (k9_relat_1 @ X21 @ X22) @ 
% 0.36/0.59                 (k9_relat_1 @ X21 @ X23)))
% 0.36/0.59          | ~ (v1_funct_1 @ X21)
% 0.36/0.59          | ~ (v1_relat_1 @ X21))),
% 0.36/0.59      inference('cnf', [status(esa)], [t121_funct_1])).
% 0.36/0.59  thf('12', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         ((r1_xboole_0 @ X0 @ X1)
% 0.36/0.59          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k3_xboole_0 @ X0 @ X1)))),
% 0.36/0.59      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.36/0.59  thf('13', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.59         ((r2_hidden @ 
% 0.36/0.59           (sk_C @ (k9_relat_1 @ X2 @ X0) @ (k9_relat_1 @ X2 @ X1)) @ 
% 0.36/0.59           (k9_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 0.36/0.59          | ~ (v1_relat_1 @ X2)
% 0.36/0.59          | ~ (v1_funct_1 @ X2)
% 0.36/0.59          | ~ (v2_funct_1 @ X2)
% 0.36/0.59          | (r1_xboole_0 @ (k9_relat_1 @ X2 @ X1) @ (k9_relat_1 @ X2 @ X0)))),
% 0.36/0.59      inference('sup+', [status(thm)], ['11', '12'])).
% 0.36/0.59  thf('14', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((r2_hidden @ 
% 0.36/0.59           (sk_C @ (k9_relat_1 @ X0 @ sk_B) @ (k9_relat_1 @ X0 @ sk_A)) @ 
% 0.36/0.59           (k3_xboole_0 @ sk_A @ sk_B))
% 0.36/0.59          | ~ (v1_funct_1 @ X0)
% 0.36/0.59          | ~ (v1_relat_1 @ X0)
% 0.36/0.59          | (r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.36/0.59          | ~ (v2_funct_1 @ X0)
% 0.36/0.59          | ~ (v1_funct_1 @ X0)
% 0.36/0.59          | ~ (v1_relat_1 @ X0))),
% 0.36/0.59      inference('sup+', [status(thm)], ['10', '13'])).
% 0.36/0.59  thf('15', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (~ (v2_funct_1 @ X0)
% 0.36/0.59          | (r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.36/0.59          | ~ (v1_relat_1 @ X0)
% 0.36/0.59          | ~ (v1_funct_1 @ X0)
% 0.36/0.59          | (r2_hidden @ 
% 0.36/0.59             (sk_C @ (k9_relat_1 @ X0 @ sk_B) @ (k9_relat_1 @ X0 @ sk_A)) @ 
% 0.36/0.59             (k3_xboole_0 @ sk_A @ sk_B)))),
% 0.36/0.59      inference('simplify', [status(thm)], ['14'])).
% 0.36/0.59  thf('16', plain,
% 0.36/0.59      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.36/0.59         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.36/0.59          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.36/0.59      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.36/0.59  thf('17', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (~ (v1_funct_1 @ X0)
% 0.36/0.59          | ~ (v1_relat_1 @ X0)
% 0.36/0.59          | (r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.36/0.59          | ~ (v2_funct_1 @ X0)
% 0.36/0.59          | ~ (r1_xboole_0 @ sk_A @ sk_B))),
% 0.36/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.59  thf('18', plain, ((r1_xboole_0 @ sk_A @ sk_B)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('19', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (~ (v1_funct_1 @ X0)
% 0.36/0.59          | ~ (v1_relat_1 @ X0)
% 0.36/0.59          | (r1_xboole_0 @ (k9_relat_1 @ X0 @ sk_A) @ (k9_relat_1 @ X0 @ sk_B))
% 0.36/0.59          | ~ (v2_funct_1 @ X0))),
% 0.36/0.59      inference('demod', [status(thm)], ['17', '18'])).
% 0.36/0.59  thf('20', plain,
% 0.36/0.59      (~ (r1_xboole_0 @ (k9_relat_1 @ sk_C_1 @ sk_A) @ 
% 0.36/0.59          (k9_relat_1 @ sk_C_1 @ sk_B))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('21', plain,
% 0.36/0.59      ((~ (v2_funct_1 @ sk_C_1)
% 0.36/0.59        | ~ (v1_relat_1 @ sk_C_1)
% 0.36/0.59        | ~ (v1_funct_1 @ sk_C_1))),
% 0.36/0.59      inference('sup-', [status(thm)], ['19', '20'])).
% 0.36/0.59  thf('22', plain, ((v2_funct_1 @ sk_C_1)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('23', plain, ((v1_relat_1 @ sk_C_1)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('24', plain, ((v1_funct_1 @ sk_C_1)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('25', plain, ($false),
% 0.36/0.59      inference('demod', [status(thm)], ['21', '22', '23', '24'])).
% 0.36/0.59  
% 0.36/0.59  % SZS output end Refutation
% 0.36/0.59  
% 0.36/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
