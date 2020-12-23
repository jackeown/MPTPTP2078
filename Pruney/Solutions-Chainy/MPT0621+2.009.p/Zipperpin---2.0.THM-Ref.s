%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.c0BN4oLOGK

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:29 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 101 expanded)
%              Number of leaves         :   22 (  42 expanded)
%              Depth                    :   17
%              Number of atoms          :  494 ( 890 expanded)
%              Number of equality atoms :   59 (  98 expanded)
%              Maximal formula depth    :   14 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(s3_funct_1__e2_24__funct_1,axiom,(
    ! [A: $i,B: $i] :
    ? [C: $i] :
      ( ! [D: $i] :
          ( ( r2_hidden @ D @ A )
         => ( ( k1_funct_1 @ C @ D )
            = B ) )
      & ( ( k1_relat_1 @ C )
        = A )
      & ( v1_funct_1 @ C )
      & ( v1_relat_1 @ C ) ) )).

thf('0',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( sk_C_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf(d13_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ B )
                  & ( r2_hidden @ ( k4_tarski @ E @ D ) @ A ) ) ) ) ) )).

thf('1',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ ( sk_D @ X6 @ X7 @ X8 ) @ X6 )
      | ( r2_hidden @ ( sk_E @ X6 @ X7 @ X8 ) @ X7 )
      | ( X6
        = ( k9_relat_1 @ X8 @ X7 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k3_xboole_0 @ X0 @ X3 ) )
      | ~ ( r1_xboole_0 @ X0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('5',plain,(
    ! [X5: $i] :
      ( r1_xboole_0 @ X5 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('6',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( k1_xboole_0
        = ( k9_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ k1_xboole_0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf('8',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k9_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ ( sk_D @ X6 @ X7 @ X8 ) @ X6 )
      | ( r2_hidden @ ( sk_E @ X6 @ X7 @ X8 ) @ X7 )
      | ( X6
        = ( k9_relat_1 @ X8 @ X7 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf('11',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X1
        = ( k9_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(s3_funct_1__e2_25__funct_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( ( k1_funct_1 @ B @ C )
            = k1_xboole_0 ) )
      & ( ( k1_relat_1 @ B )
        = A )
      & ( v1_funct_1 @ B )
      & ( v1_relat_1 @ B ) ) )).

thf('13',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k1_funct_1 @ ( sk_B @ X17 ) @ X18 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k9_relat_1 @ X1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_funct_1 @ ( sk_B @ X0 ) @ ( sk_D @ X0 @ k1_xboole_0 @ X1 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X14: $i,X15: $i] :
      ( ( k1_relat_1 @ ( sk_C_1 @ X14 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('16',plain,(
    ! [X17: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X17 ) )
      = X17 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf(t16_funct_1,conjecture,(
    ! [A: $i] :
      ( ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ! [C: $i] :
              ( ( ( v1_relat_1 @ C )
                & ( v1_funct_1 @ C ) )
             => ( ( ( ( k1_relat_1 @ B )
                    = A )
                  & ( ( k1_relat_1 @ C )
                    = A ) )
               => ( B = C ) ) ) )
     => ( A = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ! [C: $i] :
                ( ( ( v1_relat_1 @ C )
                  & ( v1_funct_1 @ C ) )
               => ( ( ( ( k1_relat_1 @ B )
                      = A )
                    & ( ( k1_relat_1 @ C )
                      = A ) )
                 => ( B = C ) ) ) )
       => ( A = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t16_funct_1])).

thf('17',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ( X20 = X19 )
      | ( ( k1_relat_1 @ X19 )
       != sk_A )
      | ( ( k1_relat_1 @ X20 )
       != sk_A )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ( X1
        = ( sk_B @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_B @ X0 ) )
      | ~ ( v1_relat_1 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X17: $i] :
      ( v1_funct_1 @ ( sk_B @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('20',plain,(
    ! [X17: $i] :
      ( v1_relat_1 @ ( sk_B @ X17 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ( X1
        = ( sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X1: $i] :
      ( ( X1
        = ( sk_B @ sk_A ) )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ( ( sk_C_1 @ X1 @ X0 )
        = ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['15','22'])).

thf('24',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_relat_1 @ ( sk_C_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('25',plain,(
    ! [X14: $i,X15: $i] :
      ( v1_funct_1 @ ( sk_C_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ( ( sk_C_1 @ X1 @ X0 )
        = ( sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,(
    ! [X1: $i] :
      ( ( sk_C_1 @ X1 @ sk_A )
      = ( sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X1
        = ( k9_relat_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ X1 @ k1_xboole_0 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('29',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X14 @ X15 ) @ X16 )
        = X14 )
      | ~ ( r2_hidden @ X16 @ X15 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0
        = ( k9_relat_1 @ X1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k1_funct_1 @ ( sk_C_1 @ X2 @ X0 ) @ ( sk_D @ X0 @ k1_xboole_0 @ X1 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ ( sk_B @ sk_A ) @ ( sk_D @ sk_A @ k1_xboole_0 @ X1 ) )
        = X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( sk_A
        = ( k9_relat_1 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup+',[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( sk_A
        = ( k9_relat_1 @ X1 @ k1_xboole_0 ) )
      | ( sk_A
        = ( k9_relat_1 @ X1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k9_relat_1 @ X1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A != X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( sk_A
        = ( k9_relat_1 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X1: $i] :
      ( ( sk_A
        = ( k9_relat_1 @ X1 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['9','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ~ ( v1_relat_1 @ X0 ) ),
    inference('simplify_reflect-',[status(thm)],['38','39'])).

thf('41',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.c0BN4oLOGK
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:46:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 66 iterations in 0.058s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.51  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.51  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.20/0.51  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.20/0.51  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.51  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.51  thf(s3_funct_1__e2_24__funct_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ?[C:$i]:
% 0.20/0.51       ( ( ![D:$i]:
% 0.20/0.51           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 0.20/0.51         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.20/0.51         ( v1_relat_1 @ C ) ) ))).
% 0.20/0.51  thf('0', plain, (![X14 : $i, X15 : $i]: (v1_relat_1 @ (sk_C_1 @ X14 @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.20/0.51  thf(d13_relat_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) =>
% 0.20/0.51       ( ![B:$i,C:$i]:
% 0.20/0.51         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.20/0.51           ( ![D:$i]:
% 0.20/0.51             ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.51               ( ?[E:$i]:
% 0.20/0.51                 ( ( r2_hidden @ E @ B ) & 
% 0.20/0.51                   ( r2_hidden @ ( k4_tarski @ E @ D ) @ A ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.51         ((r2_hidden @ (sk_D @ X6 @ X7 @ X8) @ X6)
% 0.20/0.51          | (r2_hidden @ (sk_E @ X6 @ X7 @ X8) @ X7)
% 0.20/0.51          | ((X6) = (k9_relat_1 @ X8 @ X7))
% 0.20/0.51          | ~ (v1_relat_1 @ X8))),
% 0.20/0.51      inference('cnf', [status(esa)], [d13_relat_1])).
% 0.20/0.51  thf(t2_boole, axiom,
% 0.20/0.51    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [t2_boole])).
% 0.20/0.51  thf(t4_xboole_0, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.51            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.20/0.51       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.20/0.51            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X2 @ (k3_xboole_0 @ X0 @ X3))
% 0.20/0.51          | ~ (r1_xboole_0 @ X0 @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.51  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 0.20/0.51  thf('5', plain, (![X5 : $i]: (r1_xboole_0 @ X5 @ k1_xboole_0)),
% 0.20/0.51      inference('cnf', [status(esa)], [t65_xboole_1])).
% 0.20/0.51  thf('6', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.51      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X0)
% 0.20/0.51          | ((k1_xboole_0) = (k9_relat_1 @ X0 @ X1))
% 0.20/0.51          | (r2_hidden @ (sk_E @ k1_xboole_0 @ X1 @ X0) @ X1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '6'])).
% 0.20/0.51  thf('8', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.51      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((k1_xboole_0) = (k9_relat_1 @ X0 @ k1_xboole_0))
% 0.20/0.51          | ~ (v1_relat_1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.51         ((r2_hidden @ (sk_D @ X6 @ X7 @ X8) @ X6)
% 0.20/0.51          | (r2_hidden @ (sk_E @ X6 @ X7 @ X8) @ X7)
% 0.20/0.51          | ((X6) = (k9_relat_1 @ X8 @ X7))
% 0.20/0.51          | ~ (v1_relat_1 @ X8))),
% 0.20/0.51      inference('cnf', [status(esa)], [d13_relat_1])).
% 0.20/0.51  thf('11', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 0.20/0.51      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X0)
% 0.20/0.51          | ((X1) = (k9_relat_1 @ X0 @ k1_xboole_0))
% 0.20/0.51          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ?[B:$i]:
% 0.20/0.51       ( ( ![C:$i]:
% 0.20/0.51           ( ( r2_hidden @ C @ A ) =>
% 0.20/0.51             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.51         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.20/0.51         ( v1_relat_1 @ B ) ) ))).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X17 : $i, X18 : $i]:
% 0.20/0.51         (((k1_funct_1 @ (sk_B @ X17) @ X18) = (k1_xboole_0))
% 0.20/0.51          | ~ (r2_hidden @ X18 @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((X0) = (k9_relat_1 @ X1 @ k1_xboole_0))
% 0.20/0.51          | ~ (v1_relat_1 @ X1)
% 0.20/0.51          | ((k1_funct_1 @ (sk_B @ X0) @ (sk_D @ X0 @ k1_xboole_0 @ X1))
% 0.20/0.51              = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i]: ((k1_relat_1 @ (sk_C_1 @ X14 @ X15)) = (X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.20/0.51  thf('16', plain, (![X17 : $i]: ((k1_relat_1 @ (sk_B @ X17)) = (X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.51  thf(t16_funct_1, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ![B:$i]:
% 0.20/0.51         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.51               ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.51                   ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.20/0.51                 ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.20/0.51       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( ![B:$i]:
% 0.20/0.51            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.51              ( ![C:$i]:
% 0.20/0.51                ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.51                  ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.51                      ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.20/0.51                    ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.20/0.51          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t16_funct_1])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (![X19 : $i, X20 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X19)
% 0.20/0.51          | ~ (v1_funct_1 @ X19)
% 0.20/0.51          | ((X20) = (X19))
% 0.20/0.51          | ((k1_relat_1 @ X19) != (sk_A))
% 0.20/0.51          | ((k1_relat_1 @ X20) != (sk_A))
% 0.20/0.51          | ~ (v1_funct_1 @ X20)
% 0.20/0.51          | ~ (v1_relat_1 @ X20))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((X0) != (sk_A))
% 0.20/0.51          | ~ (v1_relat_1 @ X1)
% 0.20/0.51          | ~ (v1_funct_1 @ X1)
% 0.20/0.51          | ((k1_relat_1 @ X1) != (sk_A))
% 0.20/0.51          | ((X1) = (sk_B @ X0))
% 0.20/0.51          | ~ (v1_funct_1 @ (sk_B @ X0))
% 0.20/0.51          | ~ (v1_relat_1 @ (sk_B @ X0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['16', '17'])).
% 0.20/0.51  thf('19', plain, (![X17 : $i]: (v1_funct_1 @ (sk_B @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.51  thf('20', plain, (![X17 : $i]: (v1_relat_1 @ (sk_B @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((X0) != (sk_A))
% 0.20/0.51          | ~ (v1_relat_1 @ X1)
% 0.20/0.51          | ~ (v1_funct_1 @ X1)
% 0.20/0.51          | ((k1_relat_1 @ X1) != (sk_A))
% 0.20/0.51          | ((X1) = (sk_B @ X0)))),
% 0.20/0.51      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X1 : $i]:
% 0.20/0.51         (((X1) = (sk_B @ sk_A))
% 0.20/0.51          | ((k1_relat_1 @ X1) != (sk_A))
% 0.20/0.51          | ~ (v1_funct_1 @ X1)
% 0.20/0.51          | ~ (v1_relat_1 @ X1))),
% 0.20/0.51      inference('simplify', [status(thm)], ['21'])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((X0) != (sk_A))
% 0.20/0.51          | ~ (v1_relat_1 @ (sk_C_1 @ X1 @ X0))
% 0.20/0.51          | ~ (v1_funct_1 @ (sk_C_1 @ X1 @ X0))
% 0.20/0.51          | ((sk_C_1 @ X1 @ X0) = (sk_B @ sk_A)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['15', '22'])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i]: (v1_relat_1 @ (sk_C_1 @ X14 @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i]: (v1_funct_1 @ (sk_C_1 @ X14 @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((X0) != (sk_A)) | ((sk_C_1 @ X1 @ X0) = (sk_B @ sk_A)))),
% 0.20/0.51      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.20/0.51  thf('27', plain, (![X1 : $i]: ((sk_C_1 @ X1 @ sk_A) = (sk_B @ sk_A))),
% 0.20/0.51      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X0)
% 0.20/0.51          | ((X1) = (k9_relat_1 @ X0 @ k1_xboole_0))
% 0.20/0.51          | (r2_hidden @ (sk_D @ X1 @ k1_xboole_0 @ X0) @ X1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.51         (((k1_funct_1 @ (sk_C_1 @ X14 @ X15) @ X16) = (X14))
% 0.20/0.51          | ~ (r2_hidden @ X16 @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (((X0) = (k9_relat_1 @ X1 @ k1_xboole_0))
% 0.20/0.51          | ~ (v1_relat_1 @ X1)
% 0.20/0.51          | ((k1_funct_1 @ (sk_C_1 @ X2 @ X0) @ (sk_D @ X0 @ k1_xboole_0 @ X1))
% 0.20/0.51              = (X2)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((k1_funct_1 @ (sk_B @ sk_A) @ (sk_D @ sk_A @ k1_xboole_0 @ X1))
% 0.20/0.51            = (X0))
% 0.20/0.51          | ~ (v1_relat_1 @ X1)
% 0.20/0.51          | ((sk_A) = (k9_relat_1 @ X1 @ k1_xboole_0)))),
% 0.20/0.51      inference('sup+', [status(thm)], ['27', '30'])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((k1_xboole_0) = (X0))
% 0.20/0.51          | ~ (v1_relat_1 @ X1)
% 0.20/0.51          | ((sk_A) = (k9_relat_1 @ X1 @ k1_xboole_0))
% 0.20/0.51          | ((sk_A) = (k9_relat_1 @ X1 @ k1_xboole_0))
% 0.20/0.51          | ~ (v1_relat_1 @ X1))),
% 0.20/0.51      inference('sup+', [status(thm)], ['14', '31'])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((sk_A) = (k9_relat_1 @ X1 @ k1_xboole_0))
% 0.20/0.51          | ~ (v1_relat_1 @ X1)
% 0.20/0.51          | ((k1_xboole_0) = (X0)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['32'])).
% 0.20/0.51  thf('34', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (((sk_A) != (X0))
% 0.20/0.51          | ~ (v1_relat_1 @ X1)
% 0.20/0.51          | ((sk_A) = (k9_relat_1 @ X1 @ k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      (![X1 : $i]:
% 0.20/0.51         (((sk_A) = (k9_relat_1 @ X1 @ k1_xboole_0)) | ~ (v1_relat_1 @ X1))),
% 0.20/0.51      inference('simplify', [status(thm)], ['35'])).
% 0.20/0.51  thf('37', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (((sk_A) = (k1_xboole_0)) | ~ (v1_relat_1 @ X0) | ~ (v1_relat_1 @ X0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['9', '36'])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      (![X0 : $i]: (~ (v1_relat_1 @ X0) | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.51      inference('simplify', [status(thm)], ['37'])).
% 0.20/0.51  thf('39', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('40', plain, (![X0 : $i]: ~ (v1_relat_1 @ X0)),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['38', '39'])).
% 0.20/0.51  thf('41', plain, ($false), inference('sup-', [status(thm)], ['0', '40'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.35/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
