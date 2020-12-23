%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.f6IdxeqUNE

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:44:31 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   67 (  86 expanded)
%              Number of leaves         :   19 (  34 expanded)
%              Depth                    :   17
%              Number of atoms          :  549 ( 881 expanded)
%              Number of equality atoms :   57 (  90 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

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
    ! [X13: $i,X14: $i] :
      ( ( k1_relat_1 @ ( sk_C_1 @ X13 @ X14 ) )
      = X14 ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

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

thf('1',plain,(
    ! [X16: $i] :
      ( ( k1_relat_1 @ ( sk_B @ X16 ) )
      = X16 ) ),
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

thf('2',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( X19 = X18 )
      | ( ( k1_relat_1 @ X18 )
       != sk_A )
      | ( ( k1_relat_1 @ X19 )
       != sk_A )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
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
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X16: $i] :
      ( v1_funct_1 @ ( sk_B @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('5',plain,(
    ! [X16: $i] :
      ( v1_relat_1 @ ( sk_B @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ( X1
        = ( sk_B @ X0 ) ) ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ! [X1: $i] :
      ( ( X1
        = ( sk_B @ sk_A ) )
      | ( ( k1_relat_1 @ X1 )
       != sk_A )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ~ ( v1_relat_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_C_1 @ X1 @ X0 ) )
      | ( ( sk_C_1 @ X1 @ X0 )
        = ( sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['0','7'])).

thf('9',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( sk_C_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('10',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_funct_1 @ ( sk_C_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 != sk_A )
      | ( ( sk_C_1 @ X1 @ X0 )
        = ( sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf('12',plain,(
    ! [X1: $i] :
      ( ( sk_C_1 @ X1 @ sk_A )
      = ( sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('13',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('14',plain,(
    ! [X16: $i,X17: $i] :
      ( ( ( k1_funct_1 @ ( sk_B @ X16 ) @ X17 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_25__funct_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( ( k1_funct_1 @ ( sk_B @ X0 ) @ ( sk_C @ X1 @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X0 @ sk_A ) @ ( sk_C @ X1 @ sk_A ) )
        = k1_xboole_0 )
      | ( r1_xboole_0 @ sk_A @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','15'])).

thf('17',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('18',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_funct_1 @ ( sk_C_1 @ X13 @ X14 ) @ X15 )
        = X13 )
      | ~ ( r2_hidden @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[s3_funct_1__e2_24__funct_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( ( k1_funct_1 @ ( sk_C_1 @ X2 @ X0 ) @ ( sk_C @ X1 @ X0 ) )
        = X2 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 = X0 )
      | ( r1_xboole_0 @ sk_A @ X1 )
      | ( r1_xboole_0 @ sk_A @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ sk_A @ X1 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A != X0 )
      | ( r1_xboole_0 @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X1: $i] :
      ( r1_xboole_0 @ sk_A @ X1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X9 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('26',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_xboole_0 @ X9 @ X10 )
      | ( r2_hidden @ ( sk_C @ X10 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('27',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( r1_xboole_0 @ X0 @ X2 )
      | ~ ( r2_hidden @ ( sk_C @ X0 @ X1 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_xboole_0 @ X1 @ X0 )
      | ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('32',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k3_xboole_0 @ X6 @ X7 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k3_xboole_0 @ X0 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('34',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['34'])).

thf('37',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['34'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) )
      | ( X0
        = ( k3_xboole_0 @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['35','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( X0
      = ( k3_xboole_0 @ X0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup+',[status(thm)],['33','43'])).

thf('45',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['44','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.f6IdxeqUNE
% 0.13/0.36  % Computer   : n005.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 12:43:18 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 94 iterations in 0.052s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.52  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.52  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.22/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.52  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.22/0.52  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.52  thf(s3_funct_1__e2_24__funct_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ?[C:$i]:
% 0.22/0.52       ( ( ![D:$i]:
% 0.22/0.52           ( ( r2_hidden @ D @ A ) => ( ( k1_funct_1 @ C @ D ) = ( B ) ) ) ) & 
% 0.22/0.52         ( ( k1_relat_1 @ C ) = ( A ) ) & ( v1_funct_1 @ C ) & 
% 0.22/0.52         ( v1_relat_1 @ C ) ) ))).
% 0.22/0.52  thf('0', plain,
% 0.22/0.52      (![X13 : $i, X14 : $i]: ((k1_relat_1 @ (sk_C_1 @ X13 @ X14)) = (X14))),
% 0.22/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.22/0.52  thf(s3_funct_1__e2_25__funct_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ?[B:$i]:
% 0.22/0.52       ( ( ![C:$i]:
% 0.22/0.52           ( ( r2_hidden @ C @ A ) =>
% 0.22/0.52             ( ( k1_funct_1 @ B @ C ) = ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.52         ( ( k1_relat_1 @ B ) = ( A ) ) & ( v1_funct_1 @ B ) & 
% 0.22/0.52         ( v1_relat_1 @ B ) ) ))).
% 0.22/0.52  thf('1', plain, (![X16 : $i]: ((k1_relat_1 @ (sk_B @ X16)) = (X16))),
% 0.22/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.22/0.52  thf(t16_funct_1, conjecture,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ![B:$i]:
% 0.22/0.52         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.52               ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.22/0.52                   ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.22/0.52                 ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.22/0.52       ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i]:
% 0.22/0.52        ( ( ![B:$i]:
% 0.22/0.52            ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.52              ( ![C:$i]:
% 0.22/0.52                ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.52                  ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.22/0.52                      ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.22/0.52                    ( ( B ) = ( C ) ) ) ) ) ) ) =>
% 0.22/0.52          ( ( A ) = ( k1_xboole_0 ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t16_funct_1])).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      (![X18 : $i, X19 : $i]:
% 0.22/0.52         (~ (v1_relat_1 @ X18)
% 0.22/0.52          | ~ (v1_funct_1 @ X18)
% 0.22/0.52          | ((X19) = (X18))
% 0.22/0.52          | ((k1_relat_1 @ X18) != (sk_A))
% 0.22/0.52          | ((k1_relat_1 @ X19) != (sk_A))
% 0.22/0.52          | ~ (v1_funct_1 @ X19)
% 0.22/0.52          | ~ (v1_relat_1 @ X19))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((X0) != (sk_A))
% 0.22/0.52          | ~ (v1_relat_1 @ X1)
% 0.22/0.52          | ~ (v1_funct_1 @ X1)
% 0.22/0.52          | ((k1_relat_1 @ X1) != (sk_A))
% 0.22/0.52          | ((X1) = (sk_B @ X0))
% 0.22/0.52          | ~ (v1_funct_1 @ (sk_B @ X0))
% 0.22/0.52          | ~ (v1_relat_1 @ (sk_B @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.52  thf('4', plain, (![X16 : $i]: (v1_funct_1 @ (sk_B @ X16))),
% 0.22/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.22/0.52  thf('5', plain, (![X16 : $i]: (v1_relat_1 @ (sk_B @ X16))),
% 0.22/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((X0) != (sk_A))
% 0.22/0.52          | ~ (v1_relat_1 @ X1)
% 0.22/0.52          | ~ (v1_funct_1 @ X1)
% 0.22/0.52          | ((k1_relat_1 @ X1) != (sk_A))
% 0.22/0.52          | ((X1) = (sk_B @ X0)))),
% 0.22/0.52      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      (![X1 : $i]:
% 0.22/0.52         (((X1) = (sk_B @ sk_A))
% 0.22/0.52          | ((k1_relat_1 @ X1) != (sk_A))
% 0.22/0.52          | ~ (v1_funct_1 @ X1)
% 0.22/0.52          | ~ (v1_relat_1 @ X1))),
% 0.22/0.52      inference('simplify', [status(thm)], ['6'])).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((X0) != (sk_A))
% 0.22/0.52          | ~ (v1_relat_1 @ (sk_C_1 @ X1 @ X0))
% 0.22/0.52          | ~ (v1_funct_1 @ (sk_C_1 @ X1 @ X0))
% 0.22/0.52          | ((sk_C_1 @ X1 @ X0) = (sk_B @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['0', '7'])).
% 0.22/0.52  thf('9', plain, (![X13 : $i, X14 : $i]: (v1_relat_1 @ (sk_C_1 @ X13 @ X14))),
% 0.22/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      (![X13 : $i, X14 : $i]: (v1_funct_1 @ (sk_C_1 @ X13 @ X14))),
% 0.22/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((X0) != (sk_A)) | ((sk_C_1 @ X1 @ X0) = (sk_B @ sk_A)))),
% 0.22/0.52      inference('demod', [status(thm)], ['8', '9', '10'])).
% 0.22/0.52  thf('12', plain, (![X1 : $i]: ((sk_C_1 @ X1 @ sk_A) = (sk_B @ sk_A))),
% 0.22/0.52      inference('simplify', [status(thm)], ['11'])).
% 0.22/0.52  thf(t3_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.22/0.52            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.52       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.52            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (![X9 : $i, X10 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ X9 @ X10) | (r2_hidden @ (sk_C @ X10 @ X9) @ X9))),
% 0.22/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      (![X16 : $i, X17 : $i]:
% 0.22/0.52         (((k1_funct_1 @ (sk_B @ X16) @ X17) = (k1_xboole_0))
% 0.22/0.52          | ~ (r2_hidden @ X17 @ X16))),
% 0.22/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_25__funct_1])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ X0 @ X1)
% 0.22/0.52          | ((k1_funct_1 @ (sk_B @ X0) @ (sk_C @ X1 @ X0)) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((k1_funct_1 @ (sk_C_1 @ X0 @ sk_A) @ (sk_C @ X1 @ sk_A))
% 0.22/0.52            = (k1_xboole_0))
% 0.22/0.52          | (r1_xboole_0 @ sk_A @ X1))),
% 0.22/0.52      inference('sup+', [status(thm)], ['12', '15'])).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      (![X9 : $i, X10 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ X9 @ X10) | (r2_hidden @ (sk_C @ X10 @ X9) @ X9))),
% 0.22/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.52         (((k1_funct_1 @ (sk_C_1 @ X13 @ X14) @ X15) = (X13))
% 0.22/0.52          | ~ (r2_hidden @ X15 @ X14))),
% 0.22/0.52      inference('cnf', [status(esa)], [s3_funct_1__e2_24__funct_1])).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ X0 @ X1)
% 0.22/0.52          | ((k1_funct_1 @ (sk_C_1 @ X2 @ X0) @ (sk_C @ X1 @ X0)) = (X2)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((k1_xboole_0) = (X0))
% 0.22/0.52          | (r1_xboole_0 @ sk_A @ X1)
% 0.22/0.52          | (r1_xboole_0 @ sk_A @ X1))),
% 0.22/0.52      inference('sup+', [status(thm)], ['16', '19'])).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ sk_A @ X1) | ((k1_xboole_0) = (X0)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['20'])).
% 0.22/0.52  thf('22', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]: (((sk_A) != (X0)) | (r1_xboole_0 @ sk_A @ X1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.52  thf('24', plain, (![X1 : $i]: (r1_xboole_0 @ sk_A @ X1)),
% 0.22/0.52      inference('simplify', [status(thm)], ['23'])).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (![X9 : $i, X10 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ X9 @ X10) | (r2_hidden @ (sk_C @ X10 @ X9) @ X9))),
% 0.22/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (![X9 : $i, X10 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ X9 @ X10) | (r2_hidden @ (sk_C @ X10 @ X9) @ X10))),
% 0.22/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      (![X9 : $i, X11 : $i, X12 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X11 @ X9)
% 0.22/0.52          | ~ (r2_hidden @ X11 @ X12)
% 0.22/0.52          | ~ (r1_xboole_0 @ X9 @ X12))),
% 0.22/0.52      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ X1 @ X0)
% 0.22/0.52          | ~ (r1_xboole_0 @ X0 @ X2)
% 0.22/0.52          | ~ (r2_hidden @ (sk_C @ X0 @ X1) @ X2))),
% 0.22/0.52      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((r1_xboole_0 @ X0 @ X1)
% 0.22/0.52          | ~ (r1_xboole_0 @ X1 @ X0)
% 0.22/0.52          | (r1_xboole_0 @ X0 @ X1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['25', '28'])).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (r1_xboole_0 @ X1 @ X0) | (r1_xboole_0 @ X0 @ X1))),
% 0.22/0.52      inference('simplify', [status(thm)], ['29'])).
% 0.22/0.52  thf('31', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ sk_A)),
% 0.22/0.52      inference('sup-', [status(thm)], ['24', '30'])).
% 0.22/0.52  thf(d7_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.22/0.52       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.52  thf('32', plain,
% 0.22/0.52      (![X6 : $i, X7 : $i]:
% 0.22/0.52         (((k3_xboole_0 @ X6 @ X7) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X6 @ X7))),
% 0.22/0.52      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.22/0.52  thf('33', plain, (![X0 : $i]: ((k3_xboole_0 @ X0 @ sk_A) = (k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.52  thf(d4_xboole_0, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 0.22/0.52       ( ![D:$i]:
% 0.22/0.52         ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.52           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.22/0.52         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.22/0.52          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.22/0.52          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.22/0.52      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.22/0.52  thf('35', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.22/0.52          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.22/0.52      inference('eq_fact', [status(thm)], ['34'])).
% 0.22/0.52  thf('36', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.22/0.52          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.22/0.52      inference('eq_fact', [status(thm)], ['34'])).
% 0.22/0.52  thf('37', plain,
% 0.22/0.52      (![X1 : $i, X2 : $i, X5 : $i]:
% 0.22/0.52         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 0.22/0.52          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 0.22/0.52          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 0.22/0.52          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 0.22/0.52      inference('cnf', [status(esa)], [d4_xboole_0])).
% 0.22/0.52  thf('38', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.22/0.52          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.22/0.52          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.22/0.52          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['36', '37'])).
% 0.22/0.52  thf('39', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 0.22/0.52          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.22/0.52          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['38'])).
% 0.22/0.52  thf('40', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 0.22/0.52          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 0.22/0.52      inference('eq_fact', [status(thm)], ['34'])).
% 0.22/0.52  thf('41', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 0.22/0.52          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 0.22/0.52      inference('clc', [status(thm)], ['39', '40'])).
% 0.22/0.52  thf('42', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((X0) = (k3_xboole_0 @ X0 @ X0)) | ((X0) = (k3_xboole_0 @ X0 @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['35', '41'])).
% 0.22/0.52  thf('43', plain, (![X0 : $i]: ((X0) = (k3_xboole_0 @ X0 @ X0))),
% 0.22/0.52      inference('simplify', [status(thm)], ['42'])).
% 0.22/0.52  thf('44', plain, (((sk_A) = (k1_xboole_0))),
% 0.22/0.52      inference('sup+', [status(thm)], ['33', '43'])).
% 0.22/0.52  thf('45', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('46', plain, ($false),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['44', '45'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
