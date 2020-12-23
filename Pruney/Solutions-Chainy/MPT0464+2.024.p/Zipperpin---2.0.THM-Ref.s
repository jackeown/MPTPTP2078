%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PF1jRXhqzn

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:40:11 EST 2020

% Result     : Theorem 1.02s
% Output     : Refutation 1.02s
% Verified   : 
% Statistics : Number of formulae       :   54 (  81 expanded)
%              Number of leaves         :   18 (  31 expanded)
%              Depth                    :   12
%              Number of atoms          :  510 ( 845 expanded)
%              Number of equality atoms :   15 (  21 expanded)
%              Maximal formula depth    :   14 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(d4_xboole_0,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k3_xboole_0 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( r2_hidden @ D @ A )
            & ( r2_hidden @ D @ B ) ) ) ) )).

thf('0',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('2',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X4 @ X3 )
      | ( r2_hidden @ X4 @ X2 )
      | ( X3
       != ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('3',plain,(
    ! [X1: $i,X2: $i,X4: $i] :
      ( ( r2_hidden @ X4 @ X2 )
      | ~ ( r2_hidden @ X4 @ ( k3_xboole_0 @ X1 @ X2 ) ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( r2_hidden @ ( sk_D @ ( k3_xboole_0 @ X1 @ X0 ) @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('6',plain,(
    ! [X1: $i,X2: $i,X5: $i] :
      ( ( X5
        = ( k3_xboole_0 @ X1 @ X2 ) )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X2 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X5 @ X2 @ X1 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[d4_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X0 )
      | ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(eq_fact,[status(thm)],['0'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
        = ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) )
      | ( ( k3_xboole_0 @ X1 @ X0 )
        = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k3_xboole_0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X0 @ ( k3_xboole_0 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf(t17_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ) )).

thf('13',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k3_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('16',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X6: $i,X7: $i] :
      ( r1_tarski @ ( k3_xboole_0 @ X6 @ X7 ) @ X6 ) ),
    inference(cnf,[status(esa)],[t17_xboole_1])).

thf(t48_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( ( r1_tarski @ A @ B )
               => ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( r1_tarski @ X21 @ X20 )
      | ( r1_tarski @ ( k5_relat_1 @ X22 @ X21 ) @ ( k5_relat_1 @ X22 @ X20 ) )
      | ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t48_relat_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k3_xboole_0 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X0 @ X1 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup+',[status(thm)],['12','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X2 @ ( k3_xboole_0 @ X1 @ X0 ) ) @ ( k5_relat_1 @ X2 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t19_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ A @ C ) )
     => ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ) )).

thf('25',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ X8 @ X9 )
      | ~ ( r1_tarski @ X8 @ X10 )
      | ( r1_tarski @ X8 @ ( k3_xboole_0 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t19_xboole_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X0 ) @ X3 ) )
      | ~ ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X0 @ X2 ) ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X2 )
      | ( r1_tarski @ ( k5_relat_1 @ X1 @ ( k3_xboole_0 @ X2 @ X0 ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ X1 @ X2 ) @ ( k5_relat_1 @ X1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf(t52_relat_1,conjecture,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ! [C: $i] :
              ( ( v1_relat_1 @ C )
             => ( r1_tarski @ ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( v1_relat_1 @ A )
       => ! [B: $i] :
            ( ( v1_relat_1 @ B )
           => ! [C: $i] :
                ( ( v1_relat_1 @ C )
               => ( r1_tarski @ ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t52_relat_1])).

thf('29',plain,(
    ~ ( r1_tarski @ ( k5_relat_1 @ sk_A @ ( k3_xboole_0 @ sk_B @ sk_C ) ) @ ( k3_xboole_0 @ ( k5_relat_1 @ sk_A @ sk_B ) @ ( k5_relat_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['30','31','32','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.PF1jRXhqzn
% 0.15/0.38  % Computer   : n018.cluster.edu
% 0.15/0.38  % Model      : x86_64 x86_64
% 0.15/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.38  % Memory     : 8042.1875MB
% 0.15/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.38  % CPULimit   : 60
% 0.15/0.38  % DateTime   : Tue Dec  1 09:48:12 EST 2020
% 0.15/0.38  % CPUTime    : 
% 0.15/0.38  % Running portfolio for 600 s
% 0.15/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.38  % Number of cores: 8
% 0.15/0.38  % Python version: Python 3.6.8
% 0.15/0.38  % Running in FO mode
% 1.02/1.22  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.02/1.22  % Solved by: fo/fo7.sh
% 1.02/1.22  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.02/1.22  % done 1443 iterations in 0.738s
% 1.02/1.22  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.02/1.22  % SZS output start Refutation
% 1.02/1.22  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.02/1.22  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.02/1.22  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.02/1.22  thf(sk_A_type, type, sk_A: $i).
% 1.02/1.22  thf(sk_C_type, type, sk_C: $i).
% 1.02/1.22  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.02/1.22  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.02/1.22  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.02/1.22  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.02/1.22  thf(sk_B_type, type, sk_B: $i).
% 1.02/1.22  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 1.02/1.22  thf(d4_xboole_0, axiom,
% 1.02/1.22    (![A:$i,B:$i,C:$i]:
% 1.02/1.22     ( ( ( C ) = ( k3_xboole_0 @ A @ B ) ) <=>
% 1.02/1.22       ( ![D:$i]:
% 1.02/1.22         ( ( r2_hidden @ D @ C ) <=>
% 1.02/1.22           ( ( r2_hidden @ D @ A ) & ( r2_hidden @ D @ B ) ) ) ) ))).
% 1.02/1.22  thf('0', plain,
% 1.02/1.22      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.02/1.22         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 1.02/1.22          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.02/1.22          | (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.02/1.22      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.02/1.22  thf('1', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.02/1.22          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.02/1.22      inference('eq_fact', [status(thm)], ['0'])).
% 1.02/1.22  thf('2', plain,
% 1.02/1.22      (![X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 1.02/1.22         (~ (r2_hidden @ X4 @ X3)
% 1.02/1.22          | (r2_hidden @ X4 @ X2)
% 1.02/1.22          | ((X3) != (k3_xboole_0 @ X1 @ X2)))),
% 1.02/1.22      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.02/1.22  thf('3', plain,
% 1.02/1.22      (![X1 : $i, X2 : $i, X4 : $i]:
% 1.02/1.22         ((r2_hidden @ X4 @ X2) | ~ (r2_hidden @ X4 @ (k3_xboole_0 @ X1 @ X2)))),
% 1.02/1.22      inference('simplify', [status(thm)], ['2'])).
% 1.02/1.22  thf('4', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.22         (((k3_xboole_0 @ X1 @ X0)
% 1.02/1.22            = (k3_xboole_0 @ X2 @ (k3_xboole_0 @ X1 @ X0)))
% 1.02/1.22          | (r2_hidden @ 
% 1.02/1.22             (sk_D @ (k3_xboole_0 @ X1 @ X0) @ (k3_xboole_0 @ X1 @ X0) @ X2) @ 
% 1.02/1.22             X0))),
% 1.02/1.22      inference('sup-', [status(thm)], ['1', '3'])).
% 1.02/1.22  thf('5', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.02/1.22          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.02/1.22      inference('eq_fact', [status(thm)], ['0'])).
% 1.02/1.22  thf('6', plain,
% 1.02/1.22      (![X1 : $i, X2 : $i, X5 : $i]:
% 1.02/1.22         (((X5) = (k3_xboole_0 @ X1 @ X2))
% 1.02/1.22          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X2)
% 1.02/1.22          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X1)
% 1.02/1.22          | ~ (r2_hidden @ (sk_D @ X5 @ X2 @ X1) @ X5))),
% 1.02/1.22      inference('cnf', [status(esa)], [d4_xboole_0])).
% 1.02/1.22  thf('7', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 1.02/1.22          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.02/1.22          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.02/1.22          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.02/1.22      inference('sup-', [status(thm)], ['5', '6'])).
% 1.02/1.22  thf('8', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         (~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1)
% 1.02/1.22          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.02/1.22          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.02/1.22      inference('simplify', [status(thm)], ['7'])).
% 1.02/1.22  thf('9', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         ((r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X0)
% 1.02/1.22          | ((X0) = (k3_xboole_0 @ X1 @ X0)))),
% 1.02/1.22      inference('eq_fact', [status(thm)], ['0'])).
% 1.02/1.22  thf('10', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         (((X0) = (k3_xboole_0 @ X1 @ X0))
% 1.02/1.22          | ~ (r2_hidden @ (sk_D @ X0 @ X0 @ X1) @ X1))),
% 1.02/1.22      inference('clc', [status(thm)], ['8', '9'])).
% 1.02/1.22  thf('11', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         (((k3_xboole_0 @ X1 @ X0)
% 1.02/1.22            = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))
% 1.02/1.22          | ((k3_xboole_0 @ X1 @ X0)
% 1.02/1.22              = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0))))),
% 1.02/1.22      inference('sup-', [status(thm)], ['4', '10'])).
% 1.02/1.22  thf('12', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         ((k3_xboole_0 @ X1 @ X0)
% 1.02/1.22           = (k3_xboole_0 @ X0 @ (k3_xboole_0 @ X1 @ X0)))),
% 1.02/1.22      inference('simplify', [status(thm)], ['11'])).
% 1.02/1.22  thf(t17_xboole_1, axiom,
% 1.02/1.22    (![A:$i,B:$i]: ( r1_tarski @ ( k3_xboole_0 @ A @ B ) @ A ))).
% 1.02/1.22  thf('13', plain,
% 1.02/1.22      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 1.02/1.22      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.02/1.22  thf(t3_subset, axiom,
% 1.02/1.22    (![A:$i,B:$i]:
% 1.02/1.22     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.02/1.22  thf('14', plain,
% 1.02/1.22      (![X15 : $i, X17 : $i]:
% 1.02/1.22         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 1.02/1.22      inference('cnf', [status(esa)], [t3_subset])).
% 1.02/1.22  thf('15', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         (m1_subset_1 @ (k3_xboole_0 @ X0 @ X1) @ (k1_zfmisc_1 @ X0))),
% 1.02/1.22      inference('sup-', [status(thm)], ['13', '14'])).
% 1.02/1.22  thf(cc2_relat_1, axiom,
% 1.02/1.22    (![A:$i]:
% 1.02/1.22     ( ( v1_relat_1 @ A ) =>
% 1.02/1.22       ( ![B:$i]:
% 1.02/1.22         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.02/1.22  thf('16', plain,
% 1.02/1.22      (![X18 : $i, X19 : $i]:
% 1.02/1.22         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 1.02/1.22          | (v1_relat_1 @ X18)
% 1.02/1.22          | ~ (v1_relat_1 @ X19))),
% 1.02/1.22      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.02/1.22  thf('17', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i]:
% 1.02/1.22         (~ (v1_relat_1 @ X0) | (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1)))),
% 1.02/1.22      inference('sup-', [status(thm)], ['15', '16'])).
% 1.02/1.22  thf('18', plain,
% 1.02/1.22      (![X6 : $i, X7 : $i]: (r1_tarski @ (k3_xboole_0 @ X6 @ X7) @ X6)),
% 1.02/1.22      inference('cnf', [status(esa)], [t17_xboole_1])).
% 1.02/1.22  thf(t48_relat_1, axiom,
% 1.02/1.22    (![A:$i]:
% 1.02/1.22     ( ( v1_relat_1 @ A ) =>
% 1.02/1.22       ( ![B:$i]:
% 1.02/1.22         ( ( v1_relat_1 @ B ) =>
% 1.02/1.22           ( ![C:$i]:
% 1.02/1.22             ( ( v1_relat_1 @ C ) =>
% 1.02/1.22               ( ( r1_tarski @ A @ B ) =>
% 1.02/1.22                 ( r1_tarski @ ( k5_relat_1 @ C @ A ) @ ( k5_relat_1 @ C @ B ) ) ) ) ) ) ) ))).
% 1.02/1.22  thf('19', plain,
% 1.02/1.22      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.02/1.22         (~ (v1_relat_1 @ X20)
% 1.02/1.22          | ~ (r1_tarski @ X21 @ X20)
% 1.02/1.22          | (r1_tarski @ (k5_relat_1 @ X22 @ X21) @ (k5_relat_1 @ X22 @ X20))
% 1.02/1.22          | ~ (v1_relat_1 @ X22)
% 1.02/1.22          | ~ (v1_relat_1 @ X21))),
% 1.02/1.22      inference('cnf', [status(esa)], [t48_relat_1])).
% 1.02/1.22  thf('20', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.22         (~ (v1_relat_1 @ (k3_xboole_0 @ X0 @ X1))
% 1.02/1.22          | ~ (v1_relat_1 @ X2)
% 1.02/1.22          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X0 @ X1)) @ 
% 1.02/1.22             (k5_relat_1 @ X2 @ X0))
% 1.02/1.22          | ~ (v1_relat_1 @ X0))),
% 1.02/1.22      inference('sup-', [status(thm)], ['18', '19'])).
% 1.02/1.22  thf('21', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.22         (~ (v1_relat_1 @ X1)
% 1.02/1.22          | ~ (v1_relat_1 @ X1)
% 1.02/1.22          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.02/1.22             (k5_relat_1 @ X2 @ X1))
% 1.02/1.22          | ~ (v1_relat_1 @ X2))),
% 1.02/1.22      inference('sup-', [status(thm)], ['17', '20'])).
% 1.02/1.22  thf('22', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.22         (~ (v1_relat_1 @ X2)
% 1.02/1.22          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.02/1.22             (k5_relat_1 @ X2 @ X1))
% 1.02/1.22          | ~ (v1_relat_1 @ X1))),
% 1.02/1.22      inference('simplify', [status(thm)], ['21'])).
% 1.02/1.22  thf('23', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.22         ((r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.02/1.22           (k5_relat_1 @ X2 @ X0))
% 1.02/1.22          | ~ (v1_relat_1 @ X0)
% 1.02/1.22          | ~ (v1_relat_1 @ X2))),
% 1.02/1.22      inference('sup+', [status(thm)], ['12', '22'])).
% 1.02/1.22  thf('24', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.22         (~ (v1_relat_1 @ X2)
% 1.02/1.22          | (r1_tarski @ (k5_relat_1 @ X2 @ (k3_xboole_0 @ X1 @ X0)) @ 
% 1.02/1.22             (k5_relat_1 @ X2 @ X1))
% 1.02/1.22          | ~ (v1_relat_1 @ X1))),
% 1.02/1.22      inference('simplify', [status(thm)], ['21'])).
% 1.02/1.22  thf(t19_xboole_1, axiom,
% 1.02/1.22    (![A:$i,B:$i,C:$i]:
% 1.02/1.22     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ A @ C ) ) =>
% 1.02/1.22       ( r1_tarski @ A @ ( k3_xboole_0 @ B @ C ) ) ))).
% 1.02/1.22  thf('25', plain,
% 1.02/1.22      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.02/1.22         (~ (r1_tarski @ X8 @ X9)
% 1.02/1.22          | ~ (r1_tarski @ X8 @ X10)
% 1.02/1.22          | (r1_tarski @ X8 @ (k3_xboole_0 @ X9 @ X10)))),
% 1.02/1.22      inference('cnf', [status(esa)], [t19_xboole_1])).
% 1.02/1.22  thf('26', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.02/1.22         (~ (v1_relat_1 @ X0)
% 1.02/1.22          | ~ (v1_relat_1 @ X1)
% 1.02/1.22          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ 
% 1.02/1.22             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X0) @ X3))
% 1.02/1.22          | ~ (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X0 @ X2)) @ X3))),
% 1.02/1.22      inference('sup-', [status(thm)], ['24', '25'])).
% 1.02/1.22  thf('27', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.22         (~ (v1_relat_1 @ X1)
% 1.02/1.22          | ~ (v1_relat_1 @ X0)
% 1.02/1.22          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 1.02/1.22             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0)))
% 1.02/1.22          | ~ (v1_relat_1 @ X1)
% 1.02/1.22          | ~ (v1_relat_1 @ X2))),
% 1.02/1.22      inference('sup-', [status(thm)], ['23', '26'])).
% 1.02/1.22  thf('28', plain,
% 1.02/1.22      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.02/1.22         (~ (v1_relat_1 @ X2)
% 1.02/1.22          | (r1_tarski @ (k5_relat_1 @ X1 @ (k3_xboole_0 @ X2 @ X0)) @ 
% 1.02/1.22             (k3_xboole_0 @ (k5_relat_1 @ X1 @ X2) @ (k5_relat_1 @ X1 @ X0)))
% 1.02/1.22          | ~ (v1_relat_1 @ X0)
% 1.02/1.22          | ~ (v1_relat_1 @ X1))),
% 1.02/1.22      inference('simplify', [status(thm)], ['27'])).
% 1.02/1.22  thf(t52_relat_1, conjecture,
% 1.02/1.22    (![A:$i]:
% 1.02/1.22     ( ( v1_relat_1 @ A ) =>
% 1.02/1.22       ( ![B:$i]:
% 1.02/1.22         ( ( v1_relat_1 @ B ) =>
% 1.02/1.22           ( ![C:$i]:
% 1.02/1.22             ( ( v1_relat_1 @ C ) =>
% 1.02/1.22               ( r1_tarski @
% 1.02/1.22                 ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 1.02/1.22                 ( k3_xboole_0 @
% 1.02/1.22                   ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ))).
% 1.02/1.22  thf(zf_stmt_0, negated_conjecture,
% 1.02/1.22    (~( ![A:$i]:
% 1.02/1.22        ( ( v1_relat_1 @ A ) =>
% 1.02/1.22          ( ![B:$i]:
% 1.02/1.22            ( ( v1_relat_1 @ B ) =>
% 1.02/1.22              ( ![C:$i]:
% 1.02/1.22                ( ( v1_relat_1 @ C ) =>
% 1.02/1.22                  ( r1_tarski @
% 1.02/1.22                    ( k5_relat_1 @ A @ ( k3_xboole_0 @ B @ C ) ) @ 
% 1.02/1.22                    ( k3_xboole_0 @
% 1.02/1.22                      ( k5_relat_1 @ A @ B ) @ ( k5_relat_1 @ A @ C ) ) ) ) ) ) ) ) )),
% 1.02/1.22    inference('cnf.neg', [status(esa)], [t52_relat_1])).
% 1.02/1.22  thf('29', plain,
% 1.02/1.22      (~ (r1_tarski @ (k5_relat_1 @ sk_A @ (k3_xboole_0 @ sk_B @ sk_C)) @ 
% 1.02/1.22          (k3_xboole_0 @ (k5_relat_1 @ sk_A @ sk_B) @ 
% 1.02/1.22           (k5_relat_1 @ sk_A @ sk_C)))),
% 1.02/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.22  thf('30', plain,
% 1.02/1.22      ((~ (v1_relat_1 @ sk_A) | ~ (v1_relat_1 @ sk_C) | ~ (v1_relat_1 @ sk_B))),
% 1.02/1.22      inference('sup-', [status(thm)], ['28', '29'])).
% 1.02/1.22  thf('31', plain, ((v1_relat_1 @ sk_A)),
% 1.02/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.22  thf('32', plain, ((v1_relat_1 @ sk_C)),
% 1.02/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.22  thf('33', plain, ((v1_relat_1 @ sk_B)),
% 1.02/1.22      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.02/1.22  thf('34', plain, ($false),
% 1.02/1.22      inference('demod', [status(thm)], ['30', '31', '32', '33'])).
% 1.02/1.22  
% 1.02/1.22  % SZS output end Refutation
% 1.02/1.22  
% 1.02/1.23  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
