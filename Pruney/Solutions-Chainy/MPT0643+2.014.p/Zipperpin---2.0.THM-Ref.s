%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JUo7KPXoPy

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:45:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 101 expanded)
%              Number of leaves         :   18 (  41 expanded)
%              Depth                    :   13
%              Number of atoms          :  564 (1397 expanded)
%              Number of equality atoms :   57 ( 164 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X3 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t50_funct_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v1_funct_1 @ C ) )
         => ( ( ( ( k1_relat_1 @ B )
                = A )
              & ( ( k1_relat_1 @ C )
                = A )
              & ( r1_tarski @ ( k2_relat_1 @ C ) @ A )
              & ( v2_funct_1 @ B )
              & ( ( k5_relat_1 @ C @ B )
                = B ) )
           => ( C
              = ( k6_relat_1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ! [C: $i] :
            ( ( ( v1_relat_1 @ C )
              & ( v1_funct_1 @ C ) )
           => ( ( ( ( k1_relat_1 @ B )
                  = A )
                & ( ( k1_relat_1 @ C )
                  = A )
                & ( r1_tarski @ ( k2_relat_1 @ C ) @ A )
                & ( v2_funct_1 @ B )
                & ( ( k5_relat_1 @ C @ B )
                  = B ) )
             => ( C
                = ( k6_relat_1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_funct_1])).

thf('1',plain,
    ( ( k5_relat_1 @ sk_C_1 @ sk_B_1 )
    = sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t49_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
      <=> ! [B: $i] :
            ( ( ( v1_relat_1 @ B )
              & ( v1_funct_1 @ B ) )
           => ! [C: $i] :
                ( ( ( v1_relat_1 @ C )
                  & ( v1_funct_1 @ C ) )
               => ( ( ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) )
                    & ( r1_tarski @ ( k2_relat_1 @ C ) @ ( k1_relat_1 @ A ) )
                    & ( ( k1_relat_1 @ B )
                      = ( k1_relat_1 @ C ) )
                    & ( ( k5_relat_1 @ B @ A )
                      = ( k5_relat_1 @ C @ A ) ) )
                 => ( B = C ) ) ) ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 )
      | ~ ( v1_funct_1 @ X10 )
      | ( X11 = X10 )
      | ( ( k5_relat_1 @ X11 @ X9 )
       != ( k5_relat_1 @ X10 @ X9 ) )
      | ( ( k1_relat_1 @ X11 )
       != ( k1_relat_1 @ X10 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X10 ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X11 ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t49_funct_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X1 ) @ ( k1_relat_1 @ sk_B_1 ) )
      | ( ( k1_relat_1 @ X1 )
       != ( k1_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ X1 @ sk_B_1 )
       != ( k5_relat_1 @ X0 @ sk_B_1 ) )
      | ( X1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ sk_A )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X1 ) @ sk_A )
      | ( ( k1_relat_1 @ X1 )
       != ( k1_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ X1 @ sk_B_1 )
       != ( k5_relat_1 @ X0 @ sk_B_1 ) )
      | ( X1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5','6','7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
       != ( k5_relat_1 @ X0 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( sk_C_1 = X0 )
      | ( ( k1_relat_1 @ sk_C_1 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['1','9'])).

thf('11',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( sk_B_1
       != ( k5_relat_1 @ X0 @ sk_B_1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( sk_C_1 = X0 )
      | ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11','12','13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( sk_A
       != ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ( sk_C_1
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( sk_B_1
       != ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['0','15'])).

thf('17',plain,(
    ! [X2: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X2 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('18',plain,(
    ! [X8: $i] :
      ( v1_funct_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('19',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( sk_A != X0 )
      | ( sk_C_1
        = ( k6_relat_1 @ X0 ) )
      | ( sk_B_1
       != ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['16','17','18','19'])).

thf('21',plain,
    ( ( sk_B_1
     != ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B_1 ) )
    | ( sk_C_1
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( r1_tarski @ sk_A @ sk_A ) ),
    inference(simplify,[status(thm)],['20'])).

thf(t78_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A )
        = A ) ) )).

thf('22',plain,(
    ! [X6: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X6 ) ) @ X6 )
        = X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf(t76_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B )
        & ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ) )).

thf('23',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r1_tarski @ ( k5_relat_1 @ X4 @ ( k6_relat_1 @ X5 ) ) @ X4 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t76_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X2: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X2 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('26',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('27',plain,(
    ! [X2: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X2 ) )
      = X2 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('28',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['24','25','26','27','28'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ X1 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('33',plain,(
    ! [X3: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X3 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('34',plain,(
    ! [X3: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X3 ) )
      = X3 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('35',plain,(
    ! [X7: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(demod,[status(thm)],['31','32','33','34','35'])).

thf('37',plain,
    ( ( sk_B_1
     != ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B_1 ) )
    | ( sk_C_1
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('simplify_reflect+',[status(thm)],['21','36'])).

thf('38',plain,(
    sk_C_1
 != ( k6_relat_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    sk_B_1
 != ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B_1 ) ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X6: $i] :
      ( ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X6 ) ) @ X6 )
        = X6 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t78_relat_1])).

thf('42',plain,
    ( ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B_1 )
      = sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['40','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_B_1 )
    = sk_B_1 ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    sk_B_1 != sk_B_1 ),
    inference(demod,[status(thm)],['39','44'])).

thf('46',plain,(
    $false ),
    inference(simplify,[status(thm)],['45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JUo7KPXoPy
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:20:51 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.21/0.35  % Running portfolio for 600 s
% 0.21/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.21/0.35  % Number of cores: 8
% 0.21/0.35  % Python version: Python 3.6.8
% 0.21/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 60 iterations in 0.044s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.50  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.50  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.50  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.21/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.50  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.50  thf(t71_relat_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.21/0.50       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.21/0.50  thf('0', plain, (![X3 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X3)) = (X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.50  thf(t50_funct_1, conjecture,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.50       ( ![C:$i]:
% 0.21/0.50         ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.50           ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.21/0.50               ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.21/0.50               ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) & ( v2_funct_1 @ B ) & 
% 0.21/0.50               ( ( k5_relat_1 @ C @ B ) = ( B ) ) ) =>
% 0.21/0.50             ( ( C ) = ( k6_relat_1 @ A ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i]:
% 0.21/0.50        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.50          ( ![C:$i]:
% 0.21/0.50            ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.50              ( ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.21/0.50                  ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.21/0.50                  ( r1_tarski @ ( k2_relat_1 @ C ) @ A ) & 
% 0.21/0.50                  ( v2_funct_1 @ B ) & ( ( k5_relat_1 @ C @ B ) = ( B ) ) ) =>
% 0.21/0.50                ( ( C ) = ( k6_relat_1 @ A ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t50_funct_1])).
% 0.21/0.50  thf('1', plain, (((k5_relat_1 @ sk_C_1 @ sk_B_1) = (sk_B_1))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('2', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t49_funct_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.50       ( ( v2_funct_1 @ A ) <=>
% 0.21/0.50         ( ![B:$i]:
% 0.21/0.50           ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.50             ( ![C:$i]:
% 0.21/0.50               ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.50                 ( ( ( r1_tarski @ ( k2_relat_1 @ B ) @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.50                     ( r1_tarski @ ( k2_relat_1 @ C ) @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.50                     ( ( k1_relat_1 @ B ) = ( k1_relat_1 @ C ) ) & 
% 0.21/0.50                     ( ( k5_relat_1 @ B @ A ) = ( k5_relat_1 @ C @ A ) ) ) =>
% 0.21/0.50                   ( ( B ) = ( C ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.21/0.50         (~ (v2_funct_1 @ X9)
% 0.21/0.50          | ~ (v1_relat_1 @ X10)
% 0.21/0.50          | ~ (v1_funct_1 @ X10)
% 0.21/0.50          | ((X11) = (X10))
% 0.21/0.50          | ((k5_relat_1 @ X11 @ X9) != (k5_relat_1 @ X10 @ X9))
% 0.21/0.50          | ((k1_relat_1 @ X11) != (k1_relat_1 @ X10))
% 0.21/0.50          | ~ (r1_tarski @ (k2_relat_1 @ X10) @ (k1_relat_1 @ X9))
% 0.21/0.50          | ~ (r1_tarski @ (k2_relat_1 @ X11) @ (k1_relat_1 @ X9))
% 0.21/0.50          | ~ (v1_funct_1 @ X11)
% 0.21/0.50          | ~ (v1_relat_1 @ X11)
% 0.21/0.50          | ~ (v1_funct_1 @ X9)
% 0.21/0.50          | ~ (v1_relat_1 @ X9))),
% 0.21/0.50      inference('cnf', [status(esa)], [t49_funct_1])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (r1_tarski @ (k2_relat_1 @ X0) @ sk_A)
% 0.21/0.50          | ~ (v1_relat_1 @ sk_B_1)
% 0.21/0.50          | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.50          | ~ (v1_relat_1 @ X1)
% 0.21/0.50          | ~ (v1_funct_1 @ X1)
% 0.21/0.50          | ~ (r1_tarski @ (k2_relat_1 @ X1) @ (k1_relat_1 @ sk_B_1))
% 0.21/0.50          | ((k1_relat_1 @ X1) != (k1_relat_1 @ X0))
% 0.21/0.50          | ((k5_relat_1 @ X1 @ sk_B_1) != (k5_relat_1 @ X0 @ sk_B_1))
% 0.21/0.50          | ((X1) = (X0))
% 0.21/0.50          | ~ (v1_funct_1 @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ X0)
% 0.21/0.50          | ~ (v2_funct_1 @ sk_B_1))),
% 0.21/0.50      inference('sup-', [status(thm)], ['2', '3'])).
% 0.21/0.50  thf('5', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('6', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('7', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('8', plain, ((v2_funct_1 @ sk_B_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (r1_tarski @ (k2_relat_1 @ X0) @ sk_A)
% 0.21/0.50          | ~ (v1_relat_1 @ X1)
% 0.21/0.50          | ~ (v1_funct_1 @ X1)
% 0.21/0.50          | ~ (r1_tarski @ (k2_relat_1 @ X1) @ sk_A)
% 0.21/0.50          | ((k1_relat_1 @ X1) != (k1_relat_1 @ X0))
% 0.21/0.50          | ((k5_relat_1 @ X1 @ sk_B_1) != (k5_relat_1 @ X0 @ sk_B_1))
% 0.21/0.50          | ((X1) = (X0))
% 0.21/0.50          | ~ (v1_funct_1 @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['4', '5', '6', '7', '8'])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((sk_B_1) != (k5_relat_1 @ X0 @ sk_B_1))
% 0.21/0.50          | ~ (v1_relat_1 @ X0)
% 0.21/0.50          | ~ (v1_funct_1 @ X0)
% 0.21/0.50          | ((sk_C_1) = (X0))
% 0.21/0.50          | ((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ X0))
% 0.21/0.50          | ~ (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_A)
% 0.21/0.50          | ~ (v1_funct_1 @ sk_C_1)
% 0.21/0.50          | ~ (v1_relat_1 @ sk_C_1)
% 0.21/0.50          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ sk_A))),
% 0.21/0.50      inference('sup-', [status(thm)], ['1', '9'])).
% 0.21/0.50  thf('11', plain, (((k1_relat_1 @ sk_C_1) = (sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('12', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('13', plain, ((v1_funct_1 @ sk_C_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('14', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((sk_B_1) != (k5_relat_1 @ X0 @ sk_B_1))
% 0.21/0.50          | ~ (v1_relat_1 @ X0)
% 0.21/0.50          | ~ (v1_funct_1 @ X0)
% 0.21/0.50          | ((sk_C_1) = (X0))
% 0.21/0.50          | ((sk_A) != (k1_relat_1 @ X0))
% 0.21/0.50          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['10', '11', '12', '13', '14'])).
% 0.21/0.50  thf('16', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (r1_tarski @ X0 @ sk_A)
% 0.21/0.50          | ((sk_A) != (k1_relat_1 @ (k6_relat_1 @ X0)))
% 0.21/0.50          | ((sk_C_1) = (k6_relat_1 @ X0))
% 0.21/0.50          | ~ (v1_funct_1 @ (k6_relat_1 @ X0))
% 0.21/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.50          | ((sk_B_1) != (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B_1)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['0', '15'])).
% 0.21/0.50  thf('17', plain, (![X2 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X2)) = (X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.50  thf(fc3_funct_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.21/0.50       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.21/0.50  thf('18', plain, (![X8 : $i]: (v1_funct_1 @ (k6_relat_1 @ X8))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.50  thf('19', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (r1_tarski @ X0 @ sk_A)
% 0.21/0.50          | ((sk_A) != (X0))
% 0.21/0.50          | ((sk_C_1) = (k6_relat_1 @ X0))
% 0.21/0.50          | ((sk_B_1) != (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_B_1)))),
% 0.21/0.50      inference('demod', [status(thm)], ['16', '17', '18', '19'])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      ((((sk_B_1) != (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B_1))
% 0.21/0.50        | ((sk_C_1) = (k6_relat_1 @ sk_A))
% 0.21/0.50        | ~ (r1_tarski @ sk_A @ sk_A))),
% 0.21/0.50      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.50  thf(t78_relat_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ A ) =>
% 0.21/0.50       ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ A ) ) @ A ) = ( A ) ) ))).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (![X6 : $i]:
% 0.21/0.50         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X6)) @ X6) = (X6))
% 0.21/0.50          | ~ (v1_relat_1 @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.21/0.50  thf(t76_relat_1, axiom,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ B ) =>
% 0.21/0.50       ( ( r1_tarski @ ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) @ B ) & 
% 0.21/0.50         ( r1_tarski @ ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) @ B ) ) ))).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      (![X4 : $i, X5 : $i]:
% 0.21/0.50         ((r1_tarski @ (k5_relat_1 @ X4 @ (k6_relat_1 @ X5)) @ X4)
% 0.21/0.50          | ~ (v1_relat_1 @ X4))),
% 0.21/0.50      inference('cnf', [status(esa)], [t76_relat_1])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         ((r1_tarski @ (k6_relat_1 @ X0) @ 
% 0.21/0.50           (k6_relat_1 @ (k1_relat_1 @ (k6_relat_1 @ X0))))
% 0.21/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ (k6_relat_1 @ X0)))))),
% 0.21/0.50      inference('sup+', [status(thm)], ['22', '23'])).
% 0.21/0.50  thf('25', plain, (![X2 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X2)) = (X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.50  thf('26', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.50  thf('27', plain, (![X2 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X2)) = (X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.50  thf('28', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (![X0 : $i]: (r1_tarski @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 0.21/0.50      inference('demod', [status(thm)], ['24', '25', '26', '27', '28'])).
% 0.21/0.50  thf(t25_relat_1, axiom,
% 0.21/0.50    (![A:$i]:
% 0.21/0.50     ( ( v1_relat_1 @ A ) =>
% 0.21/0.50       ( ![B:$i]:
% 0.21/0.50         ( ( v1_relat_1 @ B ) =>
% 0.21/0.50           ( ( r1_tarski @ A @ B ) =>
% 0.21/0.50             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.21/0.50               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ X0)
% 0.21/0.50          | (r1_tarski @ (k2_relat_1 @ X1) @ (k2_relat_1 @ X0))
% 0.21/0.50          | ~ (r1_tarski @ X1 @ X0)
% 0.21/0.50          | ~ (v1_relat_1 @ X1))),
% 0.21/0.50      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.21/0.50          | (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ X0)) @ 
% 0.21/0.50             (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.21/0.50          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.21/0.50  thf('32', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.50  thf('33', plain, (![X3 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X3)) = (X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.50  thf('34', plain, (![X3 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X3)) = (X3))),
% 0.21/0.50      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.21/0.50  thf('35', plain, (![X7 : $i]: (v1_relat_1 @ (k6_relat_1 @ X7))),
% 0.21/0.50      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.21/0.50  thf('36', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.21/0.50      inference('demod', [status(thm)], ['31', '32', '33', '34', '35'])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      ((((sk_B_1) != (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B_1))
% 0.21/0.50        | ((sk_C_1) = (k6_relat_1 @ sk_A)))),
% 0.21/0.50      inference('simplify_reflect+', [status(thm)], ['21', '36'])).
% 0.21/0.50  thf('38', plain, (((sk_C_1) != (k6_relat_1 @ sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('39', plain, (((sk_B_1) != (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B_1))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.21/0.50  thf('40', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      (![X6 : $i]:
% 0.21/0.50         (((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X6)) @ X6) = (X6))
% 0.21/0.50          | ~ (v1_relat_1 @ X6))),
% 0.21/0.50      inference('cnf', [status(esa)], [t78_relat_1])).
% 0.21/0.50  thf('42', plain,
% 0.21/0.50      ((((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B_1) = (sk_B_1))
% 0.21/0.50        | ~ (v1_relat_1 @ sk_B_1))),
% 0.21/0.50      inference('sup+', [status(thm)], ['40', '41'])).
% 0.21/0.50  thf('43', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('44', plain, (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_B_1) = (sk_B_1))),
% 0.21/0.50      inference('demod', [status(thm)], ['42', '43'])).
% 0.21/0.50  thf('45', plain, (((sk_B_1) != (sk_B_1))),
% 0.21/0.50      inference('demod', [status(thm)], ['39', '44'])).
% 0.21/0.50  thf('46', plain, ($false), inference('simplify', [status(thm)], ['45'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
