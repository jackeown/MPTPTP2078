%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7ItigLvg9Y

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:10 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   53 (  78 expanded)
%              Number of leaves         :   16 (  27 expanded)
%              Depth                    :   13
%              Number of atoms          :  426 ( 823 expanded)
%              Number of equality atoms :   64 ( 140 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t10_tops_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ~ ( ( B != k1_xboole_0 )
            & ( ( k7_setfam_1 @ A @ B )
              = k1_xboole_0 ) )
        & ~ ( ( ( k7_setfam_1 @ A @ B )
             != k1_xboole_0 )
            & ( B = k1_xboole_0 ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ( ~ ( ( B != k1_xboole_0 )
              & ( ( k7_setfam_1 @ A @ B )
                = k1_xboole_0 ) )
          & ~ ( ( ( k7_setfam_1 @ A @ B )
               != k1_xboole_0 )
              & ( B = k1_xboole_0 ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t10_tops_2])).

thf('0',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k7_setfam_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k7_setfam_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 )
   <= ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t46_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ~ ( ( B != k1_xboole_0 )
          & ( ( k7_setfam_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k7_setfam_1 @ X6 @ X7 )
       != k1_xboole_0 )
      | ( X7 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[t46_setfam_1])).

thf('6',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k7_setfam_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_B = k1_xboole_0 ) )
   <= ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,
    ( ( sk_B != sk_B )
   <= ( ( sk_B != k1_xboole_0 )
      & ( ( k7_setfam_1 @ sk_A @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k7_setfam_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('13',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('14',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('15',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(d8_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
         => ( ( C
              = ( k7_setfam_1 @ A @ B ) )
          <=> ! [D: $i] :
                ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
               => ( ( r2_hidden @ D @ C )
                <=> ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) )
      | ( r2_hidden @ ( sk_D @ X2 @ X4 @ X3 ) @ X2 )
      | ( r2_hidden @ ( k3_subset_1 @ X3 @ ( sk_D @ X2 @ X4 @ X3 ) ) @ X4 )
      | ( X2
        = ( k7_setfam_1 @ X3 @ X4 ) )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X3 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) )
      | ( k1_xboole_0
        = ( k7_setfam_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X0 @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) ) @ X1 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ( r2_hidden @ ( k3_subset_1 @ X0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k7_setfam_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k7_setfam_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ X0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k7_setfam_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ X12 )
      | ~ ( r1_tarski @ X12 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k7_setfam_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( r1_tarski @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k7_setfam_1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ! [X0: $i] :
        ( k1_xboole_0
        = ( k7_setfam_1 @ X0 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['13','26'])).

thf('28',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('29',plain,
    ( ! [X0: $i] :
        ( sk_B
        = ( k7_setfam_1 @ X0 @ sk_B ) )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k7_setfam_1 @ sk_A @ sk_B )
     != k1_xboole_0 )
   <= ( ( k7_setfam_1 @ sk_A @ sk_B )
     != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( ( ( k7_setfam_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ( sk_B = k1_xboole_0 ) ),
    inference(split,[status(esa)],['2'])).

thf('33',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k7_setfam_1 @ sk_A @ sk_B )
       != k1_xboole_0 )
      & ( sk_B = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( ( k7_setfam_1 @ sk_A @ sk_B )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','11','12','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7ItigLvg9Y
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:59:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 58 iterations in 0.052s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.22/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.52  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.22/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.52  thf(t10_tops_2, conjecture,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.52       ( ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.52              ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.52         ( ~( ( ( k7_setfam_1 @ A @ B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.52              ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i,B:$i]:
% 0.22/0.52        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.52          ( ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.52                 ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) & 
% 0.22/0.52            ( ~( ( ( k7_setfam_1 @ A @ B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.52                 ( ( B ) = ( k1_xboole_0 ) ) ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t10_tops_2])).
% 0.22/0.52  thf('0', plain,
% 0.22/0.52      ((((sk_B) != (k1_xboole_0))
% 0.22/0.52        | ((k7_setfam_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.22/0.52       ~ (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      ((((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))
% 0.22/0.52        | ((sk_B) = (k1_xboole_0)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      ((((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0)))
% 0.22/0.52         <= ((((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.22/0.52      inference('split', [status(esa)], ['2'])).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t46_setfam_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.52       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.52            ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      (![X6 : $i, X7 : $i]:
% 0.22/0.52         (((k7_setfam_1 @ X6 @ X7) != (k1_xboole_0))
% 0.22/0.52          | ((X7) = (k1_xboole_0))
% 0.22/0.52          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X6))))),
% 0.22/0.52      inference('cnf', [status(esa)], [t46_setfam_1])).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      ((((sk_B) = (k1_xboole_0))
% 0.22/0.52        | ((k7_setfam_1 @ sk_A @ sk_B) != (k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      (((((k1_xboole_0) != (k1_xboole_0)) | ((sk_B) = (k1_xboole_0))))
% 0.22/0.52         <= ((((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['3', '6'])).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      ((((sk_B) = (k1_xboole_0)))
% 0.22/0.52         <= ((((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.22/0.52      inference('simplify', [status(thm)], ['7'])).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      ((((sk_B) != (sk_B)))
% 0.22/0.52         <= (~ (((sk_B) = (k1_xboole_0))) & 
% 0.22/0.52             (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      ((((sk_B) = (k1_xboole_0))) | 
% 0.22/0.52       ~ (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['10'])).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      ((((sk_B) = (k1_xboole_0))) | 
% 0.22/0.52       (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.22/0.52      inference('split', [status(esa)], ['2'])).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.22/0.52      inference('split', [status(esa)], ['2'])).
% 0.22/0.52  thf(t4_subset_1, axiom,
% 0.22/0.52    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.52  thf(d8_setfam_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.52       ( ![C:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.52           ( ( ( C ) = ( k7_setfam_1 @ A @ B ) ) <=>
% 0.22/0.52             ( ![D:$i]:
% 0.22/0.52               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.52                 ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.52                   ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3)))
% 0.22/0.52          | (r2_hidden @ (sk_D @ X2 @ X4 @ X3) @ X2)
% 0.22/0.52          | (r2_hidden @ (k3_subset_1 @ X3 @ (sk_D @ X2 @ X4 @ X3)) @ X4)
% 0.22/0.52          | ((X2) = (k7_setfam_1 @ X3 @ X4))
% 0.22/0.52          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X3))))),
% 0.22/0.52      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))
% 0.22/0.52          | ((k1_xboole_0) = (k7_setfam_1 @ X0 @ X1))
% 0.22/0.52          | (r2_hidden @ (k3_subset_1 @ X0 @ (sk_D @ k1_xboole_0 @ X1 @ X0)) @ 
% 0.22/0.52             X1)
% 0.22/0.52          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X1 @ X0) @ k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((r2_hidden @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.22/0.52          | (r2_hidden @ 
% 0.22/0.52             (k3_subset_1 @ X0 @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0)) @ 
% 0.22/0.52             k1_xboole_0)
% 0.22/0.52          | ((k1_xboole_0) = (k7_setfam_1 @ X0 @ k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['14', '17'])).
% 0.22/0.52  thf(t7_ordinal1, axiom,
% 0.22/0.52    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      (![X11 : $i, X12 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X11 @ X12) | ~ (r1_tarski @ X12 @ X11))),
% 0.22/0.52      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k1_xboole_0) = (k7_setfam_1 @ X0 @ k1_xboole_0))
% 0.22/0.52          | (r2_hidden @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.22/0.52          | ~ (r1_tarski @ k1_xboole_0 @ 
% 0.22/0.52               (k3_subset_1 @ X0 @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.52  thf('21', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k1_xboole_0) = (k7_setfam_1 @ X0 @ k1_xboole_0))
% 0.22/0.52          | (r2_hidden @ (sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0) @ k1_xboole_0))),
% 0.22/0.52      inference('demod', [status(thm)], ['20', '21'])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (![X11 : $i, X12 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X11 @ X12) | ~ (r1_tarski @ X12 @ X11))),
% 0.22/0.52      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k1_xboole_0) = (k7_setfam_1 @ X0 @ k1_xboole_0))
% 0.22/0.52          | ~ (r1_tarski @ k1_xboole_0 @ 
% 0.22/0.52               (sk_D @ k1_xboole_0 @ k1_xboole_0 @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.52  thf('25', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (![X0 : $i]: ((k1_xboole_0) = (k7_setfam_1 @ X0 @ k1_xboole_0))),
% 0.22/0.52      inference('demod', [status(thm)], ['24', '25'])).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      ((![X0 : $i]: ((k1_xboole_0) = (k7_setfam_1 @ X0 @ sk_B)))
% 0.22/0.52         <= ((((sk_B) = (k1_xboole_0))))),
% 0.22/0.52      inference('sup+', [status(thm)], ['13', '26'])).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.22/0.52      inference('split', [status(esa)], ['2'])).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      ((![X0 : $i]: ((sk_B) = (k7_setfam_1 @ X0 @ sk_B)))
% 0.22/0.52         <= ((((sk_B) = (k1_xboole_0))))),
% 0.22/0.52      inference('demod', [status(thm)], ['27', '28'])).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      ((((k7_setfam_1 @ sk_A @ sk_B) != (k1_xboole_0)))
% 0.22/0.52         <= (~ (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))))),
% 0.22/0.52      inference('split', [status(esa)], ['0'])).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      ((((sk_B) != (k1_xboole_0)))
% 0.22/0.52         <= (~ (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.22/0.52             (((sk_B) = (k1_xboole_0))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.52  thf('32', plain,
% 0.22/0.52      ((((sk_B) = (k1_xboole_0))) <= ((((sk_B) = (k1_xboole_0))))),
% 0.22/0.52      inference('split', [status(esa)], ['2'])).
% 0.22/0.52  thf('33', plain,
% 0.22/0.52      ((((sk_B) != (sk_B)))
% 0.22/0.52         <= (~ (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))) & 
% 0.22/0.52             (((sk_B) = (k1_xboole_0))))),
% 0.22/0.52      inference('demod', [status(thm)], ['31', '32'])).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      (~ (((sk_B) = (k1_xboole_0))) | 
% 0.22/0.52       (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0)))),
% 0.22/0.52      inference('simplify', [status(thm)], ['33'])).
% 0.22/0.52  thf('35', plain, ($false),
% 0.22/0.52      inference('sat_resolution*', [status(thm)], ['1', '11', '12', '34'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.35/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
