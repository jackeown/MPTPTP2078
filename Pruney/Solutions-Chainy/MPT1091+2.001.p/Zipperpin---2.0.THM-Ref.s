%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7EYCFeEWeb

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:41 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 198 expanded)
%              Number of leaves         :   16 (  58 expanded)
%              Depth                    :   12
%              Number of atoms          :  345 (1422 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_finset_1_type,type,(
    v1_finset_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(t25_finset_1,conjecture,(
    ! [A: $i] :
      ( ( ( v1_finset_1 @ A )
        & ! [B: $i] :
            ( ( r2_hidden @ B @ A )
           => ( v1_finset_1 @ B ) ) )
    <=> ( v1_finset_1 @ ( k3_tarski @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_finset_1 @ A )
          & ! [B: $i] :
              ( ( r2_hidden @ B @ A )
             => ( v1_finset_1 @ B ) ) )
      <=> ( v1_finset_1 @ ( k3_tarski @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t25_finset_1])).

thf('0',plain,
    ( ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
    | ( r2_hidden @ sk_B_1 @ sk_A )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
   <= ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
    | ( v1_finset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( v1_finset_1 @ sk_A )
   <= ( v1_finset_1 @ sk_A ) ),
    inference(split,[status(esa)],['2'])).

thf(l22_finset_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_finset_1 @ A )
        & ! [B: $i] :
            ( ( r2_hidden @ B @ A )
           => ( v1_finset_1 @ B ) ) )
     => ( v1_finset_1 @ ( k3_tarski @ A ) ) ) )).

thf('4',plain,(
    ! [X9: $i] :
      ( ( v1_finset_1 @ ( k3_tarski @ X9 ) )
      | ( r2_hidden @ ( sk_B @ X9 ) @ X9 )
      | ~ ( v1_finset_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l22_finset_1])).

thf('5',plain,(
    ! [X10: $i] :
      ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
      | ( v1_finset_1 @ X10 )
      | ~ ( r2_hidden @ X10 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ! [X10: $i] :
        ( ( v1_finset_1 @ X10 )
        | ~ ( r2_hidden @ X10 @ sk_A ) )
   <= ! [X10: $i] :
        ( ( v1_finset_1 @ X10 )
        | ~ ( r2_hidden @ X10 @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('7',plain,
    ( ( ~ ( v1_finset_1 @ sk_A )
      | ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
      | ( v1_finset_1 @ ( sk_B @ sk_A ) ) )
   <= ! [X10: $i] :
        ( ( v1_finset_1 @ X10 )
        | ~ ( r2_hidden @ X10 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    ! [X9: $i] :
      ( ( v1_finset_1 @ ( k3_tarski @ X9 ) )
      | ~ ( v1_finset_1 @ ( sk_B @ X9 ) )
      | ~ ( v1_finset_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[l22_finset_1])).

thf('9',plain,
    ( ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
      | ~ ( v1_finset_1 @ sk_A ) )
   <= ! [X10: $i] :
        ( ( v1_finset_1 @ X10 )
        | ~ ( r2_hidden @ X10 @ sk_A ) ) ),
    inference(clc,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
   <= ( ( v1_finset_1 @ sk_A )
      & ! [X10: $i] :
          ( ( v1_finset_1 @ X10 )
          | ~ ( r2_hidden @ X10 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','9'])).

thf('11',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
    | ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('12',plain,
    ( ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
    | ~ ( v1_finset_1 @ sk_B_1 )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
    | ~ ( v1_finset_1 @ sk_B_1 )
    | ~ ( v1_finset_1 @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
   <= ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('15',plain,
    ( ( r2_hidden @ sk_B_1 @ sk_A )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf(l49_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ ( k3_tarski @ X1 ) )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[l49_zfmisc_1])).

thf('17',plain,
    ( ( r1_tarski @ sk_B_1 @ ( k3_tarski @ sk_A ) )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('18',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('19',plain,
    ( ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k3_tarski @ sk_A ) ) )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(cc2_finset_1,axiom,(
    ! [A: $i] :
      ( ( v1_finset_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_finset_1 @ B ) ) ) )).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_finset_1 @ X6 )
      | ~ ( v1_finset_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_finset_1])).

thf('21',plain,
    ( ( ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
      | ( v1_finset_1 @ sk_B_1 ) )
   <= ( r2_hidden @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,
    ( ( v1_finset_1 @ sk_B_1 )
   <= ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
      & ( r2_hidden @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','21'])).

thf('23',plain,
    ( ~ ( v1_finset_1 @ sk_B_1 )
   <= ~ ( v1_finset_1 @ sk_B_1 ) ),
    inference(split,[status(esa)],['12'])).

thf('24',plain,
    ( ( v1_finset_1 @ sk_B_1 )
    | ~ ( r2_hidden @ sk_B_1 @ sk_A )
    | ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( v1_finset_1 @ ( k3_tarski @ sk_A ) )
   <= ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf(fc17_finset_1,axiom,(
    ! [A: $i] :
      ( ( v1_finset_1 @ A )
     => ( v1_finset_1 @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('26',plain,(
    ! [X8: $i] :
      ( ( v1_finset_1 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( v1_finset_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc17_finset_1])).

thf(t100_zfmisc_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ) )).

thf('27',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ ( k1_zfmisc_1 @ ( k3_tarski @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t100_zfmisc_1])).

thf('28',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('29',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_finset_1 @ X6 )
      | ~ ( v1_finset_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_finset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_finset_1 @ ( k1_zfmisc_1 @ ( k3_tarski @ X0 ) ) )
      | ( v1_finset_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_finset_1 @ ( k3_tarski @ X0 ) )
      | ( v1_finset_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','31'])).

thf('33',plain,
    ( ( v1_finset_1 @ sk_A )
   <= ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','32'])).

thf('34',plain,
    ( ~ ( v1_finset_1 @ sk_A )
   <= ~ ( v1_finset_1 @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,
    ( ( v1_finset_1 @ sk_A )
    | ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( v1_finset_1 @ sk_A )
    | ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['2'])).

thf('37',plain,(
    v1_finset_1 @ sk_A ),
    inference('sat_resolution*',[status(thm)],['11','13','24','35','36'])).

thf('38',plain,
    ( ! [X10: $i] :
        ( ( v1_finset_1 @ X10 )
        | ~ ( r2_hidden @ X10 @ sk_A ) )
    | ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(split,[status(esa)],['5'])).

thf('39',plain,(
    ! [X10: $i] :
      ( ( v1_finset_1 @ X10 )
      | ~ ( r2_hidden @ X10 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['11','13','24','35','38'])).

thf('40',plain,(
    v1_finset_1 @ ( k3_tarski @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['10','37','39'])).

thf('41',plain,
    ( $false
   <= ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','40'])).

thf('42',plain,(
    ~ ( v1_finset_1 @ ( k3_tarski @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['11','13','24','35'])).

thf('43',plain,(
    $false ),
    inference(simpl_trail,[status(thm)],['41','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.7EYCFeEWeb
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:57:45 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running portfolio for 600 s
% 0.13/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 40 iterations in 0.017s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.46  thf(v1_finset_1_type, type, v1_finset_1: $i > $o).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.46  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.20/0.46  thf(t25_finset_1, conjecture,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ( v1_finset_1 @ A ) & 
% 0.20/0.46         ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( v1_finset_1 @ B ) ) ) ) <=>
% 0.20/0.46       ( v1_finset_1 @ ( k3_tarski @ A ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i]:
% 0.20/0.46        ( ( ( v1_finset_1 @ A ) & 
% 0.20/0.46            ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( v1_finset_1 @ B ) ) ) ) <=>
% 0.20/0.46          ( v1_finset_1 @ ( k3_tarski @ A ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t25_finset_1])).
% 0.20/0.46  thf('0', plain,
% 0.20/0.46      ((~ (v1_finset_1 @ (k3_tarski @ sk_A))
% 0.20/0.46        | (r2_hidden @ sk_B_1 @ sk_A)
% 0.20/0.46        | ~ (v1_finset_1 @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      ((~ (v1_finset_1 @ (k3_tarski @ sk_A)))
% 0.20/0.46         <= (~ ((v1_finset_1 @ (k3_tarski @ sk_A))))),
% 0.20/0.46      inference('split', [status(esa)], ['0'])).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (((v1_finset_1 @ (k3_tarski @ sk_A)) | (v1_finset_1 @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('3', plain, (((v1_finset_1 @ sk_A)) <= (((v1_finset_1 @ sk_A)))),
% 0.20/0.46      inference('split', [status(esa)], ['2'])).
% 0.20/0.46  thf(l22_finset_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( ( v1_finset_1 @ A ) & 
% 0.20/0.46         ( ![B:$i]: ( ( r2_hidden @ B @ A ) => ( v1_finset_1 @ B ) ) ) ) =>
% 0.20/0.46       ( v1_finset_1 @ ( k3_tarski @ A ) ) ))).
% 0.20/0.46  thf('4', plain,
% 0.20/0.46      (![X9 : $i]:
% 0.20/0.46         ((v1_finset_1 @ (k3_tarski @ X9))
% 0.20/0.46          | (r2_hidden @ (sk_B @ X9) @ X9)
% 0.20/0.46          | ~ (v1_finset_1 @ X9))),
% 0.20/0.46      inference('cnf', [status(esa)], [l22_finset_1])).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      (![X10 : $i]:
% 0.20/0.46         ((v1_finset_1 @ (k3_tarski @ sk_A))
% 0.20/0.46          | (v1_finset_1 @ X10)
% 0.20/0.46          | ~ (r2_hidden @ X10 @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      ((![X10 : $i]: ((v1_finset_1 @ X10) | ~ (r2_hidden @ X10 @ sk_A)))
% 0.20/0.46         <= ((![X10 : $i]: ((v1_finset_1 @ X10) | ~ (r2_hidden @ X10 @ sk_A))))),
% 0.20/0.46      inference('split', [status(esa)], ['5'])).
% 0.20/0.46  thf('7', plain,
% 0.20/0.46      (((~ (v1_finset_1 @ sk_A)
% 0.20/0.46         | (v1_finset_1 @ (k3_tarski @ sk_A))
% 0.20/0.46         | (v1_finset_1 @ (sk_B @ sk_A))))
% 0.20/0.46         <= ((![X10 : $i]: ((v1_finset_1 @ X10) | ~ (r2_hidden @ X10 @ sk_A))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (![X9 : $i]:
% 0.20/0.46         ((v1_finset_1 @ (k3_tarski @ X9))
% 0.20/0.46          | ~ (v1_finset_1 @ (sk_B @ X9))
% 0.20/0.46          | ~ (v1_finset_1 @ X9))),
% 0.20/0.46      inference('cnf', [status(esa)], [l22_finset_1])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      ((((v1_finset_1 @ (k3_tarski @ sk_A)) | ~ (v1_finset_1 @ sk_A)))
% 0.20/0.46         <= ((![X10 : $i]: ((v1_finset_1 @ X10) | ~ (r2_hidden @ X10 @ sk_A))))),
% 0.20/0.46      inference('clc', [status(thm)], ['7', '8'])).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      (((v1_finset_1 @ (k3_tarski @ sk_A)))
% 0.20/0.46         <= (((v1_finset_1 @ sk_A)) & 
% 0.20/0.46             (![X10 : $i]: ((v1_finset_1 @ X10) | ~ (r2_hidden @ X10 @ sk_A))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['3', '9'])).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (((r2_hidden @ sk_B_1 @ sk_A)) | 
% 0.20/0.46       ~ ((v1_finset_1 @ (k3_tarski @ sk_A))) | ~ ((v1_finset_1 @ sk_A))),
% 0.20/0.46      inference('split', [status(esa)], ['0'])).
% 0.20/0.46  thf('12', plain,
% 0.20/0.46      ((~ (v1_finset_1 @ (k3_tarski @ sk_A))
% 0.20/0.46        | ~ (v1_finset_1 @ sk_B_1)
% 0.20/0.46        | ~ (v1_finset_1 @ sk_A))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('13', plain,
% 0.20/0.46      (~ ((v1_finset_1 @ (k3_tarski @ sk_A))) | ~ ((v1_finset_1 @ sk_B_1)) | 
% 0.20/0.46       ~ ((v1_finset_1 @ sk_A))),
% 0.20/0.46      inference('split', [status(esa)], ['12'])).
% 0.20/0.46  thf('14', plain,
% 0.20/0.46      (((v1_finset_1 @ (k3_tarski @ sk_A)))
% 0.20/0.46         <= (((v1_finset_1 @ (k3_tarski @ sk_A))))),
% 0.20/0.46      inference('split', [status(esa)], ['2'])).
% 0.20/0.46  thf('15', plain,
% 0.20/0.46      (((r2_hidden @ sk_B_1 @ sk_A)) <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.20/0.46      inference('split', [status(esa)], ['0'])).
% 0.20/0.46  thf(l49_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( r2_hidden @ A @ B ) => ( r1_tarski @ A @ ( k3_tarski @ B ) ) ))).
% 0.20/0.46  thf('16', plain,
% 0.20/0.46      (![X0 : $i, X1 : $i]:
% 0.20/0.46         ((r1_tarski @ X0 @ (k3_tarski @ X1)) | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.46      inference('cnf', [status(esa)], [l49_zfmisc_1])).
% 0.20/0.46  thf('17', plain,
% 0.20/0.46      (((r1_tarski @ sk_B_1 @ (k3_tarski @ sk_A)))
% 0.20/0.46         <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.46  thf(t3_subset, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.46  thf('18', plain,
% 0.20/0.46      (![X3 : $i, X5 : $i]:
% 0.20/0.46         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.46      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.46  thf('19', plain,
% 0.20/0.46      (((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k3_tarski @ sk_A))))
% 0.20/0.46         <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.46  thf(cc2_finset_1, axiom,
% 0.20/0.46    (![A:$i]:
% 0.20/0.46     ( ( v1_finset_1 @ A ) =>
% 0.20/0.46       ( ![B:$i]:
% 0.20/0.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_finset_1 @ B ) ) ) ))).
% 0.20/0.46  thf('20', plain,
% 0.20/0.46      (![X6 : $i, X7 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.20/0.46          | (v1_finset_1 @ X6)
% 0.20/0.46          | ~ (v1_finset_1 @ X7))),
% 0.20/0.46      inference('cnf', [status(esa)], [cc2_finset_1])).
% 0.20/0.46  thf('21', plain,
% 0.20/0.46      (((~ (v1_finset_1 @ (k3_tarski @ sk_A)) | (v1_finset_1 @ sk_B_1)))
% 0.20/0.46         <= (((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.46  thf('22', plain,
% 0.20/0.46      (((v1_finset_1 @ sk_B_1))
% 0.20/0.46         <= (((v1_finset_1 @ (k3_tarski @ sk_A))) & 
% 0.20/0.46             ((r2_hidden @ sk_B_1 @ sk_A)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['14', '21'])).
% 0.20/0.46  thf('23', plain,
% 0.20/0.46      ((~ (v1_finset_1 @ sk_B_1)) <= (~ ((v1_finset_1 @ sk_B_1)))),
% 0.20/0.46      inference('split', [status(esa)], ['12'])).
% 0.20/0.46  thf('24', plain,
% 0.20/0.46      (((v1_finset_1 @ sk_B_1)) | ~ ((r2_hidden @ sk_B_1 @ sk_A)) | 
% 0.20/0.46       ~ ((v1_finset_1 @ (k3_tarski @ sk_A)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.46  thf('25', plain,
% 0.20/0.46      (((v1_finset_1 @ (k3_tarski @ sk_A)))
% 0.20/0.46         <= (((v1_finset_1 @ (k3_tarski @ sk_A))))),
% 0.20/0.46      inference('split', [status(esa)], ['2'])).
% 0.20/0.46  thf(fc17_finset_1, axiom,
% 0.20/0.46    (![A:$i]: ( ( v1_finset_1 @ A ) => ( v1_finset_1 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.46  thf('26', plain,
% 0.20/0.46      (![X8 : $i]: ((v1_finset_1 @ (k1_zfmisc_1 @ X8)) | ~ (v1_finset_1 @ X8))),
% 0.20/0.46      inference('cnf', [status(esa)], [fc17_finset_1])).
% 0.20/0.46  thf(t100_zfmisc_1, axiom,
% 0.20/0.46    (![A:$i]: ( r1_tarski @ A @ ( k1_zfmisc_1 @ ( k3_tarski @ A ) ) ))).
% 0.20/0.46  thf('27', plain,
% 0.20/0.46      (![X2 : $i]: (r1_tarski @ X2 @ (k1_zfmisc_1 @ (k3_tarski @ X2)))),
% 0.20/0.46      inference('cnf', [status(esa)], [t100_zfmisc_1])).
% 0.20/0.46  thf('28', plain,
% 0.20/0.46      (![X3 : $i, X5 : $i]:
% 0.20/0.46         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.46      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.46  thf('29', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ (k3_tarski @ X0))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.46  thf('30', plain,
% 0.20/0.46      (![X6 : $i, X7 : $i]:
% 0.20/0.46         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.20/0.46          | (v1_finset_1 @ X6)
% 0.20/0.46          | ~ (v1_finset_1 @ X7))),
% 0.20/0.46      inference('cnf', [status(esa)], [cc2_finset_1])).
% 0.20/0.46  thf('31', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (v1_finset_1 @ (k1_zfmisc_1 @ (k3_tarski @ X0)))
% 0.20/0.46          | (v1_finset_1 @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.46  thf('32', plain,
% 0.20/0.46      (![X0 : $i]: (~ (v1_finset_1 @ (k3_tarski @ X0)) | (v1_finset_1 @ X0))),
% 0.20/0.46      inference('sup-', [status(thm)], ['26', '31'])).
% 0.20/0.46  thf('33', plain,
% 0.20/0.46      (((v1_finset_1 @ sk_A)) <= (((v1_finset_1 @ (k3_tarski @ sk_A))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['25', '32'])).
% 0.20/0.46  thf('34', plain, ((~ (v1_finset_1 @ sk_A)) <= (~ ((v1_finset_1 @ sk_A)))),
% 0.20/0.46      inference('split', [status(esa)], ['0'])).
% 0.20/0.46  thf('35', plain,
% 0.20/0.46      (((v1_finset_1 @ sk_A)) | ~ ((v1_finset_1 @ (k3_tarski @ sk_A)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.46  thf('36', plain,
% 0.20/0.46      (((v1_finset_1 @ sk_A)) | ((v1_finset_1 @ (k3_tarski @ sk_A)))),
% 0.20/0.46      inference('split', [status(esa)], ['2'])).
% 0.20/0.46  thf('37', plain, (((v1_finset_1 @ sk_A))),
% 0.20/0.46      inference('sat_resolution*', [status(thm)],
% 0.20/0.46                ['11', '13', '24', '35', '36'])).
% 0.20/0.46  thf('38', plain,
% 0.20/0.46      ((![X10 : $i]: ((v1_finset_1 @ X10) | ~ (r2_hidden @ X10 @ sk_A))) | 
% 0.20/0.46       ((v1_finset_1 @ (k3_tarski @ sk_A)))),
% 0.20/0.46      inference('split', [status(esa)], ['5'])).
% 0.20/0.46  thf('39', plain,
% 0.20/0.46      ((![X10 : $i]: ((v1_finset_1 @ X10) | ~ (r2_hidden @ X10 @ sk_A)))),
% 0.20/0.46      inference('sat_resolution*', [status(thm)],
% 0.20/0.46                ['11', '13', '24', '35', '38'])).
% 0.20/0.46  thf('40', plain, ((v1_finset_1 @ (k3_tarski @ sk_A))),
% 0.20/0.46      inference('simpl_trail', [status(thm)], ['10', '37', '39'])).
% 0.20/0.46  thf('41', plain, (($false) <= (~ ((v1_finset_1 @ (k3_tarski @ sk_A))))),
% 0.20/0.46      inference('demod', [status(thm)], ['1', '40'])).
% 0.20/0.46  thf('42', plain, (~ ((v1_finset_1 @ (k3_tarski @ sk_A)))),
% 0.20/0.46      inference('sat_resolution*', [status(thm)], ['11', '13', '24', '35'])).
% 0.20/0.46  thf('43', plain, ($false),
% 0.20/0.46      inference('simpl_trail', [status(thm)], ['41', '42'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.33/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
