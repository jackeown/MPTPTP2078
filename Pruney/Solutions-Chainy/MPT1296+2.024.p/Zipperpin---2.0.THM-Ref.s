%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UUGj6b5xYi

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:14 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   66 (  89 expanded)
%              Number of leaves         :   25 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :  550 ( 858 expanded)
%              Number of equality atoms :   32 (  55 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t12_tops_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
          = ( k3_subset_1 @ A @ ( k6_setfam_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ( ( B != k1_xboole_0 )
         => ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
            = ( k3_subset_1 @ A @ ( k6_setfam_1 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t12_tops_2])).

thf('0',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(involutiveness_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
        = B ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k7_setfam_1 @ X9 @ ( k7_setfam_1 @ X9 @ X8 ) )
        = X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('2',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('5',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t11_tops_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k6_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) )
          = ( k3_subset_1 @ A @ ( k5_setfam_1 @ A @ B ) ) ) ) ) )).

thf('6',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X24 = k1_xboole_0 )
      | ( ( k6_setfam_1 @ X25 @ ( k7_setfam_1 @ X25 @ X24 ) )
        = ( k3_subset_1 @ X25 @ ( k5_setfam_1 @ X25 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[t11_tops_2])).

thf('7',plain,
    ( ( ( k6_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) ) )
      = ( k3_subset_1 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) ) ) )
    | ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k7_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) )
    = sk_B_1 ),
    inference('sup-',[status(thm)],['0','1'])).

thf('9',plain,
    ( ( ( k6_setfam_1 @ sk_A @ sk_B_1 )
      = ( k3_subset_1 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) ) ) )
    | ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(dt_k5_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('11',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X4 @ X5 ) @ ( k1_zfmisc_1 @ X4 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_setfam_1])).

thf('12',plain,(
    m1_subset_1 @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('13',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k3_subset_1 @ X2 @ ( k3_subset_1 @ X2 @ X1 ) )
        = X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('14',plain,
    ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) ) ) )
    = ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( ( ( k3_subset_1 @ sk_A @ ( k6_setfam_1 @ sk_A @ sk_B_1 ) )
      = ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) ) )
    | ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['9','14'])).

thf('16',plain,(
    ( k5_setfam_1 @ sk_A @ ( k7_setfam_1 @ sk_A @ sk_B_1 ) )
 != ( k3_subset_1 @ sk_A @ ( k6_setfam_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B_1 )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['15','16'])).

thf(t6_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i,G: $i] :
                  ( ( ( r2_hidden @ C @ D )
                    & ( r2_hidden @ D @ E )
                    & ( r2_hidden @ E @ F )
                    & ( r2_hidden @ F @ G )
                    & ( r2_hidden @ G @ B ) )
                 => ( r1_xboole_0 @ C @ A ) ) ) ) )).

thf('18',plain,(
    ! [X18: $i] :
      ( ( X18 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X18 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t6_mcart_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('19',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('20',plain,(
    ! [X6: $i,X7: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X6 @ X7 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X6 ) ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t49_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
         => ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) )
          <=> ( r2_hidden @ C @ B ) ) ) ) )).

thf('22',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r2_hidden @ X10 @ X12 )
      | ( r2_hidden @ ( k3_subset_1 @ X11 @ X10 ) @ ( k7_setfam_1 @ X11 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[t49_setfam_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ X0 @ X1 ) @ ( k7_setfam_1 @ X0 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) ) )
      | ~ ( r2_hidden @ X1 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('25',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k7_setfam_1 @ X9 @ ( k7_setfam_1 @ X9 @ X8 ) )
        = X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k7_setfam_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( k7_setfam_1 @ X0 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ X0 @ X1 ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['23','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('29',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( m1_subset_1 @ X13 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X0 @ X1 ) @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k7_setfam_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( k3_subset_1 @ X0 @ ( sk_B @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['18','31'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('33',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( k7_setfam_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ ( k3_subset_1 @ X0 @ ( sk_B @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k7_setfam_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    k1_xboole_0 = sk_B_1 ),
    inference(demod,[status(thm)],['2','17','36'])).

thf('38',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UUGj6b5xYi
% 0.15/0.36  % Computer   : n008.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 10:29:45 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 137 iterations in 0.067s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.52  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.22/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.22/0.52  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.52  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.52  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.52  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.22/0.52  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.22/0.52  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.52  thf(t12_tops_2, conjecture,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.52       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.22/0.52         ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.22/0.52           ( k3_subset_1 @ A @ ( k6_setfam_1 @ A @ B ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i,B:$i]:
% 0.22/0.52        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.52          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.22/0.52            ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.22/0.52              ( k3_subset_1 @ A @ ( k6_setfam_1 @ A @ B ) ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t12_tops_2])).
% 0.22/0.52  thf('0', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(involutiveness_k7_setfam_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.52       ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) = ( B ) ) ))).
% 0.22/0.52  thf('1', plain,
% 0.22/0.52      (![X8 : $i, X9 : $i]:
% 0.22/0.52         (((k7_setfam_1 @ X9 @ (k7_setfam_1 @ X9 @ X8)) = (X8))
% 0.22/0.52          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X9))))),
% 0.22/0.52      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 0.22/0.52  thf('2', plain,
% 0.22/0.52      (((k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(dt_k7_setfam_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.52       ( m1_subset_1 @
% 0.22/0.52         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (![X6 : $i, X7 : $i]:
% 0.22/0.52         ((m1_subset_1 @ (k7_setfam_1 @ X6 @ X7) @ 
% 0.22/0.52           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X6)))
% 0.22/0.52          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X6))))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B_1) @ 
% 0.22/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.52  thf(t11_tops_2, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.52       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.22/0.52         ( ( k6_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.22/0.52           ( k3_subset_1 @ A @ ( k5_setfam_1 @ A @ B ) ) ) ) ))).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      (![X24 : $i, X25 : $i]:
% 0.22/0.52         (((X24) = (k1_xboole_0))
% 0.22/0.52          | ((k6_setfam_1 @ X25 @ (k7_setfam_1 @ X25 @ X24))
% 0.22/0.52              = (k3_subset_1 @ X25 @ (k5_setfam_1 @ X25 @ X24)))
% 0.22/0.52          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X25))))),
% 0.22/0.52      inference('cnf', [status(esa)], [t11_tops_2])).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      ((((k6_setfam_1 @ sk_A @ 
% 0.22/0.52          (k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1)))
% 0.22/0.52          = (k3_subset_1 @ sk_A @ 
% 0.22/0.52             (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1))))
% 0.22/0.52        | ((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (((k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.22/0.52      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.52  thf('9', plain,
% 0.22/0.52      ((((k6_setfam_1 @ sk_A @ sk_B_1)
% 0.22/0.52          = (k3_subset_1 @ sk_A @ 
% 0.22/0.52             (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1))))
% 0.22/0.52        | ((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.22/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B_1) @ 
% 0.22/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.52  thf(dt_k5_setfam_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.52       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.22/0.52  thf('11', plain,
% 0.22/0.52      (![X4 : $i, X5 : $i]:
% 0.22/0.52         ((m1_subset_1 @ (k5_setfam_1 @ X4 @ X5) @ (k1_zfmisc_1 @ X4))
% 0.22/0.52          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X4))))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      ((m1_subset_1 @ (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1)) @ 
% 0.22/0.52        (k1_zfmisc_1 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.52  thf(involutiveness_k3_subset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.52       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (![X1 : $i, X2 : $i]:
% 0.22/0.52         (((k3_subset_1 @ X2 @ (k3_subset_1 @ X2 @ X1)) = (X1))
% 0.22/0.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.22/0.52      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      (((k3_subset_1 @ sk_A @ 
% 0.22/0.52         (k3_subset_1 @ sk_A @ 
% 0.22/0.52          (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1))))
% 0.22/0.52         = (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.52  thf('15', plain,
% 0.22/0.52      ((((k3_subset_1 @ sk_A @ (k6_setfam_1 @ sk_A @ sk_B_1))
% 0.22/0.52          = (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1)))
% 0.22/0.52        | ((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.22/0.52      inference('sup+', [status(thm)], ['9', '14'])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (((k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1))
% 0.22/0.52         != (k3_subset_1 @ sk_A @ (k6_setfam_1 @ sk_A @ sk_B_1)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('17', plain, (((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.22/0.52  thf(t6_mcart_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.52          ( ![B:$i]:
% 0.22/0.52            ( ~( ( r2_hidden @ B @ A ) & 
% 0.22/0.52                 ( ![C:$i,D:$i,E:$i,F:$i,G:$i]:
% 0.22/0.52                   ( ( ( r2_hidden @ C @ D ) & ( r2_hidden @ D @ E ) & 
% 0.22/0.52                       ( r2_hidden @ E @ F ) & ( r2_hidden @ F @ G ) & 
% 0.22/0.52                       ( r2_hidden @ G @ B ) ) =>
% 0.22/0.52                     ( r1_xboole_0 @ C @ A ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf('18', plain,
% 0.22/0.52      (![X18 : $i]:
% 0.22/0.52         (((X18) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X18) @ X18))),
% 0.22/0.52      inference('cnf', [status(esa)], [t6_mcart_1])).
% 0.22/0.52  thf(t4_subset_1, axiom,
% 0.22/0.52    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 0.22/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.52  thf('20', plain,
% 0.22/0.52      (![X6 : $i, X7 : $i]:
% 0.22/0.52         ((m1_subset_1 @ (k7_setfam_1 @ X6 @ X7) @ 
% 0.22/0.52           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X6)))
% 0.22/0.52          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X6))))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.22/0.52  thf('21', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (m1_subset_1 @ (k7_setfam_1 @ X0 @ k1_xboole_0) @ 
% 0.22/0.52          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.52  thf(t49_setfam_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.52       ( ![C:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.22/0.52           ( ( r2_hidden @ ( k3_subset_1 @ A @ C ) @ ( k7_setfam_1 @ A @ B ) ) <=>
% 0.22/0.52             ( r2_hidden @ C @ B ) ) ) ) ))).
% 0.22/0.52  thf('22', plain,
% 0.22/0.52      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11))
% 0.22/0.52          | ~ (r2_hidden @ X10 @ X12)
% 0.22/0.52          | (r2_hidden @ (k3_subset_1 @ X11 @ X10) @ (k7_setfam_1 @ X11 @ X12))
% 0.22/0.52          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X11))))),
% 0.22/0.52      inference('cnf', [status(esa)], [t49_setfam_1])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((r2_hidden @ (k3_subset_1 @ X0 @ X1) @ 
% 0.22/0.52           (k7_setfam_1 @ X0 @ (k7_setfam_1 @ X0 @ k1_xboole_0)))
% 0.22/0.52          | ~ (r2_hidden @ X1 @ (k7_setfam_1 @ X0 @ k1_xboole_0))
% 0.22/0.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      (![X3 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X3))),
% 0.22/0.52      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.52  thf('25', plain,
% 0.22/0.52      (![X8 : $i, X9 : $i]:
% 0.22/0.52         (((k7_setfam_1 @ X9 @ (k7_setfam_1 @ X9 @ X8)) = (X8))
% 0.22/0.52          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X9))))),
% 0.22/0.52      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 0.22/0.52  thf('26', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((k7_setfam_1 @ X0 @ (k7_setfam_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.52  thf('27', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((r2_hidden @ (k3_subset_1 @ X0 @ X1) @ k1_xboole_0)
% 0.22/0.52          | ~ (r2_hidden @ X1 @ (k7_setfam_1 @ X0 @ k1_xboole_0))
% 0.22/0.52          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.22/0.52      inference('demod', [status(thm)], ['23', '26'])).
% 0.22/0.52  thf('28', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (m1_subset_1 @ (k7_setfam_1 @ X0 @ k1_xboole_0) @ 
% 0.22/0.52          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.52  thf(t4_subset, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.22/0.52       ( m1_subset_1 @ A @ C ) ))).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X13 @ X14)
% 0.22/0.52          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.22/0.52          | (m1_subset_1 @ X13 @ X15))),
% 0.22/0.52      inference('cnf', [status(esa)], [t4_subset])).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.22/0.52          | ~ (r2_hidden @ X1 @ (k7_setfam_1 @ X0 @ k1_xboole_0)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.52  thf('31', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X1 @ (k7_setfam_1 @ X0 @ k1_xboole_0))
% 0.22/0.52          | (r2_hidden @ (k3_subset_1 @ X0 @ X1) @ k1_xboole_0))),
% 0.22/0.52      inference('clc', [status(thm)], ['27', '30'])).
% 0.22/0.52  thf('32', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k7_setfam_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.22/0.52          | (r2_hidden @ 
% 0.22/0.52             (k3_subset_1 @ X0 @ (sk_B @ (k7_setfam_1 @ X0 @ k1_xboole_0))) @ 
% 0.22/0.52             k1_xboole_0))),
% 0.22/0.52      inference('sup-', [status(thm)], ['18', '31'])).
% 0.22/0.52  thf(t7_ordinal1, axiom,
% 0.22/0.52    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.52  thf('33', plain,
% 0.22/0.52      (![X16 : $i, X17 : $i]:
% 0.22/0.52         (~ (r2_hidden @ X16 @ X17) | ~ (r1_tarski @ X17 @ X16))),
% 0.22/0.52      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (((k7_setfam_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.22/0.52          | ~ (r1_tarski @ k1_xboole_0 @ 
% 0.22/0.52               (k3_subset_1 @ X0 @ (sk_B @ (k7_setfam_1 @ X0 @ k1_xboole_0)))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.52  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.52  thf('35', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.22/0.52      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.52  thf('36', plain,
% 0.22/0.52      (![X0 : $i]: ((k7_setfam_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.52      inference('demod', [status(thm)], ['34', '35'])).
% 0.22/0.52  thf('37', plain, (((k1_xboole_0) = (sk_B_1))),
% 0.22/0.52      inference('demod', [status(thm)], ['2', '17', '36'])).
% 0.22/0.52  thf('38', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('39', plain, ($false),
% 0.22/0.52      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
