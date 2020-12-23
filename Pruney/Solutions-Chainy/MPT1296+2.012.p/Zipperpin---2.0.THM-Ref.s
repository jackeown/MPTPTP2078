%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pvrqrSW5V2

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:05:13 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :   67 (  89 expanded)
%              Number of leaves         :   26 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :  566 ( 862 expanded)
%              Number of equality atoms :   36 (  58 expanded)
%              Maximal formula depth    :   18 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k6_setfam_1_type,type,(
    k6_setfam_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_setfam_1_type,type,(
    k5_setfam_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ! [X17: $i,X18: $i] :
      ( ( ( k7_setfam_1 @ X18 @ ( k7_setfam_1 @ X18 @ X17 ) )
        = X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X18 ) ) ) ) ),
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
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
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
    ! [X27: $i,X28: $i] :
      ( ( X27 = k1_xboole_0 )
      | ( ( k6_setfam_1 @ X28 @ ( k7_setfam_1 @ X28 @ X27 ) )
        = ( k3_subset_1 @ X28 @ ( k5_setfam_1 @ X28 @ X27 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X28 ) ) ) ) ),
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
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k5_setfam_1 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X13 ) ) ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ( ( k3_subset_1 @ X7 @ ( k3_subset_1 @ X7 @ X6 ) )
        = X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
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

thf(t34_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) )).

thf('18',plain,(
    ! [X22: $i] :
      ( ( X22 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X22 ) @ X22 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('19',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('20',plain,(
    ! [X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

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

thf('22',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) )
      | ( X9
       != ( k7_setfam_1 @ X10 @ X11 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X10 @ X12 ) @ X11 )
      | ~ ( r2_hidden @ X12 @ X9 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('23',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( r2_hidden @ X12 @ ( k7_setfam_1 @ X10 @ X11 ) )
      | ( r2_hidden @ ( k3_subset_1 @ X10 @ X12 ) @ X11 )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X10 ) ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ X0 @ X1 ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,(
    ! [X8: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k3_subset_1 @ X0 @ X1 ) @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('27',plain,(
    ! [X2: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('28',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( ( k4_xboole_0 @ X4 @ ( k1_tarski @ X3 ) )
       != X4 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(clc,[status(thm)],['26','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('33',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( m1_subset_1 @ X19 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( r2_hidden @ X1 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k7_setfam_1 @ X0 @ k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k7_setfam_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','35'])).

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
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.pvrqrSW5V2
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:16:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.41/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.59  % Solved by: fo/fo7.sh
% 0.41/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.59  % done 176 iterations in 0.133s
% 0.41/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.59  % SZS output start Refutation
% 0.41/0.59  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.41/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.41/0.59  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.59  thf(k6_setfam_1_type, type, k6_setfam_1: $i > $i > $i).
% 0.41/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.59  thf(k5_setfam_1_type, type, k5_setfam_1: $i > $i > $i).
% 0.41/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.59  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.41/0.59  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.41/0.59  thf(sk_B_type, type, sk_B: $i > $i).
% 0.41/0.59  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.41/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.59  thf(t12_tops_2, conjecture,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.59       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.41/0.59         ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.41/0.59           ( k3_subset_1 @ A @ ( k6_setfam_1 @ A @ B ) ) ) ) ))).
% 0.41/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.59    (~( ![A:$i,B:$i]:
% 0.41/0.59        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.59          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.41/0.59            ( ( k5_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.41/0.59              ( k3_subset_1 @ A @ ( k6_setfam_1 @ A @ B ) ) ) ) ) )),
% 0.41/0.59    inference('cnf.neg', [status(esa)], [t12_tops_2])).
% 0.41/0.59  thf('0', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(involutiveness_k7_setfam_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.59       ( ( k7_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) = ( B ) ) ))).
% 0.41/0.59  thf('1', plain,
% 0.41/0.59      (![X17 : $i, X18 : $i]:
% 0.41/0.59         (((k7_setfam_1 @ X18 @ (k7_setfam_1 @ X18 @ X17)) = (X17))
% 0.41/0.59          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X18))))),
% 0.41/0.59      inference('cnf', [status(esa)], [involutiveness_k7_setfam_1])).
% 0.41/0.59  thf('2', plain,
% 0.41/0.59      (((k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.41/0.59  thf('3', plain,
% 0.41/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf(dt_k7_setfam_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.59       ( m1_subset_1 @
% 0.41/0.59         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.41/0.59  thf('4', plain,
% 0.41/0.59      (![X15 : $i, X16 : $i]:
% 0.41/0.59         ((m1_subset_1 @ (k7_setfam_1 @ X15 @ X16) @ 
% 0.41/0.59           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15)))
% 0.41/0.59          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.41/0.59      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.41/0.59  thf('5', plain,
% 0.41/0.59      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B_1) @ 
% 0.41/0.59        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['3', '4'])).
% 0.41/0.59  thf(t11_tops_2, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.59       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.41/0.59         ( ( k6_setfam_1 @ A @ ( k7_setfam_1 @ A @ B ) ) =
% 0.41/0.59           ( k3_subset_1 @ A @ ( k5_setfam_1 @ A @ B ) ) ) ) ))).
% 0.41/0.59  thf('6', plain,
% 0.41/0.59      (![X27 : $i, X28 : $i]:
% 0.41/0.59         (((X27) = (k1_xboole_0))
% 0.41/0.59          | ((k6_setfam_1 @ X28 @ (k7_setfam_1 @ X28 @ X27))
% 0.41/0.59              = (k3_subset_1 @ X28 @ (k5_setfam_1 @ X28 @ X27)))
% 0.41/0.59          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X28))))),
% 0.41/0.59      inference('cnf', [status(esa)], [t11_tops_2])).
% 0.41/0.59  thf('7', plain,
% 0.41/0.59      ((((k6_setfam_1 @ sk_A @ 
% 0.41/0.59          (k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1)))
% 0.41/0.59          = (k3_subset_1 @ sk_A @ 
% 0.41/0.59             (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1))))
% 0.41/0.59        | ((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['5', '6'])).
% 0.41/0.59  thf('8', plain,
% 0.41/0.59      (((k7_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1)) = (sk_B_1))),
% 0.41/0.59      inference('sup-', [status(thm)], ['0', '1'])).
% 0.41/0.59  thf('9', plain,
% 0.41/0.59      ((((k6_setfam_1 @ sk_A @ sk_B_1)
% 0.41/0.59          = (k3_subset_1 @ sk_A @ 
% 0.41/0.59             (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1))))
% 0.41/0.59        | ((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.41/0.59      inference('demod', [status(thm)], ['7', '8'])).
% 0.41/0.59  thf('10', plain,
% 0.41/0.59      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B_1) @ 
% 0.41/0.59        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['3', '4'])).
% 0.41/0.59  thf(dt_k5_setfam_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.59       ( m1_subset_1 @ ( k5_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.41/0.59  thf('11', plain,
% 0.41/0.59      (![X13 : $i, X14 : $i]:
% 0.41/0.59         ((m1_subset_1 @ (k5_setfam_1 @ X13 @ X14) @ (k1_zfmisc_1 @ X13))
% 0.41/0.59          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X13))))),
% 0.41/0.59      inference('cnf', [status(esa)], [dt_k5_setfam_1])).
% 0.41/0.59  thf('12', plain,
% 0.41/0.59      ((m1_subset_1 @ (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1)) @ 
% 0.41/0.59        (k1_zfmisc_1 @ sk_A))),
% 0.41/0.59      inference('sup-', [status(thm)], ['10', '11'])).
% 0.41/0.59  thf(involutiveness_k3_subset_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.59       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.41/0.59  thf('13', plain,
% 0.41/0.59      (![X6 : $i, X7 : $i]:
% 0.41/0.59         (((k3_subset_1 @ X7 @ (k3_subset_1 @ X7 @ X6)) = (X6))
% 0.41/0.59          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.41/0.59      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.41/0.59  thf('14', plain,
% 0.41/0.59      (((k3_subset_1 @ sk_A @ 
% 0.41/0.59         (k3_subset_1 @ sk_A @ 
% 0.41/0.59          (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1))))
% 0.41/0.59         = (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['12', '13'])).
% 0.41/0.59  thf('15', plain,
% 0.41/0.59      ((((k3_subset_1 @ sk_A @ (k6_setfam_1 @ sk_A @ sk_B_1))
% 0.41/0.59          = (k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1)))
% 0.41/0.59        | ((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0)))),
% 0.41/0.59      inference('sup+', [status(thm)], ['9', '14'])).
% 0.41/0.59  thf('16', plain,
% 0.41/0.59      (((k5_setfam_1 @ sk_A @ (k7_setfam_1 @ sk_A @ sk_B_1))
% 0.41/0.59         != (k3_subset_1 @ sk_A @ (k6_setfam_1 @ sk_A @ sk_B_1)))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('17', plain, (((k7_setfam_1 @ sk_A @ sk_B_1) = (k1_xboole_0))),
% 0.41/0.59      inference('simplify_reflect-', [status(thm)], ['15', '16'])).
% 0.41/0.59  thf(t34_mcart_1, axiom,
% 0.41/0.59    (![A:$i]:
% 0.41/0.59     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.41/0.59          ( ![B:$i]:
% 0.41/0.59            ( ~( ( r2_hidden @ B @ A ) & 
% 0.41/0.59                 ( ![C:$i,D:$i,E:$i,F:$i]:
% 0.41/0.59                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.41/0.59                        ( ( B ) = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.59  thf('18', plain,
% 0.41/0.59      (![X22 : $i]:
% 0.41/0.59         (((X22) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X22) @ X22))),
% 0.41/0.59      inference('cnf', [status(esa)], [t34_mcart_1])).
% 0.41/0.59  thf(t4_subset_1, axiom,
% 0.41/0.59    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.41/0.59  thf('19', plain,
% 0.41/0.59      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.41/0.59      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.41/0.59  thf('20', plain,
% 0.41/0.59      (![X15 : $i, X16 : $i]:
% 0.41/0.59         ((m1_subset_1 @ (k7_setfam_1 @ X15 @ X16) @ 
% 0.41/0.59           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15)))
% 0.41/0.59          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X15))))),
% 0.41/0.59      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.41/0.59  thf('21', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (m1_subset_1 @ (k7_setfam_1 @ X0 @ k1_xboole_0) @ 
% 0.41/0.59          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['19', '20'])).
% 0.41/0.59  thf(d8_setfam_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.59       ( ![C:$i]:
% 0.41/0.59         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.41/0.59           ( ( ( C ) = ( k7_setfam_1 @ A @ B ) ) <=>
% 0.41/0.59             ( ![D:$i]:
% 0.41/0.59               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.41/0.59                 ( ( r2_hidden @ D @ C ) <=>
% 0.41/0.59                   ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) ) ))).
% 0.41/0.59  thf('22', plain,
% 0.41/0.59      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10)))
% 0.41/0.59          | ((X9) != (k7_setfam_1 @ X10 @ X11))
% 0.41/0.59          | (r2_hidden @ (k3_subset_1 @ X10 @ X12) @ X11)
% 0.41/0.59          | ~ (r2_hidden @ X12 @ X9)
% 0.41/0.59          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X10))
% 0.41/0.59          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10))))),
% 0.41/0.59      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.41/0.59  thf('23', plain,
% 0.41/0.59      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10)))
% 0.41/0.59          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X10))
% 0.41/0.59          | ~ (r2_hidden @ X12 @ (k7_setfam_1 @ X10 @ X11))
% 0.41/0.59          | (r2_hidden @ (k3_subset_1 @ X10 @ X12) @ X11)
% 0.41/0.59          | ~ (m1_subset_1 @ (k7_setfam_1 @ X10 @ X11) @ 
% 0.41/0.59               (k1_zfmisc_1 @ (k1_zfmisc_1 @ X10))))),
% 0.41/0.59      inference('simplify', [status(thm)], ['22'])).
% 0.41/0.59  thf('24', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((r2_hidden @ (k3_subset_1 @ X0 @ X1) @ k1_xboole_0)
% 0.41/0.59          | ~ (r2_hidden @ X1 @ (k7_setfam_1 @ X0 @ k1_xboole_0))
% 0.41/0.59          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.41/0.59          | ~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0))))),
% 0.41/0.59      inference('sup-', [status(thm)], ['21', '23'])).
% 0.41/0.59  thf('25', plain,
% 0.41/0.59      (![X8 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X8))),
% 0.41/0.59      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.41/0.59  thf('26', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((r2_hidden @ (k3_subset_1 @ X0 @ X1) @ k1_xboole_0)
% 0.41/0.59          | ~ (r2_hidden @ X1 @ (k7_setfam_1 @ X0 @ k1_xboole_0))
% 0.41/0.59          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.41/0.59      inference('demod', [status(thm)], ['24', '25'])).
% 0.41/0.59  thf(t4_boole, axiom,
% 0.41/0.59    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.41/0.59  thf('27', plain,
% 0.41/0.59      (![X2 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.41/0.59      inference('cnf', [status(esa)], [t4_boole])).
% 0.41/0.59  thf(t65_zfmisc_1, axiom,
% 0.41/0.59    (![A:$i,B:$i]:
% 0.41/0.59     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.41/0.59       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.41/0.59  thf('28', plain,
% 0.41/0.59      (![X3 : $i, X4 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X3 @ X4)
% 0.41/0.59          | ((k4_xboole_0 @ X4 @ (k1_tarski @ X3)) != (X4)))),
% 0.41/0.59      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.41/0.59  thf('29', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['27', '28'])).
% 0.41/0.59  thf('30', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.41/0.59      inference('simplify', [status(thm)], ['29'])).
% 0.41/0.59  thf('31', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.41/0.59          | ~ (r2_hidden @ X1 @ (k7_setfam_1 @ X0 @ k1_xboole_0)))),
% 0.41/0.59      inference('clc', [status(thm)], ['26', '30'])).
% 0.41/0.59  thf('32', plain,
% 0.41/0.59      (![X0 : $i]:
% 0.41/0.59         (m1_subset_1 @ (k7_setfam_1 @ X0 @ k1_xboole_0) @ 
% 0.41/0.59          (k1_zfmisc_1 @ (k1_zfmisc_1 @ X0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['19', '20'])).
% 0.41/0.59  thf(t4_subset, axiom,
% 0.41/0.59    (![A:$i,B:$i,C:$i]:
% 0.41/0.59     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.41/0.59       ( m1_subset_1 @ A @ C ) ))).
% 0.41/0.59  thf('33', plain,
% 0.41/0.59      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.41/0.59         (~ (r2_hidden @ X19 @ X20)
% 0.41/0.59          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.41/0.59          | (m1_subset_1 @ X19 @ X21))),
% 0.41/0.59      inference('cnf', [status(esa)], [t4_subset])).
% 0.41/0.59  thf('34', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ((m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 0.41/0.59          | ~ (r2_hidden @ X1 @ (k7_setfam_1 @ X0 @ k1_xboole_0)))),
% 0.41/0.59      inference('sup-', [status(thm)], ['32', '33'])).
% 0.41/0.59  thf('35', plain,
% 0.41/0.59      (![X0 : $i, X1 : $i]:
% 0.41/0.59         ~ (r2_hidden @ X1 @ (k7_setfam_1 @ X0 @ k1_xboole_0))),
% 0.41/0.59      inference('clc', [status(thm)], ['31', '34'])).
% 0.41/0.59  thf('36', plain,
% 0.41/0.59      (![X0 : $i]: ((k7_setfam_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.59      inference('sup-', [status(thm)], ['18', '35'])).
% 0.41/0.59  thf('37', plain, (((k1_xboole_0) = (sk_B_1))),
% 0.41/0.59      inference('demod', [status(thm)], ['2', '17', '36'])).
% 0.41/0.59  thf('38', plain, (((sk_B_1) != (k1_xboole_0))),
% 0.41/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.59  thf('39', plain, ($false),
% 0.41/0.59      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.41/0.59  
% 0.41/0.59  % SZS output end Refutation
% 0.41/0.59  
% 0.41/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
