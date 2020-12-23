%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EXrM38cgGE

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:39:10 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 199 expanded)
%              Number of leaves         :   24 (  68 expanded)
%              Depth                    :   14
%              Number of atoms          :  513 (1888 expanded)
%              Number of equality atoms :   26 ( 144 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_subset_1_type,type,(
    k3_subset_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k7_setfam_1_type,type,(
    k7_setfam_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t46_setfam_1,conjecture,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ~ ( ( B != k1_xboole_0 )
          & ( ( k7_setfam_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
       => ~ ( ( B != k1_xboole_0 )
            & ( ( k7_setfam_1 @ A @ B )
              = k1_xboole_0 ) ) ) ),
    inference('cnf.neg',[status(esa)],[t46_setfam_1])).

thf('0',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('1',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X21 ) ) )
      | ( X20
       != ( k7_setfam_1 @ X21 @ X22 ) )
      | ( r2_hidden @ X23 @ X20 )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X21 @ X23 ) @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[d8_setfam_1])).

thf('2',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ X21 @ X23 ) @ X22 )
      | ( r2_hidden @ X23 @ ( k7_setfam_1 @ X21 @ X22 ) )
      | ~ ( m1_subset_1 @ ( k7_setfam_1 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X21 ) ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( k7_setfam_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['0','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_setfam_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
     => ( m1_subset_1 @ ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('5',plain,(
    ! [X24: $i,X25: $i] :
      ( ( m1_subset_1 @ ( k7_setfam_1 @ X24 @ X25 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_setfam_1])).

thf('6',plain,(
    m1_subset_1 @ ( k7_setfam_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k7_setfam_1 @ sk_A @ sk_B )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['3','8','9','10'])).

thf(t4_boole,axiom,(
    ! [A: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ A )
      = k1_xboole_0 ) )).

thf('12',plain,(
    ! [X9: $i] :
      ( ( k4_xboole_0 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t4_boole])).

thf(t65_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) )
        = A )
    <=> ~ ( r2_hidden @ B @ A ) ) )).

thf('13',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ( ( k4_xboole_0 @ X14 @ ( k1_tarski @ X13 ) )
       != X14 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['11','15'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('17',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('18',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k4_xboole_0 @ X14 @ ( k1_tarski @ X15 ) )
        = X14 )
      | ( r2_hidden @ X15 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t65_zfmisc_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_xboole_0 @ X1 @ ( k2_tarski @ X0 @ X0 ) )
        = X1 )
      | ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['17','18'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('22',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ X28 ) )
      | ( m1_subset_1 @ X26 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf(involutiveness_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) )
        = B ) ) )).

thf('25',plain,(
    ! [X18: $i,X19: $i] :
      ( ( ( k3_subset_1 @ X19 @ ( k3_subset_1 @ X19 @ X18 ) )
        = X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[involutiveness_k3_subset_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( ( k3_subset_1 @ sk_A @ ( k3_subset_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) )
        = ( sk_C @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ ( k3_subset_1 @ sk_A @ X0 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['11','15'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ sk_B )
      | ( r1_tarski @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) @ ( k1_zfmisc_1 @ sk_A ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf(dt_k3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('32',plain,(
    ! [X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k3_subset_1 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_subset_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( m1_subset_1 @ ( k3_subset_1 @ sk_A @ ( sk_C @ X0 @ sk_B ) ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( r1_tarski @ sk_B @ X0 ) ),
    inference(clc,[status(thm)],['30','33'])).

thf(l32_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k4_xboole_0 @ A @ B )
        = k1_xboole_0 )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('35',plain,(
    ! [X4: $i,X6: $i] :
      ( ( ( k4_xboole_0 @ X4 @ X6 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[l32_xboole_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ sk_B @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['19','36'])).

thf('38',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['16','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('42',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ sk_B ) ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('43',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    $false ),
    inference(demod,[status(thm)],['40','43'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.EXrM38cgGE
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:53:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.20/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.50  % Solved by: fo/fo7.sh
% 0.20/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.50  % done 117 iterations in 0.053s
% 0.20/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.50  % SZS output start Refutation
% 0.20/0.50  thf(k3_subset_1_type, type, k3_subset_1: $i > $i > $i).
% 0.20/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.50  thf(k7_setfam_1_type, type, k7_setfam_1: $i > $i > $i).
% 0.20/0.50  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.50  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.20/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.50  thf(t46_setfam_1, conjecture,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.50       ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50            ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.20/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.50    (~( ![A:$i,B:$i]:
% 0.20/0.50        ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.50          ( ~( ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.50               ( ( k7_setfam_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ) )),
% 0.20/0.50    inference('cnf.neg', [status(esa)], [t46_setfam_1])).
% 0.20/0.50  thf('0', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(d8_setfam_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.50       ( ![C:$i]:
% 0.20/0.50         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.50           ( ( ( C ) = ( k7_setfam_1 @ A @ B ) ) <=>
% 0.20/0.50             ( ![D:$i]:
% 0.20/0.50               ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.50                 ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.50                   ( r2_hidden @ ( k3_subset_1 @ A @ D ) @ B ) ) ) ) ) ) ) ))).
% 0.20/0.50  thf('1', plain,
% 0.20/0.50      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X21)))
% 0.20/0.50          | ((X20) != (k7_setfam_1 @ X21 @ X22))
% 0.20/0.50          | (r2_hidden @ X23 @ X20)
% 0.20/0.50          | ~ (r2_hidden @ (k3_subset_1 @ X21 @ X23) @ X22)
% 0.20/0.50          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X21))
% 0.20/0.50          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X21))))),
% 0.20/0.50      inference('cnf', [status(esa)], [d8_setfam_1])).
% 0.20/0.50  thf('2', plain,
% 0.20/0.50      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X21)))
% 0.20/0.50          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X21))
% 0.20/0.50          | ~ (r2_hidden @ (k3_subset_1 @ X21 @ X23) @ X22)
% 0.20/0.50          | (r2_hidden @ X23 @ (k7_setfam_1 @ X21 @ X22))
% 0.20/0.50          | ~ (m1_subset_1 @ (k7_setfam_1 @ X21 @ X22) @ 
% 0.20/0.50               (k1_zfmisc_1 @ (k1_zfmisc_1 @ X21))))),
% 0.20/0.50      inference('simplify', [status(thm)], ['1'])).
% 0.20/0.50  thf('3', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))
% 0.20/0.50          | (r2_hidden @ X0 @ (k7_setfam_1 @ sk_A @ sk_B))
% 0.20/0.50          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.50          | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A))))),
% 0.20/0.50      inference('sup-', [status(thm)], ['0', '2'])).
% 0.20/0.50  thf('4', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(dt_k7_setfam_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.20/0.50       ( m1_subset_1 @
% 0.20/0.50         ( k7_setfam_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.20/0.50  thf('5', plain,
% 0.20/0.50      (![X24 : $i, X25 : $i]:
% 0.20/0.50         ((m1_subset_1 @ (k7_setfam_1 @ X24 @ X25) @ 
% 0.20/0.50           (k1_zfmisc_1 @ (k1_zfmisc_1 @ X24)))
% 0.20/0.50          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X24))))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k7_setfam_1])).
% 0.20/0.50  thf('6', plain,
% 0.20/0.50      ((m1_subset_1 @ (k7_setfam_1 @ sk_A @ sk_B) @ 
% 0.20/0.50        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.50  thf('7', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('8', plain,
% 0.20/0.50      ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['6', '7'])).
% 0.20/0.50  thf('9', plain, (((k7_setfam_1 @ sk_A @ sk_B) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('10', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('11', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r2_hidden @ X0 @ k1_xboole_0)
% 0.20/0.50          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B)
% 0.20/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.50      inference('demod', [status(thm)], ['3', '8', '9', '10'])).
% 0.20/0.50  thf(t4_boole, axiom,
% 0.20/0.50    (![A:$i]: ( ( k4_xboole_0 @ k1_xboole_0 @ A ) = ( k1_xboole_0 ) ))).
% 0.20/0.50  thf('12', plain,
% 0.20/0.50      (![X9 : $i]: ((k4_xboole_0 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [t4_boole])).
% 0.20/0.50  thf(t65_zfmisc_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( k4_xboole_0 @ A @ ( k1_tarski @ B ) ) = ( A ) ) <=>
% 0.20/0.50       ( ~( r2_hidden @ B @ A ) ) ))).
% 0.20/0.50  thf('13', plain,
% 0.20/0.50      (![X13 : $i, X14 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X13 @ X14)
% 0.20/0.50          | ((k4_xboole_0 @ X14 @ (k1_tarski @ X13)) != (X14)))),
% 0.20/0.50      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.20/0.50  thf('14', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (((k1_xboole_0) != (k1_xboole_0)) | ~ (r2_hidden @ X0 @ k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.50  thf('15', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ k1_xboole_0)),
% 0.20/0.50      inference('simplify', [status(thm)], ['14'])).
% 0.20/0.50  thf('16', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.50          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B))),
% 0.20/0.50      inference('clc', [status(thm)], ['11', '15'])).
% 0.20/0.50  thf(t69_enumset1, axiom,
% 0.20/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.50  thf('17', plain,
% 0.20/0.50      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 0.20/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.50  thf('18', plain,
% 0.20/0.50      (![X14 : $i, X15 : $i]:
% 0.20/0.50         (((k4_xboole_0 @ X14 @ (k1_tarski @ X15)) = (X14))
% 0.20/0.50          | (r2_hidden @ X15 @ X14))),
% 0.20/0.50      inference('cnf', [status(esa)], [t65_zfmisc_1])).
% 0.20/0.50  thf('19', plain,
% 0.20/0.50      (![X0 : $i, X1 : $i]:
% 0.20/0.50         (((k4_xboole_0 @ X1 @ (k2_tarski @ X0 @ X0)) = (X1))
% 0.20/0.50          | (r2_hidden @ X0 @ X1))),
% 0.20/0.50      inference('sup+', [status(thm)], ['17', '18'])).
% 0.20/0.50  thf(d3_tarski, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.50  thf('20', plain,
% 0.20/0.50      (![X1 : $i, X3 : $i]:
% 0.20/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.50  thf('21', plain,
% 0.20/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf(t4_subset, axiom,
% 0.20/0.50    (![A:$i,B:$i,C:$i]:
% 0.20/0.50     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.20/0.50       ( m1_subset_1 @ A @ C ) ))).
% 0.20/0.50  thf('22', plain,
% 0.20/0.50      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.50         (~ (r2_hidden @ X26 @ X27)
% 0.20/0.50          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ X28))
% 0.20/0.50          | (m1_subset_1 @ X26 @ X28))),
% 0.20/0.50      inference('cnf', [status(esa)], [t4_subset])).
% 0.20/0.50  thf('23', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('24', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r1_tarski @ sk_B @ X0)
% 0.20/0.50          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['20', '23'])).
% 0.20/0.50  thf(involutiveness_k3_subset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.50       ( ( k3_subset_1 @ A @ ( k3_subset_1 @ A @ B ) ) = ( B ) ) ))).
% 0.20/0.50  thf('25', plain,
% 0.20/0.50      (![X18 : $i, X19 : $i]:
% 0.20/0.50         (((k3_subset_1 @ X19 @ (k3_subset_1 @ X19 @ X18)) = (X18))
% 0.20/0.50          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19)))),
% 0.20/0.50      inference('cnf', [status(esa)], [involutiveness_k3_subset_1])).
% 0.20/0.50  thf('26', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r1_tarski @ sk_B @ X0)
% 0.20/0.50          | ((k3_subset_1 @ sk_A @ (k3_subset_1 @ sk_A @ (sk_C @ X0 @ sk_B)))
% 0.20/0.50              = (sk_C @ X0 @ sk_B)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.50  thf('27', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))
% 0.20/0.50          | ~ (r2_hidden @ (k3_subset_1 @ sk_A @ X0) @ sk_B))),
% 0.20/0.50      inference('clc', [status(thm)], ['11', '15'])).
% 0.20/0.50  thf('28', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (r2_hidden @ (sk_C @ X0 @ sk_B) @ sk_B)
% 0.20/0.50          | (r1_tarski @ sk_B @ X0)
% 0.20/0.50          | ~ (m1_subset_1 @ (k3_subset_1 @ sk_A @ (sk_C @ X0 @ sk_B)) @ 
% 0.20/0.50               (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.50  thf('29', plain,
% 0.20/0.50      (![X1 : $i, X3 : $i]:
% 0.20/0.50         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.20/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.50  thf('30', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         (~ (m1_subset_1 @ (k3_subset_1 @ sk_A @ (sk_C @ X0 @ sk_B)) @ 
% 0.20/0.50             (k1_zfmisc_1 @ sk_A))
% 0.20/0.50          | (r1_tarski @ sk_B @ X0))),
% 0.20/0.50      inference('clc', [status(thm)], ['28', '29'])).
% 0.20/0.50  thf('31', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r1_tarski @ sk_B @ X0)
% 0.20/0.50          | (m1_subset_1 @ (sk_C @ X0 @ sk_B) @ (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['20', '23'])).
% 0.20/0.50  thf(dt_k3_subset_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.50       ( m1_subset_1 @ ( k3_subset_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.20/0.50  thf('32', plain,
% 0.20/0.50      (![X16 : $i, X17 : $i]:
% 0.20/0.50         ((m1_subset_1 @ (k3_subset_1 @ X16 @ X17) @ (k1_zfmisc_1 @ X16))
% 0.20/0.50          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X16)))),
% 0.20/0.50      inference('cnf', [status(esa)], [dt_k3_subset_1])).
% 0.20/0.50  thf('33', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((r1_tarski @ sk_B @ X0)
% 0.20/0.50          | (m1_subset_1 @ (k3_subset_1 @ sk_A @ (sk_C @ X0 @ sk_B)) @ 
% 0.20/0.50             (k1_zfmisc_1 @ sk_A)))),
% 0.20/0.50      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.50  thf('34', plain, (![X0 : $i]: (r1_tarski @ sk_B @ X0)),
% 0.20/0.50      inference('clc', [status(thm)], ['30', '33'])).
% 0.20/0.50  thf(l32_xboole_1, axiom,
% 0.20/0.50    (![A:$i,B:$i]:
% 0.20/0.50     ( ( ( k4_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.50  thf('35', plain,
% 0.20/0.50      (![X4 : $i, X6 : $i]:
% 0.20/0.50         (((k4_xboole_0 @ X4 @ X6) = (k1_xboole_0)) | ~ (r1_tarski @ X4 @ X6))),
% 0.20/0.50      inference('cnf', [status(esa)], [l32_xboole_1])).
% 0.20/0.50  thf('36', plain, (![X0 : $i]: ((k4_xboole_0 @ sk_B @ X0) = (k1_xboole_0))),
% 0.20/0.50      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.50  thf('37', plain,
% 0.20/0.50      (![X0 : $i]: (((sk_B) = (k1_xboole_0)) | (r2_hidden @ X0 @ sk_B))),
% 0.20/0.50      inference('sup+', [status(thm)], ['19', '36'])).
% 0.20/0.50  thf('38', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.50  thf('39', plain, (![X0 : $i]: (r2_hidden @ X0 @ sk_B)),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.20/0.50  thf('40', plain, (![X0 : $i]: ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['16', '39'])).
% 0.20/0.50  thf('41', plain,
% 0.20/0.50      (![X0 : $i]:
% 0.20/0.50         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A)) | ~ (r2_hidden @ X0 @ sk_B))),
% 0.20/0.50      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.50  thf('42', plain, (![X0 : $i]: (r2_hidden @ X0 @ sk_B)),
% 0.20/0.50      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.20/0.50  thf('43', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.50      inference('demod', [status(thm)], ['41', '42'])).
% 0.20/0.50  thf('44', plain, ($false), inference('demod', [status(thm)], ['40', '43'])).
% 0.20/0.50  
% 0.20/0.50  % SZS output end Refutation
% 0.20/0.50  
% 0.20/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
