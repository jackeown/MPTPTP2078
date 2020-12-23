%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZyQ4PLPA8g

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:57 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 124 expanded)
%              Number of leaves         :   20 (  43 expanded)
%              Depth                    :   14
%              Number of atoms          :  607 (1488 expanded)
%              Number of equality atoms :   41 (  88 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t22_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) )
      <=> ( ( k1_relset_1 @ B @ A @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
       => ( ! [D: $i] :
              ~ ( ( r2_hidden @ D @ B )
                & ! [E: $i] :
                    ~ ( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) )
        <=> ( ( k1_relset_1 @ B @ A @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t22_relset_1])).

thf('0',plain,
    ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
     != sk_B )
    | ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_B )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X17: $i] :
      ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
        = sk_B )
      | ( r2_hidden @ ( k4_tarski @ X17 @ ( sk_E @ X17 ) ) @ sk_C_1 )
      | ~ ( r2_hidden @ X17 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X17: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X17 @ ( sk_E @ X17 ) ) @ sk_C_1 )
        | ~ ( r2_hidden @ X17 @ sk_B ) )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X8: $i] :
      ( ( X8
        = ( k1_relat_1 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X8 @ X5 ) @ ( sk_D @ X8 @ X5 ) ) @ X5 )
      | ( r2_hidden @ ( sk_C @ X8 @ X5 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('5',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X5 )
      | ( r2_hidden @ X3 @ X6 )
      | ( X6
       != ( k1_relat_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('6',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X3 @ ( k1_relat_1 @ X5 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X3 @ X4 ) @ X5 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('9',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X10 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('10',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('13',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['10','13'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','16'])).

thf('18',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(eq_fact,[status(thm)],['17'])).

thf('19',plain,
    ( ! [X17: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X17 @ ( sk_E @ X17 ) ) @ sk_C_1 )
        | ~ ( r2_hidden @ X17 @ sk_B ) )
   <= ! [X17: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X17 @ ( sk_E @ X17 ) ) @ sk_C_1 )
        | ~ ( r2_hidden @ X17 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('20',plain,
    ( ( ( sk_B
        = ( k1_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B @ sk_C_1 ) @ ( sk_E @ ( sk_C @ sk_B @ sk_C_1 ) ) ) @ sk_C_1 ) )
   <= ! [X17: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X17 @ ( sk_E @ X17 ) ) @ sk_C_1 )
        | ~ ( r2_hidden @ X17 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X5: $i,X8: $i,X9: $i] :
      ( ( X8
        = ( k1_relat_1 @ X5 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X8 @ X5 ) @ X9 ) @ X5 )
      | ~ ( r2_hidden @ ( sk_C @ X8 @ X5 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('22',plain,
    ( ( ( sk_B
        = ( k1_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B )
      | ( sk_B
        = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ! [X17: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X17 @ ( sk_E @ X17 ) ) @ sk_C_1 )
        | ~ ( r2_hidden @ X17 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B )
      | ( sk_B
        = ( k1_relat_1 @ sk_C_1 ) ) )
   <= ! [X17: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X17 @ ( sk_E @ X17 ) ) @ sk_C_1 )
        | ~ ( r2_hidden @ X17 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(eq_fact,[status(thm)],['17'])).

thf('25',plain,
    ( ( sk_B
      = ( k1_relat_1 @ sk_C_1 ) )
   <= ! [X17: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X17 @ ( sk_E @ X17 ) ) @ sk_C_1 )
        | ~ ( r2_hidden @ X17 @ sk_B ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('27',plain,
    ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
     != sk_B )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
     != sk_B )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
     != sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
       != sk_B )
      & ! [X17: $i] :
          ( ( r2_hidden @ ( k4_tarski @ X17 @ ( sk_E @ X17 ) ) @ sk_C_1 )
          | ~ ( r2_hidden @ X17 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,
    ( ~ ! [X17: $i] :
          ( ( r2_hidden @ ( k4_tarski @ X17 @ ( sk_E @ X17 ) ) @ sk_C_1 )
          | ~ ( r2_hidden @ X17 @ sk_B ) )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
      = sk_B ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X16: $i] :
      ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
       != sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X16 ) @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ! [X16: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X16 ) @ sk_C_1 )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
     != sk_B ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_B )
   <= ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('35',plain,
    ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
      = sk_B )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('36',plain,
    ( ( ( k1_relat_1 @ sk_C_1 )
      = sk_B )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
      = sk_B ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X7 @ X6 )
      | ( r2_hidden @ ( k4_tarski @ X7 @ ( sk_D_1 @ X7 @ X5 ) ) @ X5 )
      | ( X6
       != ( k1_relat_1 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('38',plain,(
    ! [X5: $i,X7: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X7 @ ( sk_D_1 @ X7 @ X5 ) ) @ X5 )
      | ~ ( r2_hidden @ X7 @ ( k1_relat_1 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_1 @ X0 @ sk_C_1 ) ) @ sk_C_1 ) )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) ) @ sk_C_1 )
   <= ( ( r2_hidden @ sk_D_2 @ sk_B )
      & ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,
    ( ! [X16: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X16 ) @ sk_C_1 )
   <= ! [X16: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X16 ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['31'])).

thf('42',plain,
    ( ~ ! [X16: $i] :
          ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X16 ) @ sk_C_1 )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_1 )
     != sk_B )
    | ~ ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','30','32','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZyQ4PLPA8g
% 0.12/0.32  % Computer   : n004.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 09:55:24 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running portfolio for 600 s
% 0.12/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.33  % Python version: Python 3.6.8
% 0.12/0.33  % Running in FO mode
% 0.19/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.55  % Solved by: fo/fo7.sh
% 0.19/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.55  % done 76 iterations in 0.120s
% 0.19/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.55  % SZS output start Refutation
% 0.19/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.55  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.19/0.55  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.19/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.55  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.19/0.55  thf(sk_E_type, type, sk_E: $i > $i).
% 0.19/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.19/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.55  thf(t22_relset_1, conjecture,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.19/0.55       ( ( ![D:$i]:
% 0.19/0.55           ( ~( ( r2_hidden @ D @ B ) & 
% 0.19/0.55                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.19/0.55         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 0.19/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.55    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.55        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.19/0.55          ( ( ![D:$i]:
% 0.19/0.55              ( ~( ( r2_hidden @ D @ B ) & 
% 0.19/0.55                   ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.19/0.55            ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ) )),
% 0.19/0.55    inference('cnf.neg', [status(esa)], [t22_relset_1])).
% 0.19/0.55  thf('0', plain,
% 0.19/0.55      ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) != (sk_B))
% 0.19/0.55        | (r2_hidden @ sk_D_2 @ sk_B))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('1', plain,
% 0.19/0.55      (((r2_hidden @ sk_D_2 @ sk_B)) | 
% 0.19/0.55       ~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (sk_B)))),
% 0.19/0.55      inference('split', [status(esa)], ['0'])).
% 0.19/0.55  thf('2', plain,
% 0.19/0.55      (![X17 : $i]:
% 0.19/0.55         (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (sk_B))
% 0.19/0.55          | (r2_hidden @ (k4_tarski @ X17 @ (sk_E @ X17)) @ sk_C_1)
% 0.19/0.55          | ~ (r2_hidden @ X17 @ sk_B))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('3', plain,
% 0.19/0.55      ((![X17 : $i]:
% 0.19/0.55          ((r2_hidden @ (k4_tarski @ X17 @ (sk_E @ X17)) @ sk_C_1)
% 0.19/0.55           | ~ (r2_hidden @ X17 @ sk_B))) | 
% 0.19/0.55       (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (sk_B)))),
% 0.19/0.55      inference('split', [status(esa)], ['2'])).
% 0.19/0.55  thf(d4_relat_1, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.19/0.55       ( ![C:$i]:
% 0.19/0.55         ( ( r2_hidden @ C @ B ) <=>
% 0.19/0.55           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.19/0.55  thf('4', plain,
% 0.19/0.55      (![X5 : $i, X8 : $i]:
% 0.19/0.55         (((X8) = (k1_relat_1 @ X5))
% 0.19/0.55          | (r2_hidden @ (k4_tarski @ (sk_C @ X8 @ X5) @ (sk_D @ X8 @ X5)) @ X5)
% 0.19/0.55          | (r2_hidden @ (sk_C @ X8 @ X5) @ X8))),
% 0.19/0.55      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.19/0.55  thf('5', plain,
% 0.19/0.55      (![X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.55         (~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X5)
% 0.19/0.55          | (r2_hidden @ X3 @ X6)
% 0.19/0.55          | ((X6) != (k1_relat_1 @ X5)))),
% 0.19/0.55      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.19/0.55  thf('6', plain,
% 0.19/0.55      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.55         ((r2_hidden @ X3 @ (k1_relat_1 @ X5))
% 0.19/0.55          | ~ (r2_hidden @ (k4_tarski @ X3 @ X4) @ X5))),
% 0.19/0.55      inference('simplify', [status(thm)], ['5'])).
% 0.19/0.55  thf('7', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.19/0.55          | ((X1) = (k1_relat_1 @ X0))
% 0.19/0.55          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['4', '6'])).
% 0.19/0.55  thf('8', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(dt_k1_relset_1, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.55       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.55  thf('9', plain,
% 0.19/0.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.19/0.55         ((m1_subset_1 @ (k1_relset_1 @ X10 @ X11 @ X12) @ (k1_zfmisc_1 @ X10))
% 0.19/0.55          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.19/0.55      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.19/0.55  thf('10', plain,
% 0.19/0.55      ((m1_subset_1 @ (k1_relset_1 @ sk_B @ sk_A @ sk_C_1) @ 
% 0.19/0.55        (k1_zfmisc_1 @ sk_B))),
% 0.19/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.55  thf('11', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(redefinition_k1_relset_1, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.55       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.19/0.55  thf('12', plain,
% 0.19/0.55      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.19/0.55         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 0.19/0.55          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.19/0.55      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.19/0.55  thf('13', plain,
% 0.19/0.55      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.19/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.55  thf('14', plain,
% 0.19/0.55      ((m1_subset_1 @ (k1_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B))),
% 0.19/0.55      inference('demod', [status(thm)], ['10', '13'])).
% 0.19/0.55  thf(l3_subset_1, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.19/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.19/0.55  thf('15', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.55         (~ (r2_hidden @ X0 @ X1)
% 0.19/0.55          | (r2_hidden @ X0 @ X2)
% 0.19/0.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.19/0.55      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.19/0.55  thf('16', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.55  thf('17', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (((X0) = (k1_relat_1 @ sk_C_1))
% 0.19/0.55          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0)
% 0.19/0.55          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_B))),
% 0.19/0.55      inference('sup-', [status(thm)], ['7', '16'])).
% 0.19/0.55  thf('18', plain,
% 0.19/0.55      (((r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)
% 0.19/0.55        | ((sk_B) = (k1_relat_1 @ sk_C_1)))),
% 0.19/0.55      inference('eq_fact', [status(thm)], ['17'])).
% 0.19/0.55  thf('19', plain,
% 0.19/0.55      ((![X17 : $i]:
% 0.19/0.55          ((r2_hidden @ (k4_tarski @ X17 @ (sk_E @ X17)) @ sk_C_1)
% 0.19/0.55           | ~ (r2_hidden @ X17 @ sk_B)))
% 0.19/0.55         <= ((![X17 : $i]:
% 0.19/0.55                ((r2_hidden @ (k4_tarski @ X17 @ (sk_E @ X17)) @ sk_C_1)
% 0.19/0.55                 | ~ (r2_hidden @ X17 @ sk_B))))),
% 0.19/0.55      inference('split', [status(esa)], ['2'])).
% 0.19/0.55  thf('20', plain,
% 0.19/0.55      (((((sk_B) = (k1_relat_1 @ sk_C_1))
% 0.19/0.55         | (r2_hidden @ 
% 0.19/0.55            (k4_tarski @ (sk_C @ sk_B @ sk_C_1) @ 
% 0.19/0.55             (sk_E @ (sk_C @ sk_B @ sk_C_1))) @ 
% 0.19/0.55            sk_C_1)))
% 0.19/0.55         <= ((![X17 : $i]:
% 0.19/0.55                ((r2_hidden @ (k4_tarski @ X17 @ (sk_E @ X17)) @ sk_C_1)
% 0.19/0.55                 | ~ (r2_hidden @ X17 @ sk_B))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['18', '19'])).
% 0.19/0.55  thf('21', plain,
% 0.19/0.55      (![X5 : $i, X8 : $i, X9 : $i]:
% 0.19/0.55         (((X8) = (k1_relat_1 @ X5))
% 0.19/0.55          | ~ (r2_hidden @ (k4_tarski @ (sk_C @ X8 @ X5) @ X9) @ X5)
% 0.19/0.55          | ~ (r2_hidden @ (sk_C @ X8 @ X5) @ X8))),
% 0.19/0.55      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.19/0.55  thf('22', plain,
% 0.19/0.55      (((((sk_B) = (k1_relat_1 @ sk_C_1))
% 0.19/0.55         | ~ (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)
% 0.19/0.55         | ((sk_B) = (k1_relat_1 @ sk_C_1))))
% 0.19/0.55         <= ((![X17 : $i]:
% 0.19/0.55                ((r2_hidden @ (k4_tarski @ X17 @ (sk_E @ X17)) @ sk_C_1)
% 0.19/0.55                 | ~ (r2_hidden @ X17 @ sk_B))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.55  thf('23', plain,
% 0.19/0.55      (((~ (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)
% 0.19/0.55         | ((sk_B) = (k1_relat_1 @ sk_C_1))))
% 0.19/0.55         <= ((![X17 : $i]:
% 0.19/0.55                ((r2_hidden @ (k4_tarski @ X17 @ (sk_E @ X17)) @ sk_C_1)
% 0.19/0.55                 | ~ (r2_hidden @ X17 @ sk_B))))),
% 0.19/0.55      inference('simplify', [status(thm)], ['22'])).
% 0.19/0.55  thf('24', plain,
% 0.19/0.55      (((r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)
% 0.19/0.55        | ((sk_B) = (k1_relat_1 @ sk_C_1)))),
% 0.19/0.55      inference('eq_fact', [status(thm)], ['17'])).
% 0.19/0.55  thf('25', plain,
% 0.19/0.55      ((((sk_B) = (k1_relat_1 @ sk_C_1)))
% 0.19/0.55         <= ((![X17 : $i]:
% 0.19/0.55                ((r2_hidden @ (k4_tarski @ X17 @ (sk_E @ X17)) @ sk_C_1)
% 0.19/0.55                 | ~ (r2_hidden @ X17 @ sk_B))))),
% 0.19/0.55      inference('clc', [status(thm)], ['23', '24'])).
% 0.19/0.55  thf('26', plain,
% 0.19/0.55      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.19/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.55  thf('27', plain,
% 0.19/0.55      ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) != (sk_B)))
% 0.19/0.55         <= (~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (sk_B))))),
% 0.19/0.55      inference('split', [status(esa)], ['0'])).
% 0.19/0.55  thf('28', plain,
% 0.19/0.55      ((((k1_relat_1 @ sk_C_1) != (sk_B)))
% 0.19/0.55         <= (~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (sk_B))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.19/0.55  thf('29', plain,
% 0.19/0.55      ((((sk_B) != (sk_B)))
% 0.19/0.55         <= (~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (sk_B))) & 
% 0.19/0.55             (![X17 : $i]:
% 0.19/0.55                ((r2_hidden @ (k4_tarski @ X17 @ (sk_E @ X17)) @ sk_C_1)
% 0.19/0.55                 | ~ (r2_hidden @ X17 @ sk_B))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['25', '28'])).
% 0.19/0.55  thf('30', plain,
% 0.19/0.55      (~
% 0.19/0.55       (![X17 : $i]:
% 0.19/0.55          ((r2_hidden @ (k4_tarski @ X17 @ (sk_E @ X17)) @ sk_C_1)
% 0.19/0.55           | ~ (r2_hidden @ X17 @ sk_B))) | 
% 0.19/0.55       (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (sk_B)))),
% 0.19/0.55      inference('simplify', [status(thm)], ['29'])).
% 0.19/0.55  thf('31', plain,
% 0.19/0.55      (![X16 : $i]:
% 0.19/0.55         (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) != (sk_B))
% 0.19/0.55          | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X16) @ sk_C_1))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('32', plain,
% 0.19/0.55      ((![X16 : $i]: ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X16) @ sk_C_1)) | 
% 0.19/0.55       ~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (sk_B)))),
% 0.19/0.55      inference('split', [status(esa)], ['31'])).
% 0.19/0.55  thf('33', plain,
% 0.19/0.55      (((r2_hidden @ sk_D_2 @ sk_B)) <= (((r2_hidden @ sk_D_2 @ sk_B)))),
% 0.19/0.55      inference('split', [status(esa)], ['0'])).
% 0.19/0.55  thf('34', plain,
% 0.19/0.55      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.19/0.55      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.55  thf('35', plain,
% 0.19/0.55      ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (sk_B)))
% 0.19/0.55         <= ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (sk_B))))),
% 0.19/0.55      inference('split', [status(esa)], ['2'])).
% 0.19/0.55  thf('36', plain,
% 0.19/0.55      ((((k1_relat_1 @ sk_C_1) = (sk_B)))
% 0.19/0.55         <= ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (sk_B))))),
% 0.19/0.55      inference('sup+', [status(thm)], ['34', '35'])).
% 0.19/0.55  thf('37', plain,
% 0.19/0.55      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.19/0.55         (~ (r2_hidden @ X7 @ X6)
% 0.19/0.55          | (r2_hidden @ (k4_tarski @ X7 @ (sk_D_1 @ X7 @ X5)) @ X5)
% 0.19/0.55          | ((X6) != (k1_relat_1 @ X5)))),
% 0.19/0.55      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.19/0.55  thf('38', plain,
% 0.19/0.55      (![X5 : $i, X7 : $i]:
% 0.19/0.55         ((r2_hidden @ (k4_tarski @ X7 @ (sk_D_1 @ X7 @ X5)) @ X5)
% 0.19/0.55          | ~ (r2_hidden @ X7 @ (k1_relat_1 @ X5)))),
% 0.19/0.55      inference('simplify', [status(thm)], ['37'])).
% 0.19/0.55  thf('39', plain,
% 0.19/0.55      ((![X0 : $i]:
% 0.19/0.55          (~ (r2_hidden @ X0 @ sk_B)
% 0.19/0.55           | (r2_hidden @ (k4_tarski @ X0 @ (sk_D_1 @ X0 @ sk_C_1)) @ sk_C_1)))
% 0.19/0.55         <= ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (sk_B))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['36', '38'])).
% 0.19/0.55  thf('40', plain,
% 0.19/0.55      (((r2_hidden @ (k4_tarski @ sk_D_2 @ (sk_D_1 @ sk_D_2 @ sk_C_1)) @ sk_C_1))
% 0.19/0.55         <= (((r2_hidden @ sk_D_2 @ sk_B)) & 
% 0.19/0.55             (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (sk_B))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['33', '39'])).
% 0.19/0.55  thf('41', plain,
% 0.19/0.55      ((![X16 : $i]: ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X16) @ sk_C_1))
% 0.19/0.55         <= ((![X16 : $i]: ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X16) @ sk_C_1)))),
% 0.19/0.55      inference('split', [status(esa)], ['31'])).
% 0.19/0.55  thf('42', plain,
% 0.19/0.55      (~ (![X16 : $i]: ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X16) @ sk_C_1)) | 
% 0.19/0.55       ~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_1) = (sk_B))) | 
% 0.19/0.55       ~ ((r2_hidden @ sk_D_2 @ sk_B))),
% 0.19/0.55      inference('sup-', [status(thm)], ['40', '41'])).
% 0.19/0.55  thf('43', plain, ($false),
% 0.19/0.55      inference('sat_resolution*', [status(thm)], ['1', '3', '30', '32', '42'])).
% 0.19/0.55  
% 0.19/0.55  % SZS output end Refutation
% 0.19/0.55  
% 0.19/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
