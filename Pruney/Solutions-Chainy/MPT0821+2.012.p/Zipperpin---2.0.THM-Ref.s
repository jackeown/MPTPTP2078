%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BiLCho2kEi

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:57 EST 2020

% Result     : Theorem 0.35s
% Output     : Refutation 0.35s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 121 expanded)
%              Number of leaves         :   23 (  44 expanded)
%              Depth                    :   14
%              Number of atoms          :  585 (1368 expanded)
%              Number of equality atoms :   39 (  80 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

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
    ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
     != sk_B )
    | ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_B )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X22: $i] :
      ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
        = sk_B )
      | ( r2_hidden @ ( k4_tarski @ X22 @ ( sk_E @ X22 ) ) @ sk_C_2 )
      | ~ ( r2_hidden @ X22 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X22: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X22 @ ( sk_E @ X22 ) ) @ sk_C_2 )
        | ~ ( r2_hidden @ X22 @ sk_B ) )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('5',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X15 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('6',plain,(
    m1_subset_1 @ ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('9',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','9'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('13',plain,(
    ! [X0: $i,X2: $i] :
      ( ( r2_xboole_0 @ X0 @ X2 )
      | ( X0 = X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('14',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = sk_B )
    | ( r2_xboole_0 @ ( k1_relat_1 @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('15',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('16',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = sk_B )
    | ( r2_hidden @ ( sk_C @ sk_B @ ( k1_relat_1 @ sk_C_2 ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ! [X22: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X22 @ ( sk_E @ X22 ) ) @ sk_C_2 )
        | ~ ( r2_hidden @ X22 @ sk_B ) )
   <= ! [X22: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X22 @ ( sk_E @ X22 ) ) @ sk_C_2 )
        | ~ ( r2_hidden @ X22 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('18',plain,
    ( ( ( ( k1_relat_1 @ sk_C_2 )
        = sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ sk_B @ ( k1_relat_1 @ sk_C_2 ) ) @ ( sk_E @ ( sk_C @ sk_B @ ( k1_relat_1 @ sk_C_2 ) ) ) ) @ sk_C_2 ) )
   <= ! [X22: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X22 @ ( sk_E @ X22 ) ) @ sk_C_2 )
        | ~ ( r2_hidden @ X22 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X10 )
      | ( r2_hidden @ X8 @ X11 )
      | ( X11
       != ( k1_relat_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('20',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X8 @ ( k1_relat_1 @ X10 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ X9 ) @ X10 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,
    ( ( ( ( k1_relat_1 @ sk_C_2 )
        = sk_B )
      | ( r2_hidden @ ( sk_C @ sk_B @ ( k1_relat_1 @ sk_C_2 ) ) @ ( k1_relat_1 @ sk_C_2 ) ) )
   <= ! [X22: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X22 @ ( sk_E @ X22 ) ) @ sk_C_2 )
        | ~ ( r2_hidden @ X22 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_xboole_0 @ X3 @ X4 )
      | ~ ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('23',plain,
    ( ( ( ( k1_relat_1 @ sk_C_2 )
        = sk_B )
      | ~ ( r2_xboole_0 @ ( k1_relat_1 @ sk_C_2 ) @ sk_B ) )
   <= ! [X22: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X22 @ ( sk_E @ X22 ) ) @ sk_C_2 )
        | ~ ( r2_hidden @ X22 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = sk_B )
    | ( r2_xboole_0 @ ( k1_relat_1 @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('25',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = sk_B )
   <= ! [X22: $i] :
        ( ( r2_hidden @ ( k4_tarski @ X22 @ ( sk_E @ X22 ) ) @ sk_C_2 )
        | ~ ( r2_hidden @ X22 @ sk_B ) ) ),
    inference(clc,[status(thm)],['23','24'])).

thf('26',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('27',plain,
    ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
     != sk_B )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('28',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
     != sk_B )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
     != sk_B ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
       != sk_B )
      & ! [X22: $i] :
          ( ( r2_hidden @ ( k4_tarski @ X22 @ ( sk_E @ X22 ) ) @ sk_C_2 )
          | ~ ( r2_hidden @ X22 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf('30',plain,
    ( ~ ! [X22: $i] :
          ( ( r2_hidden @ ( k4_tarski @ X22 @ ( sk_E @ X22 ) ) @ sk_C_2 )
          | ~ ( r2_hidden @ X22 @ sk_B ) )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
      = sk_B ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X21: $i] :
      ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
       != sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X21 ) @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ! [X21: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X21 ) @ sk_C_2 )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
     != sk_B ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_B )
   <= ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('34',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('35',plain,
    ( ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
      = sk_B )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('36',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = sk_B )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
      = sk_B ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X12 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ X12 @ ( sk_D_1 @ X12 @ X10 ) ) @ X10 )
      | ( X11
       != ( k1_relat_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('38',plain,(
    ! [X10: $i,X12: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X12 @ ( sk_D_1 @ X12 @ X10 ) ) @ X10 )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X10 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( r2_hidden @ ( k4_tarski @ X0 @ ( sk_D_1 @ X0 @ sk_C_2 ) ) @ sk_C_2 ) )
   <= ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,
    ( ( r2_hidden @ ( k4_tarski @ sk_D_2 @ ( sk_D_1 @ sk_D_2 @ sk_C_2 ) ) @ sk_C_2 )
   <= ( ( r2_hidden @ sk_D_2 @ sk_B )
      & ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['33','39'])).

thf('41',plain,
    ( ! [X21: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X21 ) @ sk_C_2 )
   <= ! [X21: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X21 ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['31'])).

thf('42',plain,
    ( ~ ! [X21: $i] :
          ~ ( r2_hidden @ ( k4_tarski @ sk_D_2 @ X21 ) @ sk_C_2 )
    | ( ( k1_relset_1 @ sk_B @ sk_A @ sk_C_2 )
     != sk_B )
    | ~ ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','30','32','42'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.BiLCho2kEi
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 13:50:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.35/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.35/0.53  % Solved by: fo/fo7.sh
% 0.35/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.35/0.53  % done 76 iterations in 0.066s
% 0.35/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.35/0.53  % SZS output start Refutation
% 0.35/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.35/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.35/0.53  thf(sk_E_type, type, sk_E: $i > $i).
% 0.35/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.35/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.35/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.35/0.53  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.35/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.35/0.53  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.35/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.35/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.35/0.53  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.35/0.53  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.35/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.35/0.53  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.35/0.53  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.35/0.53  thf(t22_relset_1, conjecture,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.35/0.53       ( ( ![D:$i]:
% 0.35/0.53           ( ~( ( r2_hidden @ D @ B ) & 
% 0.35/0.53                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.35/0.53         ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ))).
% 0.35/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.35/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.35/0.53        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.35/0.53          ( ( ![D:$i]:
% 0.35/0.53              ( ~( ( r2_hidden @ D @ B ) & 
% 0.35/0.53                   ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ D @ E ) @ C ) ) ) ) ) ) <=>
% 0.35/0.53            ( ( k1_relset_1 @ B @ A @ C ) = ( B ) ) ) ) )),
% 0.35/0.53    inference('cnf.neg', [status(esa)], [t22_relset_1])).
% 0.35/0.53  thf('0', plain,
% 0.35/0.53      ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) != (sk_B))
% 0.35/0.53        | (r2_hidden @ sk_D_2 @ sk_B))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('1', plain,
% 0.35/0.53      (((r2_hidden @ sk_D_2 @ sk_B)) | 
% 0.35/0.53       ~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B)))),
% 0.35/0.53      inference('split', [status(esa)], ['0'])).
% 0.35/0.53  thf('2', plain,
% 0.35/0.53      (![X22 : $i]:
% 0.35/0.53         (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))
% 0.35/0.53          | (r2_hidden @ (k4_tarski @ X22 @ (sk_E @ X22)) @ sk_C_2)
% 0.35/0.53          | ~ (r2_hidden @ X22 @ sk_B))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('3', plain,
% 0.35/0.53      ((![X22 : $i]:
% 0.35/0.53          ((r2_hidden @ (k4_tarski @ X22 @ (sk_E @ X22)) @ sk_C_2)
% 0.35/0.53           | ~ (r2_hidden @ X22 @ sk_B))) | 
% 0.35/0.53       (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B)))),
% 0.35/0.53      inference('split', [status(esa)], ['2'])).
% 0.35/0.53  thf('4', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(dt_k1_relset_1, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.53       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.35/0.53  thf('5', plain,
% 0.35/0.53      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.35/0.53         ((m1_subset_1 @ (k1_relset_1 @ X15 @ X16 @ X17) @ (k1_zfmisc_1 @ X15))
% 0.35/0.53          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.35/0.53      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.35/0.53  thf('6', plain,
% 0.35/0.53      ((m1_subset_1 @ (k1_relset_1 @ sk_B @ sk_A @ sk_C_2) @ 
% 0.35/0.53        (k1_zfmisc_1 @ sk_B))),
% 0.35/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.35/0.53  thf('7', plain,
% 0.35/0.53      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf(redefinition_k1_relset_1, axiom,
% 0.35/0.53    (![A:$i,B:$i,C:$i]:
% 0.35/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.35/0.53       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.35/0.53  thf('8', plain,
% 0.35/0.53      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.35/0.53         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 0.35/0.53          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.35/0.53      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.35/0.53  thf('9', plain,
% 0.35/0.53      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.35/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.35/0.53  thf('10', plain,
% 0.35/0.53      ((m1_subset_1 @ (k1_relat_1 @ sk_C_2) @ (k1_zfmisc_1 @ sk_B))),
% 0.35/0.53      inference('demod', [status(thm)], ['6', '9'])).
% 0.35/0.53  thf(t3_subset, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.35/0.53  thf('11', plain,
% 0.35/0.53      (![X5 : $i, X6 : $i]:
% 0.35/0.53         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.35/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.35/0.53  thf('12', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_2) @ sk_B)),
% 0.35/0.53      inference('sup-', [status(thm)], ['10', '11'])).
% 0.35/0.53  thf(d8_xboole_0, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.35/0.53       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.35/0.53  thf('13', plain,
% 0.35/0.53      (![X0 : $i, X2 : $i]:
% 0.35/0.53         ((r2_xboole_0 @ X0 @ X2) | ((X0) = (X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.35/0.53      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.35/0.53  thf('14', plain,
% 0.35/0.53      ((((k1_relat_1 @ sk_C_2) = (sk_B))
% 0.35/0.53        | (r2_xboole_0 @ (k1_relat_1 @ sk_C_2) @ sk_B))),
% 0.35/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.35/0.53  thf(t6_xboole_0, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.35/0.53          ( ![C:$i]:
% 0.35/0.53            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 0.35/0.53  thf('15', plain,
% 0.35/0.53      (![X3 : $i, X4 : $i]:
% 0.35/0.53         (~ (r2_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.35/0.53      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.35/0.53  thf('16', plain,
% 0.35/0.53      ((((k1_relat_1 @ sk_C_2) = (sk_B))
% 0.35/0.53        | (r2_hidden @ (sk_C @ sk_B @ (k1_relat_1 @ sk_C_2)) @ sk_B))),
% 0.35/0.53      inference('sup-', [status(thm)], ['14', '15'])).
% 0.35/0.53  thf('17', plain,
% 0.35/0.53      ((![X22 : $i]:
% 0.35/0.53          ((r2_hidden @ (k4_tarski @ X22 @ (sk_E @ X22)) @ sk_C_2)
% 0.35/0.53           | ~ (r2_hidden @ X22 @ sk_B)))
% 0.35/0.53         <= ((![X22 : $i]:
% 0.35/0.53                ((r2_hidden @ (k4_tarski @ X22 @ (sk_E @ X22)) @ sk_C_2)
% 0.35/0.53                 | ~ (r2_hidden @ X22 @ sk_B))))),
% 0.35/0.53      inference('split', [status(esa)], ['2'])).
% 0.35/0.53  thf('18', plain,
% 0.35/0.53      (((((k1_relat_1 @ sk_C_2) = (sk_B))
% 0.35/0.53         | (r2_hidden @ 
% 0.35/0.53            (k4_tarski @ (sk_C @ sk_B @ (k1_relat_1 @ sk_C_2)) @ 
% 0.35/0.53             (sk_E @ (sk_C @ sk_B @ (k1_relat_1 @ sk_C_2)))) @ 
% 0.35/0.53            sk_C_2)))
% 0.35/0.53         <= ((![X22 : $i]:
% 0.35/0.53                ((r2_hidden @ (k4_tarski @ X22 @ (sk_E @ X22)) @ sk_C_2)
% 0.35/0.53                 | ~ (r2_hidden @ X22 @ sk_B))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['16', '17'])).
% 0.35/0.53  thf(d4_relat_1, axiom,
% 0.35/0.53    (![A:$i,B:$i]:
% 0.35/0.53     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.35/0.53       ( ![C:$i]:
% 0.35/0.53         ( ( r2_hidden @ C @ B ) <=>
% 0.35/0.53           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.35/0.53  thf('19', plain,
% 0.35/0.53      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.35/0.53         (~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ X10)
% 0.35/0.53          | (r2_hidden @ X8 @ X11)
% 0.35/0.53          | ((X11) != (k1_relat_1 @ X10)))),
% 0.35/0.53      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.35/0.53  thf('20', plain,
% 0.35/0.53      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.35/0.53         ((r2_hidden @ X8 @ (k1_relat_1 @ X10))
% 0.35/0.53          | ~ (r2_hidden @ (k4_tarski @ X8 @ X9) @ X10))),
% 0.35/0.53      inference('simplify', [status(thm)], ['19'])).
% 0.35/0.53  thf('21', plain,
% 0.35/0.53      (((((k1_relat_1 @ sk_C_2) = (sk_B))
% 0.35/0.53         | (r2_hidden @ (sk_C @ sk_B @ (k1_relat_1 @ sk_C_2)) @ 
% 0.35/0.53            (k1_relat_1 @ sk_C_2))))
% 0.35/0.53         <= ((![X22 : $i]:
% 0.35/0.53                ((r2_hidden @ (k4_tarski @ X22 @ (sk_E @ X22)) @ sk_C_2)
% 0.35/0.53                 | ~ (r2_hidden @ X22 @ sk_B))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['18', '20'])).
% 0.35/0.53  thf('22', plain,
% 0.35/0.53      (![X3 : $i, X4 : $i]:
% 0.35/0.53         (~ (r2_xboole_0 @ X3 @ X4) | ~ (r2_hidden @ (sk_C @ X4 @ X3) @ X3))),
% 0.35/0.53      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.35/0.53  thf('23', plain,
% 0.35/0.53      (((((k1_relat_1 @ sk_C_2) = (sk_B))
% 0.35/0.53         | ~ (r2_xboole_0 @ (k1_relat_1 @ sk_C_2) @ sk_B)))
% 0.35/0.53         <= ((![X22 : $i]:
% 0.35/0.53                ((r2_hidden @ (k4_tarski @ X22 @ (sk_E @ X22)) @ sk_C_2)
% 0.35/0.53                 | ~ (r2_hidden @ X22 @ sk_B))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['21', '22'])).
% 0.35/0.53  thf('24', plain,
% 0.35/0.53      ((((k1_relat_1 @ sk_C_2) = (sk_B))
% 0.35/0.53        | (r2_xboole_0 @ (k1_relat_1 @ sk_C_2) @ sk_B))),
% 0.35/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.35/0.53  thf('25', plain,
% 0.35/0.53      ((((k1_relat_1 @ sk_C_2) = (sk_B)))
% 0.35/0.53         <= ((![X22 : $i]:
% 0.35/0.53                ((r2_hidden @ (k4_tarski @ X22 @ (sk_E @ X22)) @ sk_C_2)
% 0.35/0.53                 | ~ (r2_hidden @ X22 @ sk_B))))),
% 0.35/0.53      inference('clc', [status(thm)], ['23', '24'])).
% 0.35/0.53  thf('26', plain,
% 0.35/0.53      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.35/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.35/0.53  thf('27', plain,
% 0.35/0.53      ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) != (sk_B)))
% 0.35/0.53         <= (~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))))),
% 0.35/0.53      inference('split', [status(esa)], ['0'])).
% 0.35/0.53  thf('28', plain,
% 0.35/0.53      ((((k1_relat_1 @ sk_C_2) != (sk_B)))
% 0.35/0.53         <= (~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['26', '27'])).
% 0.35/0.53  thf('29', plain,
% 0.35/0.53      ((((sk_B) != (sk_B)))
% 0.35/0.53         <= (~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))) & 
% 0.35/0.53             (![X22 : $i]:
% 0.35/0.53                ((r2_hidden @ (k4_tarski @ X22 @ (sk_E @ X22)) @ sk_C_2)
% 0.35/0.53                 | ~ (r2_hidden @ X22 @ sk_B))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['25', '28'])).
% 0.35/0.53  thf('30', plain,
% 0.35/0.53      (~
% 0.35/0.53       (![X22 : $i]:
% 0.35/0.53          ((r2_hidden @ (k4_tarski @ X22 @ (sk_E @ X22)) @ sk_C_2)
% 0.35/0.53           | ~ (r2_hidden @ X22 @ sk_B))) | 
% 0.35/0.53       (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B)))),
% 0.35/0.53      inference('simplify', [status(thm)], ['29'])).
% 0.35/0.53  thf('31', plain,
% 0.35/0.53      (![X21 : $i]:
% 0.35/0.53         (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) != (sk_B))
% 0.35/0.53          | ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X21) @ sk_C_2))),
% 0.35/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.35/0.53  thf('32', plain,
% 0.35/0.53      ((![X21 : $i]: ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X21) @ sk_C_2)) | 
% 0.35/0.53       ~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B)))),
% 0.35/0.53      inference('split', [status(esa)], ['31'])).
% 0.35/0.53  thf('33', plain,
% 0.35/0.53      (((r2_hidden @ sk_D_2 @ sk_B)) <= (((r2_hidden @ sk_D_2 @ sk_B)))),
% 0.35/0.53      inference('split', [status(esa)], ['0'])).
% 0.35/0.53  thf('34', plain,
% 0.35/0.53      (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.35/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.35/0.53  thf('35', plain,
% 0.35/0.53      ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B)))
% 0.35/0.53         <= ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))))),
% 0.35/0.53      inference('split', [status(esa)], ['2'])).
% 0.35/0.53  thf('36', plain,
% 0.35/0.53      ((((k1_relat_1 @ sk_C_2) = (sk_B)))
% 0.35/0.53         <= ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))))),
% 0.35/0.53      inference('sup+', [status(thm)], ['34', '35'])).
% 0.35/0.53  thf('37', plain,
% 0.35/0.53      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.35/0.53         (~ (r2_hidden @ X12 @ X11)
% 0.35/0.53          | (r2_hidden @ (k4_tarski @ X12 @ (sk_D_1 @ X12 @ X10)) @ X10)
% 0.35/0.53          | ((X11) != (k1_relat_1 @ X10)))),
% 0.35/0.53      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.35/0.53  thf('38', plain,
% 0.35/0.53      (![X10 : $i, X12 : $i]:
% 0.35/0.53         ((r2_hidden @ (k4_tarski @ X12 @ (sk_D_1 @ X12 @ X10)) @ X10)
% 0.35/0.53          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X10)))),
% 0.35/0.53      inference('simplify', [status(thm)], ['37'])).
% 0.35/0.53  thf('39', plain,
% 0.35/0.53      ((![X0 : $i]:
% 0.35/0.53          (~ (r2_hidden @ X0 @ sk_B)
% 0.35/0.53           | (r2_hidden @ (k4_tarski @ X0 @ (sk_D_1 @ X0 @ sk_C_2)) @ sk_C_2)))
% 0.35/0.53         <= ((((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['36', '38'])).
% 0.35/0.53  thf('40', plain,
% 0.35/0.53      (((r2_hidden @ (k4_tarski @ sk_D_2 @ (sk_D_1 @ sk_D_2 @ sk_C_2)) @ sk_C_2))
% 0.35/0.53         <= (((r2_hidden @ sk_D_2 @ sk_B)) & 
% 0.35/0.53             (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))))),
% 0.35/0.53      inference('sup-', [status(thm)], ['33', '39'])).
% 0.35/0.53  thf('41', plain,
% 0.35/0.53      ((![X21 : $i]: ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X21) @ sk_C_2))
% 0.35/0.53         <= ((![X21 : $i]: ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X21) @ sk_C_2)))),
% 0.35/0.53      inference('split', [status(esa)], ['31'])).
% 0.35/0.53  thf('42', plain,
% 0.35/0.53      (~ (![X21 : $i]: ~ (r2_hidden @ (k4_tarski @ sk_D_2 @ X21) @ sk_C_2)) | 
% 0.35/0.53       ~ (((k1_relset_1 @ sk_B @ sk_A @ sk_C_2) = (sk_B))) | 
% 0.35/0.53       ~ ((r2_hidden @ sk_D_2 @ sk_B))),
% 0.35/0.53      inference('sup-', [status(thm)], ['40', '41'])).
% 0.35/0.53  thf('43', plain, ($false),
% 0.35/0.53      inference('sat_resolution*', [status(thm)], ['1', '3', '30', '32', '42'])).
% 0.35/0.53  
% 0.35/0.53  % SZS output end Refutation
% 0.35/0.53  
% 0.38/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
