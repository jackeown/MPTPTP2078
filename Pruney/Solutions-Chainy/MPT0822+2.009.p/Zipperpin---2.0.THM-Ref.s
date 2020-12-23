%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sSjKK1F3yg

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:59 EST 2020

% Result     : Theorem 1.06s
% Output     : Refutation 1.06s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 101 expanded)
%              Number of leaves         :   22 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :  584 (1168 expanded)
%              Number of equality atoms :   34 (  66 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(t23_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) )
      <=> ( ( k2_relset_1 @ A @ B @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
       => ( ! [D: $i] :
              ~ ( ( r2_hidden @ D @ B )
                & ! [E: $i] :
                    ~ ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) )
        <=> ( ( k2_relset_1 @ A @ B @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_relset_1])).

thf('0',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B )
    | ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X24: $i] :
      ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
        = sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_2 )
      | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X24 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X17 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('6',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X22 @ X20 )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('9',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['6','9'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,
    ( ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X24 @ sk_B ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('15',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( k4_tarski @ ( sk_E @ ( sk_C @ X0 @ sk_B ) ) @ ( sk_C @ X0 @ sk_B ) ) @ sk_C_2 ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 )
      | ( r2_hidden @ X11 @ X13 )
      | ( X13
       != ( k2_relat_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('17',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X11 @ ( k2_relat_1 @ X12 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X11 ) @ X12 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,
    ( ! [X0: $i] :
        ( ( r1_tarski @ sk_B @ X0 )
        | ( r2_hidden @ ( sk_C @ X0 @ sk_B ) @ ( k2_relat_1 @ sk_C_2 ) ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('20',plain,
    ( ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) )
      | ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r1_tarski @ sk_B @ ( k2_relat_1 @ sk_C_2 ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('22',plain,(
    ! [X4: $i,X6: $i] :
      ( ( X4 = X6 )
      | ~ ( r1_tarski @ X6 @ X4 )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('23',plain,
    ( ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B )
      | ( ( k2_relat_1 @ sk_C_2 )
        = sk_B ) )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
      = sk_B )
   <= ! [X24: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_2 )
        | ~ ( r2_hidden @ X24 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['12','23'])).

thf('25',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('26',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('27',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
     != sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
       != sk_B )
      & ! [X24: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_2 )
          | ~ ( r2_hidden @ X24 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,
    ( ~ ! [X24: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X24 ) @ X24 ) @ sk_C_2 )
          | ~ ( r2_hidden @ X24 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X23: $i] :
      ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
       != sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ X23 @ sk_D_2 ) @ sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ! [X23: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ X23 @ sk_D_2 ) @ sk_C_2 )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B ) ),
    inference(split,[status(esa)],['30'])).

thf('32',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_B )
   <= ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('34',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('35',plain,
    ( ( ( k2_relat_1 @ sk_C_2 )
      = sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X14 @ X12 ) @ X14 ) @ X12 )
      | ( X13
       != ( k2_relat_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('37',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X14 @ X12 ) @ X14 ) @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k2_relat_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X0 @ sk_C_2 ) @ X0 ) @ sk_C_2 ) )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['35','37'])).

thf('39',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_C_2 ) @ sk_D_2 ) @ sk_C_2 )
   <= ( ( r2_hidden @ sk_D_2 @ sk_B )
      & ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,
    ( ! [X23: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ X23 @ sk_D_2 ) @ sk_C_2 )
   <= ! [X23: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ X23 @ sk_D_2 ) @ sk_C_2 ) ),
    inference(split,[status(esa)],['30'])).

thf('41',plain,
    ( ~ ! [X23: $i] :
          ~ ( r2_hidden @ ( k4_tarski @ X23 @ sk_D_2 ) @ sk_C_2 )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
     != sk_B )
    | ~ ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','29','31','41'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sSjKK1F3yg
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:56:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.06/1.28  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.06/1.28  % Solved by: fo/fo7.sh
% 1.06/1.28  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.06/1.28  % done 102 iterations in 0.863s
% 1.06/1.28  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.06/1.28  % SZS output start Refutation
% 1.06/1.28  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.06/1.28  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.06/1.28  thf(sk_A_type, type, sk_A: $i).
% 1.06/1.28  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.06/1.28  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 1.06/1.28  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.06/1.28  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.06/1.28  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 1.06/1.28  thf(sk_D_2_type, type, sk_D_2: $i).
% 1.06/1.28  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.06/1.28  thf(sk_B_type, type, sk_B: $i).
% 1.06/1.28  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.06/1.28  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.06/1.28  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.06/1.28  thf(sk_E_type, type, sk_E: $i > $i).
% 1.06/1.28  thf(t23_relset_1, conjecture,
% 1.06/1.28    (![A:$i,B:$i,C:$i]:
% 1.06/1.28     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.06/1.28       ( ( ![D:$i]:
% 1.06/1.28           ( ~( ( r2_hidden @ D @ B ) & 
% 1.06/1.28                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) ) ) ) ) ) <=>
% 1.06/1.28         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 1.06/1.28  thf(zf_stmt_0, negated_conjecture,
% 1.06/1.28    (~( ![A:$i,B:$i,C:$i]:
% 1.06/1.28        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.06/1.28          ( ( ![D:$i]:
% 1.06/1.28              ( ~( ( r2_hidden @ D @ B ) & 
% 1.06/1.28                   ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) ) ) ) ) ) <=>
% 1.06/1.28            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 1.06/1.28    inference('cnf.neg', [status(esa)], [t23_relset_1])).
% 1.06/1.28  thf('0', plain,
% 1.06/1.28      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B))
% 1.06/1.28        | (r2_hidden @ sk_D_2 @ sk_B))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('1', plain,
% 1.06/1.28      (((r2_hidden @ sk_D_2 @ sk_B)) | 
% 1.06/1.28       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B)))),
% 1.06/1.28      inference('split', [status(esa)], ['0'])).
% 1.06/1.28  thf('2', plain,
% 1.06/1.28      (![X24 : $i]:
% 1.06/1.28         (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))
% 1.06/1.28          | (r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_2)
% 1.06/1.28          | ~ (r2_hidden @ X24 @ sk_B))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('3', plain,
% 1.06/1.28      ((![X24 : $i]:
% 1.06/1.28          ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_2)
% 1.06/1.28           | ~ (r2_hidden @ X24 @ sk_B))) | 
% 1.06/1.28       (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B)))),
% 1.06/1.28      inference('split', [status(esa)], ['2'])).
% 1.06/1.28  thf('4', plain,
% 1.06/1.28      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf(dt_k2_relset_1, axiom,
% 1.06/1.28    (![A:$i,B:$i,C:$i]:
% 1.06/1.28     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.06/1.28       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.06/1.28  thf('5', plain,
% 1.06/1.28      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.06/1.28         ((m1_subset_1 @ (k2_relset_1 @ X17 @ X18 @ X19) @ (k1_zfmisc_1 @ X18))
% 1.06/1.28          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.06/1.28      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 1.06/1.28  thf('6', plain,
% 1.06/1.28      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C_2) @ 
% 1.06/1.28        (k1_zfmisc_1 @ sk_B))),
% 1.06/1.28      inference('sup-', [status(thm)], ['4', '5'])).
% 1.06/1.28  thf('7', plain,
% 1.06/1.28      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf(redefinition_k2_relset_1, axiom,
% 1.06/1.28    (![A:$i,B:$i,C:$i]:
% 1.06/1.28     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.06/1.28       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.06/1.28  thf('8', plain,
% 1.06/1.28      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.06/1.28         (((k2_relset_1 @ X21 @ X22 @ X20) = (k2_relat_1 @ X20))
% 1.06/1.28          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.06/1.28      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.06/1.28  thf('9', plain,
% 1.06/1.28      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 1.06/1.28      inference('sup-', [status(thm)], ['7', '8'])).
% 1.06/1.28  thf('10', plain,
% 1.06/1.28      ((m1_subset_1 @ (k2_relat_1 @ sk_C_2) @ (k1_zfmisc_1 @ sk_B))),
% 1.06/1.28      inference('demod', [status(thm)], ['6', '9'])).
% 1.06/1.28  thf(t3_subset, axiom,
% 1.06/1.28    (![A:$i,B:$i]:
% 1.06/1.28     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.06/1.28  thf('11', plain,
% 1.06/1.28      (![X7 : $i, X8 : $i]:
% 1.06/1.28         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 1.06/1.28      inference('cnf', [status(esa)], [t3_subset])).
% 1.06/1.28  thf('12', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 1.06/1.28      inference('sup-', [status(thm)], ['10', '11'])).
% 1.06/1.28  thf(d3_tarski, axiom,
% 1.06/1.28    (![A:$i,B:$i]:
% 1.06/1.28     ( ( r1_tarski @ A @ B ) <=>
% 1.06/1.28       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 1.06/1.28  thf('13', plain,
% 1.06/1.28      (![X1 : $i, X3 : $i]:
% 1.06/1.28         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 1.06/1.28      inference('cnf', [status(esa)], [d3_tarski])).
% 1.06/1.28  thf('14', plain,
% 1.06/1.28      ((![X24 : $i]:
% 1.06/1.28          ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_2)
% 1.06/1.28           | ~ (r2_hidden @ X24 @ sk_B)))
% 1.06/1.28         <= ((![X24 : $i]:
% 1.06/1.28                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_2)
% 1.06/1.28                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 1.06/1.28      inference('split', [status(esa)], ['2'])).
% 1.06/1.28  thf('15', plain,
% 1.06/1.28      ((![X0 : $i]:
% 1.06/1.28          ((r1_tarski @ sk_B @ X0)
% 1.06/1.28           | (r2_hidden @ 
% 1.06/1.28              (k4_tarski @ (sk_E @ (sk_C @ X0 @ sk_B)) @ (sk_C @ X0 @ sk_B)) @ 
% 1.06/1.28              sk_C_2)))
% 1.06/1.28         <= ((![X24 : $i]:
% 1.06/1.28                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_2)
% 1.06/1.28                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 1.06/1.28      inference('sup-', [status(thm)], ['13', '14'])).
% 1.06/1.28  thf(d5_relat_1, axiom,
% 1.06/1.28    (![A:$i,B:$i]:
% 1.06/1.28     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 1.06/1.28       ( ![C:$i]:
% 1.06/1.28         ( ( r2_hidden @ C @ B ) <=>
% 1.06/1.28           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 1.06/1.28  thf('16', plain,
% 1.06/1.28      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 1.06/1.28         (~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12)
% 1.06/1.28          | (r2_hidden @ X11 @ X13)
% 1.06/1.28          | ((X13) != (k2_relat_1 @ X12)))),
% 1.06/1.28      inference('cnf', [status(esa)], [d5_relat_1])).
% 1.06/1.28  thf('17', plain,
% 1.06/1.28      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.06/1.28         ((r2_hidden @ X11 @ (k2_relat_1 @ X12))
% 1.06/1.28          | ~ (r2_hidden @ (k4_tarski @ X10 @ X11) @ X12))),
% 1.06/1.28      inference('simplify', [status(thm)], ['16'])).
% 1.06/1.28  thf('18', plain,
% 1.06/1.28      ((![X0 : $i]:
% 1.06/1.28          ((r1_tarski @ sk_B @ X0)
% 1.06/1.28           | (r2_hidden @ (sk_C @ X0 @ sk_B) @ (k2_relat_1 @ sk_C_2))))
% 1.06/1.28         <= ((![X24 : $i]:
% 1.06/1.28                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_2)
% 1.06/1.28                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 1.06/1.28      inference('sup-', [status(thm)], ['15', '17'])).
% 1.06/1.28  thf('19', plain,
% 1.06/1.28      (![X1 : $i, X3 : $i]:
% 1.06/1.28         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 1.06/1.28      inference('cnf', [status(esa)], [d3_tarski])).
% 1.06/1.28  thf('20', plain,
% 1.06/1.28      ((((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))
% 1.06/1.28         | (r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2))))
% 1.06/1.28         <= ((![X24 : $i]:
% 1.06/1.28                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_2)
% 1.06/1.28                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 1.06/1.28      inference('sup-', [status(thm)], ['18', '19'])).
% 1.06/1.28  thf('21', plain,
% 1.06/1.28      (((r1_tarski @ sk_B @ (k2_relat_1 @ sk_C_2)))
% 1.06/1.28         <= ((![X24 : $i]:
% 1.06/1.28                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_2)
% 1.06/1.28                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 1.06/1.28      inference('simplify', [status(thm)], ['20'])).
% 1.06/1.28  thf(d10_xboole_0, axiom,
% 1.06/1.28    (![A:$i,B:$i]:
% 1.06/1.28     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.06/1.28  thf('22', plain,
% 1.06/1.28      (![X4 : $i, X6 : $i]:
% 1.06/1.28         (((X4) = (X6)) | ~ (r1_tarski @ X6 @ X4) | ~ (r1_tarski @ X4 @ X6))),
% 1.06/1.28      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.06/1.28  thf('23', plain,
% 1.06/1.28      (((~ (r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)
% 1.06/1.28         | ((k2_relat_1 @ sk_C_2) = (sk_B))))
% 1.06/1.28         <= ((![X24 : $i]:
% 1.06/1.28                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_2)
% 1.06/1.28                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 1.06/1.28      inference('sup-', [status(thm)], ['21', '22'])).
% 1.06/1.28  thf('24', plain,
% 1.06/1.28      ((((k2_relat_1 @ sk_C_2) = (sk_B)))
% 1.06/1.28         <= ((![X24 : $i]:
% 1.06/1.28                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_2)
% 1.06/1.28                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 1.06/1.28      inference('sup-', [status(thm)], ['12', '23'])).
% 1.06/1.28  thf('25', plain,
% 1.06/1.28      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 1.06/1.28      inference('sup-', [status(thm)], ['7', '8'])).
% 1.06/1.28  thf('26', plain,
% 1.06/1.28      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B)))
% 1.06/1.28         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 1.06/1.28      inference('split', [status(esa)], ['0'])).
% 1.06/1.28  thf('27', plain,
% 1.06/1.28      ((((k2_relat_1 @ sk_C_2) != (sk_B)))
% 1.06/1.28         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 1.06/1.28      inference('sup-', [status(thm)], ['25', '26'])).
% 1.06/1.28  thf('28', plain,
% 1.06/1.28      ((((sk_B) != (sk_B)))
% 1.06/1.28         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))) & 
% 1.06/1.28             (![X24 : $i]:
% 1.06/1.28                ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_2)
% 1.06/1.28                 | ~ (r2_hidden @ X24 @ sk_B))))),
% 1.06/1.28      inference('sup-', [status(thm)], ['24', '27'])).
% 1.06/1.28  thf('29', plain,
% 1.06/1.28      (~
% 1.06/1.28       (![X24 : $i]:
% 1.06/1.28          ((r2_hidden @ (k4_tarski @ (sk_E @ X24) @ X24) @ sk_C_2)
% 1.06/1.28           | ~ (r2_hidden @ X24 @ sk_B))) | 
% 1.06/1.28       (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B)))),
% 1.06/1.28      inference('simplify', [status(thm)], ['28'])).
% 1.06/1.28  thf('30', plain,
% 1.06/1.28      (![X23 : $i]:
% 1.06/1.28         (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B))
% 1.06/1.28          | ~ (r2_hidden @ (k4_tarski @ X23 @ sk_D_2) @ sk_C_2))),
% 1.06/1.28      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.06/1.28  thf('31', plain,
% 1.06/1.28      ((![X23 : $i]: ~ (r2_hidden @ (k4_tarski @ X23 @ sk_D_2) @ sk_C_2)) | 
% 1.06/1.28       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B)))),
% 1.06/1.28      inference('split', [status(esa)], ['30'])).
% 1.06/1.28  thf('32', plain,
% 1.06/1.28      (((r2_hidden @ sk_D_2 @ sk_B)) <= (((r2_hidden @ sk_D_2 @ sk_B)))),
% 1.06/1.28      inference('split', [status(esa)], ['0'])).
% 1.06/1.28  thf('33', plain,
% 1.06/1.28      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 1.06/1.28      inference('sup-', [status(thm)], ['7', '8'])).
% 1.06/1.28  thf('34', plain,
% 1.06/1.28      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B)))
% 1.06/1.28         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 1.06/1.28      inference('split', [status(esa)], ['2'])).
% 1.06/1.28  thf('35', plain,
% 1.06/1.28      ((((k2_relat_1 @ sk_C_2) = (sk_B)))
% 1.06/1.28         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 1.06/1.28      inference('sup+', [status(thm)], ['33', '34'])).
% 1.06/1.28  thf('36', plain,
% 1.06/1.28      (![X12 : $i, X13 : $i, X14 : $i]:
% 1.06/1.28         (~ (r2_hidden @ X14 @ X13)
% 1.06/1.28          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X14 @ X12) @ X14) @ X12)
% 1.06/1.28          | ((X13) != (k2_relat_1 @ X12)))),
% 1.06/1.28      inference('cnf', [status(esa)], [d5_relat_1])).
% 1.06/1.28  thf('37', plain,
% 1.06/1.28      (![X12 : $i, X14 : $i]:
% 1.06/1.28         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X14 @ X12) @ X14) @ X12)
% 1.06/1.28          | ~ (r2_hidden @ X14 @ (k2_relat_1 @ X12)))),
% 1.06/1.28      inference('simplify', [status(thm)], ['36'])).
% 1.06/1.28  thf('38', plain,
% 1.06/1.28      ((![X0 : $i]:
% 1.06/1.28          (~ (r2_hidden @ X0 @ sk_B)
% 1.06/1.28           | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X0 @ sk_C_2) @ X0) @ sk_C_2)))
% 1.06/1.28         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 1.06/1.28      inference('sup-', [status(thm)], ['35', '37'])).
% 1.06/1.28  thf('39', plain,
% 1.06/1.28      (((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_C_2) @ sk_D_2) @ sk_C_2))
% 1.06/1.28         <= (((r2_hidden @ sk_D_2 @ sk_B)) & 
% 1.06/1.28             (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))))),
% 1.06/1.28      inference('sup-', [status(thm)], ['32', '38'])).
% 1.06/1.28  thf('40', plain,
% 1.06/1.28      ((![X23 : $i]: ~ (r2_hidden @ (k4_tarski @ X23 @ sk_D_2) @ sk_C_2))
% 1.06/1.28         <= ((![X23 : $i]: ~ (r2_hidden @ (k4_tarski @ X23 @ sk_D_2) @ sk_C_2)))),
% 1.06/1.28      inference('split', [status(esa)], ['30'])).
% 1.06/1.28  thf('41', plain,
% 1.06/1.28      (~ (![X23 : $i]: ~ (r2_hidden @ (k4_tarski @ X23 @ sk_D_2) @ sk_C_2)) | 
% 1.06/1.28       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (sk_B))) | 
% 1.06/1.28       ~ ((r2_hidden @ sk_D_2 @ sk_B))),
% 1.06/1.28      inference('sup-', [status(thm)], ['39', '40'])).
% 1.06/1.28  thf('42', plain, ($false),
% 1.06/1.28      inference('sat_resolution*', [status(thm)], ['1', '3', '29', '31', '41'])).
% 1.06/1.28  
% 1.06/1.28  % SZS output end Refutation
% 1.06/1.28  
% 1.06/1.29  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
