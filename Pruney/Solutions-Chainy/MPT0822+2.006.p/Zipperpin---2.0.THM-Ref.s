%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.35KEOwDcmz

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:58 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 133 expanded)
%              Number of leaves         :   25 (  48 expanded)
%              Depth                    :   14
%              Number of atoms          :  656 (1522 expanded)
%              Number of equality atoms :   42 (  86 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B )
    | ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_B )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    ! [X21: $i] :
      ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
        = sk_B )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ X21 ) @ X21 ) @ sk_C_1 )
      | ~ ( r2_hidden @ X21 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ! [X21: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X21 ) @ X21 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X21 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('6',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X7: $i] :
      ( ( X7
        = ( k2_relat_1 @ X4 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X7 @ X4 ) @ ( sk_C @ X7 @ X4 ) ) @ X4 )
      | ( r2_hidden @ ( sk_C @ X7 @ X4 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('8',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ( X5
       != ( k2_relat_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('9',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ ( k2_relat_1 @ X4 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X3 ) @ X4 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','9'])).

thf(t202_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k2_relat_1 @ X12 ) )
      | ( r2_hidden @ X11 @ X13 )
      | ~ ( v5_relat_1 @ X12 @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t202_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1
        = ( k2_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v5_relat_1 @ X0 @ X2 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_B )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('17',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('18',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_B )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['13','18'])).

thf('20',plain,
    ( ( sk_B
      = ( k2_relat_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B ) ),
    inference(eq_fact,[status(thm)],['19'])).

thf('21',plain,
    ( ! [X21: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X21 ) @ X21 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X21 @ sk_B ) )
   <= ! [X21: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X21 ) @ X21 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X21 @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('22',plain,
    ( ( ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E @ ( sk_C @ sk_B @ sk_C_1 ) ) @ ( sk_C @ sk_B @ sk_C_1 ) ) @ sk_C_1 ) )
   <= ! [X21: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X21 ) @ X21 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X21 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X4: $i,X7: $i,X8: $i] :
      ( ( X7
        = ( k2_relat_1 @ X4 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X8 @ ( sk_C @ X7 @ X4 ) ) @ X4 )
      | ~ ( r2_hidden @ ( sk_C @ X7 @ X4 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('24',plain,
    ( ( ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) )
      | ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X21: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X21 ) @ X21 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X21 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ~ ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B )
      | ( sk_B
        = ( k2_relat_1 @ sk_C_1 ) ) )
   <= ! [X21: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X21 ) @ X21 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X21 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,
    ( ( sk_B
      = ( k2_relat_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_C_1 ) @ sk_B ) ),
    inference(eq_fact,[status(thm)],['19'])).

thf('27',plain,
    ( ( sk_B
      = ( k2_relat_1 @ sk_C_1 ) )
   <= ! [X21: $i] :
        ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X21 ) @ X21 ) @ sk_C_1 )
        | ~ ( r2_hidden @ X21 @ sk_B ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('30',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('32',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
     != sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_B != sk_B )
   <= ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
       != sk_B )
      & ! [X21: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X21 ) @ X21 ) @ sk_C_1 )
          | ~ ( r2_hidden @ X21 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,
    ( ~ ! [X21: $i] :
          ( ( r2_hidden @ ( k4_tarski @ ( sk_E @ X21 ) @ X21 ) @ sk_C_1 )
          | ~ ( r2_hidden @ X21 @ sk_B ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X20: $i] :
      ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
       != sk_B )
      | ~ ( r2_hidden @ ( k4_tarski @ X20 @ sk_D_2 ) @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ! [X20: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ X20 @ sk_D_2 ) @ sk_C_1 )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B ) ),
    inference(split,[status(esa)],['35'])).

thf('37',plain,
    ( ( r2_hidden @ sk_D_2 @ sk_B )
   <= ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('39',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference(split,[status(esa)],['2'])).

thf('40',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = sk_B )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X6 @ X5 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X6 @ X4 ) @ X6 ) @ X4 )
      | ( X5
       != ( k2_relat_1 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('42',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X6 @ X4 ) @ X6 ) @ X4 )
      | ~ ( r2_hidden @ X6 @ ( k2_relat_1 @ X4 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ sk_B )
        | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X0 @ sk_C_1 ) @ X0 ) @ sk_C_1 ) )
   <= ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
      = sk_B ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_D_2 @ sk_C_1 ) @ sk_D_2 ) @ sk_C_1 )
   <= ( ( r2_hidden @ sk_D_2 @ sk_B )
      & ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['37','43'])).

thf('45',plain,
    ( ! [X20: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ X20 @ sk_D_2 ) @ sk_C_1 )
   <= ! [X20: $i] :
        ~ ( r2_hidden @ ( k4_tarski @ X20 @ sk_D_2 ) @ sk_C_1 ) ),
    inference(split,[status(esa)],['35'])).

thf('46',plain,
    ( ~ ! [X20: $i] :
          ~ ( r2_hidden @ ( k4_tarski @ X20 @ sk_D_2 ) @ sk_C_1 )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_1 )
     != sk_B )
    | ~ ( r2_hidden @ sk_D_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','34','36','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.35KEOwDcmz
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:08:33 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.49  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.49  % Solved by: fo/fo7.sh
% 0.19/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.49  % done 62 iterations in 0.040s
% 0.19/0.49  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.49  % SZS output start Refutation
% 0.19/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.19/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.49  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.19/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.19/0.49  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.19/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.49  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.19/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.19/0.49  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.19/0.49  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.19/0.49  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.49  thf(sk_E_type, type, sk_E: $i > $i).
% 0.19/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.49  thf(t23_relset_1, conjecture,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.49       ( ( ![D:$i]:
% 0.19/0.49           ( ~( ( r2_hidden @ D @ B ) & 
% 0.19/0.49                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) ) ) ) ) ) <=>
% 0.19/0.49         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.19/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.49    (~( ![A:$i,B:$i,C:$i]:
% 0.19/0.49        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.49          ( ( ![D:$i]:
% 0.19/0.49              ( ~( ( r2_hidden @ D @ B ) & 
% 0.19/0.49                   ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) ) ) ) ) ) <=>
% 0.19/0.49            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.19/0.49    inference('cnf.neg', [status(esa)], [t23_relset_1])).
% 0.19/0.49  thf('0', plain,
% 0.19/0.49      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B))
% 0.19/0.49        | (r2_hidden @ sk_D_2 @ sk_B))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('1', plain,
% 0.19/0.49      (((r2_hidden @ sk_D_2 @ sk_B)) | 
% 0.19/0.49       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))),
% 0.19/0.49      inference('split', [status(esa)], ['0'])).
% 0.19/0.49  thf('2', plain,
% 0.19/0.49      (![X21 : $i]:
% 0.19/0.49         (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))
% 0.19/0.49          | (r2_hidden @ (k4_tarski @ (sk_E @ X21) @ X21) @ sk_C_1)
% 0.19/0.49          | ~ (r2_hidden @ X21 @ sk_B))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('3', plain,
% 0.19/0.49      ((![X21 : $i]:
% 0.19/0.49          ((r2_hidden @ (k4_tarski @ (sk_E @ X21) @ X21) @ sk_C_1)
% 0.19/0.49           | ~ (r2_hidden @ X21 @ sk_B))) | 
% 0.19/0.49       (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))),
% 0.19/0.49      inference('split', [status(esa)], ['2'])).
% 0.19/0.49  thf('4', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(cc2_relset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.49       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.19/0.49  thf('5', plain,
% 0.19/0.49      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.49         ((v5_relat_1 @ X14 @ X16)
% 0.19/0.49          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.19/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.49  thf('6', plain, ((v5_relat_1 @ sk_C_1 @ sk_B)),
% 0.19/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.19/0.49  thf(d5_relat_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.19/0.49       ( ![C:$i]:
% 0.19/0.49         ( ( r2_hidden @ C @ B ) <=>
% 0.19/0.49           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.19/0.49  thf('7', plain,
% 0.19/0.49      (![X4 : $i, X7 : $i]:
% 0.19/0.49         (((X7) = (k2_relat_1 @ X4))
% 0.19/0.49          | (r2_hidden @ (k4_tarski @ (sk_D @ X7 @ X4) @ (sk_C @ X7 @ X4)) @ X4)
% 0.19/0.49          | (r2_hidden @ (sk_C @ X7 @ X4) @ X7))),
% 0.19/0.49      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.19/0.49  thf('8', plain,
% 0.19/0.49      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.19/0.49         (~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ X4)
% 0.19/0.49          | (r2_hidden @ X3 @ X5)
% 0.19/0.49          | ((X5) != (k2_relat_1 @ X4)))),
% 0.19/0.49      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.19/0.49  thf('9', plain,
% 0.19/0.49      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.19/0.49         ((r2_hidden @ X3 @ (k2_relat_1 @ X4))
% 0.19/0.49          | ~ (r2_hidden @ (k4_tarski @ X2 @ X3) @ X4))),
% 0.19/0.49      inference('simplify', [status(thm)], ['8'])).
% 0.19/0.49  thf('10', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         ((r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.19/0.49          | ((X1) = (k2_relat_1 @ X0))
% 0.19/0.49          | (r2_hidden @ (sk_C @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['7', '9'])).
% 0.19/0.49  thf(t202_relat_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]:
% 0.19/0.49     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.19/0.49       ( ![C:$i]:
% 0.19/0.49         ( ( r2_hidden @ C @ ( k2_relat_1 @ B ) ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.19/0.49  thf('11', plain,
% 0.19/0.49      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X11 @ (k2_relat_1 @ X12))
% 0.19/0.49          | (r2_hidden @ X11 @ X13)
% 0.19/0.49          | ~ (v5_relat_1 @ X12 @ X13)
% 0.19/0.49          | ~ (v1_relat_1 @ X12))),
% 0.19/0.49      inference('cnf', [status(esa)], [t202_relat_1])).
% 0.19/0.49  thf('12', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.19/0.49         (((X1) = (k2_relat_1 @ X0))
% 0.19/0.49          | (r2_hidden @ (sk_C @ X1 @ X0) @ X1)
% 0.19/0.49          | ~ (v1_relat_1 @ X0)
% 0.19/0.49          | ~ (v5_relat_1 @ X0 @ X2)
% 0.19/0.49          | (r2_hidden @ (sk_C @ X1 @ X0) @ X2))),
% 0.19/0.49      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.49  thf('13', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_B)
% 0.19/0.49          | ~ (v1_relat_1 @ sk_C_1)
% 0.19/0.49          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0)
% 0.19/0.49          | ((X0) = (k2_relat_1 @ sk_C_1)))),
% 0.19/0.49      inference('sup-', [status(thm)], ['6', '12'])).
% 0.19/0.49  thf('14', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(cc2_relat_1, axiom,
% 0.19/0.49    (![A:$i]:
% 0.19/0.49     ( ( v1_relat_1 @ A ) =>
% 0.19/0.49       ( ![B:$i]:
% 0.19/0.49         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.19/0.49  thf('15', plain,
% 0.19/0.49      (![X0 : $i, X1 : $i]:
% 0.19/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.19/0.49          | (v1_relat_1 @ X0)
% 0.19/0.49          | ~ (v1_relat_1 @ X1))),
% 0.19/0.49      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.19/0.49  thf('16', plain,
% 0.19/0.49      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['14', '15'])).
% 0.19/0.49  thf(fc6_relat_1, axiom,
% 0.19/0.49    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.19/0.49  thf('17', plain,
% 0.19/0.49      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.19/0.49      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.19/0.49  thf('18', plain, ((v1_relat_1 @ sk_C_1)),
% 0.19/0.49      inference('demod', [status(thm)], ['16', '17'])).
% 0.19/0.49  thf('19', plain,
% 0.19/0.49      (![X0 : $i]:
% 0.19/0.49         ((r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_B)
% 0.19/0.49          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ X0)
% 0.19/0.49          | ((X0) = (k2_relat_1 @ sk_C_1)))),
% 0.19/0.49      inference('demod', [status(thm)], ['13', '18'])).
% 0.19/0.49  thf('20', plain,
% 0.19/0.49      ((((sk_B) = (k2_relat_1 @ sk_C_1))
% 0.19/0.49        | (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B))),
% 0.19/0.49      inference('eq_fact', [status(thm)], ['19'])).
% 0.19/0.49  thf('21', plain,
% 0.19/0.49      ((![X21 : $i]:
% 0.19/0.49          ((r2_hidden @ (k4_tarski @ (sk_E @ X21) @ X21) @ sk_C_1)
% 0.19/0.49           | ~ (r2_hidden @ X21 @ sk_B)))
% 0.19/0.49         <= ((![X21 : $i]:
% 0.19/0.49                ((r2_hidden @ (k4_tarski @ (sk_E @ X21) @ X21) @ sk_C_1)
% 0.19/0.49                 | ~ (r2_hidden @ X21 @ sk_B))))),
% 0.19/0.49      inference('split', [status(esa)], ['2'])).
% 0.19/0.49  thf('22', plain,
% 0.19/0.49      (((((sk_B) = (k2_relat_1 @ sk_C_1))
% 0.19/0.49         | (r2_hidden @ 
% 0.19/0.49            (k4_tarski @ (sk_E @ (sk_C @ sk_B @ sk_C_1)) @ 
% 0.19/0.49             (sk_C @ sk_B @ sk_C_1)) @ 
% 0.19/0.49            sk_C_1)))
% 0.19/0.49         <= ((![X21 : $i]:
% 0.19/0.49                ((r2_hidden @ (k4_tarski @ (sk_E @ X21) @ X21) @ sk_C_1)
% 0.19/0.49                 | ~ (r2_hidden @ X21 @ sk_B))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['20', '21'])).
% 0.19/0.49  thf('23', plain,
% 0.19/0.49      (![X4 : $i, X7 : $i, X8 : $i]:
% 0.19/0.49         (((X7) = (k2_relat_1 @ X4))
% 0.19/0.49          | ~ (r2_hidden @ (k4_tarski @ X8 @ (sk_C @ X7 @ X4)) @ X4)
% 0.19/0.49          | ~ (r2_hidden @ (sk_C @ X7 @ X4) @ X7))),
% 0.19/0.49      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.19/0.49  thf('24', plain,
% 0.19/0.49      (((((sk_B) = (k2_relat_1 @ sk_C_1))
% 0.19/0.49         | ~ (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)
% 0.19/0.49         | ((sk_B) = (k2_relat_1 @ sk_C_1))))
% 0.19/0.49         <= ((![X21 : $i]:
% 0.19/0.49                ((r2_hidden @ (k4_tarski @ (sk_E @ X21) @ X21) @ sk_C_1)
% 0.19/0.49                 | ~ (r2_hidden @ X21 @ sk_B))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['22', '23'])).
% 0.19/0.49  thf('25', plain,
% 0.19/0.49      (((~ (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B)
% 0.19/0.49         | ((sk_B) = (k2_relat_1 @ sk_C_1))))
% 0.19/0.49         <= ((![X21 : $i]:
% 0.19/0.49                ((r2_hidden @ (k4_tarski @ (sk_E @ X21) @ X21) @ sk_C_1)
% 0.19/0.49                 | ~ (r2_hidden @ X21 @ sk_B))))),
% 0.19/0.49      inference('simplify', [status(thm)], ['24'])).
% 0.19/0.49  thf('26', plain,
% 0.19/0.49      ((((sk_B) = (k2_relat_1 @ sk_C_1))
% 0.19/0.49        | (r2_hidden @ (sk_C @ sk_B @ sk_C_1) @ sk_B))),
% 0.19/0.49      inference('eq_fact', [status(thm)], ['19'])).
% 0.19/0.49  thf('27', plain,
% 0.19/0.49      ((((sk_B) = (k2_relat_1 @ sk_C_1)))
% 0.19/0.49         <= ((![X21 : $i]:
% 0.19/0.49                ((r2_hidden @ (k4_tarski @ (sk_E @ X21) @ X21) @ sk_C_1)
% 0.19/0.49                 | ~ (r2_hidden @ X21 @ sk_B))))),
% 0.19/0.49      inference('clc', [status(thm)], ['25', '26'])).
% 0.19/0.49  thf('28', plain,
% 0.19/0.49      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf(redefinition_k2_relset_1, axiom,
% 0.19/0.49    (![A:$i,B:$i,C:$i]:
% 0.19/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.49       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.19/0.49  thf('29', plain,
% 0.19/0.49      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.49         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.19/0.49          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.19/0.49      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.19/0.49  thf('30', plain,
% 0.19/0.49      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['28', '29'])).
% 0.19/0.49  thf('31', plain,
% 0.19/0.49      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B)))
% 0.19/0.49         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 0.19/0.49      inference('split', [status(esa)], ['0'])).
% 0.19/0.49  thf('32', plain,
% 0.19/0.49      ((((k2_relat_1 @ sk_C_1) != (sk_B)))
% 0.19/0.49         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['30', '31'])).
% 0.19/0.49  thf('33', plain,
% 0.19/0.49      ((((sk_B) != (sk_B)))
% 0.19/0.49         <= (~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))) & 
% 0.19/0.49             (![X21 : $i]:
% 0.19/0.49                ((r2_hidden @ (k4_tarski @ (sk_E @ X21) @ X21) @ sk_C_1)
% 0.19/0.49                 | ~ (r2_hidden @ X21 @ sk_B))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['27', '32'])).
% 0.19/0.49  thf('34', plain,
% 0.19/0.49      (~
% 0.19/0.49       (![X21 : $i]:
% 0.19/0.49          ((r2_hidden @ (k4_tarski @ (sk_E @ X21) @ X21) @ sk_C_1)
% 0.19/0.49           | ~ (r2_hidden @ X21 @ sk_B))) | 
% 0.19/0.49       (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['33'])).
% 0.19/0.49  thf('35', plain,
% 0.19/0.49      (![X20 : $i]:
% 0.19/0.49         (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) != (sk_B))
% 0.19/0.49          | ~ (r2_hidden @ (k4_tarski @ X20 @ sk_D_2) @ sk_C_1))),
% 0.19/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.49  thf('36', plain,
% 0.19/0.49      ((![X20 : $i]: ~ (r2_hidden @ (k4_tarski @ X20 @ sk_D_2) @ sk_C_1)) | 
% 0.19/0.49       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))),
% 0.19/0.49      inference('split', [status(esa)], ['35'])).
% 0.19/0.49  thf('37', plain,
% 0.19/0.49      (((r2_hidden @ sk_D_2 @ sk_B)) <= (((r2_hidden @ sk_D_2 @ sk_B)))),
% 0.19/0.49      inference('split', [status(esa)], ['0'])).
% 0.19/0.49  thf('38', plain,
% 0.19/0.49      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.19/0.49      inference('sup-', [status(thm)], ['28', '29'])).
% 0.19/0.49  thf('39', plain,
% 0.19/0.49      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B)))
% 0.19/0.49         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 0.19/0.49      inference('split', [status(esa)], ['2'])).
% 0.19/0.49  thf('40', plain,
% 0.19/0.49      ((((k2_relat_1 @ sk_C_1) = (sk_B)))
% 0.19/0.49         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 0.19/0.49      inference('sup+', [status(thm)], ['38', '39'])).
% 0.19/0.49  thf('41', plain,
% 0.19/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.19/0.49         (~ (r2_hidden @ X6 @ X5)
% 0.19/0.49          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X6 @ X4) @ X6) @ X4)
% 0.19/0.49          | ((X5) != (k2_relat_1 @ X4)))),
% 0.19/0.49      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.19/0.49  thf('42', plain,
% 0.19/0.49      (![X4 : $i, X6 : $i]:
% 0.19/0.49         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X6 @ X4) @ X6) @ X4)
% 0.19/0.49          | ~ (r2_hidden @ X6 @ (k2_relat_1 @ X4)))),
% 0.19/0.49      inference('simplify', [status(thm)], ['41'])).
% 0.19/0.49  thf('43', plain,
% 0.19/0.49      ((![X0 : $i]:
% 0.19/0.49          (~ (r2_hidden @ X0 @ sk_B)
% 0.19/0.49           | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X0 @ sk_C_1) @ X0) @ sk_C_1)))
% 0.19/0.49         <= ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['40', '42'])).
% 0.19/0.49  thf('44', plain,
% 0.19/0.49      (((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_D_2 @ sk_C_1) @ sk_D_2) @ sk_C_1))
% 0.19/0.49         <= (((r2_hidden @ sk_D_2 @ sk_B)) & 
% 0.19/0.49             (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))))),
% 0.19/0.49      inference('sup-', [status(thm)], ['37', '43'])).
% 0.19/0.49  thf('45', plain,
% 0.19/0.49      ((![X20 : $i]: ~ (r2_hidden @ (k4_tarski @ X20 @ sk_D_2) @ sk_C_1))
% 0.19/0.49         <= ((![X20 : $i]: ~ (r2_hidden @ (k4_tarski @ X20 @ sk_D_2) @ sk_C_1)))),
% 0.19/0.49      inference('split', [status(esa)], ['35'])).
% 0.19/0.49  thf('46', plain,
% 0.19/0.49      (~ (![X20 : $i]: ~ (r2_hidden @ (k4_tarski @ X20 @ sk_D_2) @ sk_C_1)) | 
% 0.19/0.49       ~ (((k2_relset_1 @ sk_A @ sk_B @ sk_C_1) = (sk_B))) | 
% 0.19/0.49       ~ ((r2_hidden @ sk_D_2 @ sk_B))),
% 0.19/0.49      inference('sup-', [status(thm)], ['44', '45'])).
% 0.19/0.49  thf('47', plain, ($false),
% 0.19/0.49      inference('sat_resolution*', [status(thm)], ['1', '3', '34', '36', '46'])).
% 0.19/0.49  
% 0.19/0.49  % SZS output end Refutation
% 0.19/0.49  
% 0.19/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
