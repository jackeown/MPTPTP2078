%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5gerZR93HB

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 119 expanded)
%              Number of leaves         :   27 (  46 expanded)
%              Depth                    :   12
%              Number of atoms          :  434 (1085 expanded)
%              Number of equality atoms :   14 (  42 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_5_type,type,(
    sk_D_5: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t6_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
     => ~ ( ( r2_hidden @ A @ D )
          & ! [E: $i,F: $i] :
              ~ ( ( A
                  = ( k4_tarski @ E @ F ) )
                & ( r2_hidden @ E @ B )
                & ( r2_hidden @ F @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
       => ~ ( ( r2_hidden @ A @ D )
            & ! [E: $i,F: $i] :
                ~ ( ( A
                    = ( k4_tarski @ E @ F ) )
                  & ( r2_hidden @ E @ B )
                  & ( r2_hidden @ F @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_relset_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_D_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('2',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ( r2_hidden @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_B @ sk_C_3 ) )
      | ~ ( r2_hidden @ X0 @ sk_D_5 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['0','3'])).

thf(l139_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ! [D: $i,E: $i] :
            ( ( k4_tarski @ D @ E )
           != A ) ) )).

thf('5',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k4_tarski @ ( sk_D @ X4 ) @ ( sk_E @ X4 ) )
        = X4 )
      | ~ ( r2_hidden @ X4 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[l139_zfmisc_1])).

thf('6',plain,
    ( ( k4_tarski @ ( sk_D @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    r2_hidden @ sk_A @ sk_D_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ( k4_tarski @ ( sk_D @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('9',plain,(
    ! [X14: $i,X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ X16 )
      | ( r2_hidden @ X14 @ X17 )
      | ( X17
       != ( k1_relat_1 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('10',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X14 @ ( k1_relat_1 @ X16 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X14 @ X15 ) @ X16 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_D @ sk_A ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['8','10'])).

thf('12',plain,(
    r2_hidden @ ( sk_D @ sk_A ) @ ( k1_relat_1 @ sk_D_5 ) ),
    inference('sup-',[status(thm)],['7','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D_5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v4_relat_1 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('15',plain,(
    v4_relat_1 @ sk_D_5 @ sk_B ),
    inference('sup-',[status(thm)],['13','14'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( v4_relat_1 @ X10 @ X11 )
      | ( r1_tarski @ ( k1_relat_1 @ X10 ) @ X11 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_D_5 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_5 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D_5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('19',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('20',plain,(
    v1_relat_1 @ sk_D_5 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_5 ) @ sk_B ),
    inference(demod,[status(thm)],['17','20'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_5 ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    r2_hidden @ ( sk_D @ sk_A ) @ sk_B ),
    inference('sup-',[status(thm)],['12','23'])).

thf('25',plain,(
    ! [X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X34 @ sk_B )
      | ~ ( r2_hidden @ X35 @ sk_C_3 )
      | ( sk_A
       != ( k4_tarski @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k4_tarski @ ( sk_D @ sk_A ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( sk_A != sk_A )
    | ~ ( r2_hidden @ ( sk_E @ sk_A ) @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['6','26'])).

thf('28',plain,(
    ~ ( r2_hidden @ ( sk_E @ sk_A ) @ sk_C_3 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    r2_hidden @ sk_A @ sk_D_5 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( k4_tarski @ ( sk_D @ sk_A ) @ ( sk_E @ sk_A ) )
    = sk_A ),
    inference('sup-',[status(thm)],['4','5'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('31',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X21 @ X22 ) @ X23 )
      | ( r2_hidden @ X22 @ X24 )
      | ( X24
       != ( k2_relat_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('32',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ X22 @ ( k2_relat_1 @ X23 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X21 @ X22 ) @ X23 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ sk_A @ X0 )
      | ( r2_hidden @ ( sk_E @ sk_A ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,(
    r2_hidden @ ( sk_E @ sk_A ) @ ( k2_relat_1 @ sk_D_5 ) ),
    inference('sup-',[status(thm)],['29','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D_5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v5_relat_1 @ X31 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('37',plain,(
    v5_relat_1 @ sk_D_5 @ sk_C_3 ),
    inference('sup-',[status(thm)],['35','36'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('38',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( v5_relat_1 @ X12 @ X13 )
      | ( r1_tarski @ ( k2_relat_1 @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_D_5 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_5 ) @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_D_5 ),
    inference('sup-',[status(thm)],['18','19'])).

thf('41',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_5 ) @ sk_C_3 ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_C_3 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_5 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    r2_hidden @ ( sk_E @ sk_A ) @ sk_C_3 ),
    inference('sup-',[status(thm)],['34','43'])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['28','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.5gerZR93HB
% 0.12/0.34  % Computer   : n022.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:53:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.49  % Solved by: fo/fo7.sh
% 0.20/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.49  % done 79 iterations in 0.034s
% 0.20/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.49  % SZS output start Refutation
% 0.20/0.49  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.49  thf(sk_D_5_type, type, sk_D_5: $i).
% 0.20/0.49  thf(sk_D_type, type, sk_D: $i > $i).
% 0.20/0.49  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.49  thf(sk_E_type, type, sk_E: $i > $i).
% 0.20/0.49  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.49  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.20/0.49  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.49  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.49  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.49  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.49  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.49  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.49  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.49  thf(t6_relset_1, conjecture,
% 0.20/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.20/0.49       ( ~( ( r2_hidden @ A @ D ) & 
% 0.20/0.49            ( ![E:$i,F:$i]:
% 0.20/0.49              ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ E @ B ) & 
% 0.20/0.49                   ( r2_hidden @ F @ C ) ) ) ) ) ) ))).
% 0.20/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.49    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.49        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.20/0.49          ( ~( ( r2_hidden @ A @ D ) & 
% 0.20/0.49               ( ![E:$i,F:$i]:
% 0.20/0.49                 ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & 
% 0.20/0.49                      ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) ) ) ) ) ) ) )),
% 0.20/0.49    inference('cnf.neg', [status(esa)], [t6_relset_1])).
% 0.20/0.49  thf('0', plain, ((r2_hidden @ sk_A @ sk_D_5)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('1', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_D_5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_3)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(l3_subset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.49  thf('2', plain,
% 0.20/0.49      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X7 @ X8)
% 0.20/0.49          | (r2_hidden @ X7 @ X9)
% 0.20/0.49          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.20/0.49      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.20/0.49  thf('3', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_B @ sk_C_3))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ sk_D_5))),
% 0.20/0.49      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.49  thf('4', plain, ((r2_hidden @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C_3))),
% 0.20/0.49      inference('sup-', [status(thm)], ['0', '3'])).
% 0.20/0.49  thf(l139_zfmisc_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ~( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.20/0.49          ( ![D:$i,E:$i]: ( ( k4_tarski @ D @ E ) != ( A ) ) ) ) ))).
% 0.20/0.49  thf('5', plain,
% 0.20/0.49      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.20/0.49         (((k4_tarski @ (sk_D @ X4) @ (sk_E @ X4)) = (X4))
% 0.20/0.49          | ~ (r2_hidden @ X4 @ (k2_zfmisc_1 @ X5 @ X6)))),
% 0.20/0.49      inference('cnf', [status(esa)], [l139_zfmisc_1])).
% 0.20/0.49  thf('6', plain, (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf('7', plain, ((r2_hidden @ sk_A @ sk_D_5)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('8', plain, (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf(d4_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.20/0.49       ( ![C:$i]:
% 0.20/0.49         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.49           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.20/0.49  thf('9', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.49         (~ (r2_hidden @ (k4_tarski @ X14 @ X15) @ X16)
% 0.20/0.49          | (r2_hidden @ X14 @ X17)
% 0.20/0.49          | ((X17) != (k1_relat_1 @ X16)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.20/0.49  thf('10', plain,
% 0.20/0.49      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.49         ((r2_hidden @ X14 @ (k1_relat_1 @ X16))
% 0.20/0.49          | ~ (r2_hidden @ (k4_tarski @ X14 @ X15) @ X16))),
% 0.20/0.49      inference('simplify', [status(thm)], ['9'])).
% 0.20/0.49  thf('11', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r2_hidden @ sk_A @ X0)
% 0.20/0.49          | (r2_hidden @ (sk_D @ sk_A) @ (k1_relat_1 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['8', '10'])).
% 0.20/0.49  thf('12', plain, ((r2_hidden @ (sk_D @ sk_A) @ (k1_relat_1 @ sk_D_5))),
% 0.20/0.49      inference('sup-', [status(thm)], ['7', '11'])).
% 0.20/0.49  thf('13', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_D_5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_3)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(cc2_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.49  thf('14', plain,
% 0.20/0.49      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.49         ((v4_relat_1 @ X31 @ X32)
% 0.20/0.49          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.49  thf('15', plain, ((v4_relat_1 @ sk_D_5 @ sk_B)),
% 0.20/0.49      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.49  thf(d18_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.49  thf('16', plain,
% 0.20/0.49      (![X10 : $i, X11 : $i]:
% 0.20/0.49         (~ (v4_relat_1 @ X10 @ X11)
% 0.20/0.49          | (r1_tarski @ (k1_relat_1 @ X10) @ X11)
% 0.20/0.49          | ~ (v1_relat_1 @ X10))),
% 0.20/0.49      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.20/0.49  thf('17', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ sk_D_5) | (r1_tarski @ (k1_relat_1 @ sk_D_5) @ sk_B))),
% 0.20/0.49      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.49  thf('18', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_D_5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_3)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf(cc1_relset_1, axiom,
% 0.20/0.49    (![A:$i,B:$i,C:$i]:
% 0.20/0.49     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.49       ( v1_relat_1 @ C ) ))).
% 0.20/0.49  thf('19', plain,
% 0.20/0.49      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.49         ((v1_relat_1 @ X28)
% 0.20/0.49          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.49  thf('20', plain, ((v1_relat_1 @ sk_D_5)),
% 0.20/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.49  thf('21', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_5) @ sk_B)),
% 0.20/0.49      inference('demod', [status(thm)], ['17', '20'])).
% 0.20/0.49  thf(d3_tarski, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.49       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.49  thf('22', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.49          | (r2_hidden @ X0 @ X2)
% 0.20/0.49          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.49  thf('23', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_5)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.49  thf('24', plain, ((r2_hidden @ (sk_D @ sk_A) @ sk_B)),
% 0.20/0.49      inference('sup-', [status(thm)], ['12', '23'])).
% 0.20/0.49  thf('25', plain,
% 0.20/0.49      (![X34 : $i, X35 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X34 @ sk_B)
% 0.20/0.49          | ~ (r2_hidden @ X35 @ sk_C_3)
% 0.20/0.49          | ((sk_A) != (k4_tarski @ X34 @ X35)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('26', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (((sk_A) != (k4_tarski @ (sk_D @ sk_A) @ X0))
% 0.20/0.49          | ~ (r2_hidden @ X0 @ sk_C_3))),
% 0.20/0.49      inference('sup-', [status(thm)], ['24', '25'])).
% 0.20/0.49  thf('27', plain,
% 0.20/0.49      ((((sk_A) != (sk_A)) | ~ (r2_hidden @ (sk_E @ sk_A) @ sk_C_3))),
% 0.20/0.49      inference('sup-', [status(thm)], ['6', '26'])).
% 0.20/0.49  thf('28', plain, (~ (r2_hidden @ (sk_E @ sk_A) @ sk_C_3)),
% 0.20/0.49      inference('simplify', [status(thm)], ['27'])).
% 0.20/0.49  thf('29', plain, ((r2_hidden @ sk_A @ sk_D_5)),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('30', plain, (((k4_tarski @ (sk_D @ sk_A) @ (sk_E @ sk_A)) = (sk_A))),
% 0.20/0.49      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.49  thf(d5_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.20/0.49       ( ![C:$i]:
% 0.20/0.49         ( ( r2_hidden @ C @ B ) <=>
% 0.20/0.49           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.20/0.49  thf('31', plain,
% 0.20/0.49      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.49         (~ (r2_hidden @ (k4_tarski @ X21 @ X22) @ X23)
% 0.20/0.49          | (r2_hidden @ X22 @ X24)
% 0.20/0.49          | ((X24) != (k2_relat_1 @ X23)))),
% 0.20/0.49      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.20/0.49  thf('32', plain,
% 0.20/0.49      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.49         ((r2_hidden @ X22 @ (k2_relat_1 @ X23))
% 0.20/0.49          | ~ (r2_hidden @ (k4_tarski @ X21 @ X22) @ X23))),
% 0.20/0.49      inference('simplify', [status(thm)], ['31'])).
% 0.20/0.49  thf('33', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         (~ (r2_hidden @ sk_A @ X0)
% 0.20/0.49          | (r2_hidden @ (sk_E @ sk_A) @ (k2_relat_1 @ X0)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['30', '32'])).
% 0.20/0.49  thf('34', plain, ((r2_hidden @ (sk_E @ sk_A) @ (k2_relat_1 @ sk_D_5))),
% 0.20/0.49      inference('sup-', [status(thm)], ['29', '33'])).
% 0.20/0.49  thf('35', plain,
% 0.20/0.49      ((m1_subset_1 @ sk_D_5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_3)))),
% 0.20/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.49  thf('36', plain,
% 0.20/0.49      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.49         ((v5_relat_1 @ X31 @ X33)
% 0.20/0.49          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.20/0.49      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.49  thf('37', plain, ((v5_relat_1 @ sk_D_5 @ sk_C_3)),
% 0.20/0.49      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.49  thf(d19_relat_1, axiom,
% 0.20/0.49    (![A:$i,B:$i]:
% 0.20/0.49     ( ( v1_relat_1 @ B ) =>
% 0.20/0.49       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.49  thf('38', plain,
% 0.20/0.49      (![X12 : $i, X13 : $i]:
% 0.20/0.49         (~ (v5_relat_1 @ X12 @ X13)
% 0.20/0.49          | (r1_tarski @ (k2_relat_1 @ X12) @ X13)
% 0.20/0.49          | ~ (v1_relat_1 @ X12))),
% 0.20/0.49      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.20/0.49  thf('39', plain,
% 0.20/0.49      ((~ (v1_relat_1 @ sk_D_5) | (r1_tarski @ (k2_relat_1 @ sk_D_5) @ sk_C_3))),
% 0.20/0.49      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.49  thf('40', plain, ((v1_relat_1 @ sk_D_5)),
% 0.20/0.49      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.49  thf('41', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_5) @ sk_C_3)),
% 0.20/0.49      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.49  thf('42', plain,
% 0.20/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.49         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.49          | (r2_hidden @ X0 @ X2)
% 0.20/0.49          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.49      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.49  thf('43', plain,
% 0.20/0.49      (![X0 : $i]:
% 0.20/0.49         ((r2_hidden @ X0 @ sk_C_3)
% 0.20/0.49          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_5)))),
% 0.20/0.49      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.49  thf('44', plain, ((r2_hidden @ (sk_E @ sk_A) @ sk_C_3)),
% 0.20/0.49      inference('sup-', [status(thm)], ['34', '43'])).
% 0.20/0.49  thf('45', plain, ($false), inference('demod', [status(thm)], ['28', '44'])).
% 0.20/0.49  
% 0.20/0.49  % SZS output end Refutation
% 0.20/0.49  
% 0.20/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
