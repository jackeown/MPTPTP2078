%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xG1l845NwO

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 351 expanded)
%              Number of leaves         :   29 ( 115 expanded)
%              Depth                    :   16
%              Number of atoms          :  515 (4621 expanded)
%              Number of equality atoms :   30 ( 285 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(t2_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ! [C: $i] :
          ( ( r2_hidden @ C @ A )
        <=> ( r2_hidden @ C @ B ) )
     => ( A = B ) ) )).

thf('0',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf(t16_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( ( r2_hidden @ E @ A )
                    & ( D
                      = ( k1_funct_1 @ C @ E ) ) ) )
       => ( ( k2_relset_1 @ A @ B @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ! [D: $i] :
              ~ ( ( r2_hidden @ D @ B )
                & ! [E: $i] :
                    ~ ( ( r2_hidden @ E @ A )
                      & ( D
                        = ( k1_funct_1 @ C @ E ) ) ) )
         => ( ( k2_relset_1 @ A @ B @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_funct_2])).

thf('1',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('3',plain,(
    v5_relat_1 @ sk_C_2 @ sk_B ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v5_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('7',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('8',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ),
    inference(demod,[status(thm)],['5','8'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_C_2 ) @ X0 ) @ X0 )
      | ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_C_2 ) @ X0 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['0','11'])).

thf('13',plain,
    ( ( sk_B
      = ( k2_relat_1 @ sk_C_2 ) )
    | ( r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) @ sk_B ) ),
    inference(eq_fact,[status(thm)],['12'])).

thf('14',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('16',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('17',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
    r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['13','18'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('21',plain,(
    ~ ( r1_tarski @ sk_B @ ( sk_C_1 @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['13','18'])).

thf('23',plain,(
    ! [X24: $i] :
      ( ~ ( r2_hidden @ X24 @ sk_B )
      | ( r2_hidden @ ( sk_E @ X24 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    r2_hidden @ ( sk_E @ ( sk_C_1 @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) ) @ sk_A ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf('26',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X20 @ X21 )
      | ( X22 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( r2_hidden @ ( k1_funct_1 @ X23 @ X20 ) @ ( k2_relset_1 @ X21 @ X22 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t6_funct_2])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 ) )
      | ~ ( v1_funct_2 @ sk_C_2 @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('29',plain,(
    v1_funct_2 @ sk_C_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ X0 ) @ ( k2_relat_1 @ sk_C_2 ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['27','28','29','30'])).

thf('32',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C_1 @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) ) ) @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf('33',plain,(
    r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['13','18'])).

thf('34',plain,(
    ! [X24: $i] :
      ( ~ ( r2_hidden @ X24 @ sk_B )
      | ( X24
        = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( sk_C_1 @ ( k2_relat_1 @ sk_C_2 ) @ sk_B )
    = ( k1_funct_1 @ sk_C_2 @ ( sk_E @ ( sk_C_1 @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X5 = X4 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X4 )
      | ~ ( r2_hidden @ ( sk_C_1 @ X4 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_tarski])).

thf('38',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) @ sk_B )
    | ( sk_B
      = ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r2_hidden @ ( sk_C_1 @ ( k2_relat_1 @ sk_C_2 ) @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['13','18'])).

thf('40',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_B
      = ( k2_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != sk_B ),
    inference(demod,[status(thm)],['14','17'])).

thf('42',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf('43',plain,(
    sk_B = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['40','41'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('44',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('45',plain,(
    $false ),
    inference(demod,[status(thm)],['21','42','43','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.xG1l845NwO
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:57:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.53  % Solved by: fo/fo7.sh
% 0.20/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.53  % done 138 iterations in 0.077s
% 0.20/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.53  % SZS output start Refutation
% 0.20/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.53  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.53  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.20/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.53  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.20/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.53  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.53  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.53  thf(sk_E_type, type, sk_E: $i > $i).
% 0.20/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.53  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.53  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.53  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.53  thf(t2_tarski, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ![C:$i]: ( ( r2_hidden @ C @ A ) <=> ( r2_hidden @ C @ B ) ) ) =>
% 0.20/0.53       ( ( A ) = ( B ) ) ))).
% 0.20/0.53  thf('0', plain,
% 0.20/0.53      (![X4 : $i, X5 : $i]:
% 0.20/0.53         (((X5) = (X4))
% 0.20/0.53          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 0.20/0.53          | (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 0.20/0.53      inference('cnf', [status(esa)], [t2_tarski])).
% 0.20/0.53  thf(t16_funct_2, conjecture,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.53         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.53       ( ( ![D:$i]:
% 0.20/0.53           ( ~( ( r2_hidden @ D @ B ) & 
% 0.20/0.53                ( ![E:$i]:
% 0.20/0.53                  ( ~( ( r2_hidden @ E @ A ) & 
% 0.20/0.53                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.20/0.53         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.20/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.53    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.53        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.53            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.53          ( ( ![D:$i]:
% 0.20/0.53              ( ~( ( r2_hidden @ D @ B ) & 
% 0.20/0.53                   ( ![E:$i]:
% 0.20/0.53                     ( ~( ( r2_hidden @ E @ A ) & 
% 0.20/0.53                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.20/0.53            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(cc2_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.53         ((v5_relat_1 @ X14 @ X16)
% 0.20/0.53          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.53  thf('3', plain, ((v5_relat_1 @ sk_C_2 @ sk_B)),
% 0.20/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.53  thf(d19_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ B ) =>
% 0.20/0.53       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i]:
% 0.20/0.53         (~ (v5_relat_1 @ X7 @ X8)
% 0.20/0.53          | (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 0.20/0.53          | ~ (v1_relat_1 @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      ((~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(cc1_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( v1_relat_1 @ C ) ))).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.53         ((v1_relat_1 @ X11)
% 0.20/0.53          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.53  thf('8', plain, ((v1_relat_1 @ sk_C_2)),
% 0.20/0.53      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.53  thf('9', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B)),
% 0.20/0.53      inference('demod', [status(thm)], ['5', '8'])).
% 0.20/0.53  thf(d3_tarski, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( r1_tarski @ A @ B ) <=>
% 0.20/0.53       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.20/0.53  thf('10', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.53          | (r2_hidden @ X0 @ X2)
% 0.20/0.53          | ~ (r1_tarski @ X1 @ X2))),
% 0.20/0.53      inference('cnf', [status(esa)], [d3_tarski])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r2_hidden @ (sk_C_1 @ (k2_relat_1 @ sk_C_2) @ X0) @ X0)
% 0.20/0.53          | ((X0) = (k2_relat_1 @ sk_C_2))
% 0.20/0.53          | (r2_hidden @ (sk_C_1 @ (k2_relat_1 @ sk_C_2) @ X0) @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '11'])).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      ((((sk_B) = (k2_relat_1 @ sk_C_2))
% 0.20/0.53        | (r2_hidden @ (sk_C_1 @ (k2_relat_1 @ sk_C_2) @ sk_B) @ sk_B))),
% 0.20/0.53      inference('eq_fact', [status(thm)], ['12'])).
% 0.20/0.53  thf('14', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) != (sk_B))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.53         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.20/0.53          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.53  thf('17', plain,
% 0.20/0.53      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf('18', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['14', '17'])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      ((r2_hidden @ (sk_C_1 @ (k2_relat_1 @ sk_C_2) @ sk_B) @ sk_B)),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['13', '18'])).
% 0.20/0.53  thf(t7_ordinal1, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      (![X9 : $i, X10 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X9 @ X10) | ~ (r1_tarski @ X10 @ X9))),
% 0.20/0.53      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (~ (r1_tarski @ sk_B @ (sk_C_1 @ (k2_relat_1 @ sk_C_2) @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      ((r2_hidden @ (sk_C_1 @ (k2_relat_1 @ sk_C_2) @ sk_B) @ sk_B)),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['13', '18'])).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (![X24 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X24 @ sk_B) | (r2_hidden @ (sk_E @ X24) @ sk_A))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('24', plain,
% 0.20/0.53      ((r2_hidden @ (sk_E @ (sk_C_1 @ (k2_relat_1 @ sk_C_2) @ sk_B)) @ sk_A)),
% 0.20/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(t6_funct_2, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.53         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.53       ( ( r2_hidden @ C @ A ) =>
% 0.20/0.53         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.53           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X20 @ X21)
% 0.20/0.53          | ((X22) = (k1_xboole_0))
% 0.20/0.53          | ~ (v1_funct_1 @ X23)
% 0.20/0.53          | ~ (v1_funct_2 @ X23 @ X21 @ X22)
% 0.20/0.53          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.20/0.53          | (r2_hidden @ (k1_funct_1 @ X23 @ X20) @ 
% 0.20/0.53             (k2_relset_1 @ X21 @ X22 @ X23)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t6_funct_2])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ 
% 0.20/0.53           (k2_relset_1 @ sk_A @ sk_B @ sk_C_2))
% 0.20/0.53          | ~ (v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)
% 0.20/0.53          | ~ (v1_funct_1 @ sk_C_2)
% 0.20/0.53          | ((sk_B) = (k1_xboole_0))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.53      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.53  thf('28', plain,
% 0.20/0.53      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.53  thf('29', plain, ((v1_funct_2 @ sk_C_2 @ sk_A @ sk_B)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('30', plain, ((v1_funct_1 @ sk_C_2)),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((r2_hidden @ (k1_funct_1 @ sk_C_2 @ X0) @ (k2_relat_1 @ sk_C_2))
% 0.20/0.53          | ((sk_B) = (k1_xboole_0))
% 0.20/0.53          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['27', '28', '29', '30'])).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      ((((sk_B) = (k1_xboole_0))
% 0.20/0.53        | (r2_hidden @ 
% 0.20/0.53           (k1_funct_1 @ sk_C_2 @ 
% 0.20/0.53            (sk_E @ (sk_C_1 @ (k2_relat_1 @ sk_C_2) @ sk_B))) @ 
% 0.20/0.53           (k2_relat_1 @ sk_C_2)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['24', '31'])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      ((r2_hidden @ (sk_C_1 @ (k2_relat_1 @ sk_C_2) @ sk_B) @ sk_B)),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['13', '18'])).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (![X24 : $i]:
% 0.20/0.53         (~ (r2_hidden @ X24 @ sk_B)
% 0.20/0.53          | ((X24) = (k1_funct_1 @ sk_C_2 @ (sk_E @ X24))))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('35', plain,
% 0.20/0.53      (((sk_C_1 @ (k2_relat_1 @ sk_C_2) @ sk_B)
% 0.20/0.53         = (k1_funct_1 @ sk_C_2 @ 
% 0.20/0.53            (sk_E @ (sk_C_1 @ (k2_relat_1 @ sk_C_2) @ sk_B))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.53  thf('36', plain,
% 0.20/0.53      ((((sk_B) = (k1_xboole_0))
% 0.20/0.53        | (r2_hidden @ (sk_C_1 @ (k2_relat_1 @ sk_C_2) @ sk_B) @ 
% 0.20/0.53           (k2_relat_1 @ sk_C_2)))),
% 0.20/0.53      inference('demod', [status(thm)], ['32', '35'])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      (![X4 : $i, X5 : $i]:
% 0.20/0.53         (((X5) = (X4))
% 0.20/0.53          | ~ (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X4)
% 0.20/0.53          | ~ (r2_hidden @ (sk_C_1 @ X4 @ X5) @ X5))),
% 0.20/0.53      inference('cnf', [status(esa)], [t2_tarski])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      ((((sk_B) = (k1_xboole_0))
% 0.20/0.53        | ~ (r2_hidden @ (sk_C_1 @ (k2_relat_1 @ sk_C_2) @ sk_B) @ sk_B)
% 0.20/0.53        | ((sk_B) = (k2_relat_1 @ sk_C_2)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['36', '37'])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      ((r2_hidden @ (sk_C_1 @ (k2_relat_1 @ sk_C_2) @ sk_B) @ sk_B)),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['13', '18'])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      ((((sk_B) = (k1_xboole_0)) | ((sk_B) = (k2_relat_1 @ sk_C_2)))),
% 0.20/0.53      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.53  thf('41', plain, (((k2_relat_1 @ sk_C_2) != (sk_B))),
% 0.20/0.53      inference('demod', [status(thm)], ['14', '17'])).
% 0.20/0.53  thf('42', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.20/0.53  thf('43', plain, (((sk_B) = (k1_xboole_0))),
% 0.20/0.53      inference('simplify_reflect-', [status(thm)], ['40', '41'])).
% 0.20/0.53  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.20/0.53  thf('44', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.20/0.53      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.20/0.53  thf('45', plain, ($false),
% 0.20/0.53      inference('demod', [status(thm)], ['21', '42', '43', '44'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
