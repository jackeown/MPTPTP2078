%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QZDSNvWygN

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:38 EST 2020

% Result     : Theorem 0.24s
% Output     : Refutation 0.24s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 139 expanded)
%              Number of leaves         :   28 (  54 expanded)
%              Depth                    :   14
%              Number of atoms          :  481 (1806 expanded)
%              Number of equality atoms :   12 (  53 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(t115_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
            & ! [F: $i] :
                ~ ( ( r2_hidden @ F @ A )
                  & ( r2_hidden @ F @ C )
                  & ( E
                    = ( k1_funct_1 @ D @ F ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
              & ! [F: $i] :
                  ~ ( ( r2_hidden @ F @ A )
                    & ( r2_hidden @ F @ C )
                    & ( E
                      = ( k1_funct_1 @ D @ F ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t115_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( ( k7_relset_1 @ X24 @ X25 @ X23 @ X26 )
        = ( k9_relat_1 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('5',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k9_relat_1 @ X16 @ X14 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X16 @ X14 @ X15 ) @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('9',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['6','9'])).

thf('15',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('16',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( m1_subset_1 @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('19',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('20',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('21',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X27: $i] :
      ( ~ ( r2_hidden @ X27 @ sk_A )
      | ~ ( r2_hidden @ X27 @ sk_C )
      | ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['6','9'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('26',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X17 @ X19 ) @ X18 )
      | ( X19
        = ( k1_funct_1 @ X18 @ X17 ) )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('29',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('32',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k9_relat_1 @ X16 @ X14 ) )
      | ( r2_hidden @ ( sk_D @ X16 @ X14 @ X15 ) @ X14 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('35',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( sk_E != sk_E ) ),
    inference(demod,[status(thm)],['24','30','35'])).

thf('37',plain,(
    v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['13','37'])).

thf('39',plain,(
    $false ),
    inference('sup-',[status(thm)],['10','38'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QZDSNvWygN
% 0.14/0.37  % Computer   : n007.cluster.edu
% 0.14/0.37  % Model      : x86_64 x86_64
% 0.14/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.37  % Memory     : 8042.1875MB
% 0.14/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.37  % CPULimit   : 60
% 0.14/0.37  % DateTime   : Tue Dec  1 13:33:06 EST 2020
% 0.14/0.37  % CPUTime    : 
% 0.14/0.37  % Running portfolio for 600 s
% 0.14/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.38  % Number of cores: 8
% 0.14/0.38  % Python version: Python 3.6.8
% 0.14/0.38  % Running in FO mode
% 0.24/0.53  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.24/0.53  % Solved by: fo/fo7.sh
% 0.24/0.53  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.24/0.53  % done 78 iterations in 0.045s
% 0.24/0.53  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.24/0.53  % SZS output start Refutation
% 0.24/0.53  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.24/0.53  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.24/0.53  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.24/0.53  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.24/0.53  thf(sk_E_type, type, sk_E: $i).
% 0.24/0.53  thf(sk_C_type, type, sk_C: $i).
% 0.24/0.53  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.24/0.53  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.24/0.53  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.24/0.53  thf(sk_B_type, type, sk_B: $i).
% 0.24/0.53  thf(sk_A_type, type, sk_A: $i).
% 0.24/0.53  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.24/0.53  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.24/0.53  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.24/0.53  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.24/0.53  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.24/0.53  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.24/0.53  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.24/0.53  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.24/0.53  thf(t115_funct_2, conjecture,
% 0.24/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.53     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.24/0.53         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.24/0.53       ( ![E:$i]:
% 0.24/0.53         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.24/0.53              ( ![F:$i]:
% 0.24/0.53                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.24/0.53                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.24/0.53  thf(zf_stmt_0, negated_conjecture,
% 0.24/0.53    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.53        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.24/0.53            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.24/0.53          ( ![E:$i]:
% 0.24/0.53            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.24/0.53                 ( ![F:$i]:
% 0.24/0.53                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.24/0.53                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 0.24/0.53    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 0.24/0.53  thf('0', plain,
% 0.24/0.53      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('1', plain,
% 0.24/0.53      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf(redefinition_k7_relset_1, axiom,
% 0.24/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.53       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.24/0.53  thf('2', plain,
% 0.24/0.53      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.24/0.53         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.24/0.53          | ((k7_relset_1 @ X24 @ X25 @ X23 @ X26) = (k9_relat_1 @ X23 @ X26)))),
% 0.24/0.53      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.24/0.53  thf('3', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.24/0.53           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.24/0.53      inference('sup-', [status(thm)], ['1', '2'])).
% 0.24/0.53  thf('4', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.24/0.53      inference('demod', [status(thm)], ['0', '3'])).
% 0.24/0.53  thf(t143_relat_1, axiom,
% 0.24/0.53    (![A:$i,B:$i,C:$i]:
% 0.24/0.53     ( ( v1_relat_1 @ C ) =>
% 0.24/0.53       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.24/0.53         ( ?[D:$i]:
% 0.24/0.53           ( ( r2_hidden @ D @ B ) & 
% 0.24/0.53             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.24/0.53             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.24/0.53  thf('5', plain,
% 0.24/0.53      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.24/0.53         (~ (r2_hidden @ X15 @ (k9_relat_1 @ X16 @ X14))
% 0.24/0.53          | (r2_hidden @ (k4_tarski @ (sk_D @ X16 @ X14 @ X15) @ X15) @ X16)
% 0.24/0.53          | ~ (v1_relat_1 @ X16))),
% 0.24/0.53      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.24/0.53  thf('6', plain,
% 0.24/0.53      ((~ (v1_relat_1 @ sk_D_1)
% 0.24/0.53        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ 
% 0.24/0.53           sk_D_1))),
% 0.24/0.53      inference('sup-', [status(thm)], ['4', '5'])).
% 0.24/0.53  thf('7', plain,
% 0.24/0.53      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf(cc1_relset_1, axiom,
% 0.24/0.53    (![A:$i,B:$i,C:$i]:
% 0.24/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.24/0.53       ( v1_relat_1 @ C ) ))).
% 0.24/0.53  thf('8', plain,
% 0.24/0.53      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.24/0.53         ((v1_relat_1 @ X20)
% 0.24/0.53          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.24/0.53      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.24/0.53  thf('9', plain, ((v1_relat_1 @ sk_D_1)),
% 0.24/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.24/0.53  thf('10', plain,
% 0.24/0.53      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ sk_D_1)),
% 0.24/0.53      inference('demod', [status(thm)], ['6', '9'])).
% 0.24/0.53  thf('11', plain,
% 0.24/0.53      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf(t5_subset, axiom,
% 0.24/0.53    (![A:$i,B:$i,C:$i]:
% 0.24/0.53     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.24/0.53          ( v1_xboole_0 @ C ) ) ))).
% 0.24/0.53  thf('12', plain,
% 0.24/0.53      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.24/0.53         (~ (r2_hidden @ X10 @ X11)
% 0.24/0.53          | ~ (v1_xboole_0 @ X12)
% 0.24/0.53          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.24/0.53      inference('cnf', [status(esa)], [t5_subset])).
% 0.24/0.53  thf('13', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.24/0.53          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.24/0.53      inference('sup-', [status(thm)], ['11', '12'])).
% 0.24/0.53  thf('14', plain,
% 0.24/0.53      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ sk_D_1)),
% 0.24/0.53      inference('demod', [status(thm)], ['6', '9'])).
% 0.24/0.53  thf('15', plain,
% 0.24/0.53      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf(t4_subset, axiom,
% 0.24/0.53    (![A:$i,B:$i,C:$i]:
% 0.24/0.53     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.24/0.53       ( m1_subset_1 @ A @ C ) ))).
% 0.24/0.53  thf('16', plain,
% 0.24/0.53      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.24/0.53         (~ (r2_hidden @ X7 @ X8)
% 0.24/0.53          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.24/0.53          | (m1_subset_1 @ X7 @ X9))),
% 0.24/0.53      inference('cnf', [status(esa)], [t4_subset])).
% 0.24/0.53  thf('17', plain,
% 0.24/0.53      (![X0 : $i]:
% 0.24/0.53         ((m1_subset_1 @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.24/0.53          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.24/0.53      inference('sup-', [status(thm)], ['15', '16'])).
% 0.24/0.53  thf('18', plain,
% 0.24/0.53      ((m1_subset_1 @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ 
% 0.24/0.53        (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.24/0.53      inference('sup-', [status(thm)], ['14', '17'])).
% 0.24/0.53  thf(t2_subset, axiom,
% 0.24/0.53    (![A:$i,B:$i]:
% 0.24/0.53     ( ( m1_subset_1 @ A @ B ) =>
% 0.24/0.53       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.24/0.53  thf('19', plain,
% 0.24/0.53      (![X5 : $i, X6 : $i]:
% 0.24/0.53         ((r2_hidden @ X5 @ X6)
% 0.24/0.53          | (v1_xboole_0 @ X6)
% 0.24/0.53          | ~ (m1_subset_1 @ X5 @ X6))),
% 0.24/0.53      inference('cnf', [status(esa)], [t2_subset])).
% 0.24/0.53  thf('20', plain,
% 0.24/0.53      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.24/0.53        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ 
% 0.24/0.53           (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.24/0.53      inference('sup-', [status(thm)], ['18', '19'])).
% 0.24/0.53  thf(l54_zfmisc_1, axiom,
% 0.24/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.24/0.53     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.24/0.53       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.24/0.53  thf('21', plain,
% 0.24/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.24/0.53         ((r2_hidden @ X0 @ X1)
% 0.24/0.53          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 0.24/0.53      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.24/0.53  thf('22', plain,
% 0.24/0.53      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.24/0.53        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_A))),
% 0.24/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.24/0.53  thf('23', plain,
% 0.24/0.53      (![X27 : $i]:
% 0.24/0.53         (~ (r2_hidden @ X27 @ sk_A)
% 0.24/0.53          | ~ (r2_hidden @ X27 @ sk_C)
% 0.24/0.53          | ((sk_E) != (k1_funct_1 @ sk_D_1 @ X27)))),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('24', plain,
% 0.24/0.53      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.24/0.53        | ((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E)))
% 0.24/0.53        | ~ (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C))),
% 0.24/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.24/0.53  thf('25', plain,
% 0.24/0.53      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ sk_D_1)),
% 0.24/0.53      inference('demod', [status(thm)], ['6', '9'])).
% 0.24/0.53  thf(t8_funct_1, axiom,
% 0.24/0.53    (![A:$i,B:$i,C:$i]:
% 0.24/0.53     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.24/0.53       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.24/0.53         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.24/0.53           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.24/0.53  thf('26', plain,
% 0.24/0.53      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.24/0.53         (~ (r2_hidden @ (k4_tarski @ X17 @ X19) @ X18)
% 0.24/0.53          | ((X19) = (k1_funct_1 @ X18 @ X17))
% 0.24/0.53          | ~ (v1_funct_1 @ X18)
% 0.24/0.53          | ~ (v1_relat_1 @ X18))),
% 0.24/0.53      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.24/0.53  thf('27', plain,
% 0.24/0.53      ((~ (v1_relat_1 @ sk_D_1)
% 0.24/0.53        | ~ (v1_funct_1 @ sk_D_1)
% 0.24/0.53        | ((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E))))),
% 0.24/0.53      inference('sup-', [status(thm)], ['25', '26'])).
% 0.24/0.53  thf('28', plain, ((v1_relat_1 @ sk_D_1)),
% 0.24/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.24/0.53  thf('29', plain, ((v1_funct_1 @ sk_D_1)),
% 0.24/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.24/0.53  thf('30', plain,
% 0.24/0.53      (((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E)))),
% 0.24/0.53      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.24/0.53  thf('31', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.24/0.53      inference('demod', [status(thm)], ['0', '3'])).
% 0.24/0.53  thf('32', plain,
% 0.24/0.53      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.24/0.53         (~ (r2_hidden @ X15 @ (k9_relat_1 @ X16 @ X14))
% 0.24/0.53          | (r2_hidden @ (sk_D @ X16 @ X14 @ X15) @ X14)
% 0.24/0.53          | ~ (v1_relat_1 @ X16))),
% 0.24/0.53      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.24/0.53  thf('33', plain,
% 0.24/0.53      ((~ (v1_relat_1 @ sk_D_1)
% 0.24/0.53        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C))),
% 0.24/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.24/0.53  thf('34', plain, ((v1_relat_1 @ sk_D_1)),
% 0.24/0.53      inference('sup-', [status(thm)], ['7', '8'])).
% 0.24/0.53  thf('35', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C)),
% 0.24/0.53      inference('demod', [status(thm)], ['33', '34'])).
% 0.24/0.53  thf('36', plain,
% 0.24/0.53      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | ((sk_E) != (sk_E)))),
% 0.24/0.53      inference('demod', [status(thm)], ['24', '30', '35'])).
% 0.24/0.53  thf('37', plain, ((v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.24/0.53      inference('simplify', [status(thm)], ['36'])).
% 0.24/0.53  thf('38', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D_1)),
% 0.24/0.53      inference('demod', [status(thm)], ['13', '37'])).
% 0.24/0.53  thf('39', plain, ($false), inference('sup-', [status(thm)], ['10', '38'])).
% 0.24/0.53  
% 0.24/0.53  % SZS output end Refutation
% 0.24/0.53  
% 0.24/0.54  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
