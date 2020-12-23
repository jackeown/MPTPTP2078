%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8VF6ZsFrMJ

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 127 expanded)
%              Number of leaves         :   29 (  52 expanded)
%              Depth                    :   11
%              Number of atoms          :  468 (1560 expanded)
%              Number of equality atoms :   16 (  50 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

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
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( ( k7_relset_1 @ X19 @ X20 @ X18 @ X21 )
        = ( k9_relat_1 @ X18 @ X21 ) ) ) ),
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
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k9_relat_1 @ X3 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X1 @ X2 ) @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v1_relat_1 @ X12 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('9',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
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

thf('11',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X9 @ X11 ) @ X10 )
      | ( X11
        = ( k1_funct_1 @ X10 @ X9 ) )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('14',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('17',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k9_relat_1 @ X3 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X3 @ X1 @ X2 ) @ ( k1_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('20',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('22',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v4_relat_1 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('23',plain,(
    v4_relat_1 @ sk_D_1 @ sk_A ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X4: $i,X5: $i] :
      ( ( X4
        = ( k7_relat_1 @ X4 @ X5 ) )
      | ~ ( v4_relat_1 @ X4 @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( sk_D_1
      = ( k7_relat_1 @ sk_D_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('27',plain,
    ( sk_D_1
    = ( k7_relat_1 @ sk_D_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','26'])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('28',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k1_relat_1 @ ( k7_relat_1 @ X8 @ X7 ) ) )
      | ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_A ),
    inference('sup-',[status(thm)],['20','31'])).

thf('33',plain,(
    ! [X22: $i] :
      ( ~ ( r2_hidden @ X22 @ sk_A )
      | ~ ( r2_hidden @ X22 @ sk_C )
      | ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('36',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k9_relat_1 @ X3 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X3 @ X1 @ X2 ) @ X1 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('39',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    sk_E
 != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['34','39'])).

thf('41',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['15','40'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8VF6ZsFrMJ
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:39:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.47  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.47  % Solved by: fo/fo7.sh
% 0.22/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.47  % done 32 iterations in 0.018s
% 0.22/0.47  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.47  % SZS output start Refutation
% 0.22/0.47  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.47  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.47  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.22/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.47  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.47  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.22/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.47  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.47  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.47  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.47  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.47  thf(t115_funct_2, conjecture,
% 0.22/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.47     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.47         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.47       ( ![E:$i]:
% 0.22/0.47         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.22/0.47              ( ![F:$i]:
% 0.22/0.47                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.22/0.47                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.22/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.47    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.47        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.47            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.47          ( ![E:$i]:
% 0.22/0.47            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.22/0.47                 ( ![F:$i]:
% 0.22/0.47                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.22/0.47                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 0.22/0.47    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 0.22/0.47  thf('0', plain,
% 0.22/0.47      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('1', plain,
% 0.22/0.47      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(redefinition_k7_relset_1, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.47       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.22/0.47  thf('2', plain,
% 0.22/0.47      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.22/0.47         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.22/0.47          | ((k7_relset_1 @ X19 @ X20 @ X18 @ X21) = (k9_relat_1 @ X18 @ X21)))),
% 0.22/0.47      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.22/0.47  thf('3', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.22/0.47           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.22/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.47  thf('4', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.22/0.47      inference('demod', [status(thm)], ['0', '3'])).
% 0.22/0.47  thf(t143_relat_1, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ C ) =>
% 0.22/0.47       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.22/0.47         ( ?[D:$i]:
% 0.22/0.47           ( ( r2_hidden @ D @ B ) & 
% 0.22/0.47             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.22/0.47             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.22/0.47  thf('5', plain,
% 0.22/0.47      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.47         (~ (r2_hidden @ X2 @ (k9_relat_1 @ X3 @ X1))
% 0.22/0.47          | (r2_hidden @ (k4_tarski @ (sk_D @ X3 @ X1 @ X2) @ X2) @ X3)
% 0.22/0.47          | ~ (v1_relat_1 @ X3))),
% 0.22/0.47      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.22/0.47  thf('6', plain,
% 0.22/0.47      ((~ (v1_relat_1 @ sk_D_1)
% 0.22/0.47        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ 
% 0.22/0.47           sk_D_1))),
% 0.22/0.47      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.47  thf('7', plain,
% 0.22/0.47      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(cc1_relset_1, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i]:
% 0.22/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.47       ( v1_relat_1 @ C ) ))).
% 0.22/0.47  thf('8', plain,
% 0.22/0.47      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.47         ((v1_relat_1 @ X12)
% 0.22/0.47          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.22/0.47      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.47  thf('9', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.47  thf('10', plain,
% 0.22/0.47      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ sk_D_1)),
% 0.22/0.47      inference('demod', [status(thm)], ['6', '9'])).
% 0.22/0.47  thf(t8_funct_1, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i]:
% 0.22/0.47     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.47       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.22/0.47         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.22/0.47           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.22/0.47  thf('11', plain,
% 0.22/0.47      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.22/0.47         (~ (r2_hidden @ (k4_tarski @ X9 @ X11) @ X10)
% 0.22/0.47          | ((X11) = (k1_funct_1 @ X10 @ X9))
% 0.22/0.47          | ~ (v1_funct_1 @ X10)
% 0.22/0.47          | ~ (v1_relat_1 @ X10))),
% 0.22/0.47      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.22/0.47  thf('12', plain,
% 0.22/0.47      ((~ (v1_relat_1 @ sk_D_1)
% 0.22/0.47        | ~ (v1_funct_1 @ sk_D_1)
% 0.22/0.47        | ((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E))))),
% 0.22/0.47      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.47  thf('13', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.47  thf('14', plain, ((v1_funct_1 @ sk_D_1)),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('15', plain,
% 0.22/0.47      (((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E)))),
% 0.22/0.47      inference('demod', [status(thm)], ['12', '13', '14'])).
% 0.22/0.47  thf('16', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.22/0.47      inference('demod', [status(thm)], ['0', '3'])).
% 0.22/0.47  thf('17', plain,
% 0.22/0.47      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.47         (~ (r2_hidden @ X2 @ (k9_relat_1 @ X3 @ X1))
% 0.22/0.47          | (r2_hidden @ (sk_D @ X3 @ X1 @ X2) @ (k1_relat_1 @ X3))
% 0.22/0.47          | ~ (v1_relat_1 @ X3))),
% 0.22/0.47      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.22/0.47  thf('18', plain,
% 0.22/0.47      ((~ (v1_relat_1 @ sk_D_1)
% 0.22/0.47        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['16', '17'])).
% 0.22/0.47  thf('19', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.47  thf('20', plain,
% 0.22/0.47      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.22/0.47      inference('demod', [status(thm)], ['18', '19'])).
% 0.22/0.47  thf('21', plain,
% 0.22/0.47      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf(cc2_relset_1, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i]:
% 0.22/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.47       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.47  thf('22', plain,
% 0.22/0.47      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.47         ((v4_relat_1 @ X15 @ X16)
% 0.22/0.47          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.22/0.47      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.47  thf('23', plain, ((v4_relat_1 @ sk_D_1 @ sk_A)),
% 0.22/0.47      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.47  thf(t209_relat_1, axiom,
% 0.22/0.47    (![A:$i,B:$i]:
% 0.22/0.47     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.22/0.47       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.22/0.47  thf('24', plain,
% 0.22/0.47      (![X4 : $i, X5 : $i]:
% 0.22/0.47         (((X4) = (k7_relat_1 @ X4 @ X5))
% 0.22/0.47          | ~ (v4_relat_1 @ X4 @ X5)
% 0.22/0.47          | ~ (v1_relat_1 @ X4))),
% 0.22/0.47      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.22/0.47  thf('25', plain,
% 0.22/0.47      ((~ (v1_relat_1 @ sk_D_1) | ((sk_D_1) = (k7_relat_1 @ sk_D_1 @ sk_A)))),
% 0.22/0.47      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.47  thf('26', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.47  thf('27', plain, (((sk_D_1) = (k7_relat_1 @ sk_D_1 @ sk_A))),
% 0.22/0.47      inference('demod', [status(thm)], ['25', '26'])).
% 0.22/0.47  thf(t86_relat_1, axiom,
% 0.22/0.47    (![A:$i,B:$i,C:$i]:
% 0.22/0.47     ( ( v1_relat_1 @ C ) =>
% 0.22/0.47       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 0.22/0.47         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 0.22/0.47  thf('28', plain,
% 0.22/0.47      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.22/0.47         (~ (r2_hidden @ X6 @ (k1_relat_1 @ (k7_relat_1 @ X8 @ X7)))
% 0.22/0.47          | (r2_hidden @ X6 @ X7)
% 0.22/0.47          | ~ (v1_relat_1 @ X8))),
% 0.22/0.47      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.22/0.47  thf('29', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.22/0.47          | ~ (v1_relat_1 @ sk_D_1)
% 0.22/0.47          | (r2_hidden @ X0 @ sk_A))),
% 0.22/0.47      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.47  thf('30', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.47  thf('31', plain,
% 0.22/0.47      (![X0 : $i]:
% 0.22/0.47         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_1)) | (r2_hidden @ X0 @ sk_A))),
% 0.22/0.47      inference('demod', [status(thm)], ['29', '30'])).
% 0.22/0.47  thf('32', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_A)),
% 0.22/0.47      inference('sup-', [status(thm)], ['20', '31'])).
% 0.22/0.47  thf('33', plain,
% 0.22/0.47      (![X22 : $i]:
% 0.22/0.47         (~ (r2_hidden @ X22 @ sk_A)
% 0.22/0.47          | ~ (r2_hidden @ X22 @ sk_C)
% 0.22/0.47          | ((sk_E) != (k1_funct_1 @ sk_D_1 @ X22)))),
% 0.22/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.47  thf('34', plain,
% 0.22/0.47      ((((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E)))
% 0.22/0.47        | ~ (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C))),
% 0.22/0.47      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.47  thf('35', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.22/0.47      inference('demod', [status(thm)], ['0', '3'])).
% 0.22/0.47  thf('36', plain,
% 0.22/0.47      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.47         (~ (r2_hidden @ X2 @ (k9_relat_1 @ X3 @ X1))
% 0.22/0.47          | (r2_hidden @ (sk_D @ X3 @ X1 @ X2) @ X1)
% 0.22/0.47          | ~ (v1_relat_1 @ X3))),
% 0.22/0.47      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.22/0.47  thf('37', plain,
% 0.22/0.47      ((~ (v1_relat_1 @ sk_D_1)
% 0.22/0.47        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C))),
% 0.22/0.47      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.47  thf('38', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.47      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.47  thf('39', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C)),
% 0.22/0.47      inference('demod', [status(thm)], ['37', '38'])).
% 0.22/0.47  thf('40', plain,
% 0.22/0.47      (((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E)))),
% 0.22/0.47      inference('demod', [status(thm)], ['34', '39'])).
% 0.22/0.47  thf('41', plain, ($false),
% 0.22/0.47      inference('simplify_reflect-', [status(thm)], ['15', '40'])).
% 0.22/0.47  
% 0.22/0.47  % SZS output end Refutation
% 0.22/0.47  
% 0.22/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
