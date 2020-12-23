%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7VkfhshuVz

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:44 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.70s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 111 expanded)
%              Number of leaves         :   26 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :  423 (1383 expanded)
%              Number of equality atoms :   12 (  42 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(t116_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
            & ! [F: $i] :
                ( ( m1_subset_1 @ F @ A )
               => ~ ( ( r2_hidden @ F @ C )
                    & ( E
                      = ( k1_funct_1 @ D @ F ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
              & ! [F: $i] :
                  ( ( m1_subset_1 @ F @ A )
                 => ~ ( ( r2_hidden @ F @ C )
                      & ( E
                        = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t116_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X68: $i,X69: $i,X70: $i,X71: $i] :
      ( ~ ( m1_subset_1 @ X68 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X69 @ X70 ) ) )
      | ( ( k7_relset_1 @ X69 @ X70 @ X68 @ X71 )
        = ( k9_relat_1 @ X68 @ X71 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C_2 ) ),
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
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X39 @ ( k9_relat_1 @ X40 @ X38 ) )
      | ( r2_hidden @ ( sk_D @ X40 @ X38 @ X39 ) @ X38 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('8',plain,(
    ! [X56: $i,X57: $i,X58: $i] :
      ( ( v1_relat_1 @ X56 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X57 @ X58 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('9',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) @ sk_C_2 ),
    inference(demod,[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X91: $i] :
      ( ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ X91 ) )
      | ~ ( r2_hidden @ X91 @ sk_C_2 )
      | ~ ( m1_subset_1 @ X91 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) @ sk_A )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('14',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X39 @ ( k9_relat_1 @ X40 @ X38 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X40 @ X38 @ X39 ) @ X39 ) @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) @ sk_E ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('17',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('18',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X52 @ X54 ) @ X53 )
      | ( X54
        = ( k1_funct_1 @ X53 @ X52 ) )
      | ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_relat_1 @ X53 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('19',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('21',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) @ sk_A )
    | ( sk_E != sk_E ) ),
    inference(demod,[status(thm)],['12','22'])).

thf('24',plain,(
    ~ ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) @ sk_A ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('26',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('27',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ( r2_hidden @ X22 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_2 ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf(t106_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('30',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ ( k2_zfmisc_1 @ X11 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('31',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) @ sk_A ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('32',plain,(
    ! [X29: $i,X30: $i] :
      ( ( m1_subset_1 @ X29 @ X30 )
      | ~ ( r2_hidden @ X29 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('33',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_C_2 @ sk_E ) @ sk_A ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    $false ),
    inference(demod,[status(thm)],['24','33'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.7VkfhshuVz
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:12:36 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.20/0.35  % Running portfolio for 600 s
% 0.20/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.20/0.35  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.70/0.89  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.70/0.89  % Solved by: fo/fo7.sh
% 0.70/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.89  % done 912 iterations in 0.433s
% 0.70/0.89  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.70/0.89  % SZS output start Refutation
% 0.70/0.89  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.70/0.89  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.70/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.89  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.70/0.89  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.70/0.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.70/0.89  thf(sk_E_type, type, sk_E: $i).
% 0.70/0.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.70/0.89  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.70/0.89  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.70/0.89  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.70/0.89  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.70/0.89  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.70/0.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.70/0.89  thf(sk_B_2_type, type, sk_B_2: $i).
% 0.70/0.89  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.70/0.89  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.70/0.89  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.70/0.89  thf(t116_funct_2, conjecture,
% 0.70/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.70/0.89     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.70/0.89         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.70/0.89       ( ![E:$i]:
% 0.70/0.89         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.70/0.89              ( ![F:$i]:
% 0.70/0.89                ( ( m1_subset_1 @ F @ A ) =>
% 0.70/0.89                  ( ~( ( r2_hidden @ F @ C ) & 
% 0.70/0.89                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 0.70/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.89    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.70/0.89        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.70/0.89            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.70/0.89          ( ![E:$i]:
% 0.70/0.89            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.70/0.89                 ( ![F:$i]:
% 0.70/0.89                   ( ( m1_subset_1 @ F @ A ) =>
% 0.70/0.89                     ( ~( ( r2_hidden @ F @ C ) & 
% 0.70/0.89                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.70/0.89    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 0.70/0.89  thf('0', plain,
% 0.70/0.89      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ sk_C_2))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('1', plain,
% 0.70/0.89      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf(redefinition_k7_relset_1, axiom,
% 0.70/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.70/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.89       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.70/0.89  thf('2', plain,
% 0.70/0.89      (![X68 : $i, X69 : $i, X70 : $i, X71 : $i]:
% 0.70/0.89         (~ (m1_subset_1 @ X68 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X69 @ X70)))
% 0.70/0.89          | ((k7_relset_1 @ X69 @ X70 @ X68 @ X71) = (k9_relat_1 @ X68 @ X71)))),
% 0.70/0.89      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.70/0.89  thf('3', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((k7_relset_1 @ sk_A @ sk_B_2 @ sk_D_1 @ X0)
% 0.70/0.89           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['1', '2'])).
% 0.70/0.89  thf('4', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_2))),
% 0.70/0.89      inference('demod', [status(thm)], ['0', '3'])).
% 0.70/0.89  thf(t143_relat_1, axiom,
% 0.70/0.89    (![A:$i,B:$i,C:$i]:
% 0.70/0.89     ( ( v1_relat_1 @ C ) =>
% 0.70/0.89       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.70/0.89         ( ?[D:$i]:
% 0.70/0.89           ( ( r2_hidden @ D @ B ) & 
% 0.70/0.89             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.70/0.89             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.70/0.89  thf('5', plain,
% 0.70/0.89      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.70/0.89         (~ (r2_hidden @ X39 @ (k9_relat_1 @ X40 @ X38))
% 0.70/0.89          | (r2_hidden @ (sk_D @ X40 @ X38 @ X39) @ X38)
% 0.70/0.89          | ~ (v1_relat_1 @ X40))),
% 0.70/0.89      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.70/0.89  thf('6', plain,
% 0.70/0.89      ((~ (v1_relat_1 @ sk_D_1)
% 0.70/0.89        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_C_2))),
% 0.70/0.89      inference('sup-', [status(thm)], ['4', '5'])).
% 0.70/0.89  thf('7', plain,
% 0.70/0.89      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf(cc1_relset_1, axiom,
% 0.70/0.89    (![A:$i,B:$i,C:$i]:
% 0.70/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.89       ( v1_relat_1 @ C ) ))).
% 0.70/0.89  thf('8', plain,
% 0.70/0.89      (![X56 : $i, X57 : $i, X58 : $i]:
% 0.70/0.89         ((v1_relat_1 @ X56)
% 0.70/0.89          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X57 @ X58))))),
% 0.70/0.89      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.70/0.89  thf('9', plain, ((v1_relat_1 @ sk_D_1)),
% 0.70/0.89      inference('sup-', [status(thm)], ['7', '8'])).
% 0.70/0.89  thf('10', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_C_2)),
% 0.70/0.89      inference('demod', [status(thm)], ['6', '9'])).
% 0.70/0.89  thf('11', plain,
% 0.70/0.89      (![X91 : $i]:
% 0.70/0.89         (((sk_E) != (k1_funct_1 @ sk_D_1 @ X91))
% 0.70/0.89          | ~ (r2_hidden @ X91 @ sk_C_2)
% 0.70/0.89          | ~ (m1_subset_1 @ X91 @ sk_A))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('12', plain,
% 0.70/0.89      ((~ (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_A)
% 0.70/0.89        | ((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E))))),
% 0.70/0.89      inference('sup-', [status(thm)], ['10', '11'])).
% 0.70/0.89  thf('13', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C_2))),
% 0.70/0.89      inference('demod', [status(thm)], ['0', '3'])).
% 0.70/0.89  thf('14', plain,
% 0.70/0.89      (![X38 : $i, X39 : $i, X40 : $i]:
% 0.70/0.89         (~ (r2_hidden @ X39 @ (k9_relat_1 @ X40 @ X38))
% 0.70/0.89          | (r2_hidden @ (k4_tarski @ (sk_D @ X40 @ X38 @ X39) @ X39) @ X40)
% 0.70/0.89          | ~ (v1_relat_1 @ X40))),
% 0.70/0.89      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.70/0.89  thf('15', plain,
% 0.70/0.89      ((~ (v1_relat_1 @ sk_D_1)
% 0.70/0.89        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_E) @ 
% 0.70/0.89           sk_D_1))),
% 0.70/0.89      inference('sup-', [status(thm)], ['13', '14'])).
% 0.70/0.89  thf('16', plain, ((v1_relat_1 @ sk_D_1)),
% 0.70/0.89      inference('sup-', [status(thm)], ['7', '8'])).
% 0.70/0.89  thf('17', plain,
% 0.70/0.89      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_E) @ 
% 0.70/0.89        sk_D_1)),
% 0.70/0.89      inference('demod', [status(thm)], ['15', '16'])).
% 0.70/0.89  thf(t8_funct_1, axiom,
% 0.70/0.89    (![A:$i,B:$i,C:$i]:
% 0.70/0.89     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.70/0.89       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.70/0.89         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.70/0.89           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.70/0.89  thf('18', plain,
% 0.70/0.89      (![X52 : $i, X53 : $i, X54 : $i]:
% 0.70/0.89         (~ (r2_hidden @ (k4_tarski @ X52 @ X54) @ X53)
% 0.70/0.89          | ((X54) = (k1_funct_1 @ X53 @ X52))
% 0.70/0.89          | ~ (v1_funct_1 @ X53)
% 0.70/0.89          | ~ (v1_relat_1 @ X53))),
% 0.70/0.89      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.70/0.89  thf('19', plain,
% 0.70/0.89      ((~ (v1_relat_1 @ sk_D_1)
% 0.70/0.89        | ~ (v1_funct_1 @ sk_D_1)
% 0.70/0.89        | ((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E))))),
% 0.70/0.89      inference('sup-', [status(thm)], ['17', '18'])).
% 0.70/0.89  thf('20', plain, ((v1_relat_1 @ sk_D_1)),
% 0.70/0.89      inference('sup-', [status(thm)], ['7', '8'])).
% 0.70/0.89  thf('21', plain, ((v1_funct_1 @ sk_D_1)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('22', plain,
% 0.70/0.89      (((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E)))),
% 0.70/0.89      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.70/0.89  thf('23', plain,
% 0.70/0.89      ((~ (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_A)
% 0.70/0.89        | ((sk_E) != (sk_E)))),
% 0.70/0.89      inference('demod', [status(thm)], ['12', '22'])).
% 0.70/0.89  thf('24', plain, (~ (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_A)),
% 0.70/0.89      inference('simplify', [status(thm)], ['23'])).
% 0.70/0.89  thf('25', plain,
% 0.70/0.89      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_E) @ 
% 0.70/0.89        sk_D_1)),
% 0.70/0.89      inference('demod', [status(thm)], ['15', '16'])).
% 0.70/0.89  thf('26', plain,
% 0.70/0.89      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_2)))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf(l3_subset_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.70/0.89       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.70/0.89  thf('27', plain,
% 0.70/0.89      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.70/0.89         (~ (r2_hidden @ X22 @ X23)
% 0.70/0.89          | (r2_hidden @ X22 @ X24)
% 0.70/0.89          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ X24)))),
% 0.70/0.89      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.70/0.89  thf('28', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B_2))
% 0.70/0.89          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.70/0.89      inference('sup-', [status(thm)], ['26', '27'])).
% 0.70/0.89  thf('29', plain,
% 0.70/0.89      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_E) @ 
% 0.70/0.89        (k2_zfmisc_1 @ sk_A @ sk_B_2))),
% 0.70/0.89      inference('sup-', [status(thm)], ['25', '28'])).
% 0.70/0.89  thf(t106_zfmisc_1, axiom,
% 0.70/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.70/0.89     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.70/0.89       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.70/0.89  thf('30', plain,
% 0.70/0.89      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.70/0.89         ((r2_hidden @ X10 @ X11)
% 0.70/0.89          | ~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ (k2_zfmisc_1 @ X11 @ X13)))),
% 0.70/0.89      inference('cnf', [status(esa)], [t106_zfmisc_1])).
% 0.70/0.89  thf('31', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_A)),
% 0.70/0.89      inference('sup-', [status(thm)], ['29', '30'])).
% 0.70/0.89  thf(t1_subset, axiom,
% 0.70/0.89    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.70/0.89  thf('32', plain,
% 0.70/0.89      (![X29 : $i, X30 : $i]:
% 0.70/0.89         ((m1_subset_1 @ X29 @ X30) | ~ (r2_hidden @ X29 @ X30))),
% 0.70/0.89      inference('cnf', [status(esa)], [t1_subset])).
% 0.70/0.89  thf('33', plain, ((m1_subset_1 @ (sk_D @ sk_D_1 @ sk_C_2 @ sk_E) @ sk_A)),
% 0.70/0.89      inference('sup-', [status(thm)], ['31', '32'])).
% 0.70/0.89  thf('34', plain, ($false), inference('demod', [status(thm)], ['24', '33'])).
% 0.70/0.89  
% 0.70/0.89  % SZS output end Refutation
% 0.70/0.89  
% 0.70/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
