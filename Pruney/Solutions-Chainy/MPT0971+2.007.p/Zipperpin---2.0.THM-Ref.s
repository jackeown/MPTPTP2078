%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0gLxGHdXjZ

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 133 expanded)
%              Number of leaves         :   29 (  54 expanded)
%              Depth                    :   13
%              Number of atoms          :  419 (1437 expanded)
%              Number of equality atoms :   20 (  58 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t17_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ~ ( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) )
          & ! [E: $i] :
              ~ ( ( r2_hidden @ E @ A )
                & ( ( k1_funct_1 @ D @ E )
                  = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ~ ( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) )
            & ! [E: $i] :
                ~ ( ( r2_hidden @ E @ A )
                  & ( ( k1_funct_1 @ D @ E )
                    = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_C @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('7',plain,(
    v4_relat_1 @ sk_D_1 @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X6
        = ( k7_relat_1 @ X6 @ X7 ) )
      | ~ ( v4_relat_1 @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( sk_D_1
      = ( k7_relat_1 @ sk_D_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('12',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( sk_D_1
    = ( k7_relat_1 @ sk_D_1 @ sk_A ) ),
    inference(demod,[status(thm)],['9','12'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) )
        = ( k9_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('15',plain,
    ( ( ( k2_relat_1 @ sk_D_1 )
      = ( k9_relat_1 @ sk_D_1 @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('17',plain,
    ( ( k2_relat_1 @ sk_D_1 )
    = ( k9_relat_1 @ sk_D_1 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('18',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k9_relat_1 @ X3 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X1 @ X2 ) @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_1 ) )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_A @ X0 ) @ X0 ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_A @ X0 ) @ X0 ) @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_A @ sk_C ) @ sk_C ) @ sk_D_1 ),
    inference('sup-',[status(thm)],['4','21'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X8 @ X10 ) @ X9 )
      | ( X10
        = ( k1_funct_1 @ X9 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_C
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('26',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( sk_C
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    r2_hidden @ sk_C @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('29',plain,
    ( ( k2_relat_1 @ sk_D_1 )
    = ( k9_relat_1 @ sk_D_1 @ sk_A ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('30',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k9_relat_1 @ X3 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X3 @ X1 @ X2 ) @ X1 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_1 ) )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_A @ X0 ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['10','11'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_1 ) )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_A @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_A @ sk_C ) @ sk_A ),
    inference('sup-',[status(thm)],['28','33'])).

thf('35',plain,(
    ! [X20: $i] :
      ( ~ ( r2_hidden @ X20 @ sk_A )
      | ( ( k1_funct_1 @ sk_D_1 @ X20 )
       != sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_A @ sk_C ) )
 != sk_C ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['27','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.0gLxGHdXjZ
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:15:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.46  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.46  % Solved by: fo/fo7.sh
% 0.20/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.46  % done 33 iterations in 0.018s
% 0.20/0.46  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.46  % SZS output start Refutation
% 0.20/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.46  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.46  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.46  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.46  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.46  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.46  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.46  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.46  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.46  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.46  thf(t17_funct_2, conjecture,
% 0.20/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.46         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.46       ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 0.20/0.46            ( ![E:$i]:
% 0.20/0.46              ( ~( ( r2_hidden @ E @ A ) & ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ))).
% 0.20/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.46    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.46        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.46            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.46          ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 0.20/0.46               ( ![E:$i]:
% 0.20/0.46                 ( ~( ( r2_hidden @ E @ A ) & 
% 0.20/0.46                      ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ) )),
% 0.20/0.46    inference('cnf.neg', [status(esa)], [t17_funct_2])).
% 0.20/0.46  thf('0', plain, ((r2_hidden @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D_1))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('1', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.46       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.46  thf('2', plain,
% 0.20/0.46      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.46         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.20/0.46          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.20/0.46      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.46  thf('3', plain,
% 0.20/0.46      (((k2_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.20/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.46  thf('4', plain, ((r2_hidden @ sk_C @ (k2_relat_1 @ sk_D_1))),
% 0.20/0.46      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.46  thf('5', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(cc2_relset_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.46       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.46  thf('6', plain,
% 0.20/0.46      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.20/0.46         ((v4_relat_1 @ X14 @ X15)
% 0.20/0.46          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.20/0.46      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.46  thf('7', plain, ((v4_relat_1 @ sk_D_1 @ sk_A)),
% 0.20/0.46      inference('sup-', [status(thm)], ['5', '6'])).
% 0.20/0.46  thf(t209_relat_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.46       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.20/0.46  thf('8', plain,
% 0.20/0.46      (![X6 : $i, X7 : $i]:
% 0.20/0.46         (((X6) = (k7_relat_1 @ X6 @ X7))
% 0.20/0.46          | ~ (v4_relat_1 @ X6 @ X7)
% 0.20/0.46          | ~ (v1_relat_1 @ X6))),
% 0.20/0.46      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.20/0.46  thf('9', plain,
% 0.20/0.46      ((~ (v1_relat_1 @ sk_D_1) | ((sk_D_1) = (k7_relat_1 @ sk_D_1 @ sk_A)))),
% 0.20/0.46      inference('sup-', [status(thm)], ['7', '8'])).
% 0.20/0.46  thf('10', plain,
% 0.20/0.46      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf(cc1_relset_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.46       ( v1_relat_1 @ C ) ))).
% 0.20/0.46  thf('11', plain,
% 0.20/0.46      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.20/0.46         ((v1_relat_1 @ X11)
% 0.20/0.46          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.20/0.46      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.46  thf('12', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.46  thf('13', plain, (((sk_D_1) = (k7_relat_1 @ sk_D_1 @ sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['9', '12'])).
% 0.20/0.46  thf(t148_relat_1, axiom,
% 0.20/0.46    (![A:$i,B:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ B ) =>
% 0.20/0.46       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.46  thf('14', plain,
% 0.20/0.46      (![X4 : $i, X5 : $i]:
% 0.20/0.46         (((k2_relat_1 @ (k7_relat_1 @ X4 @ X5)) = (k9_relat_1 @ X4 @ X5))
% 0.20/0.46          | ~ (v1_relat_1 @ X4))),
% 0.20/0.46      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.46  thf('15', plain,
% 0.20/0.46      ((((k2_relat_1 @ sk_D_1) = (k9_relat_1 @ sk_D_1 @ sk_A))
% 0.20/0.46        | ~ (v1_relat_1 @ sk_D_1))),
% 0.20/0.46      inference('sup+', [status(thm)], ['13', '14'])).
% 0.20/0.46  thf('16', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.46  thf('17', plain, (((k2_relat_1 @ sk_D_1) = (k9_relat_1 @ sk_D_1 @ sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.46  thf(t143_relat_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( v1_relat_1 @ C ) =>
% 0.20/0.46       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.20/0.46         ( ?[D:$i]:
% 0.20/0.46           ( ( r2_hidden @ D @ B ) & 
% 0.20/0.46             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.20/0.46             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.20/0.46  thf('18', plain,
% 0.20/0.46      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X2 @ (k9_relat_1 @ X3 @ X1))
% 0.20/0.46          | (r2_hidden @ (k4_tarski @ (sk_D @ X3 @ X1 @ X2) @ X2) @ X3)
% 0.20/0.46          | ~ (v1_relat_1 @ X3))),
% 0.20/0.46      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.20/0.46  thf('19', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_1))
% 0.20/0.46          | ~ (v1_relat_1 @ sk_D_1)
% 0.20/0.46          | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_A @ X0) @ X0) @ 
% 0.20/0.46             sk_D_1))),
% 0.20/0.46      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.46  thf('20', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.46  thf('21', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_1))
% 0.20/0.46          | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_A @ X0) @ X0) @ 
% 0.20/0.46             sk_D_1))),
% 0.20/0.46      inference('demod', [status(thm)], ['19', '20'])).
% 0.20/0.46  thf('22', plain,
% 0.20/0.46      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_A @ sk_C) @ sk_C) @ sk_D_1)),
% 0.20/0.46      inference('sup-', [status(thm)], ['4', '21'])).
% 0.20/0.46  thf(t8_funct_1, axiom,
% 0.20/0.46    (![A:$i,B:$i,C:$i]:
% 0.20/0.46     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.46       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.46         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.46           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.20/0.46  thf('23', plain,
% 0.20/0.46      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.20/0.46         (~ (r2_hidden @ (k4_tarski @ X8 @ X10) @ X9)
% 0.20/0.46          | ((X10) = (k1_funct_1 @ X9 @ X8))
% 0.20/0.46          | ~ (v1_funct_1 @ X9)
% 0.20/0.46          | ~ (v1_relat_1 @ X9))),
% 0.20/0.46      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.20/0.46  thf('24', plain,
% 0.20/0.46      ((~ (v1_relat_1 @ sk_D_1)
% 0.20/0.46        | ~ (v1_funct_1 @ sk_D_1)
% 0.20/0.46        | ((sk_C) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_A @ sk_C))))),
% 0.20/0.46      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.46  thf('25', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.46  thf('26', plain, ((v1_funct_1 @ sk_D_1)),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('27', plain,
% 0.20/0.46      (((sk_C) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_A @ sk_C)))),
% 0.20/0.46      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.20/0.46  thf('28', plain, ((r2_hidden @ sk_C @ (k2_relat_1 @ sk_D_1))),
% 0.20/0.46      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.46  thf('29', plain, (((k2_relat_1 @ sk_D_1) = (k9_relat_1 @ sk_D_1 @ sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['15', '16'])).
% 0.20/0.46  thf('30', plain,
% 0.20/0.46      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X2 @ (k9_relat_1 @ X3 @ X1))
% 0.20/0.46          | (r2_hidden @ (sk_D @ X3 @ X1 @ X2) @ X1)
% 0.20/0.46          | ~ (v1_relat_1 @ X3))),
% 0.20/0.46      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.20/0.46  thf('31', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_1))
% 0.20/0.46          | ~ (v1_relat_1 @ sk_D_1)
% 0.20/0.46          | (r2_hidden @ (sk_D @ sk_D_1 @ sk_A @ X0) @ sk_A))),
% 0.20/0.46      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.46  thf('32', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.46      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.46  thf('33', plain,
% 0.20/0.46      (![X0 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_1))
% 0.20/0.46          | (r2_hidden @ (sk_D @ sk_D_1 @ sk_A @ X0) @ sk_A))),
% 0.20/0.46      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.46  thf('34', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_A @ sk_C) @ sk_A)),
% 0.20/0.46      inference('sup-', [status(thm)], ['28', '33'])).
% 0.20/0.46  thf('35', plain,
% 0.20/0.46      (![X20 : $i]:
% 0.20/0.46         (~ (r2_hidden @ X20 @ sk_A) | ((k1_funct_1 @ sk_D_1 @ X20) != (sk_C)))),
% 0.20/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.46  thf('36', plain,
% 0.20/0.46      (((k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_A @ sk_C)) != (sk_C))),
% 0.20/0.46      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.46  thf('37', plain, ($false),
% 0.20/0.46      inference('simplify_reflect-', [status(thm)], ['27', '36'])).
% 0.20/0.46  
% 0.20/0.46  % SZS output end Refutation
% 0.20/0.46  
% 0.20/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
