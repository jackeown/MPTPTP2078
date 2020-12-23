%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZS844b789c

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:29 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   55 (  92 expanded)
%              Number of leaves         :   26 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :  357 (1057 expanded)
%              Number of equality atoms :   16 (  44 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

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

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('2',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k7_relset_1 @ X14 @ X15 @ X16 @ X14 )
        = ( k2_relset_1 @ X14 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('3',plain,
    ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('5',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ( ( k7_relset_1 @ X11 @ X12 @ X10 @ X13 )
        = ( k9_relat_1 @ X10 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k9_relat_1 @ sk_D_1 @ sk_A )
    = ( k2_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    r2_hidden @ sk_C @ ( k9_relat_1 @ sk_D_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','7'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('9',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k9_relat_1 @ X3 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X1 @ X2 ) @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_A @ sk_C ) @ sk_C ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('12',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_A @ sk_C ) @ sk_C ) @ sk_D_1 ),
    inference(demod,[status(thm)],['10','13'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('15',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X4 @ X6 ) @ X5 )
      | ( X6
        = ( k1_funct_1 @ X5 @ X4 ) )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('16',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_C
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('18',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( sk_C
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf('20',plain,(
    r2_hidden @ sk_C @ ( k9_relat_1 @ sk_D_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','7'])).

thf('21',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X2 @ ( k9_relat_1 @ X3 @ X1 ) )
      | ( r2_hidden @ ( sk_D @ X3 @ X1 @ X2 ) @ X1 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_A @ sk_C ) @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('24',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_A @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X17: $i] :
      ( ~ ( r2_hidden @ X17 @ sk_A )
      | ( ( k1_funct_1 @ sk_D_1 @ X17 )
       != sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_A @ sk_C ) )
 != sk_C ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['19','26'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ZS844b789c
% 0.16/0.36  % Computer   : n005.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 20:13:03 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  % Running portfolio for 600 s
% 0.16/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.36  % Number of cores: 8
% 0.16/0.36  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.22/0.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.46  % Solved by: fo/fo7.sh
% 0.22/0.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.46  % done 23 iterations in 0.010s
% 0.22/0.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.46  % SZS output start Refutation
% 0.22/0.46  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.46  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.22/0.46  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.22/0.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.46  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.22/0.46  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.46  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.22/0.46  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.46  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.46  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.22/0.46  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.46  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.46  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.46  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.46  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.46  thf(t17_funct_2, conjecture,
% 0.22/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.46     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.46         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.46       ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 0.22/0.46            ( ![E:$i]:
% 0.22/0.46              ( ~( ( r2_hidden @ E @ A ) & ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ))).
% 0.22/0.46  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.46    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.46        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.46            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.46          ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 0.22/0.46               ( ![E:$i]:
% 0.22/0.46                 ( ~( ( r2_hidden @ E @ A ) & 
% 0.22/0.46                      ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ) )),
% 0.22/0.46    inference('cnf.neg', [status(esa)], [t17_funct_2])).
% 0.22/0.46  thf('0', plain, ((r2_hidden @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D_1))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('1', plain,
% 0.22/0.46      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf(t38_relset_1, axiom,
% 0.22/0.46    (![A:$i,B:$i,C:$i]:
% 0.22/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.46       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.22/0.46         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.22/0.46  thf('2', plain,
% 0.22/0.46      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.46         (((k7_relset_1 @ X14 @ X15 @ X16 @ X14)
% 0.22/0.46            = (k2_relset_1 @ X14 @ X15 @ X16))
% 0.22/0.46          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.22/0.46      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.22/0.46  thf('3', plain,
% 0.22/0.46      (((k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_A)
% 0.22/0.46         = (k2_relset_1 @ sk_A @ sk_B @ sk_D_1))),
% 0.22/0.46      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.46  thf('4', plain,
% 0.22/0.46      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf(redefinition_k7_relset_1, axiom,
% 0.22/0.46    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.46       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.22/0.46  thf('5', plain,
% 0.22/0.46      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.46         (~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12)))
% 0.22/0.46          | ((k7_relset_1 @ X11 @ X12 @ X10 @ X13) = (k9_relat_1 @ X10 @ X13)))),
% 0.22/0.46      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.22/0.46  thf('6', plain,
% 0.22/0.46      (![X0 : $i]:
% 0.22/0.46         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.22/0.46           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.22/0.46      inference('sup-', [status(thm)], ['4', '5'])).
% 0.22/0.46  thf('7', plain,
% 0.22/0.46      (((k9_relat_1 @ sk_D_1 @ sk_A) = (k2_relset_1 @ sk_A @ sk_B @ sk_D_1))),
% 0.22/0.46      inference('demod', [status(thm)], ['3', '6'])).
% 0.22/0.46  thf('8', plain, ((r2_hidden @ sk_C @ (k9_relat_1 @ sk_D_1 @ sk_A))),
% 0.22/0.46      inference('demod', [status(thm)], ['0', '7'])).
% 0.22/0.46  thf(t143_relat_1, axiom,
% 0.22/0.46    (![A:$i,B:$i,C:$i]:
% 0.22/0.46     ( ( v1_relat_1 @ C ) =>
% 0.22/0.46       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.22/0.46         ( ?[D:$i]:
% 0.22/0.46           ( ( r2_hidden @ D @ B ) & 
% 0.22/0.46             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.22/0.46             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.22/0.46  thf('9', plain,
% 0.22/0.46      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.46         (~ (r2_hidden @ X2 @ (k9_relat_1 @ X3 @ X1))
% 0.22/0.46          | (r2_hidden @ (k4_tarski @ (sk_D @ X3 @ X1 @ X2) @ X2) @ X3)
% 0.22/0.46          | ~ (v1_relat_1 @ X3))),
% 0.22/0.46      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.22/0.46  thf('10', plain,
% 0.22/0.46      ((~ (v1_relat_1 @ sk_D_1)
% 0.22/0.46        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_A @ sk_C) @ sk_C) @ 
% 0.22/0.46           sk_D_1))),
% 0.22/0.46      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.46  thf('11', plain,
% 0.22/0.46      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf(cc1_relset_1, axiom,
% 0.22/0.46    (![A:$i,B:$i,C:$i]:
% 0.22/0.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.46       ( v1_relat_1 @ C ) ))).
% 0.22/0.46  thf('12', plain,
% 0.22/0.46      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.46         ((v1_relat_1 @ X7)
% 0.22/0.46          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.22/0.46      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.46  thf('13', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.46      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.46  thf('14', plain,
% 0.22/0.46      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_A @ sk_C) @ sk_C) @ sk_D_1)),
% 0.22/0.46      inference('demod', [status(thm)], ['10', '13'])).
% 0.22/0.46  thf(t8_funct_1, axiom,
% 0.22/0.46    (![A:$i,B:$i,C:$i]:
% 0.22/0.46     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.46       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.22/0.46         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.22/0.46           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.22/0.46  thf('15', plain,
% 0.22/0.46      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.22/0.46         (~ (r2_hidden @ (k4_tarski @ X4 @ X6) @ X5)
% 0.22/0.46          | ((X6) = (k1_funct_1 @ X5 @ X4))
% 0.22/0.46          | ~ (v1_funct_1 @ X5)
% 0.22/0.46          | ~ (v1_relat_1 @ X5))),
% 0.22/0.46      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.22/0.46  thf('16', plain,
% 0.22/0.46      ((~ (v1_relat_1 @ sk_D_1)
% 0.22/0.46        | ~ (v1_funct_1 @ sk_D_1)
% 0.22/0.46        | ((sk_C) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_A @ sk_C))))),
% 0.22/0.46      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.46  thf('17', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.46      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.46  thf('18', plain, ((v1_funct_1 @ sk_D_1)),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('19', plain,
% 0.22/0.46      (((sk_C) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_A @ sk_C)))),
% 0.22/0.46      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.22/0.46  thf('20', plain, ((r2_hidden @ sk_C @ (k9_relat_1 @ sk_D_1 @ sk_A))),
% 0.22/0.46      inference('demod', [status(thm)], ['0', '7'])).
% 0.22/0.46  thf('21', plain,
% 0.22/0.46      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.22/0.46         (~ (r2_hidden @ X2 @ (k9_relat_1 @ X3 @ X1))
% 0.22/0.46          | (r2_hidden @ (sk_D @ X3 @ X1 @ X2) @ X1)
% 0.22/0.46          | ~ (v1_relat_1 @ X3))),
% 0.22/0.46      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.22/0.46  thf('22', plain,
% 0.22/0.46      ((~ (v1_relat_1 @ sk_D_1)
% 0.22/0.46        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_A @ sk_C) @ sk_A))),
% 0.22/0.46      inference('sup-', [status(thm)], ['20', '21'])).
% 0.22/0.46  thf('23', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.46      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.46  thf('24', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_A @ sk_C) @ sk_A)),
% 0.22/0.46      inference('demod', [status(thm)], ['22', '23'])).
% 0.22/0.46  thf('25', plain,
% 0.22/0.46      (![X17 : $i]:
% 0.22/0.46         (~ (r2_hidden @ X17 @ sk_A) | ((k1_funct_1 @ sk_D_1 @ X17) != (sk_C)))),
% 0.22/0.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.46  thf('26', plain,
% 0.22/0.46      (((k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_A @ sk_C)) != (sk_C))),
% 0.22/0.46      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.46  thf('27', plain, ($false),
% 0.22/0.46      inference('simplify_reflect-', [status(thm)], ['19', '26'])).
% 0.22/0.46  
% 0.22/0.46  % SZS output end Refutation
% 0.22/0.46  
% 0.22/0.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
