%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zJAPJAg3bw

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 (  86 expanded)
%              Number of leaves         :   20 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :  337 (1276 expanded)
%              Number of equality atoms :   28 (  90 expanded)
%              Maximal formula depth    :   14 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t85_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( v2_funct_1 @ B )
       => ! [C: $i,D: $i] :
            ( ( ( r2_hidden @ C @ A )
              & ( r2_hidden @ D @ A )
              & ( ( k1_funct_1 @ B @ C )
                = ( k1_funct_1 @ B @ D ) ) )
           => ( C = D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( v2_funct_1 @ B )
         => ! [C: $i,D: $i] :
              ( ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ D @ A )
                & ( ( k1_funct_1 @ B @ C )
                  = ( k1_funct_1 @ B @ D ) ) )
             => ( C = D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t85_funct_2])).

thf('0',plain,
    ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
    = ( k1_funct_1 @ sk_B_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k1_relset_1 @ X9 @ X9 @ X10 )
        = X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X9 ) ) )
      | ~ ( v1_funct_2 @ X10 @ X9 @ X9 )
      | ~ ( v1_funct_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k1_relset_1 @ X7 @ X8 @ X6 )
        = ( k1_relat_1 @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('8',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['3','4','5','8'])).

thf(d8_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
      <=> ! [B: $i,C: $i] :
            ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) )
              & ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
              & ( ( k1_funct_1 @ A @ B )
                = ( k1_funct_1 @ A @ C ) ) )
           => ( B = C ) ) ) ) )).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ( ( k1_funct_1 @ X0 @ X1 )
       != ( k1_funct_1 @ X0 @ X2 ) )
      | ( X1 = X2 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d8_funct_1])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_B_1 ) )
      | ~ ( v2_funct_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('13',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('14',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['3','4','5','8'])).

thf('17',plain,(
    v2_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( X0 = X1 )
      | ( ( k1_funct_1 @ sk_B_1 @ X0 )
       != ( k1_funct_1 @ sk_B_1 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','14','15','16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_D = X0 )
      | ~ ( r2_hidden @ sk_D @ sk_A ) ) ),
    inference('sup-',[status(thm)],['0','18'])).

thf('20',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( ( k1_funct_1 @ sk_B_1 @ sk_C_1 )
       != ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ( sk_D = X0 ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( sk_D = sk_C_1 )
    | ~ ( r2_hidden @ sk_C_1 @ sk_A ) ),
    inference(eq_res,[status(thm)],['21'])).

thf('23',plain,(
    r2_hidden @ sk_C_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    sk_D = sk_C_1 ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,(
    sk_C_1 != sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['24','25'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.zJAPJAg3bw
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:47:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.47  % Solved by: fo/fo7.sh
% 0.21/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.47  % done 21 iterations in 0.015s
% 0.21/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.47  % SZS output start Refutation
% 0.21/0.47  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.47  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.21/0.47  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.47  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.47  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.47  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.47  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.47  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.47  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.47  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.47  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.47  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.47  thf(t85_funct_2, conjecture,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.47         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.47       ( ( v2_funct_1 @ B ) =>
% 0.21/0.47         ( ![C:$i,D:$i]:
% 0.21/0.47           ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.21/0.47               ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.21/0.47             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.21/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.47    (~( ![A:$i,B:$i]:
% 0.21/0.47        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.47            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.47          ( ( v2_funct_1 @ B ) =>
% 0.21/0.47            ( ![C:$i,D:$i]:
% 0.21/0.47              ( ( ( r2_hidden @ C @ A ) & ( r2_hidden @ D @ A ) & 
% 0.21/0.47                  ( ( k1_funct_1 @ B @ C ) = ( k1_funct_1 @ B @ D ) ) ) =>
% 0.21/0.47                ( ( C ) = ( D ) ) ) ) ) ) )),
% 0.21/0.47    inference('cnf.neg', [status(esa)], [t85_funct_2])).
% 0.21/0.47  thf('0', plain,
% 0.21/0.47      (((k1_funct_1 @ sk_B_1 @ sk_C_1) = (k1_funct_1 @ sk_B_1 @ sk_D))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('1', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(t67_funct_2, axiom,
% 0.21/0.47    (![A:$i,B:$i]:
% 0.21/0.47     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.47         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.47       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.21/0.47  thf('2', plain,
% 0.21/0.47      (![X9 : $i, X10 : $i]:
% 0.21/0.47         (((k1_relset_1 @ X9 @ X9 @ X10) = (X9))
% 0.21/0.47          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X9)))
% 0.21/0.47          | ~ (v1_funct_2 @ X10 @ X9 @ X9)
% 0.21/0.47          | ~ (v1_funct_1 @ X10))),
% 0.21/0.47      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.21/0.47  thf('3', plain,
% 0.21/0.47      ((~ (v1_funct_1 @ sk_B_1)
% 0.21/0.47        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.21/0.47        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (sk_A)))),
% 0.21/0.47      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.47  thf('4', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('5', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('6', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.47       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.47  thf('7', plain,
% 0.21/0.47      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.47         (((k1_relset_1 @ X7 @ X8 @ X6) = (k1_relat_1 @ X6))
% 0.21/0.47          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 0.21/0.47      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.47  thf('8', plain,
% 0.21/0.47      (((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k1_relat_1 @ sk_B_1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.47  thf('9', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['3', '4', '5', '8'])).
% 0.21/0.47  thf(d8_funct_1, axiom,
% 0.21/0.47    (![A:$i]:
% 0.21/0.47     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.47       ( ( v2_funct_1 @ A ) <=>
% 0.21/0.47         ( ![B:$i,C:$i]:
% 0.21/0.47           ( ( ( r2_hidden @ B @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.47               ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.47               ( ( k1_funct_1 @ A @ B ) = ( k1_funct_1 @ A @ C ) ) ) =>
% 0.21/0.47             ( ( B ) = ( C ) ) ) ) ) ))).
% 0.21/0.47  thf('10', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.47         (~ (v2_funct_1 @ X0)
% 0.21/0.47          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ X0))
% 0.21/0.47          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 0.21/0.47          | ((k1_funct_1 @ X0 @ X1) != (k1_funct_1 @ X0 @ X2))
% 0.21/0.47          | ((X1) = (X2))
% 0.21/0.47          | ~ (v1_funct_1 @ X0)
% 0.21/0.47          | ~ (v1_relat_1 @ X0))),
% 0.21/0.47      inference('cnf', [status(esa)], [d8_funct_1])).
% 0.21/0.47  thf('11', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.47          | ~ (v1_relat_1 @ sk_B_1)
% 0.21/0.47          | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.47          | ((X0) = (X1))
% 0.21/0.47          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 0.21/0.47          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_B_1))
% 0.21/0.47          | ~ (v2_funct_1 @ sk_B_1))),
% 0.21/0.47      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.47  thf('12', plain,
% 0.21/0.47      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf(cc1_relset_1, axiom,
% 0.21/0.47    (![A:$i,B:$i,C:$i]:
% 0.21/0.47     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.47       ( v1_relat_1 @ C ) ))).
% 0.21/0.47  thf('13', plain,
% 0.21/0.47      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.47         ((v1_relat_1 @ X3)
% 0.21/0.47          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 0.21/0.47      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.47  thf('14', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.47      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.47  thf('15', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('16', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['3', '4', '5', '8'])).
% 0.21/0.47  thf('17', plain, ((v2_funct_1 @ sk_B_1)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('18', plain,
% 0.21/0.47      (![X0 : $i, X1 : $i]:
% 0.21/0.47         (~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.47          | ((X0) = (X1))
% 0.21/0.47          | ((k1_funct_1 @ sk_B_1 @ X0) != (k1_funct_1 @ sk_B_1 @ X1))
% 0.21/0.47          | ~ (r2_hidden @ X1 @ sk_A))),
% 0.21/0.47      inference('demod', [status(thm)], ['11', '14', '15', '16', '17'])).
% 0.21/0.47  thf('19', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((k1_funct_1 @ sk_B_1 @ sk_C_1) != (k1_funct_1 @ sk_B_1 @ X0))
% 0.21/0.47          | ~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.47          | ((sk_D) = (X0))
% 0.21/0.47          | ~ (r2_hidden @ sk_D @ sk_A))),
% 0.21/0.47      inference('sup-', [status(thm)], ['0', '18'])).
% 0.21/0.47  thf('20', plain, ((r2_hidden @ sk_D @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('21', plain,
% 0.21/0.47      (![X0 : $i]:
% 0.21/0.47         (((k1_funct_1 @ sk_B_1 @ sk_C_1) != (k1_funct_1 @ sk_B_1 @ X0))
% 0.21/0.47          | ~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.47          | ((sk_D) = (X0)))),
% 0.21/0.47      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.47  thf('22', plain, ((((sk_D) = (sk_C_1)) | ~ (r2_hidden @ sk_C_1 @ sk_A))),
% 0.21/0.47      inference('eq_res', [status(thm)], ['21'])).
% 0.21/0.47  thf('23', plain, ((r2_hidden @ sk_C_1 @ sk_A)),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('24', plain, (((sk_D) = (sk_C_1))),
% 0.21/0.47      inference('demod', [status(thm)], ['22', '23'])).
% 0.21/0.47  thf('25', plain, (((sk_C_1) != (sk_D))),
% 0.21/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.47  thf('26', plain, ($false),
% 0.21/0.47      inference('simplify_reflect-', [status(thm)], ['24', '25'])).
% 0.21/0.47  
% 0.21/0.47  % SZS output end Refutation
% 0.21/0.47  
% 0.21/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
