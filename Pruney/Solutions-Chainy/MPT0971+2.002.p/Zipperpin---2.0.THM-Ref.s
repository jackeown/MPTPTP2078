%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.M046pBpOUK

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   61 (  93 expanded)
%              Number of leaves         :   26 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :  362 ( 991 expanded)
%              Number of equality atoms :   16 (  41 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    r2_hidden @ sk_C_2 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_C_2 @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(d5_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( B
            = ( k2_relat_1 @ A ) )
        <=> ! [C: $i] :
              ( ( r2_hidden @ C @ B )
            <=> ? [D: $i] :
                  ( ( C
                    = ( k1_funct_1 @ A @ D ) )
                  & ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ( X9
       != ( k2_relat_1 @ X7 ) )
      | ( r2_hidden @ ( sk_D_1 @ X10 @ X7 ) @ ( k1_relat_1 @ X7 ) )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('6',plain,(
    ! [X7: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k2_relat_1 @ X7 ) )
      | ( r2_hidden @ ( sk_D_1 @ X10 @ X7 ) @ ( k1_relat_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_C_2 @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('10',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ ( sk_D_1 @ sk_C_2 @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v4_relat_1 @ X16 @ X17 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('15',plain,(
    v4_relat_1 @ sk_D_2 @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('16',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v4_relat_1 @ X4 @ X5 )
      | ( r1_tarski @ ( k1_relat_1 @ X4 ) @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('17',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('19',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_2 ) @ sk_A ),
    inference(demod,[status(thm)],['17','18'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    r2_hidden @ ( sk_D_1 @ sk_C_2 @ sk_D_2 ) @ sk_A ),
    inference('sup-',[status(thm)],['12','21'])).

thf('23',plain,(
    ! [X22: $i] :
      ( ~ ( r2_hidden @ X22 @ sk_A )
      | ( ( k1_funct_1 @ sk_D_2 @ X22 )
       != sk_C_2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_C_2 @ sk_D_2 ) )
 != sk_C_2 ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    r2_hidden @ sk_C_2 @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('26',plain,(
    ! [X7: $i,X9: $i,X10: $i] :
      ( ( X9
       != ( k2_relat_1 @ X7 ) )
      | ( X10
        = ( k1_funct_1 @ X7 @ ( sk_D_1 @ X10 @ X7 ) ) )
      | ~ ( r2_hidden @ X10 @ X9 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('27',plain,(
    ! [X7: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X10 @ ( k2_relat_1 @ X7 ) )
      | ( X10
        = ( k1_funct_1 @ X7 @ ( sk_D_1 @ X10 @ X7 ) ) ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( sk_C_2
      = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_C_2 @ sk_D_2 ) ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('31',plain,
    ( sk_C_2
    = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_C_2 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    sk_C_2 != sk_C_2 ),
    inference(demod,[status(thm)],['24','31'])).

thf('33',plain,(
    $false ),
    inference(simplify,[status(thm)],['32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.M046pBpOUK
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:00:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.51  % Solved by: fo/fo7.sh
% 0.21/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.51  % done 57 iterations in 0.045s
% 0.21/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.51  % SZS output start Refutation
% 0.21/0.51  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.21/0.51  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.51  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.21/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.51  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.21/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.51  thf(t17_funct_2, conjecture,
% 0.21/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.51         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.51       ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 0.21/0.51            ( ![E:$i]:
% 0.21/0.51              ( ~( ( r2_hidden @ E @ A ) & ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.51    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.51        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.51            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.51          ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 0.21/0.51               ( ![E:$i]:
% 0.21/0.51                 ( ~( ( r2_hidden @ E @ A ) & 
% 0.21/0.51                      ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ) )),
% 0.21/0.51    inference('cnf.neg', [status(esa)], [t17_funct_2])).
% 0.21/0.51  thf('0', plain,
% 0.21/0.51      ((r2_hidden @ sk_C_2 @ (k2_relset_1 @ sk_A @ sk_B @ sk_D_2))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('1', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.51  thf('2', plain,
% 0.21/0.51      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.21/0.51         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 0.21/0.51          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.21/0.51      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.51  thf('3', plain,
% 0.21/0.51      (((k2_relset_1 @ sk_A @ sk_B @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 0.21/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.51  thf('4', plain, ((r2_hidden @ sk_C_2 @ (k2_relat_1 @ sk_D_2))),
% 0.21/0.51      inference('demod', [status(thm)], ['0', '3'])).
% 0.21/0.51  thf(d5_funct_1, axiom,
% 0.21/0.51    (![A:$i]:
% 0.21/0.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.51       ( ![B:$i]:
% 0.21/0.51         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.21/0.51           ( ![C:$i]:
% 0.21/0.51             ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.51               ( ?[D:$i]:
% 0.21/0.51                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.21/0.51                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.21/0.51  thf('5', plain,
% 0.21/0.51      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.21/0.51         (((X9) != (k2_relat_1 @ X7))
% 0.21/0.51          | (r2_hidden @ (sk_D_1 @ X10 @ X7) @ (k1_relat_1 @ X7))
% 0.21/0.51          | ~ (r2_hidden @ X10 @ X9)
% 0.21/0.51          | ~ (v1_funct_1 @ X7)
% 0.21/0.51          | ~ (v1_relat_1 @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.21/0.51  thf('6', plain,
% 0.21/0.51      (![X7 : $i, X10 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X7)
% 0.21/0.51          | ~ (v1_funct_1 @ X7)
% 0.21/0.51          | ~ (r2_hidden @ X10 @ (k2_relat_1 @ X7))
% 0.21/0.51          | (r2_hidden @ (sk_D_1 @ X10 @ X7) @ (k1_relat_1 @ X7)))),
% 0.21/0.51      inference('simplify', [status(thm)], ['5'])).
% 0.21/0.51  thf('7', plain,
% 0.21/0.51      (((r2_hidden @ (sk_D_1 @ sk_C_2 @ sk_D_2) @ (k1_relat_1 @ sk_D_2))
% 0.21/0.51        | ~ (v1_funct_1 @ sk_D_2)
% 0.21/0.51        | ~ (v1_relat_1 @ sk_D_2))),
% 0.21/0.51      inference('sup-', [status(thm)], ['4', '6'])).
% 0.21/0.51  thf('8', plain, ((v1_funct_1 @ sk_D_2)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('9', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(cc1_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( v1_relat_1 @ C ) ))).
% 0.21/0.51  thf('10', plain,
% 0.21/0.51      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.51         ((v1_relat_1 @ X13)
% 0.21/0.51          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.51  thf('11', plain, ((v1_relat_1 @ sk_D_2)),
% 0.21/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.51  thf('12', plain,
% 0.21/0.51      ((r2_hidden @ (sk_D_1 @ sk_C_2 @ sk_D_2) @ (k1_relat_1 @ sk_D_2))),
% 0.21/0.51      inference('demod', [status(thm)], ['7', '8', '11'])).
% 0.21/0.51  thf('13', plain,
% 0.21/0.51      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf(cc2_relset_1, axiom,
% 0.21/0.51    (![A:$i,B:$i,C:$i]:
% 0.21/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.51  thf('14', plain,
% 0.21/0.51      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.51         ((v4_relat_1 @ X16 @ X17)
% 0.21/0.51          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.21/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.51  thf('15', plain, ((v4_relat_1 @ sk_D_2 @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.51  thf(d18_relat_1, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( v1_relat_1 @ B ) =>
% 0.21/0.51       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.51  thf('16', plain,
% 0.21/0.51      (![X4 : $i, X5 : $i]:
% 0.21/0.51         (~ (v4_relat_1 @ X4 @ X5)
% 0.21/0.51          | (r1_tarski @ (k1_relat_1 @ X4) @ X5)
% 0.21/0.51          | ~ (v1_relat_1 @ X4))),
% 0.21/0.51      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.21/0.51  thf('17', plain,
% 0.21/0.51      ((~ (v1_relat_1 @ sk_D_2) | (r1_tarski @ (k1_relat_1 @ sk_D_2) @ sk_A))),
% 0.21/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.51  thf('18', plain, ((v1_relat_1 @ sk_D_2)),
% 0.21/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.51  thf('19', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_2) @ sk_A)),
% 0.21/0.51      inference('demod', [status(thm)], ['17', '18'])).
% 0.21/0.51  thf(d3_tarski, axiom,
% 0.21/0.51    (![A:$i,B:$i]:
% 0.21/0.51     ( ( r1_tarski @ A @ B ) <=>
% 0.21/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.21/0.51  thf('20', plain,
% 0.21/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.21/0.51          | (r2_hidden @ X0 @ X2)
% 0.21/0.51          | ~ (r1_tarski @ X1 @ X2))),
% 0.21/0.51      inference('cnf', [status(esa)], [d3_tarski])).
% 0.21/0.51  thf('21', plain,
% 0.21/0.51      (![X0 : $i]:
% 0.21/0.51         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_2)))),
% 0.21/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.51  thf('22', plain, ((r2_hidden @ (sk_D_1 @ sk_C_2 @ sk_D_2) @ sk_A)),
% 0.21/0.51      inference('sup-', [status(thm)], ['12', '21'])).
% 0.21/0.51  thf('23', plain,
% 0.21/0.51      (![X22 : $i]:
% 0.21/0.51         (~ (r2_hidden @ X22 @ sk_A)
% 0.21/0.51          | ((k1_funct_1 @ sk_D_2 @ X22) != (sk_C_2)))),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('24', plain,
% 0.21/0.51      (((k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_C_2 @ sk_D_2)) != (sk_C_2))),
% 0.21/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.51  thf('25', plain, ((r2_hidden @ sk_C_2 @ (k2_relat_1 @ sk_D_2))),
% 0.21/0.51      inference('demod', [status(thm)], ['0', '3'])).
% 0.21/0.51  thf('26', plain,
% 0.21/0.51      (![X7 : $i, X9 : $i, X10 : $i]:
% 0.21/0.51         (((X9) != (k2_relat_1 @ X7))
% 0.21/0.51          | ((X10) = (k1_funct_1 @ X7 @ (sk_D_1 @ X10 @ X7)))
% 0.21/0.51          | ~ (r2_hidden @ X10 @ X9)
% 0.21/0.51          | ~ (v1_funct_1 @ X7)
% 0.21/0.51          | ~ (v1_relat_1 @ X7))),
% 0.21/0.51      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.21/0.51  thf('27', plain,
% 0.21/0.51      (![X7 : $i, X10 : $i]:
% 0.21/0.51         (~ (v1_relat_1 @ X7)
% 0.21/0.51          | ~ (v1_funct_1 @ X7)
% 0.21/0.51          | ~ (r2_hidden @ X10 @ (k2_relat_1 @ X7))
% 0.21/0.51          | ((X10) = (k1_funct_1 @ X7 @ (sk_D_1 @ X10 @ X7))))),
% 0.21/0.51      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.51  thf('28', plain,
% 0.21/0.51      ((((sk_C_2) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_C_2 @ sk_D_2)))
% 0.21/0.51        | ~ (v1_funct_1 @ sk_D_2)
% 0.21/0.51        | ~ (v1_relat_1 @ sk_D_2))),
% 0.21/0.51      inference('sup-', [status(thm)], ['25', '27'])).
% 0.21/0.51  thf('29', plain, ((v1_funct_1 @ sk_D_2)),
% 0.21/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.51  thf('30', plain, ((v1_relat_1 @ sk_D_2)),
% 0.21/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.51  thf('31', plain,
% 0.21/0.51      (((sk_C_2) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_C_2 @ sk_D_2)))),
% 0.21/0.51      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.21/0.51  thf('32', plain, (((sk_C_2) != (sk_C_2))),
% 0.21/0.51      inference('demod', [status(thm)], ['24', '31'])).
% 0.21/0.51  thf('33', plain, ($false), inference('simplify', [status(thm)], ['32'])).
% 0.21/0.51  
% 0.21/0.51  % SZS output end Refutation
% 0.21/0.51  
% 0.21/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
