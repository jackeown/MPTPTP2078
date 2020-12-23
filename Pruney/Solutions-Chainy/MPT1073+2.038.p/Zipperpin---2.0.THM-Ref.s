%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ss9rJcLW1Q

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:19 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 122 expanded)
%              Number of leaves         :   25 (  47 expanded)
%              Depth                    :   14
%              Number of atoms          :  444 (1472 expanded)
%              Number of equality atoms :   19 (  63 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(t190_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ B @ C )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
     => ~ ( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) )
          & ! [E: $i] :
              ( ( m1_subset_1 @ E @ B )
             => ( A
               != ( k1_funct_1 @ D @ E ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ B @ C )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
       => ~ ( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) )
            & ! [E: $i] :
                ( ( m1_subset_1 @ E @ B )
               => ( A
                 != ( k1_funct_1 @ D @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t190_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_A @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_2 )
    = ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_2 ) ),
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
    ! [X11: $i,X13: $i,X14: $i] :
      ( ( X13
       != ( k2_relat_1 @ X11 ) )
      | ( r2_hidden @ ( sk_D_1 @ X14 @ X11 ) @ ( k1_relat_1 @ X11 ) )
      | ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('6',plain,(
    ! [X11: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( r2_hidden @ X14 @ ( k2_relat_1 @ X11 ) )
      | ( r2_hidden @ ( sk_D_1 @ X14 @ X11 ) @ ( k1_relat_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('10',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v1_relat_1 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['7','8','11'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('13',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X18 ) )
      | ( X19
       != ( k1_funct_1 @ X18 @ X17 ) )
      | ( r2_hidden @ ( k4_tarski @ X17 @ X19 ) @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('14',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ( r2_hidden @ ( k4_tarski @ X17 @ ( k1_funct_1 @ X18 @ X17 ) ) @ X18 )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X18 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_A @ sk_D_2 ) ) ) @ sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    r2_hidden @ sk_A @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('17',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ( X13
       != ( k2_relat_1 @ X11 ) )
      | ( X14
        = ( k1_funct_1 @ X11 @ ( sk_D_1 @ X14 @ X11 ) ) )
      | ~ ( r2_hidden @ X14 @ X13 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('18',plain,(
    ! [X11: $i,X14: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( r2_hidden @ X14 @ ( k2_relat_1 @ X11 ) )
      | ( X14
        = ( k1_funct_1 @ X11 @ ( sk_D_1 @ X14 @ X11 ) ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( sk_A
      = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_A @ sk_D_2 ) ) )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('22',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_A @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('25',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ sk_A ) @ sk_D_2 ),
    inference(demod,[status(thm)],['15','22','23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('27',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ sk_A ) @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['25','28'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('31',plain,(
    r2_hidden @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['29','30'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('32',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('33',plain,(
    m1_subset_1 @ ( sk_D_1 @ sk_A @ sk_D_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X26: $i] :
      ( ( sk_A
       != ( k1_funct_1 @ sk_D_2 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    sk_A
 != ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_A @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( sk_A
    = ( k1_funct_1 @ sk_D_2 @ ( sk_D_1 @ sk_A @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('37',plain,(
    sk_A != sk_A ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    $false ),
    inference(simplify,[status(thm)],['37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.ss9rJcLW1Q
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:53:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.36/0.55  % Solved by: fo/fo7.sh
% 0.36/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.55  % done 78 iterations in 0.096s
% 0.36/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.36/0.55  % SZS output start Refutation
% 0.36/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.36/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.36/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.55  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.36/0.55  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.36/0.55  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.36/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.36/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.36/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.55  thf(t190_funct_2, conjecture,
% 0.36/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.55     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.36/0.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.36/0.55       ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.36/0.55            ( ![E:$i]:
% 0.36/0.55              ( ( m1_subset_1 @ E @ B ) => ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ))).
% 0.36/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.55    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.55        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.36/0.55            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.36/0.55          ( ~( ( r2_hidden @ A @ ( k2_relset_1 @ B @ C @ D ) ) & 
% 0.36/0.55               ( ![E:$i]:
% 0.36/0.55                 ( ( m1_subset_1 @ E @ B ) =>
% 0.36/0.55                   ( ( A ) != ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) )),
% 0.36/0.55    inference('cnf.neg', [status(esa)], [t190_funct_2])).
% 0.36/0.55  thf('0', plain,
% 0.36/0.55      ((r2_hidden @ sk_A @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_2))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('1', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(redefinition_k2_relset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.55       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.36/0.55  thf('2', plain,
% 0.36/0.55      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.36/0.55         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 0.36/0.55          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.36/0.55      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.36/0.55  thf('3', plain,
% 0.36/0.55      (((k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_2) = (k2_relat_1 @ sk_D_2))),
% 0.36/0.55      inference('sup-', [status(thm)], ['1', '2'])).
% 0.36/0.55  thf('4', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_2))),
% 0.36/0.55      inference('demod', [status(thm)], ['0', '3'])).
% 0.36/0.55  thf(d5_funct_1, axiom,
% 0.36/0.55    (![A:$i]:
% 0.36/0.55     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.36/0.55       ( ![B:$i]:
% 0.36/0.55         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.36/0.55           ( ![C:$i]:
% 0.36/0.55             ( ( r2_hidden @ C @ B ) <=>
% 0.36/0.55               ( ?[D:$i]:
% 0.36/0.55                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.36/0.55                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.36/0.55  thf('5', plain,
% 0.36/0.55      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.36/0.55         (((X13) != (k2_relat_1 @ X11))
% 0.36/0.55          | (r2_hidden @ (sk_D_1 @ X14 @ X11) @ (k1_relat_1 @ X11))
% 0.36/0.55          | ~ (r2_hidden @ X14 @ X13)
% 0.36/0.55          | ~ (v1_funct_1 @ X11)
% 0.36/0.55          | ~ (v1_relat_1 @ X11))),
% 0.36/0.55      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.36/0.55  thf('6', plain,
% 0.36/0.55      (![X11 : $i, X14 : $i]:
% 0.36/0.55         (~ (v1_relat_1 @ X11)
% 0.36/0.55          | ~ (v1_funct_1 @ X11)
% 0.36/0.55          | ~ (r2_hidden @ X14 @ (k2_relat_1 @ X11))
% 0.36/0.55          | (r2_hidden @ (sk_D_1 @ X14 @ X11) @ (k1_relat_1 @ X11)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['5'])).
% 0.36/0.55  thf('7', plain,
% 0.36/0.55      (((r2_hidden @ (sk_D_1 @ sk_A @ sk_D_2) @ (k1_relat_1 @ sk_D_2))
% 0.36/0.55        | ~ (v1_funct_1 @ sk_D_2)
% 0.36/0.55        | ~ (v1_relat_1 @ sk_D_2))),
% 0.36/0.55      inference('sup-', [status(thm)], ['4', '6'])).
% 0.36/0.55  thf('8', plain, ((v1_funct_1 @ sk_D_2)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('9', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(cc1_relset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.55       ( v1_relat_1 @ C ) ))).
% 0.36/0.55  thf('10', plain,
% 0.36/0.55      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.36/0.55         ((v1_relat_1 @ X20)
% 0.36/0.55          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.36/0.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.36/0.55  thf('11', plain, ((v1_relat_1 @ sk_D_2)),
% 0.36/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.36/0.55  thf('12', plain,
% 0.36/0.55      ((r2_hidden @ (sk_D_1 @ sk_A @ sk_D_2) @ (k1_relat_1 @ sk_D_2))),
% 0.36/0.55      inference('demod', [status(thm)], ['7', '8', '11'])).
% 0.36/0.55  thf(t8_funct_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i]:
% 0.36/0.55     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.36/0.55       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.36/0.55         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.36/0.55           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.36/0.55  thf('13', plain,
% 0.36/0.55      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X17 @ (k1_relat_1 @ X18))
% 0.36/0.55          | ((X19) != (k1_funct_1 @ X18 @ X17))
% 0.36/0.55          | (r2_hidden @ (k4_tarski @ X17 @ X19) @ X18)
% 0.36/0.55          | ~ (v1_funct_1 @ X18)
% 0.36/0.55          | ~ (v1_relat_1 @ X18))),
% 0.36/0.55      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.36/0.55  thf('14', plain,
% 0.36/0.55      (![X17 : $i, X18 : $i]:
% 0.36/0.55         (~ (v1_relat_1 @ X18)
% 0.36/0.55          | ~ (v1_funct_1 @ X18)
% 0.36/0.55          | (r2_hidden @ (k4_tarski @ X17 @ (k1_funct_1 @ X18 @ X17)) @ X18)
% 0.36/0.55          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X18)))),
% 0.36/0.55      inference('simplify', [status(thm)], ['13'])).
% 0.36/0.55  thf('15', plain,
% 0.36/0.55      (((r2_hidden @ 
% 0.36/0.55         (k4_tarski @ (sk_D_1 @ sk_A @ sk_D_2) @ 
% 0.36/0.55          (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_A @ sk_D_2))) @ 
% 0.36/0.55         sk_D_2)
% 0.36/0.55        | ~ (v1_funct_1 @ sk_D_2)
% 0.36/0.55        | ~ (v1_relat_1 @ sk_D_2))),
% 0.36/0.55      inference('sup-', [status(thm)], ['12', '14'])).
% 0.36/0.55  thf('16', plain, ((r2_hidden @ sk_A @ (k2_relat_1 @ sk_D_2))),
% 0.36/0.55      inference('demod', [status(thm)], ['0', '3'])).
% 0.36/0.55  thf('17', plain,
% 0.36/0.55      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.36/0.55         (((X13) != (k2_relat_1 @ X11))
% 0.36/0.55          | ((X14) = (k1_funct_1 @ X11 @ (sk_D_1 @ X14 @ X11)))
% 0.36/0.55          | ~ (r2_hidden @ X14 @ X13)
% 0.36/0.55          | ~ (v1_funct_1 @ X11)
% 0.36/0.55          | ~ (v1_relat_1 @ X11))),
% 0.36/0.55      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.36/0.55  thf('18', plain,
% 0.36/0.55      (![X11 : $i, X14 : $i]:
% 0.36/0.55         (~ (v1_relat_1 @ X11)
% 0.36/0.55          | ~ (v1_funct_1 @ X11)
% 0.36/0.55          | ~ (r2_hidden @ X14 @ (k2_relat_1 @ X11))
% 0.36/0.55          | ((X14) = (k1_funct_1 @ X11 @ (sk_D_1 @ X14 @ X11))))),
% 0.36/0.55      inference('simplify', [status(thm)], ['17'])).
% 0.36/0.55  thf('19', plain,
% 0.36/0.55      ((((sk_A) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_A @ sk_D_2)))
% 0.36/0.55        | ~ (v1_funct_1 @ sk_D_2)
% 0.36/0.55        | ~ (v1_relat_1 @ sk_D_2))),
% 0.36/0.55      inference('sup-', [status(thm)], ['16', '18'])).
% 0.36/0.55  thf('20', plain, ((v1_funct_1 @ sk_D_2)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('21', plain, ((v1_relat_1 @ sk_D_2)),
% 0.36/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.36/0.55  thf('22', plain,
% 0.36/0.55      (((sk_A) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_A @ sk_D_2)))),
% 0.36/0.55      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.36/0.55  thf('23', plain, ((v1_funct_1 @ sk_D_2)),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('24', plain, ((v1_relat_1 @ sk_D_2)),
% 0.36/0.55      inference('sup-', [status(thm)], ['9', '10'])).
% 0.36/0.55  thf('25', plain,
% 0.36/0.55      ((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_A @ sk_D_2) @ sk_A) @ sk_D_2)),
% 0.36/0.55      inference('demod', [status(thm)], ['15', '22', '23', '24'])).
% 0.36/0.55  thf('26', plain,
% 0.36/0.55      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf(l3_subset_1, axiom,
% 0.36/0.55    (![A:$i,B:$i]:
% 0.36/0.55     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.36/0.55       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.36/0.55  thf('27', plain,
% 0.36/0.55      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.36/0.55         (~ (r2_hidden @ X5 @ X6)
% 0.36/0.55          | (r2_hidden @ X5 @ X7)
% 0.36/0.55          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.36/0.55      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.36/0.55  thf('28', plain,
% 0.36/0.55      (![X0 : $i]:
% 0.36/0.55         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_B @ sk_C_1))
% 0.36/0.55          | ~ (r2_hidden @ X0 @ sk_D_2))),
% 0.36/0.55      inference('sup-', [status(thm)], ['26', '27'])).
% 0.36/0.55  thf('29', plain,
% 0.36/0.55      ((r2_hidden @ (k4_tarski @ (sk_D_1 @ sk_A @ sk_D_2) @ sk_A) @ 
% 0.36/0.55        (k2_zfmisc_1 @ sk_B @ sk_C_1))),
% 0.36/0.55      inference('sup-', [status(thm)], ['25', '28'])).
% 0.36/0.55  thf(l54_zfmisc_1, axiom,
% 0.36/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.36/0.55     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.36/0.55       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.36/0.55  thf('30', plain,
% 0.36/0.55      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.36/0.55         ((r2_hidden @ X0 @ X1)
% 0.36/0.55          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 0.36/0.55      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.36/0.55  thf('31', plain, ((r2_hidden @ (sk_D_1 @ sk_A @ sk_D_2) @ sk_B)),
% 0.36/0.55      inference('sup-', [status(thm)], ['29', '30'])).
% 0.36/0.55  thf(t1_subset, axiom,
% 0.36/0.55    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.36/0.55  thf('32', plain,
% 0.36/0.55      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.36/0.55      inference('cnf', [status(esa)], [t1_subset])).
% 0.36/0.55  thf('33', plain, ((m1_subset_1 @ (sk_D_1 @ sk_A @ sk_D_2) @ sk_B)),
% 0.36/0.55      inference('sup-', [status(thm)], ['31', '32'])).
% 0.36/0.55  thf('34', plain,
% 0.36/0.55      (![X26 : $i]:
% 0.36/0.55         (((sk_A) != (k1_funct_1 @ sk_D_2 @ X26))
% 0.36/0.55          | ~ (m1_subset_1 @ X26 @ sk_B))),
% 0.36/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.55  thf('35', plain,
% 0.36/0.55      (((sk_A) != (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_A @ sk_D_2)))),
% 0.36/0.55      inference('sup-', [status(thm)], ['33', '34'])).
% 0.36/0.55  thf('36', plain,
% 0.36/0.55      (((sk_A) = (k1_funct_1 @ sk_D_2 @ (sk_D_1 @ sk_A @ sk_D_2)))),
% 0.36/0.55      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.36/0.55  thf('37', plain, (((sk_A) != (sk_A))),
% 0.36/0.55      inference('demod', [status(thm)], ['35', '36'])).
% 0.36/0.55  thf('38', plain, ($false), inference('simplify', [status(thm)], ['37'])).
% 0.36/0.55  
% 0.36/0.55  % SZS output end Refutation
% 0.36/0.55  
% 0.36/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
