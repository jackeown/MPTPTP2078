%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.d0dTg0jTlT

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:47 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 114 expanded)
%              Number of leaves         :   26 (  45 expanded)
%              Depth                    :   11
%              Number of atoms          :  456 (1432 expanded)
%              Number of equality atoms :   15 (  48 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ),
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
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k7_relset_1 @ X25 @ X26 @ X24 @ X27 )
        = ( k9_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(d13_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ B )
                  & ( r2_hidden @ ( k4_tarski @ E @ D ) @ A ) ) ) ) ) )).

thf('5',plain,(
    ! [X11: $i,X12: $i,X14: $i,X15: $i] :
      ( ( X14
       != ( k9_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( sk_E_1 @ X15 @ X11 @ X12 ) @ X11 )
      | ~ ( r2_hidden @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf('6',plain,(
    ! [X11: $i,X12: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( r2_hidden @ X15 @ ( k9_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( sk_E_1 @ X15 @ X11 @ X12 ) @ X11 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_C )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('10',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_C ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    ! [X28: $i] :
      ( ( sk_E_2
       != ( k1_funct_1 @ sk_D_1 @ X28 ) )
      | ~ ( r2_hidden @ X28 @ sk_C )
      | ~ ( m1_subset_1 @ X28 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_A )
    | ( sk_E_2
     != ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('15',plain,(
    ! [X11: $i,X12: $i,X14: $i,X15: $i] :
      ( ( X14
       != ( k9_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ X15 @ X11 @ X12 ) @ X15 ) @ X12 )
      | ~ ( r2_hidden @ X15 @ X14 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf('16',plain,(
    ! [X11: $i,X12: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X12 )
      | ~ ( r2_hidden @ X15 @ ( k9_relat_1 @ X12 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ X15 @ X11 @ X12 ) @ X15 ) @ X12 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 ) @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['8','9'])).

thf('19',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 ) @ sk_D_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('20',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X18 @ X20 ) @ X19 )
      | ( X20
        = ( k1_funct_1 @ X19 @ X18 ) )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_E_2
      = ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['8','9'])).

thf('23',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( sk_E_2
    = ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ~ ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_A )
    | ( sk_E_2 != sk_E_2 ) ),
    inference(demod,[status(thm)],['13','24'])).

thf('26',plain,(
    ~ ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 ) @ sk_D_1 ),
    inference(demod,[status(thm)],['17','18'])).

thf('28',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('29',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('33',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('34',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('35',plain,(
    m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    $false ),
    inference(demod,[status(thm)],['26','35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.d0dTg0jTlT
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:54:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.57  % Solved by: fo/fo7.sh
% 0.20/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.57  % done 85 iterations in 0.116s
% 0.20/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.57  % SZS output start Refutation
% 0.20/0.57  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.57  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.57  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.57  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.20/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.57  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.57  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.20/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.57  thf(t116_funct_2, conjecture,
% 0.20/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.57     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.57       ( ![E:$i]:
% 0.20/0.57         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.20/0.57              ( ![F:$i]:
% 0.20/0.57                ( ( m1_subset_1 @ F @ A ) =>
% 0.20/0.57                  ( ~( ( r2_hidden @ F @ C ) & 
% 0.20/0.57                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.57    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.57        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.57            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.57          ( ![E:$i]:
% 0.20/0.57            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.20/0.57                 ( ![F:$i]:
% 0.20/0.57                   ( ( m1_subset_1 @ F @ A ) =>
% 0.20/0.57                     ( ~( ( r2_hidden @ F @ C ) & 
% 0.20/0.57                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.57    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 0.20/0.57  thf('0', plain,
% 0.20/0.57      ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('1', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(redefinition_k7_relset_1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.57       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.20/0.57  thf('2', plain,
% 0.20/0.57      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.57         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.20/0.57          | ((k7_relset_1 @ X25 @ X26 @ X24 @ X27) = (k9_relat_1 @ X24 @ X27)))),
% 0.20/0.57      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.20/0.57  thf('3', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.20/0.57           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.20/0.57      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.57  thf('4', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.20/0.57      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.57  thf(d13_relat_1, axiom,
% 0.20/0.57    (![A:$i]:
% 0.20/0.57     ( ( v1_relat_1 @ A ) =>
% 0.20/0.57       ( ![B:$i,C:$i]:
% 0.20/0.57         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.20/0.57           ( ![D:$i]:
% 0.20/0.57             ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.57               ( ?[E:$i]:
% 0.20/0.57                 ( ( r2_hidden @ E @ B ) & 
% 0.20/0.57                   ( r2_hidden @ ( k4_tarski @ E @ D ) @ A ) ) ) ) ) ) ) ))).
% 0.20/0.57  thf('5', plain,
% 0.20/0.57      (![X11 : $i, X12 : $i, X14 : $i, X15 : $i]:
% 0.20/0.57         (((X14) != (k9_relat_1 @ X12 @ X11))
% 0.20/0.57          | (r2_hidden @ (sk_E_1 @ X15 @ X11 @ X12) @ X11)
% 0.20/0.57          | ~ (r2_hidden @ X15 @ X14)
% 0.20/0.57          | ~ (v1_relat_1 @ X12))),
% 0.20/0.57      inference('cnf', [status(esa)], [d13_relat_1])).
% 0.20/0.57  thf('6', plain,
% 0.20/0.57      (![X11 : $i, X12 : $i, X15 : $i]:
% 0.20/0.57         (~ (v1_relat_1 @ X12)
% 0.20/0.57          | ~ (r2_hidden @ X15 @ (k9_relat_1 @ X12 @ X11))
% 0.20/0.57          | (r2_hidden @ (sk_E_1 @ X15 @ X11 @ X12) @ X11))),
% 0.20/0.57      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.57  thf('7', plain,
% 0.20/0.57      (((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_C)
% 0.20/0.57        | ~ (v1_relat_1 @ sk_D_1))),
% 0.20/0.57      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.57  thf('8', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(cc1_relset_1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.57       ( v1_relat_1 @ C ) ))).
% 0.20/0.57  thf('9', plain,
% 0.20/0.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.57         ((v1_relat_1 @ X21)
% 0.20/0.57          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.20/0.57      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.57  thf('10', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.57  thf('11', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_C)),
% 0.20/0.57      inference('demod', [status(thm)], ['7', '10'])).
% 0.20/0.57  thf('12', plain,
% 0.20/0.57      (![X28 : $i]:
% 0.20/0.57         (((sk_E_2) != (k1_funct_1 @ sk_D_1 @ X28))
% 0.20/0.57          | ~ (r2_hidden @ X28 @ sk_C)
% 0.20/0.57          | ~ (m1_subset_1 @ X28 @ sk_A))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('13', plain,
% 0.20/0.57      ((~ (m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_A)
% 0.20/0.57        | ((sk_E_2)
% 0.20/0.57            != (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.57  thf('14', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.20/0.57      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.57  thf('15', plain,
% 0.20/0.57      (![X11 : $i, X12 : $i, X14 : $i, X15 : $i]:
% 0.20/0.57         (((X14) != (k9_relat_1 @ X12 @ X11))
% 0.20/0.57          | (r2_hidden @ (k4_tarski @ (sk_E_1 @ X15 @ X11 @ X12) @ X15) @ X12)
% 0.20/0.57          | ~ (r2_hidden @ X15 @ X14)
% 0.20/0.57          | ~ (v1_relat_1 @ X12))),
% 0.20/0.57      inference('cnf', [status(esa)], [d13_relat_1])).
% 0.20/0.57  thf('16', plain,
% 0.20/0.57      (![X11 : $i, X12 : $i, X15 : $i]:
% 0.20/0.57         (~ (v1_relat_1 @ X12)
% 0.20/0.57          | ~ (r2_hidden @ X15 @ (k9_relat_1 @ X12 @ X11))
% 0.20/0.57          | (r2_hidden @ (k4_tarski @ (sk_E_1 @ X15 @ X11 @ X12) @ X15) @ X12))),
% 0.20/0.57      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.57  thf('17', plain,
% 0.20/0.57      (((r2_hidden @ 
% 0.20/0.57         (k4_tarski @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2) @ sk_D_1)
% 0.20/0.57        | ~ (v1_relat_1 @ sk_D_1))),
% 0.20/0.57      inference('sup-', [status(thm)], ['14', '16'])).
% 0.20/0.57  thf('18', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.57  thf('19', plain,
% 0.20/0.57      ((r2_hidden @ (k4_tarski @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2) @ 
% 0.20/0.57        sk_D_1)),
% 0.20/0.57      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.57  thf(t8_funct_1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i]:
% 0.20/0.57     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.57       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.20/0.57         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.20/0.57           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.20/0.57  thf('20', plain,
% 0.20/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.20/0.57         (~ (r2_hidden @ (k4_tarski @ X18 @ X20) @ X19)
% 0.20/0.57          | ((X20) = (k1_funct_1 @ X19 @ X18))
% 0.20/0.57          | ~ (v1_funct_1 @ X19)
% 0.20/0.57          | ~ (v1_relat_1 @ X19))),
% 0.20/0.57      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.20/0.57  thf('21', plain,
% 0.20/0.57      ((~ (v1_relat_1 @ sk_D_1)
% 0.20/0.57        | ~ (v1_funct_1 @ sk_D_1)
% 0.20/0.57        | ((sk_E_2) = (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1))))),
% 0.20/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.57  thf('22', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.57  thf('23', plain, ((v1_funct_1 @ sk_D_1)),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf('24', plain,
% 0.20/0.57      (((sk_E_2) = (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1)))),
% 0.20/0.57      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.20/0.57  thf('25', plain,
% 0.20/0.57      ((~ (m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_A)
% 0.20/0.57        | ((sk_E_2) != (sk_E_2)))),
% 0.20/0.57      inference('demod', [status(thm)], ['13', '24'])).
% 0.20/0.57  thf('26', plain,
% 0.20/0.57      (~ (m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_A)),
% 0.20/0.57      inference('simplify', [status(thm)], ['25'])).
% 0.20/0.57  thf('27', plain,
% 0.20/0.57      ((r2_hidden @ (k4_tarski @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2) @ 
% 0.20/0.57        sk_D_1)),
% 0.20/0.57      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.57  thf('28', plain,
% 0.20/0.57      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.57  thf(l3_subset_1, axiom,
% 0.20/0.57    (![A:$i,B:$i]:
% 0.20/0.57     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.57  thf('29', plain,
% 0.20/0.57      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.20/0.57         (~ (r2_hidden @ X5 @ X6)
% 0.20/0.57          | (r2_hidden @ X5 @ X7)
% 0.20/0.57          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.20/0.57      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.20/0.57  thf('30', plain,
% 0.20/0.57      (![X0 : $i]:
% 0.20/0.57         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.20/0.57          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.20/0.57      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.57  thf('31', plain,
% 0.20/0.57      ((r2_hidden @ (k4_tarski @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2) @ 
% 0.20/0.57        (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.20/0.57      inference('sup-', [status(thm)], ['27', '30'])).
% 0.20/0.57  thf(l54_zfmisc_1, axiom,
% 0.20/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.57     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.20/0.57       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.20/0.57  thf('32', plain,
% 0.20/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.57         ((r2_hidden @ X0 @ X1)
% 0.20/0.57          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 0.20/0.57      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.20/0.57  thf('33', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_A)),
% 0.20/0.57      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.57  thf(t1_subset, axiom,
% 0.20/0.57    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.20/0.57  thf('34', plain,
% 0.20/0.57      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.20/0.57      inference('cnf', [status(esa)], [t1_subset])).
% 0.20/0.57  thf('35', plain, ((m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_A)),
% 0.20/0.57      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.57  thf('36', plain, ($false), inference('demod', [status(thm)], ['26', '35'])).
% 0.20/0.57  
% 0.20/0.57  % SZS output end Refutation
% 0.20/0.57  
% 0.41/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
