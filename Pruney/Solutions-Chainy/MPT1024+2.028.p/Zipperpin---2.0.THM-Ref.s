%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jhrqudWCBX

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:37 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 110 expanded)
%              Number of leaves         :   25 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  426 (1402 expanded)
%              Number of equality atoms :   15 (  48 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( ( k7_relset_1 @ X23 @ X24 @ X22 @ X25 )
        = ( k9_relat_1 @ X22 @ X25 ) ) ) ),
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
    ! [X9: $i,X10: $i,X12: $i,X13: $i] :
      ( ( X12
       != ( k9_relat_1 @ X10 @ X9 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ X13 @ X9 @ X10 ) @ X13 ) @ X10 )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf('6',plain,(
    ! [X9: $i,X10: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( r2_hidden @ X13 @ ( k9_relat_1 @ X10 @ X9 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ X13 @ X9 @ X10 ) @ X13 ) @ X10 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( r2_hidden @ ( k4_tarski @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 ) @ sk_D_1 )
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('10',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 ) @ sk_D_1 ),
    inference(demod,[status(thm)],['7','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('13',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ( r2_hidden @ X5 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf(l54_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ X0 @ X2 ) @ ( k2_zfmisc_1 @ X1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l54_zfmisc_1])).

thf('17',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X26: $i] :
      ( ~ ( r2_hidden @ X26 @ sk_A )
      | ~ ( r2_hidden @ X26 @ sk_C )
      | ( sk_E_2
       != ( k1_funct_1 @ sk_D_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( sk_E_2
     != ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) ) )
    | ~ ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 ) @ sk_D_1 ),
    inference(demod,[status(thm)],['7','10'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X16 @ X18 ) @ X17 )
      | ( X18
        = ( k1_funct_1 @ X17 @ X16 ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_E_2
      = ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['8','9'])).

thf('24',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( sk_E_2
    = ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
    r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('27',plain,(
    ! [X9: $i,X10: $i,X12: $i,X13: $i] :
      ( ( X12
       != ( k9_relat_1 @ X10 @ X9 ) )
      | ( r2_hidden @ ( sk_E_1 @ X13 @ X9 @ X10 ) @ X9 )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d13_relat_1])).

thf('28',plain,(
    ! [X9: $i,X10: $i,X13: $i] :
      ( ~ ( v1_relat_1 @ X10 )
      | ~ ( r2_hidden @ X13 @ ( k9_relat_1 @ X10 @ X9 ) )
      | ( r2_hidden @ ( sk_E_1 @ X13 @ X9 @ X10 ) @ X9 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_C )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['8','9'])).

thf('31',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    sk_E_2 != sk_E_2 ),
    inference(demod,[status(thm)],['19','25','31'])).

thf('33',plain,(
    $false ),
    inference(simplify,[status(thm)],['32'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.jhrqudWCBX
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:28:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.44/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.44/0.63  % Solved by: fo/fo7.sh
% 0.44/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.63  % done 80 iterations in 0.176s
% 0.44/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.44/0.63  % SZS output start Refutation
% 0.44/0.63  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.44/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.44/0.63  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.44/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.63  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.44/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.44/0.63  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.44/0.63  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.44/0.63  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.44/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.63  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.44/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.63  thf(t115_funct_2, conjecture,
% 0.44/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.63     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.44/0.63         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.63       ( ![E:$i]:
% 0.44/0.63         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.44/0.63              ( ![F:$i]:
% 0.44/0.63                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.44/0.63                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.44/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.63    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.63        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.44/0.63            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.44/0.63          ( ![E:$i]:
% 0.44/0.63            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.44/0.63                 ( ![F:$i]:
% 0.44/0.63                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.44/0.63                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 0.44/0.63    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 0.44/0.63  thf('0', plain,
% 0.44/0.63      ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('1', plain,
% 0.44/0.63      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf(redefinition_k7_relset_1, axiom,
% 0.44/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.63       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.44/0.63  thf('2', plain,
% 0.44/0.63      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.44/0.63         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.44/0.63          | ((k7_relset_1 @ X23 @ X24 @ X22 @ X25) = (k9_relat_1 @ X22 @ X25)))),
% 0.44/0.63      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.44/0.63  thf('3', plain,
% 0.44/0.63      (![X0 : $i]:
% 0.44/0.63         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.44/0.63           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.44/0.63      inference('sup-', [status(thm)], ['1', '2'])).
% 0.44/0.63  thf('4', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.44/0.63      inference('demod', [status(thm)], ['0', '3'])).
% 0.44/0.63  thf(d13_relat_1, axiom,
% 0.44/0.63    (![A:$i]:
% 0.44/0.63     ( ( v1_relat_1 @ A ) =>
% 0.44/0.63       ( ![B:$i,C:$i]:
% 0.44/0.63         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.44/0.63           ( ![D:$i]:
% 0.44/0.63             ( ( r2_hidden @ D @ C ) <=>
% 0.44/0.63               ( ?[E:$i]:
% 0.44/0.63                 ( ( r2_hidden @ E @ B ) & 
% 0.44/0.63                   ( r2_hidden @ ( k4_tarski @ E @ D ) @ A ) ) ) ) ) ) ) ))).
% 0.44/0.63  thf('5', plain,
% 0.44/0.63      (![X9 : $i, X10 : $i, X12 : $i, X13 : $i]:
% 0.44/0.63         (((X12) != (k9_relat_1 @ X10 @ X9))
% 0.44/0.63          | (r2_hidden @ (k4_tarski @ (sk_E_1 @ X13 @ X9 @ X10) @ X13) @ X10)
% 0.44/0.63          | ~ (r2_hidden @ X13 @ X12)
% 0.44/0.63          | ~ (v1_relat_1 @ X10))),
% 0.44/0.63      inference('cnf', [status(esa)], [d13_relat_1])).
% 0.44/0.63  thf('6', plain,
% 0.44/0.63      (![X9 : $i, X10 : $i, X13 : $i]:
% 0.44/0.63         (~ (v1_relat_1 @ X10)
% 0.44/0.63          | ~ (r2_hidden @ X13 @ (k9_relat_1 @ X10 @ X9))
% 0.44/0.63          | (r2_hidden @ (k4_tarski @ (sk_E_1 @ X13 @ X9 @ X10) @ X13) @ X10))),
% 0.44/0.63      inference('simplify', [status(thm)], ['5'])).
% 0.44/0.63  thf('7', plain,
% 0.44/0.63      (((r2_hidden @ 
% 0.44/0.63         (k4_tarski @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2) @ sk_D_1)
% 0.44/0.63        | ~ (v1_relat_1 @ sk_D_1))),
% 0.44/0.63      inference('sup-', [status(thm)], ['4', '6'])).
% 0.44/0.63  thf('8', plain,
% 0.44/0.63      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf(cc1_relset_1, axiom,
% 0.44/0.63    (![A:$i,B:$i,C:$i]:
% 0.44/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.63       ( v1_relat_1 @ C ) ))).
% 0.44/0.63  thf('9', plain,
% 0.44/0.63      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.44/0.63         ((v1_relat_1 @ X19)
% 0.44/0.63          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.44/0.63      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.44/0.63  thf('10', plain, ((v1_relat_1 @ sk_D_1)),
% 0.44/0.63      inference('sup-', [status(thm)], ['8', '9'])).
% 0.44/0.63  thf('11', plain,
% 0.44/0.63      ((r2_hidden @ (k4_tarski @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2) @ 
% 0.44/0.63        sk_D_1)),
% 0.44/0.63      inference('demod', [status(thm)], ['7', '10'])).
% 0.44/0.63  thf('12', plain,
% 0.44/0.63      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf(l3_subset_1, axiom,
% 0.44/0.63    (![A:$i,B:$i]:
% 0.44/0.63     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.44/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.44/0.63  thf('13', plain,
% 0.44/0.63      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.44/0.63         (~ (r2_hidden @ X5 @ X6)
% 0.44/0.63          | (r2_hidden @ X5 @ X7)
% 0.44/0.63          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.44/0.63      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.44/0.63  thf('14', plain,
% 0.44/0.63      (![X0 : $i]:
% 0.44/0.63         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_A @ sk_B))
% 0.44/0.63          | ~ (r2_hidden @ X0 @ sk_D_1))),
% 0.44/0.63      inference('sup-', [status(thm)], ['12', '13'])).
% 0.44/0.63  thf('15', plain,
% 0.44/0.63      ((r2_hidden @ (k4_tarski @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2) @ 
% 0.44/0.63        (k2_zfmisc_1 @ sk_A @ sk_B))),
% 0.44/0.63      inference('sup-', [status(thm)], ['11', '14'])).
% 0.44/0.63  thf(l54_zfmisc_1, axiom,
% 0.44/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.44/0.63     ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) ) <=>
% 0.44/0.63       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ D ) ) ))).
% 0.44/0.63  thf('16', plain,
% 0.44/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.44/0.63         ((r2_hidden @ X0 @ X1)
% 0.44/0.63          | ~ (r2_hidden @ (k4_tarski @ X0 @ X2) @ (k2_zfmisc_1 @ X1 @ X3)))),
% 0.44/0.63      inference('cnf', [status(esa)], [l54_zfmisc_1])).
% 0.44/0.63  thf('17', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_A)),
% 0.44/0.63      inference('sup-', [status(thm)], ['15', '16'])).
% 0.44/0.63  thf('18', plain,
% 0.44/0.63      (![X26 : $i]:
% 0.44/0.63         (~ (r2_hidden @ X26 @ sk_A)
% 0.44/0.63          | ~ (r2_hidden @ X26 @ sk_C)
% 0.44/0.63          | ((sk_E_2) != (k1_funct_1 @ sk_D_1 @ X26)))),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('19', plain,
% 0.44/0.63      ((((sk_E_2) != (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1)))
% 0.44/0.63        | ~ (r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_C))),
% 0.44/0.63      inference('sup-', [status(thm)], ['17', '18'])).
% 0.44/0.63  thf('20', plain,
% 0.44/0.63      ((r2_hidden @ (k4_tarski @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2) @ 
% 0.44/0.63        sk_D_1)),
% 0.44/0.63      inference('demod', [status(thm)], ['7', '10'])).
% 0.44/0.63  thf(t8_funct_1, axiom,
% 0.44/0.63    (![A:$i,B:$i,C:$i]:
% 0.44/0.63     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.44/0.63       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.44/0.63         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.44/0.63           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.44/0.63  thf('21', plain,
% 0.44/0.63      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.44/0.63         (~ (r2_hidden @ (k4_tarski @ X16 @ X18) @ X17)
% 0.44/0.63          | ((X18) = (k1_funct_1 @ X17 @ X16))
% 0.44/0.63          | ~ (v1_funct_1 @ X17)
% 0.44/0.63          | ~ (v1_relat_1 @ X17))),
% 0.44/0.63      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.44/0.63  thf('22', plain,
% 0.44/0.63      ((~ (v1_relat_1 @ sk_D_1)
% 0.44/0.63        | ~ (v1_funct_1 @ sk_D_1)
% 0.44/0.63        | ((sk_E_2) = (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1))))),
% 0.44/0.63      inference('sup-', [status(thm)], ['20', '21'])).
% 0.44/0.63  thf('23', plain, ((v1_relat_1 @ sk_D_1)),
% 0.44/0.63      inference('sup-', [status(thm)], ['8', '9'])).
% 0.44/0.63  thf('24', plain, ((v1_funct_1 @ sk_D_1)),
% 0.44/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.63  thf('25', plain,
% 0.44/0.63      (((sk_E_2) = (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1)))),
% 0.44/0.63      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.44/0.63  thf('26', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.44/0.63      inference('demod', [status(thm)], ['0', '3'])).
% 0.44/0.63  thf('27', plain,
% 0.44/0.63      (![X9 : $i, X10 : $i, X12 : $i, X13 : $i]:
% 0.44/0.63         (((X12) != (k9_relat_1 @ X10 @ X9))
% 0.44/0.63          | (r2_hidden @ (sk_E_1 @ X13 @ X9 @ X10) @ X9)
% 0.44/0.63          | ~ (r2_hidden @ X13 @ X12)
% 0.44/0.63          | ~ (v1_relat_1 @ X10))),
% 0.44/0.63      inference('cnf', [status(esa)], [d13_relat_1])).
% 0.44/0.63  thf('28', plain,
% 0.44/0.63      (![X9 : $i, X10 : $i, X13 : $i]:
% 0.44/0.63         (~ (v1_relat_1 @ X10)
% 0.44/0.63          | ~ (r2_hidden @ X13 @ (k9_relat_1 @ X10 @ X9))
% 0.44/0.63          | (r2_hidden @ (sk_E_1 @ X13 @ X9 @ X10) @ X9))),
% 0.44/0.63      inference('simplify', [status(thm)], ['27'])).
% 0.44/0.63  thf('29', plain,
% 0.44/0.63      (((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_C)
% 0.44/0.63        | ~ (v1_relat_1 @ sk_D_1))),
% 0.44/0.63      inference('sup-', [status(thm)], ['26', '28'])).
% 0.44/0.63  thf('30', plain, ((v1_relat_1 @ sk_D_1)),
% 0.44/0.63      inference('sup-', [status(thm)], ['8', '9'])).
% 0.44/0.63  thf('31', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_C)),
% 0.44/0.63      inference('demod', [status(thm)], ['29', '30'])).
% 0.44/0.63  thf('32', plain, (((sk_E_2) != (sk_E_2))),
% 0.44/0.63      inference('demod', [status(thm)], ['19', '25', '31'])).
% 0.44/0.63  thf('33', plain, ($false), inference('simplify', [status(thm)], ['32'])).
% 0.44/0.63  
% 0.44/0.63  % SZS output end Refutation
% 0.44/0.63  
% 0.44/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
