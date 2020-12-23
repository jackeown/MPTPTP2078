%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CgsxdP9f4O

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 145 expanded)
%              Number of leaves         :   33 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  477 (1713 expanded)
%              Number of equality atoms :   15 (  55 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( ( k7_relset_1 @ X29 @ X30 @ X28 @ X31 )
        = ( k9_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(d12_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_funct_1 @ A )
        & ( v1_relat_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) )
                  & ( r2_hidden @ E @ B )
                  & ( D
                    = ( k1_funct_1 @ A @ E ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( D
          = ( k1_funct_1 @ A @ E ) )
        & ( r2_hidden @ E @ B )
        & ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) )).

thf('5',plain,(
    ! [X18: $i,X19: $i,X21: $i,X22: $i] :
      ( ( X21
       != ( k9_relat_1 @ X19 @ X18 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X22 @ X18 @ X19 ) @ X22 @ X18 @ X19 )
      | ~ ( r2_hidden @ X22 @ X21 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X18: $i,X19: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( r2_hidden @ X22 @ ( k9_relat_1 @ X19 @ X18 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X22 @ X18 @ X19 ) @ X22 @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 @ sk_C @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 @ sk_C @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8','13'])).

thf('15',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X13 @ ( k1_relat_1 @ X12 ) )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('16',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('19',plain,(
    v4_relat_1 @ sk_D_1 @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('20',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( v4_relat_1 @ X8 @ X9 )
      | ( r1_tarski @ ( k1_relat_1 @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('23',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ),
    inference(demod,[status(thm)],['21','22'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X3: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X5 ) )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['16','27'])).

thf('29',plain,(
    ! [X32: $i] :
      ( ~ ( r2_hidden @ X32 @ sk_A )
      | ~ ( r2_hidden @ X32 @ sk_C )
      | ( sk_E_2
       != ( k1_funct_1 @ sk_D_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( sk_E_2
     != ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) ) )
    | ~ ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 @ sk_C @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8','13'])).

thf('32',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X14
        = ( k1_funct_1 @ X12 @ X13 ) )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('33',plain,
    ( sk_E_2
    = ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 @ sk_C @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8','13'])).

thf('35',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X13 @ X15 )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('36',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_C ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    sk_E_2 != sk_E_2 ),
    inference(demod,[status(thm)],['30','33','36'])).

thf('38',plain,(
    $false ),
    inference(simplify,[status(thm)],['37'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.CgsxdP9f4O
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:37:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.34  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 79 iterations in 0.061s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.20/0.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.51  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.51  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.51  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(t115_funct_2, conjecture,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.51         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.51       ( ![E:$i]:
% 0.20/0.51         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.20/0.51              ( ![F:$i]:
% 0.20/0.51                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.20/0.51                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.51            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.51          ( ![E:$i]:
% 0.20/0.51            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.20/0.51                 ( ![F:$i]:
% 0.20/0.51                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.20/0.51                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(redefinition_k7_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.20/0.51          | ((k7_relset_1 @ X29 @ X30 @ X28 @ X31) = (k9_relat_1 @ X28 @ X31)))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.20/0.51           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.51  thf('4', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.20/0.51      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.51  thf(d12_funct_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.20/0.51       ( ![B:$i,C:$i]:
% 0.20/0.51         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.20/0.51           ( ![D:$i]:
% 0.20/0.51             ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.51               ( ?[E:$i]:
% 0.20/0.51                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 0.20/0.51                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.51  thf(zf_stmt_2, axiom,
% 0.20/0.51    (![E:$i,D:$i,B:$i,A:$i]:
% 0.20/0.51     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.20/0.51       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 0.20/0.51         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_3, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.20/0.51       ( ![B:$i,C:$i]:
% 0.20/0.51         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.20/0.51           ( ![D:$i]:
% 0.20/0.51             ( ( r2_hidden @ D @ C ) <=>
% 0.20/0.51               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 0.20/0.51  thf('5', plain,
% 0.20/0.51      (![X18 : $i, X19 : $i, X21 : $i, X22 : $i]:
% 0.20/0.51         (((X21) != (k9_relat_1 @ X19 @ X18))
% 0.20/0.51          | (zip_tseitin_0 @ (sk_E_1 @ X22 @ X18 @ X19) @ X22 @ X18 @ X19)
% 0.20/0.51          | ~ (r2_hidden @ X22 @ X21)
% 0.20/0.51          | ~ (v1_funct_1 @ X19)
% 0.20/0.51          | ~ (v1_relat_1 @ X19))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X18 : $i, X19 : $i, X22 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X19)
% 0.20/0.51          | ~ (v1_funct_1 @ X19)
% 0.20/0.51          | ~ (r2_hidden @ X22 @ (k9_relat_1 @ X19 @ X18))
% 0.20/0.51          | (zip_tseitin_0 @ (sk_E_1 @ X22 @ X18 @ X19) @ X22 @ X18 @ X19))),
% 0.20/0.51      inference('simplify', [status(thm)], ['5'])).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.20/0.51         sk_D_1)
% 0.20/0.51        | ~ (v1_funct_1 @ sk_D_1)
% 0.20/0.51        | ~ (v1_relat_1 @ sk_D_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['4', '6'])).
% 0.20/0.51  thf('8', plain, ((v1_funct_1 @ sk_D_1)),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(cc2_relat_1, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ A ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.20/0.51          | (v1_relat_1 @ X6)
% 0.20/0.51          | ~ (v1_relat_1 @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.51  thf(fc6_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.51  thf('13', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.20/0.51        sk_D_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.51         ((r2_hidden @ X13 @ (k1_relat_1 @ X12))
% 0.20/0.51          | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X12))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ (k1_relat_1 @ sk_D_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(cc2_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.51         ((v4_relat_1 @ X25 @ X26)
% 0.20/0.51          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.51  thf('19', plain, ((v4_relat_1 @ sk_D_1 @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.51  thf(d18_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ B ) =>
% 0.20/0.51       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i]:
% 0.20/0.51         (~ (v4_relat_1 @ X8 @ X9)
% 0.20/0.51          | (r1_tarski @ (k1_relat_1 @ X8) @ X9)
% 0.20/0.51          | ~ (v1_relat_1 @ X8))),
% 0.20/0.51      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.51  thf('22', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.51  thf('23', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ sk_A)),
% 0.20/0.51      inference('demod', [status(thm)], ['21', '22'])).
% 0.20/0.51  thf(t3_subset, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (![X3 : $i, X5 : $i]:
% 0.20/0.51         ((m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      ((m1_subset_1 @ (k1_relat_1 @ sk_D_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.51  thf(l3_subset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.20/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ X1)
% 0.20/0.51          | (r2_hidden @ X0 @ X2)
% 0.20/0.51          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.20/0.51      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.51  thf('28', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['16', '27'])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      (![X32 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X32 @ sk_A)
% 0.20/0.51          | ~ (r2_hidden @ X32 @ sk_C)
% 0.20/0.51          | ((sk_E_2) != (k1_funct_1 @ sk_D_1 @ X32)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      ((((sk_E_2) != (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1)))
% 0.20/0.51        | ~ (r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.20/0.51        sk_D_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.51         (((X14) = (k1_funct_1 @ X12 @ X13))
% 0.20/0.51          | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X12))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (((sk_E_2) = (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.20/0.51        sk_D_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.51         ((r2_hidden @ X13 @ X15) | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X12))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.51  thf('36', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_C)),
% 0.20/0.51      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.51  thf('37', plain, (((sk_E_2) != (sk_E_2))),
% 0.20/0.51      inference('demod', [status(thm)], ['30', '33', '36'])).
% 0.20/0.51  thf('38', plain, ($false), inference('simplify', [status(thm)], ['37'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
