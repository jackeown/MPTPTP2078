%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hIZhKTNPfB

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:45 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 134 expanded)
%              Number of leaves         :   32 (  55 expanded)
%              Depth                    :   11
%              Number of atoms          :  475 (1669 expanded)
%              Number of equality atoms :   15 (  55 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k7_relset_1 @ X28 @ X29 @ X27 @ X30 )
        = ( k9_relat_1 @ X27 @ X30 ) ) ) ),
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
    ! [X14: $i,X15: $i,X17: $i,X18: $i] :
      ( ( X17
       != ( k9_relat_1 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X18 @ X14 @ X15 ) @ X18 @ X14 @ X15 )
      | ~ ( r2_hidden @ X18 @ X17 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X14: $i,X15: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( r2_hidden @ X18 @ ( k9_relat_1 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X18 @ X14 @ X15 ) @ X18 @ X14 @ X15 ) ) ),
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('10',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 @ sk_C @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('13',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X9 @ X11 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('14',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X31: $i] :
      ( ( sk_E_2
       != ( k1_funct_1 @ sk_D_1 @ X31 ) )
      | ~ ( r2_hidden @ X31 @ sk_C )
      | ~ ( m1_subset_1 @ X31 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_A )
    | ( sk_E_2
     != ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 @ sk_C @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('18',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X10
        = ( k1_funct_1 @ X8 @ X9 ) )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('19',plain,
    ( sk_E_2
    = ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ~ ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_A )
    | ( sk_E_2 != sk_E_2 ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    ~ ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_A ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 @ sk_C @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('23',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X9 @ ( k1_relat_1 @ X8 ) )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('24',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('26',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v4_relat_1 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('27',plain,(
    v4_relat_1 @ sk_D_1 @ sk_A ),
    inference('sup-',[status(thm)],['25','26'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('28',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v4_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('31',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ sk_A ),
    inference(demod,[status(thm)],['29','30'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('32',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('33',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('34',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['24','35'])).

thf('37',plain,(
    $false ),
    inference(demod,[status(thm)],['21','36'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hIZhKTNPfB
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:21:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 80 iterations in 0.063s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.51  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.20/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.51  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.51  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.51  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.51  thf(t116_funct_2, conjecture,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.51         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.51       ( ![E:$i]:
% 0.20/0.51         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.20/0.51              ( ![F:$i]:
% 0.20/0.51                ( ( m1_subset_1 @ F @ A ) =>
% 0.20/0.51                  ( ~( ( r2_hidden @ F @ C ) & 
% 0.20/0.51                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.51            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.51          ( ![E:$i]:
% 0.20/0.51            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.20/0.51                 ( ![F:$i]:
% 0.20/0.51                   ( ( m1_subset_1 @ F @ A ) =>
% 0.20/0.51                     ( ~( ( r2_hidden @ F @ C ) & 
% 0.20/0.51                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t116_funct_2])).
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
% 0.20/0.51      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.51         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.20/0.51          | ((k7_relset_1 @ X28 @ X29 @ X27 @ X30) = (k9_relat_1 @ X27 @ X30)))),
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
% 0.20/0.51      (![X14 : $i, X15 : $i, X17 : $i, X18 : $i]:
% 0.20/0.51         (((X17) != (k9_relat_1 @ X15 @ X14))
% 0.20/0.51          | (zip_tseitin_0 @ (sk_E_1 @ X18 @ X14 @ X15) @ X18 @ X14 @ X15)
% 0.20/0.51          | ~ (r2_hidden @ X18 @ X17)
% 0.20/0.51          | ~ (v1_funct_1 @ X15)
% 0.20/0.51          | ~ (v1_relat_1 @ X15))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.20/0.51  thf('6', plain,
% 0.20/0.51      (![X14 : $i, X15 : $i, X18 : $i]:
% 0.20/0.51         (~ (v1_relat_1 @ X15)
% 0.20/0.51          | ~ (v1_funct_1 @ X15)
% 0.20/0.51          | ~ (r2_hidden @ X18 @ (k9_relat_1 @ X15 @ X14))
% 0.20/0.51          | (zip_tseitin_0 @ (sk_E_1 @ X18 @ X14 @ X15) @ X18 @ X14 @ X15))),
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
% 0.20/0.51  thf(cc1_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( v1_relat_1 @ C ) ))).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.20/0.51         ((v1_relat_1 @ X21)
% 0.20/0.51          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.51  thf('11', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.20/0.51        sk_D_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['7', '8', '11'])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.51         ((r2_hidden @ X9 @ X11) | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X8))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.51  thf('14', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_C)),
% 0.20/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      (![X31 : $i]:
% 0.20/0.51         (((sk_E_2) != (k1_funct_1 @ sk_D_1 @ X31))
% 0.20/0.51          | ~ (r2_hidden @ X31 @ sk_C)
% 0.20/0.51          | ~ (m1_subset_1 @ X31 @ sk_A))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      ((~ (m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_A)
% 0.20/0.51        | ((sk_E_2)
% 0.20/0.51            != (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1))))),
% 0.20/0.51      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.20/0.51        sk_D_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['7', '8', '11'])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.51         (((X10) = (k1_funct_1 @ X8 @ X9))
% 0.20/0.51          | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X8))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (((sk_E_2) = (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['17', '18'])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      ((~ (m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_A)
% 0.20/0.51        | ((sk_E_2) != (sk_E_2)))),
% 0.20/0.51      inference('demod', [status(thm)], ['16', '19'])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      (~ (m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_A)),
% 0.20/0.51      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.20/0.51        sk_D_1)),
% 0.20/0.51      inference('demod', [status(thm)], ['7', '8', '11'])).
% 0.20/0.51  thf('23', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.51         ((r2_hidden @ X9 @ (k1_relat_1 @ X8))
% 0.20/0.51          | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X8))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ (k1_relat_1 @ sk_D_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(cc2_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.51         ((v4_relat_1 @ X24 @ X25)
% 0.20/0.51          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.51  thf('27', plain, ((v4_relat_1 @ sk_D_1 @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.51  thf(d18_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ B ) =>
% 0.20/0.51       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.20/0.51  thf('28', plain,
% 0.20/0.51      (![X6 : $i, X7 : $i]:
% 0.20/0.51         (~ (v4_relat_1 @ X6 @ X7)
% 0.20/0.51          | (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 0.20/0.51          | ~ (v1_relat_1 @ X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.20/0.51  thf('29', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.51  thf('30', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.51  thf('31', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ sk_A)),
% 0.20/0.51      inference('demod', [status(thm)], ['29', '30'])).
% 0.20/0.51  thf(t3_subset, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.51  thf('32', plain,
% 0.20/0.51      (![X0 : $i, X2 : $i]:
% 0.20/0.51         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      ((m1_subset_1 @ (k1_relat_1 @ sk_D_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.51  thf(t4_subset, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.20/0.51       ( m1_subset_1 @ A @ C ) ))).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X3 @ X4)
% 0.20/0.51          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.20/0.51          | (m1_subset_1 @ X3 @ X5))),
% 0.20/0.51      inference('cnf', [status(esa)], [t4_subset])).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((m1_subset_1 @ X0 @ sk_A)
% 0.20/0.51          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.51  thf('36', plain, ((m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_A)),
% 0.20/0.51      inference('sup-', [status(thm)], ['24', '35'])).
% 0.20/0.51  thf('37', plain, ($false), inference('demod', [status(thm)], ['21', '36'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
