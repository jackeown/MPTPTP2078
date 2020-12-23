%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6WrNCdRnsV

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:38 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 142 expanded)
%              Number of leaves         :   32 (  58 expanded)
%              Depth                    :   11
%              Number of atoms          :  456 (1692 expanded)
%              Number of equality atoms :   15 (  55 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1 ) ),
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
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( ( k7_relset_1 @ X27 @ X28 @ X26 @ X29 )
        = ( k9_relat_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) ),
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
    ! [X16: $i,X17: $i,X19: $i,X20: $i] :
      ( ( X19
       != ( k9_relat_1 @ X17 @ X16 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X20 @ X16 @ X17 ) @ X20 @ X16 @ X17 )
      | ~ ( r2_hidden @ X20 @ X19 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X16: $i,X17: $i,X20: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( r2_hidden @ X20 @ ( k9_relat_1 @ X17 @ X16 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X20 @ X16 @ X17 ) @ X20 @ X16 @ X17 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1 ) @ sk_E_2 @ sk_C_1 @ sk_D_1 )
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
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('12',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1 ) @ sk_E_2 @ sk_C_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8','13'])).

thf('15',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X11 @ ( k1_relat_1 @ X10 ) )
      | ~ ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('16',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1 ) @ ( k1_relat_1 @ sk_D_1 ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v4_relat_1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
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
    ! [X6: $i,X7: $i] :
      ( ~ ( v4_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
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

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['16','25'])).

thf('27',plain,(
    ! [X30: $i] :
      ( ~ ( r2_hidden @ X30 @ sk_A )
      | ~ ( r2_hidden @ X30 @ sk_C_1 )
      | ( sk_E_2
       != ( k1_funct_1 @ sk_D_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( sk_E_2
     != ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1 ) ) )
    | ~ ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1 ) @ sk_E_2 @ sk_C_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8','13'])).

thf('30',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X12
        = ( k1_funct_1 @ X10 @ X11 ) )
      | ~ ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('31',plain,
    ( sk_E_2
    = ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1 ) @ sk_E_2 @ sk_C_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8','13'])).

thf('33',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( r2_hidden @ X11 @ X13 )
      | ~ ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('34',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1 ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    sk_E_2 != sk_E_2 ),
    inference(demod,[status(thm)],['28','31','34'])).

thf('36',plain,(
    $false ),
    inference(simplify,[status(thm)],['35'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6WrNCdRnsV
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:45:06 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.22/0.36  % Number of cores: 8
% 0.22/0.36  % Python version: Python 3.6.8
% 0.22/0.36  % Running in FO mode
% 0.22/0.50  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.50  % Solved by: fo/fo7.sh
% 0.22/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.50  % done 79 iterations in 0.039s
% 0.22/0.50  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.50  % SZS output start Refutation
% 0.22/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.50  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.22/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.50  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.50  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.50  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.22/0.50  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.22/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.50  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.50  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.22/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.22/0.50  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.50  thf(t115_funct_2, conjecture,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.50         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.50       ( ![E:$i]:
% 0.22/0.50         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.22/0.50              ( ![F:$i]:
% 0.22/0.50                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.22/0.50                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.50    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.50            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.50          ( ![E:$i]:
% 0.22/0.50            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.22/0.50                 ( ![F:$i]:
% 0.22/0.50                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.22/0.50                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 0.22/0.50    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 0.22/0.50  thf('0', plain,
% 0.22/0.50      ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C_1))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('1', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(redefinition_k7_relset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.22/0.50  thf('2', plain,
% 0.22/0.50      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.22/0.50          | ((k7_relset_1 @ X27 @ X28 @ X26 @ X29) = (k9_relat_1 @ X26 @ X29)))),
% 0.22/0.50      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.22/0.50  thf('3', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.22/0.50           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.22/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.50  thf('4', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 0.22/0.50      inference('demod', [status(thm)], ['0', '3'])).
% 0.22/0.50  thf(d12_funct_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.22/0.50       ( ![B:$i,C:$i]:
% 0.22/0.50         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.22/0.50           ( ![D:$i]:
% 0.22/0.50             ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.50               ( ?[E:$i]:
% 0.22/0.50                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 0.22/0.50                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.22/0.50  thf(zf_stmt_2, axiom,
% 0.22/0.50    (![E:$i,D:$i,B:$i,A:$i]:
% 0.22/0.50     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.22/0.50       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 0.22/0.50         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 0.22/0.50  thf(zf_stmt_3, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.22/0.50       ( ![B:$i,C:$i]:
% 0.22/0.50         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.22/0.50           ( ![D:$i]:
% 0.22/0.50             ( ( r2_hidden @ D @ C ) <=>
% 0.22/0.50               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 0.22/0.50  thf('5', plain,
% 0.22/0.50      (![X16 : $i, X17 : $i, X19 : $i, X20 : $i]:
% 0.22/0.50         (((X19) != (k9_relat_1 @ X17 @ X16))
% 0.22/0.50          | (zip_tseitin_0 @ (sk_E_1 @ X20 @ X16 @ X17) @ X20 @ X16 @ X17)
% 0.22/0.50          | ~ (r2_hidden @ X20 @ X19)
% 0.22/0.50          | ~ (v1_funct_1 @ X17)
% 0.22/0.50          | ~ (v1_relat_1 @ X17))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.22/0.50  thf('6', plain,
% 0.22/0.50      (![X16 : $i, X17 : $i, X20 : $i]:
% 0.22/0.50         (~ (v1_relat_1 @ X17)
% 0.22/0.50          | ~ (v1_funct_1 @ X17)
% 0.22/0.50          | ~ (r2_hidden @ X20 @ (k9_relat_1 @ X17 @ X16))
% 0.22/0.50          | (zip_tseitin_0 @ (sk_E_1 @ X20 @ X16 @ X17) @ X20 @ X16 @ X17))),
% 0.22/0.50      inference('simplify', [status(thm)], ['5'])).
% 0.22/0.50  thf('7', plain,
% 0.22/0.50      (((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1) @ sk_E_2 @ 
% 0.22/0.50         sk_C_1 @ sk_D_1)
% 0.22/0.50        | ~ (v1_funct_1 @ sk_D_1)
% 0.22/0.50        | ~ (v1_relat_1 @ sk_D_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['4', '6'])).
% 0.22/0.50  thf('8', plain, ((v1_funct_1 @ sk_D_1)),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('9', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(cc2_relat_1, axiom,
% 0.22/0.50    (![A:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ A ) =>
% 0.22/0.50       ( ![B:$i]:
% 0.22/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.22/0.50  thf('10', plain,
% 0.22/0.50      (![X4 : $i, X5 : $i]:
% 0.22/0.50         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.22/0.50          | (v1_relat_1 @ X4)
% 0.22/0.50          | ~ (v1_relat_1 @ X5))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.22/0.50  thf('11', plain,
% 0.22/0.50      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['9', '10'])).
% 0.22/0.50  thf(fc6_relat_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.22/0.50  thf('12', plain,
% 0.22/0.50      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.22/0.50      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.50  thf('13', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.50  thf('14', plain,
% 0.22/0.50      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1) @ sk_E_2 @ 
% 0.22/0.50        sk_C_1 @ sk_D_1)),
% 0.22/0.50      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.22/0.50  thf('15', plain,
% 0.22/0.50      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.50         ((r2_hidden @ X11 @ (k1_relat_1 @ X10))
% 0.22/0.50          | ~ (zip_tseitin_0 @ X11 @ X12 @ X13 @ X10))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.22/0.50  thf('16', plain,
% 0.22/0.50      ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1) @ (k1_relat_1 @ sk_D_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.50  thf('17', plain,
% 0.22/0.50      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf(cc2_relset_1, axiom,
% 0.22/0.50    (![A:$i,B:$i,C:$i]:
% 0.22/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.50       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.50  thf('18', plain,
% 0.22/0.50      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.50         ((v4_relat_1 @ X23 @ X24)
% 0.22/0.50          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.22/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.50  thf('19', plain, ((v4_relat_1 @ sk_D_1 @ sk_A)),
% 0.22/0.50      inference('sup-', [status(thm)], ['17', '18'])).
% 0.22/0.50  thf(d18_relat_1, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( v1_relat_1 @ B ) =>
% 0.22/0.50       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.50  thf('20', plain,
% 0.22/0.50      (![X6 : $i, X7 : $i]:
% 0.22/0.50         (~ (v4_relat_1 @ X6 @ X7)
% 0.22/0.50          | (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 0.22/0.50          | ~ (v1_relat_1 @ X6))),
% 0.22/0.50      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.22/0.50  thf('21', plain,
% 0.22/0.50      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ sk_A))),
% 0.22/0.50      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.50  thf('22', plain, ((v1_relat_1 @ sk_D_1)),
% 0.22/0.50      inference('demod', [status(thm)], ['11', '12'])).
% 0.22/0.50  thf('23', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ sk_A)),
% 0.22/0.50      inference('demod', [status(thm)], ['21', '22'])).
% 0.22/0.50  thf(d3_tarski, axiom,
% 0.22/0.50    (![A:$i,B:$i]:
% 0.22/0.50     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.50       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.50  thf('24', plain,
% 0.22/0.50      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.50          | (r2_hidden @ X0 @ X2)
% 0.22/0.50          | ~ (r1_tarski @ X1 @ X2))),
% 0.22/0.50      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.50  thf('25', plain,
% 0.22/0.50      (![X0 : $i]:
% 0.22/0.50         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['23', '24'])).
% 0.22/0.50  thf('26', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1) @ sk_A)),
% 0.22/0.50      inference('sup-', [status(thm)], ['16', '25'])).
% 0.22/0.50  thf('27', plain,
% 0.22/0.50      (![X30 : $i]:
% 0.22/0.50         (~ (r2_hidden @ X30 @ sk_A)
% 0.22/0.50          | ~ (r2_hidden @ X30 @ sk_C_1)
% 0.22/0.50          | ((sk_E_2) != (k1_funct_1 @ sk_D_1 @ X30)))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.50  thf('28', plain,
% 0.22/0.50      ((((sk_E_2)
% 0.22/0.50          != (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1)))
% 0.22/0.50        | ~ (r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1) @ sk_C_1))),
% 0.22/0.50      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.50  thf('29', plain,
% 0.22/0.50      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1) @ sk_E_2 @ 
% 0.22/0.50        sk_C_1 @ sk_D_1)),
% 0.22/0.50      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.22/0.50  thf('30', plain,
% 0.22/0.50      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.50         (((X12) = (k1_funct_1 @ X10 @ X11))
% 0.22/0.50          | ~ (zip_tseitin_0 @ X11 @ X12 @ X13 @ X10))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.22/0.50  thf('31', plain,
% 0.22/0.50      (((sk_E_2) = (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1)))),
% 0.22/0.50      inference('sup-', [status(thm)], ['29', '30'])).
% 0.22/0.50  thf('32', plain,
% 0.22/0.50      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1) @ sk_E_2 @ 
% 0.22/0.50        sk_C_1 @ sk_D_1)),
% 0.22/0.50      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.22/0.50  thf('33', plain,
% 0.22/0.50      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.50         ((r2_hidden @ X11 @ X13) | ~ (zip_tseitin_0 @ X11 @ X12 @ X13 @ X10))),
% 0.22/0.50      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.22/0.50  thf('34', plain,
% 0.22/0.50      ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1) @ sk_C_1)),
% 0.22/0.50      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.50  thf('35', plain, (((sk_E_2) != (sk_E_2))),
% 0.22/0.50      inference('demod', [status(thm)], ['28', '31', '34'])).
% 0.22/0.50  thf('36', plain, ($false), inference('simplify', [status(thm)], ['35'])).
% 0.22/0.50  
% 0.22/0.50  % SZS output end Refutation
% 0.22/0.50  
% 0.22/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
