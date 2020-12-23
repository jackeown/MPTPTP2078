%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SFeUJCFVpD

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:58 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :   71 (  92 expanded)
%              Number of leaves         :   34 (  44 expanded)
%              Depth                    :   11
%              Number of atoms          :  454 ( 890 expanded)
%              Number of equality atoms :   27 (  45 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(t7_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_hidden @ C @ A )
       => ( ( B = k1_xboole_0 )
          | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r2_hidden @ C @ A )
         => ( ( B = k1_xboole_0 )
            | ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_funct_2])).

thf('0',plain,(
    ~ ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_2 ) @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r2_hidden @ sk_C_2 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('3',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('4',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('6',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('7',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('8',plain,
    ( ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('13',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('14',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['4','11','14'])).

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

thf('16',plain,(
    ! [X7: $i,X9: $i,X11: $i,X12: $i] :
      ( ( X9
       != ( k2_relat_1 @ X7 ) )
      | ( r2_hidden @ X11 @ X9 )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X7 ) )
      | ( X11
       != ( k1_funct_1 @ X7 @ X12 ) )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('17',plain,(
    ! [X7: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X7 )
      | ~ ( v1_funct_1 @ X7 )
      | ~ ( r2_hidden @ X12 @ ( k1_relat_1 @ X7 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X7 @ X12 ) @ ( k2_relat_1 @ X7 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) )
      | ~ ( v1_funct_1 @ sk_D_2 )
      | ~ ( v1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['15','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('22',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_2 @ X0 ) @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference(demod,[status(thm)],['18','19','22'])).

thf('24',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_2 ) @ ( k2_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['1','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('26',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('27',plain,(
    v5_relat_1 @ sk_D_2 @ sk_B ),
    inference('sup-',[status(thm)],['25','26'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('28',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v5_relat_1 @ X4 @ X5 )
      | ( r1_tarski @ ( k2_relat_1 @ X4 ) @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['20','21'])).

thf('31',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ sk_B ),
    inference(demod,[status(thm)],['29','30'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_2 @ sk_C_2 ) @ sk_B ),
    inference('sup-',[status(thm)],['24','33'])).

thf('35',plain,(
    $false ),
    inference(demod,[status(thm)],['0','34'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SFeUJCFVpD
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:24:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.43/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.43/0.59  % Solved by: fo/fo7.sh
% 0.43/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.59  % done 96 iterations in 0.146s
% 0.43/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.43/0.59  % SZS output start Refutation
% 0.43/0.59  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.43/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.59  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.43/0.59  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.43/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.43/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.43/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.43/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.43/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.43/0.59  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.43/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.43/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.43/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.43/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.43/0.59  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.43/0.59  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.43/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.43/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.43/0.59  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.43/0.59  thf(t7_funct_2, conjecture,
% 0.43/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.59     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.43/0.59         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.43/0.59       ( ( r2_hidden @ C @ A ) =>
% 0.43/0.59         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.43/0.59           ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ))).
% 0.43/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.59    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.59        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.43/0.59            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.43/0.59          ( ( r2_hidden @ C @ A ) =>
% 0.43/0.59            ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.43/0.59              ( r2_hidden @ ( k1_funct_1 @ D @ C ) @ B ) ) ) ) )),
% 0.43/0.59    inference('cnf.neg', [status(esa)], [t7_funct_2])).
% 0.43/0.59  thf('0', plain, (~ (r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_2) @ sk_B)),
% 0.43/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.59  thf('1', plain, ((r2_hidden @ sk_C_2 @ sk_A)),
% 0.43/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.59  thf('2', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B)),
% 0.43/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.59  thf(d1_funct_2, axiom,
% 0.43/0.59    (![A:$i,B:$i,C:$i]:
% 0.43/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.59       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.43/0.59           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.43/0.59             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.43/0.59         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.43/0.59           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.43/0.59             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.43/0.59  thf(zf_stmt_1, axiom,
% 0.43/0.59    (![C:$i,B:$i,A:$i]:
% 0.43/0.59     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.43/0.59       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.43/0.59  thf('3', plain,
% 0.43/0.59      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.43/0.59         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 0.43/0.59          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 0.43/0.59          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 0.43/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.43/0.59  thf('4', plain,
% 0.43/0.59      ((~ (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 0.43/0.59        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_2)))),
% 0.43/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.43/0.59  thf(zf_stmt_2, axiom,
% 0.43/0.59    (![B:$i,A:$i]:
% 0.43/0.59     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.43/0.59       ( zip_tseitin_0 @ B @ A ) ))).
% 0.43/0.59  thf('5', plain,
% 0.43/0.59      (![X22 : $i, X23 : $i]:
% 0.43/0.59         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 0.43/0.59      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.43/0.59  thf('6', plain,
% 0.43/0.59      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.43/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.59  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.43/0.59  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.43/0.59  thf(zf_stmt_5, axiom,
% 0.43/0.59    (![A:$i,B:$i,C:$i]:
% 0.43/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.59       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.43/0.59         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.43/0.59           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.43/0.59             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.43/0.59  thf('7', plain,
% 0.43/0.59      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.43/0.59         (~ (zip_tseitin_0 @ X27 @ X28)
% 0.43/0.59          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 0.43/0.59          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 0.43/0.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.43/0.59  thf('8', plain,
% 0.43/0.59      (((zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)
% 0.43/0.59        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.43/0.59      inference('sup-', [status(thm)], ['6', '7'])).
% 0.43/0.59  thf('9', plain,
% 0.43/0.59      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A))),
% 0.43/0.59      inference('sup-', [status(thm)], ['5', '8'])).
% 0.43/0.59  thf('10', plain, (((sk_B) != (k1_xboole_0))),
% 0.43/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.59  thf('11', plain, ((zip_tseitin_1 @ sk_D_2 @ sk_B @ sk_A)),
% 0.43/0.59      inference('simplify_reflect-', [status(thm)], ['9', '10'])).
% 0.43/0.59  thf('12', plain,
% 0.43/0.59      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.43/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.59  thf(redefinition_k1_relset_1, axiom,
% 0.43/0.59    (![A:$i,B:$i,C:$i]:
% 0.43/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.59       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.43/0.59  thf('13', plain,
% 0.43/0.59      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.43/0.59         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.43/0.59          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.43/0.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.43/0.59  thf('14', plain,
% 0.43/0.59      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 0.43/0.59      inference('sup-', [status(thm)], ['12', '13'])).
% 0.43/0.59  thf('15', plain, (((sk_A) = (k1_relat_1 @ sk_D_2))),
% 0.43/0.59      inference('demod', [status(thm)], ['4', '11', '14'])).
% 0.43/0.59  thf(d5_funct_1, axiom,
% 0.43/0.59    (![A:$i]:
% 0.43/0.59     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.43/0.59       ( ![B:$i]:
% 0.43/0.59         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.43/0.60           ( ![C:$i]:
% 0.43/0.60             ( ( r2_hidden @ C @ B ) <=>
% 0.43/0.60               ( ?[D:$i]:
% 0.43/0.60                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.43/0.60                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.43/0.60  thf('16', plain,
% 0.43/0.60      (![X7 : $i, X9 : $i, X11 : $i, X12 : $i]:
% 0.43/0.60         (((X9) != (k2_relat_1 @ X7))
% 0.43/0.60          | (r2_hidden @ X11 @ X9)
% 0.43/0.60          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X7))
% 0.43/0.60          | ((X11) != (k1_funct_1 @ X7 @ X12))
% 0.43/0.60          | ~ (v1_funct_1 @ X7)
% 0.43/0.60          | ~ (v1_relat_1 @ X7))),
% 0.43/0.60      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.43/0.60  thf('17', plain,
% 0.43/0.60      (![X7 : $i, X12 : $i]:
% 0.43/0.60         (~ (v1_relat_1 @ X7)
% 0.43/0.60          | ~ (v1_funct_1 @ X7)
% 0.43/0.60          | ~ (r2_hidden @ X12 @ (k1_relat_1 @ X7))
% 0.43/0.60          | (r2_hidden @ (k1_funct_1 @ X7 @ X12) @ (k2_relat_1 @ X7)))),
% 0.43/0.60      inference('simplify', [status(thm)], ['16'])).
% 0.43/0.60  thf('18', plain,
% 0.43/0.60      (![X0 : $i]:
% 0.43/0.60         (~ (r2_hidden @ X0 @ sk_A)
% 0.43/0.60          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2))
% 0.43/0.60          | ~ (v1_funct_1 @ sk_D_2)
% 0.43/0.60          | ~ (v1_relat_1 @ sk_D_2))),
% 0.43/0.60      inference('sup-', [status(thm)], ['15', '17'])).
% 0.43/0.60  thf('19', plain, ((v1_funct_1 @ sk_D_2)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('20', plain,
% 0.43/0.60      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf(cc1_relset_1, axiom,
% 0.43/0.60    (![A:$i,B:$i,C:$i]:
% 0.43/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.60       ( v1_relat_1 @ C ) ))).
% 0.43/0.60  thf('21', plain,
% 0.43/0.60      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.43/0.60         ((v1_relat_1 @ X13)
% 0.43/0.60          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.43/0.60      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.43/0.60  thf('22', plain, ((v1_relat_1 @ sk_D_2)),
% 0.43/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.43/0.60  thf('23', plain,
% 0.43/0.60      (![X0 : $i]:
% 0.43/0.60         (~ (r2_hidden @ X0 @ sk_A)
% 0.43/0.60          | (r2_hidden @ (k1_funct_1 @ sk_D_2 @ X0) @ (k2_relat_1 @ sk_D_2)))),
% 0.43/0.60      inference('demod', [status(thm)], ['18', '19', '22'])).
% 0.43/0.60  thf('24', plain,
% 0.43/0.60      ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_2) @ (k2_relat_1 @ sk_D_2))),
% 0.43/0.60      inference('sup-', [status(thm)], ['1', '23'])).
% 0.43/0.60  thf('25', plain,
% 0.43/0.60      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf(cc2_relset_1, axiom,
% 0.43/0.60    (![A:$i,B:$i,C:$i]:
% 0.43/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.60       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.43/0.60  thf('26', plain,
% 0.43/0.60      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.43/0.60         ((v5_relat_1 @ X16 @ X18)
% 0.43/0.60          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.43/0.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.43/0.60  thf('27', plain, ((v5_relat_1 @ sk_D_2 @ sk_B)),
% 0.43/0.60      inference('sup-', [status(thm)], ['25', '26'])).
% 0.43/0.60  thf(d19_relat_1, axiom,
% 0.43/0.60    (![A:$i,B:$i]:
% 0.43/0.60     ( ( v1_relat_1 @ B ) =>
% 0.43/0.60       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.43/0.60  thf('28', plain,
% 0.43/0.60      (![X4 : $i, X5 : $i]:
% 0.43/0.60         (~ (v5_relat_1 @ X4 @ X5)
% 0.43/0.60          | (r1_tarski @ (k2_relat_1 @ X4) @ X5)
% 0.43/0.60          | ~ (v1_relat_1 @ X4))),
% 0.43/0.60      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.43/0.60  thf('29', plain,
% 0.43/0.60      ((~ (v1_relat_1 @ sk_D_2) | (r1_tarski @ (k2_relat_1 @ sk_D_2) @ sk_B))),
% 0.43/0.60      inference('sup-', [status(thm)], ['27', '28'])).
% 0.43/0.60  thf('30', plain, ((v1_relat_1 @ sk_D_2)),
% 0.43/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.43/0.60  thf('31', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_2) @ sk_B)),
% 0.43/0.60      inference('demod', [status(thm)], ['29', '30'])).
% 0.43/0.60  thf(d3_tarski, axiom,
% 0.43/0.60    (![A:$i,B:$i]:
% 0.43/0.60     ( ( r1_tarski @ A @ B ) <=>
% 0.43/0.60       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.43/0.60  thf('32', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.60         (~ (r2_hidden @ X0 @ X1)
% 0.43/0.60          | (r2_hidden @ X0 @ X2)
% 0.43/0.60          | ~ (r1_tarski @ X1 @ X2))),
% 0.43/0.60      inference('cnf', [status(esa)], [d3_tarski])).
% 0.43/0.60  thf('33', plain,
% 0.43/0.60      (![X0 : $i]:
% 0.43/0.60         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_2)))),
% 0.43/0.60      inference('sup-', [status(thm)], ['31', '32'])).
% 0.43/0.60  thf('34', plain, ((r2_hidden @ (k1_funct_1 @ sk_D_2 @ sk_C_2) @ sk_B)),
% 0.43/0.60      inference('sup-', [status(thm)], ['24', '33'])).
% 0.43/0.60  thf('35', plain, ($false), inference('demod', [status(thm)], ['0', '34'])).
% 0.43/0.60  
% 0.43/0.60  % SZS output end Refutation
% 0.43/0.60  
% 0.43/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
