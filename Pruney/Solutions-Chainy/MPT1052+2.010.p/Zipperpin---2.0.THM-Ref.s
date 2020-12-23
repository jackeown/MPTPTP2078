%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iyZJTaaKLE

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:25 EST 2020

% Result     : Theorem 0.44s
% Output     : Refutation 0.44s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 109 expanded)
%              Number of leaves         :   36 (  48 expanded)
%              Depth                    :   10
%              Number of atoms          :  471 ( 851 expanded)
%              Number of equality atoms :   31 (  51 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(t169_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
       => ( ( ( k1_relat_1 @ C )
            = A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
         => ( ( ( k1_relat_1 @ C )
              = A )
            & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t169_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t121_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('1',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_funct_2 @ X25 @ X26 @ X27 )
      | ~ ( r2_hidden @ X25 @ ( k1_funct_2 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t121_funct_2])).

thf('2',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference('sup-',[status(thm)],['0','1'])).

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
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ( X17
        = ( k1_relset_1 @ X17 @ X18 @ X19 ) )
      | ~ ( zip_tseitin_1 @ X19 @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('4',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r2_hidden @ sk_C @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( r2_hidden @ X25 @ ( k1_funct_2 @ X26 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t121_funct_2])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('9',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X20 @ X21 )
      | ( zip_tseitin_1 @ X22 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('13',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('15',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(fc3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_xboole_0 @ B ) )
     => ( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ) )).

thf('17',plain,(
    ! [X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ~ ( v1_xboole_0 @ X24 )
      | ( v1_xboole_0 @ ( k1_funct_2 @ X23 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_2])).

thf('18',plain,(
    r2_hidden @ sk_C @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('20',plain,(
    ~ ( v1_xboole_0 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','21'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('23',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('24',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( X16 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('25',plain,(
    ! [X15: $i] :
      ( zip_tseitin_0 @ X15 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['23','25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X1 )
      | ( zip_tseitin_0 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
    zip_tseitin_0 @ sk_B_1 @ sk_A ),
    inference(eq_fact,[status(thm)],['27'])).

thf('29',plain,(
    zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['13','28'])).

thf('30',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['10','29'])).

thf('31',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != sk_A )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != sk_A )
   <= ( ( k1_relat_1 @ sk_C )
     != sk_A ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('34',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v5_relat_1 @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('35',plain,(
    v5_relat_1 @ sk_C @ sk_B_1 ),
    inference('sup-',[status(thm)],['33','34'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('36',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v5_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['31'])).

thf('41',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != sk_A )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['31'])).

thf('43',plain,(
    ( k1_relat_1 @ sk_C )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['41','42'])).

thf('44',plain,(
    ( k1_relat_1 @ sk_C )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['32','43'])).

thf('45',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['30','44'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.iyZJTaaKLE
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:15:18 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.18/0.33  % Number of cores: 8
% 0.18/0.33  % Python version: Python 3.6.8
% 0.18/0.34  % Running in FO mode
% 0.44/0.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.44/0.67  % Solved by: fo/fo7.sh
% 0.44/0.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.44/0.67  % done 191 iterations in 0.234s
% 0.44/0.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.44/0.67  % SZS output start Refutation
% 0.44/0.67  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.44/0.67  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.44/0.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.44/0.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.44/0.67  thf(sk_C_type, type, sk_C: $i).
% 0.44/0.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.44/0.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.44/0.67  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.44/0.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.44/0.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.44/0.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.44/0.67  thf(sk_A_type, type, sk_A: $i).
% 0.44/0.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.44/0.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.44/0.67  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.44/0.67  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.44/0.67  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.44/0.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.44/0.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.44/0.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.44/0.67  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.44/0.67  thf(t169_funct_2, conjecture,
% 0.44/0.67    (![A:$i,B:$i,C:$i]:
% 0.44/0.67     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.44/0.67       ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.44/0.67         ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.44/0.67           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ))).
% 0.44/0.67  thf(zf_stmt_0, negated_conjecture,
% 0.44/0.67    (~( ![A:$i,B:$i,C:$i]:
% 0.44/0.67        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.44/0.67          ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.44/0.67            ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.44/0.67              ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ) )),
% 0.44/0.67    inference('cnf.neg', [status(esa)], [t169_funct_2])).
% 0.44/0.67  thf('0', plain, ((r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf(t121_funct_2, axiom,
% 0.44/0.67    (![A:$i,B:$i,C:$i]:
% 0.44/0.67     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.44/0.67       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.44/0.67         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.44/0.67  thf('1', plain,
% 0.44/0.67      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.44/0.67         ((v1_funct_2 @ X25 @ X26 @ X27)
% 0.44/0.67          | ~ (r2_hidden @ X25 @ (k1_funct_2 @ X26 @ X27)))),
% 0.44/0.67      inference('cnf', [status(esa)], [t121_funct_2])).
% 0.44/0.67  thf('2', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.44/0.67      inference('sup-', [status(thm)], ['0', '1'])).
% 0.44/0.67  thf(d1_funct_2, axiom,
% 0.44/0.67    (![A:$i,B:$i,C:$i]:
% 0.44/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.67       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.44/0.67           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.44/0.67             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.44/0.67         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.67           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.44/0.67             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.44/0.67  thf(zf_stmt_1, axiom,
% 0.44/0.67    (![C:$i,B:$i,A:$i]:
% 0.44/0.67     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.44/0.67       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.44/0.67  thf('3', plain,
% 0.44/0.67      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.44/0.67         (~ (v1_funct_2 @ X19 @ X17 @ X18)
% 0.44/0.67          | ((X17) = (k1_relset_1 @ X17 @ X18 @ X19))
% 0.44/0.67          | ~ (zip_tseitin_1 @ X19 @ X18 @ X17))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.44/0.67  thf('4', plain,
% 0.44/0.67      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.44/0.67        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['2', '3'])).
% 0.44/0.67  thf('5', plain, ((r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('6', plain,
% 0.44/0.67      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.44/0.67         ((m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.44/0.67          | ~ (r2_hidden @ X25 @ (k1_funct_2 @ X26 @ X27)))),
% 0.44/0.67      inference('cnf', [status(esa)], [t121_funct_2])).
% 0.44/0.67  thf('7', plain,
% 0.44/0.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['5', '6'])).
% 0.44/0.67  thf(redefinition_k1_relset_1, axiom,
% 0.44/0.67    (![A:$i,B:$i,C:$i]:
% 0.44/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.67       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.44/0.67  thf('8', plain,
% 0.44/0.67      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.44/0.67         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 0.44/0.67          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.44/0.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.44/0.67  thf('9', plain,
% 0.44/0.67      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.44/0.67      inference('sup-', [status(thm)], ['7', '8'])).
% 0.44/0.67  thf('10', plain,
% 0.44/0.67      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.44/0.67        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.44/0.67      inference('demod', [status(thm)], ['4', '9'])).
% 0.44/0.67  thf('11', plain,
% 0.44/0.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['5', '6'])).
% 0.44/0.67  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.44/0.67  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.44/0.67  thf(zf_stmt_4, axiom,
% 0.44/0.67    (![B:$i,A:$i]:
% 0.44/0.67     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.44/0.67       ( zip_tseitin_0 @ B @ A ) ))).
% 0.44/0.67  thf(zf_stmt_5, axiom,
% 0.44/0.67    (![A:$i,B:$i,C:$i]:
% 0.44/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.67       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.44/0.67         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.44/0.67           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.44/0.67             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.44/0.67  thf('12', plain,
% 0.44/0.67      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.44/0.67         (~ (zip_tseitin_0 @ X20 @ X21)
% 0.44/0.67          | (zip_tseitin_1 @ X22 @ X20 @ X21)
% 0.44/0.67          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20))))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.44/0.67  thf('13', plain,
% 0.44/0.67      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.44/0.67        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.44/0.67      inference('sup-', [status(thm)], ['11', '12'])).
% 0.44/0.67  thf('14', plain,
% 0.44/0.67      (![X15 : $i, X16 : $i]:
% 0.44/0.67         ((zip_tseitin_0 @ X15 @ X16) | ((X15) = (k1_xboole_0)))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.44/0.67  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.44/0.67  thf('15', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.44/0.67      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.44/0.67  thf('16', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.44/0.67      inference('sup+', [status(thm)], ['14', '15'])).
% 0.44/0.67  thf(fc3_funct_2, axiom,
% 0.44/0.67    (![A:$i,B:$i]:
% 0.44/0.67     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_xboole_0 @ B ) ) =>
% 0.44/0.67       ( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ))).
% 0.44/0.67  thf('17', plain,
% 0.44/0.67      (![X23 : $i, X24 : $i]:
% 0.44/0.67         ((v1_xboole_0 @ X23)
% 0.44/0.67          | ~ (v1_xboole_0 @ X24)
% 0.44/0.67          | (v1_xboole_0 @ (k1_funct_2 @ X23 @ X24)))),
% 0.44/0.67      inference('cnf', [status(esa)], [fc3_funct_2])).
% 0.44/0.67  thf('18', plain, ((r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf(d1_xboole_0, axiom,
% 0.44/0.67    (![A:$i]:
% 0.44/0.67     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.44/0.67  thf('19', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.44/0.67      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.44/0.67  thf('20', plain, (~ (v1_xboole_0 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.44/0.67      inference('sup-', [status(thm)], ['18', '19'])).
% 0.44/0.67  thf('21', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A))),
% 0.44/0.67      inference('sup-', [status(thm)], ['17', '20'])).
% 0.44/0.67  thf('22', plain,
% 0.44/0.67      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_A))),
% 0.44/0.67      inference('sup-', [status(thm)], ['16', '21'])).
% 0.44/0.67  thf(l13_xboole_0, axiom,
% 0.44/0.67    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.44/0.67  thf('23', plain,
% 0.44/0.67      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.44/0.67      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.44/0.67  thf('24', plain,
% 0.44/0.67      (![X15 : $i, X16 : $i]:
% 0.44/0.67         ((zip_tseitin_0 @ X15 @ X16) | ((X16) != (k1_xboole_0)))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.44/0.67  thf('25', plain, (![X15 : $i]: (zip_tseitin_0 @ X15 @ k1_xboole_0)),
% 0.44/0.67      inference('simplify', [status(thm)], ['24'])).
% 0.44/0.67  thf('26', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.44/0.67      inference('sup+', [status(thm)], ['23', '25'])).
% 0.44/0.67  thf('27', plain,
% 0.44/0.67      (![X0 : $i, X1 : $i]:
% 0.44/0.67         ((zip_tseitin_0 @ sk_B_1 @ X1) | (zip_tseitin_0 @ X0 @ sk_A))),
% 0.44/0.67      inference('sup-', [status(thm)], ['22', '26'])).
% 0.44/0.67  thf('28', plain, ((zip_tseitin_0 @ sk_B_1 @ sk_A)),
% 0.44/0.67      inference('eq_fact', [status(thm)], ['27'])).
% 0.44/0.67  thf('29', plain, ((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)),
% 0.44/0.67      inference('demod', [status(thm)], ['13', '28'])).
% 0.44/0.67  thf('30', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.44/0.67      inference('demod', [status(thm)], ['10', '29'])).
% 0.44/0.67  thf('31', plain,
% 0.44/0.67      ((((k1_relat_1 @ sk_C) != (sk_A))
% 0.44/0.67        | ~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('32', plain,
% 0.44/0.67      ((((k1_relat_1 @ sk_C) != (sk_A)))
% 0.44/0.67         <= (~ (((k1_relat_1 @ sk_C) = (sk_A))))),
% 0.44/0.67      inference('split', [status(esa)], ['31'])).
% 0.44/0.67  thf('33', plain,
% 0.44/0.67      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.44/0.67      inference('sup-', [status(thm)], ['5', '6'])).
% 0.44/0.67  thf(cc2_relset_1, axiom,
% 0.44/0.67    (![A:$i,B:$i,C:$i]:
% 0.44/0.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.44/0.67       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.44/0.67  thf('34', plain,
% 0.44/0.67      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.44/0.67         ((v5_relat_1 @ X9 @ X11)
% 0.44/0.67          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.44/0.67      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.44/0.67  thf('35', plain, ((v5_relat_1 @ sk_C @ sk_B_1)),
% 0.44/0.67      inference('sup-', [status(thm)], ['33', '34'])).
% 0.44/0.67  thf(d19_relat_1, axiom,
% 0.44/0.67    (![A:$i,B:$i]:
% 0.44/0.67     ( ( v1_relat_1 @ B ) =>
% 0.44/0.67       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.44/0.67  thf('36', plain,
% 0.44/0.67      (![X7 : $i, X8 : $i]:
% 0.44/0.67         (~ (v5_relat_1 @ X7 @ X8)
% 0.44/0.67          | (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 0.44/0.67          | ~ (v1_relat_1 @ X7))),
% 0.44/0.67      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.44/0.67  thf('37', plain,
% 0.44/0.67      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))),
% 0.44/0.67      inference('sup-', [status(thm)], ['35', '36'])).
% 0.44/0.67  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 0.44/0.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.44/0.67  thf('39', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)),
% 0.44/0.67      inference('demod', [status(thm)], ['37', '38'])).
% 0.44/0.67  thf('40', plain,
% 0.44/0.67      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))
% 0.44/0.67         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.44/0.67      inference('split', [status(esa)], ['31'])).
% 0.44/0.67  thf('41', plain, (((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))),
% 0.44/0.67      inference('sup-', [status(thm)], ['39', '40'])).
% 0.44/0.67  thf('42', plain,
% 0.44/0.67      (~ (((k1_relat_1 @ sk_C) = (sk_A))) | 
% 0.44/0.67       ~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))),
% 0.44/0.67      inference('split', [status(esa)], ['31'])).
% 0.44/0.67  thf('43', plain, (~ (((k1_relat_1 @ sk_C) = (sk_A)))),
% 0.44/0.67      inference('sat_resolution*', [status(thm)], ['41', '42'])).
% 0.44/0.67  thf('44', plain, (((k1_relat_1 @ sk_C) != (sk_A))),
% 0.44/0.67      inference('simpl_trail', [status(thm)], ['32', '43'])).
% 0.44/0.67  thf('45', plain, ($false),
% 0.44/0.67      inference('simplify_reflect-', [status(thm)], ['30', '44'])).
% 0.44/0.67  
% 0.44/0.67  % SZS output end Refutation
% 0.44/0.67  
% 0.44/0.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
