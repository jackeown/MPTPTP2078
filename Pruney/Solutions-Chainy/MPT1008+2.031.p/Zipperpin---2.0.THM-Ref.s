%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.R3OGiCU35m

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 121 expanded)
%              Number of leaves         :   42 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :  596 (1259 expanded)
%              Number of equality atoms :   53 (  97 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t62_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
          = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C )
            = ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t62_funct_2])).

thf('0',plain,(
    v1_funct_2 @ sk_C @ ( k1_tarski @ sk_A ) @ sk_B ),
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

thf('1',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_2 @ X33 @ X31 @ X32 )
      | ( X31
        = ( k1_relset_1 @ X31 @ X32 @ X33 ) )
      | ~ ( zip_tseitin_1 @ X33 @ X32 @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X29: $i,X30: $i] :
      ( ( zip_tseitin_0 @ X29 @ X30 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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

thf('5',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( zip_tseitin_0 @ X34 @ X35 )
      | ( zip_tseitin_1 @ X36 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('14',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('16',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','16'])).

thf('18',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['13','17'])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X16 ) )
      | ( ( k11_relat_1 @ X16 @ X15 )
        = ( k1_tarski @ ( k1_funct_1 @ X16 @ X15 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('20',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k11_relat_1 @ sk_C @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('22',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('25',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k11_relat_1 @ X9 @ X10 )
        = ( k9_relat_1 @ X9 @ ( k1_tarski @ X10 ) ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('27',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('28',plain,(
    v4_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X13: $i,X14: $i] :
      ( ( X13
        = ( k7_relat_1 @ X13 @ X14 ) )
      | ~ ( v4_relat_1 @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('32',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) )
        = ( k9_relat_1 @ X11 @ X12 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('34',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k9_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k11_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['25','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('39',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k11_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['20','23','24','39'])).

thf('41',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('43',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('44',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','44'])).

thf('46',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['40','45'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.R3OGiCU35m
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:18:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.20/0.56  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.56  % Solved by: fo/fo7.sh
% 0.20/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.56  % done 106 iterations in 0.109s
% 0.20/0.56  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.56  % SZS output start Refutation
% 0.20/0.56  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.56  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.56  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.56  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.56  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.56  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.20/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.56  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.56  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.56  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.56  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.56  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.20/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.56  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.56  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.56  thf(t62_funct_2, conjecture,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.20/0.56         ( m1_subset_1 @
% 0.20/0.56           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.20/0.56       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.56         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.20/0.56           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.56    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.56        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.20/0.56            ( m1_subset_1 @
% 0.20/0.56              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.20/0.56          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.56            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.20/0.56              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.20/0.56    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.20/0.56  thf('0', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(d1_funct_2, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.56       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.56           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.20/0.56             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.56         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.56           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.20/0.56             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.56  thf(zf_stmt_1, axiom,
% 0.20/0.56    (![C:$i,B:$i,A:$i]:
% 0.20/0.56     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.56       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.56  thf('1', plain,
% 0.20/0.56      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.56         (~ (v1_funct_2 @ X33 @ X31 @ X32)
% 0.20/0.56          | ((X31) = (k1_relset_1 @ X31 @ X32 @ X33))
% 0.20/0.56          | ~ (zip_tseitin_1 @ X33 @ X32 @ X31))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.56  thf('2', plain,
% 0.20/0.56      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.20/0.56        | ((k1_tarski @ sk_A)
% 0.20/0.56            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.56  thf(zf_stmt_2, axiom,
% 0.20/0.56    (![B:$i,A:$i]:
% 0.20/0.56     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.56       ( zip_tseitin_0 @ B @ A ) ))).
% 0.20/0.56  thf('3', plain,
% 0.20/0.56      (![X29 : $i, X30 : $i]:
% 0.20/0.56         ((zip_tseitin_0 @ X29 @ X30) | ((X29) = (k1_xboole_0)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.56  thf('4', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_C @ 
% 0.20/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.56  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.20/0.56  thf(zf_stmt_5, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.56       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.20/0.56         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.56           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.56             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.20/0.56  thf('5', plain,
% 0.20/0.56      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.20/0.56         (~ (zip_tseitin_0 @ X34 @ X35)
% 0.20/0.56          | (zip_tseitin_1 @ X36 @ X34 @ X35)
% 0.20/0.56          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.56  thf('6', plain,
% 0.20/0.56      (((zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.20/0.56        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.56  thf('7', plain,
% 0.20/0.56      ((((sk_B) = (k1_xboole_0))
% 0.20/0.56        | (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A)))),
% 0.20/0.56      inference('sup-', [status(thm)], ['3', '6'])).
% 0.20/0.56  thf('8', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('9', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))),
% 0.20/0.56      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.20/0.56  thf('10', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_C @ 
% 0.20/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.56  thf('11', plain,
% 0.20/0.56      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.56         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 0.20/0.56          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.20/0.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.56  thf('12', plain,
% 0.20/0.56      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.20/0.56      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.56  thf('13', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.20/0.56      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.20/0.56  thf(t69_enumset1, axiom,
% 0.20/0.56    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.56  thf('14', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.20/0.56      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.56  thf(d2_tarski, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.20/0.56       ( ![D:$i]:
% 0.20/0.56         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.20/0.56  thf('15', plain,
% 0.20/0.56      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.56         (((X1) != (X0))
% 0.20/0.56          | (r2_hidden @ X1 @ X2)
% 0.20/0.56          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.20/0.56      inference('cnf', [status(esa)], [d2_tarski])).
% 0.20/0.56  thf('16', plain,
% 0.20/0.56      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.20/0.56      inference('simplify', [status(thm)], ['15'])).
% 0.20/0.56  thf('17', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.56      inference('sup+', [status(thm)], ['14', '16'])).
% 0.20/0.56  thf('18', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.20/0.56      inference('sup+', [status(thm)], ['13', '17'])).
% 0.20/0.56  thf(t117_funct_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.56       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.56         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.20/0.56  thf('19', plain,
% 0.20/0.56      (![X15 : $i, X16 : $i]:
% 0.20/0.56         (~ (r2_hidden @ X15 @ (k1_relat_1 @ X16))
% 0.20/0.56          | ((k11_relat_1 @ X16 @ X15) = (k1_tarski @ (k1_funct_1 @ X16 @ X15)))
% 0.20/0.56          | ~ (v1_funct_1 @ X16)
% 0.20/0.56          | ~ (v1_relat_1 @ X16))),
% 0.20/0.56      inference('cnf', [status(esa)], [t117_funct_1])).
% 0.20/0.56  thf('20', plain,
% 0.20/0.56      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.56        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.56        | ((k11_relat_1 @ sk_C @ sk_A)
% 0.20/0.56            = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.56  thf('21', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_C @ 
% 0.20/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(cc1_relset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.56       ( v1_relat_1 @ C ) ))).
% 0.20/0.56  thf('22', plain,
% 0.20/0.56      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.56         ((v1_relat_1 @ X17)
% 0.20/0.56          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.20/0.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.56  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.56  thf('24', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(d16_relat_1, axiom,
% 0.20/0.56    (![A:$i]:
% 0.20/0.56     ( ( v1_relat_1 @ A ) =>
% 0.20/0.56       ( ![B:$i]:
% 0.20/0.56         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.20/0.56  thf('25', plain,
% 0.20/0.56      (![X9 : $i, X10 : $i]:
% 0.20/0.56         (((k11_relat_1 @ X9 @ X10) = (k9_relat_1 @ X9 @ (k1_tarski @ X10)))
% 0.20/0.56          | ~ (v1_relat_1 @ X9))),
% 0.20/0.56      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.20/0.56  thf('26', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_C @ 
% 0.20/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(cc2_relset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.56       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.56  thf('27', plain,
% 0.20/0.56      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.56         ((v4_relat_1 @ X20 @ X21)
% 0.20/0.56          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.20/0.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.56  thf('28', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 0.20/0.56      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.56  thf(t209_relat_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.56       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.20/0.56  thf('29', plain,
% 0.20/0.56      (![X13 : $i, X14 : $i]:
% 0.20/0.56         (((X13) = (k7_relat_1 @ X13 @ X14))
% 0.20/0.56          | ~ (v4_relat_1 @ X13 @ X14)
% 0.20/0.56          | ~ (v1_relat_1 @ X13))),
% 0.20/0.56      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.20/0.56  thf('30', plain,
% 0.20/0.56      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.56        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A))))),
% 0.20/0.56      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.56  thf('31', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.56  thf('32', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['30', '31'])).
% 0.20/0.56  thf(t148_relat_1, axiom,
% 0.20/0.56    (![A:$i,B:$i]:
% 0.20/0.56     ( ( v1_relat_1 @ B ) =>
% 0.20/0.56       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.56  thf('33', plain,
% 0.20/0.56      (![X11 : $i, X12 : $i]:
% 0.20/0.56         (((k2_relat_1 @ (k7_relat_1 @ X11 @ X12)) = (k9_relat_1 @ X11 @ X12))
% 0.20/0.56          | ~ (v1_relat_1 @ X11))),
% 0.20/0.56      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.56  thf('34', plain,
% 0.20/0.56      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)))
% 0.20/0.56        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.56      inference('sup+', [status(thm)], ['32', '33'])).
% 0.20/0.56  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.56  thf('36', plain,
% 0.20/0.56      (((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['34', '35'])).
% 0.20/0.56  thf('37', plain,
% 0.20/0.56      ((((k2_relat_1 @ sk_C) = (k11_relat_1 @ sk_C @ sk_A))
% 0.20/0.56        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.56      inference('sup+', [status(thm)], ['25', '36'])).
% 0.20/0.56  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.56  thf('39', plain, (((k2_relat_1 @ sk_C) = (k11_relat_1 @ sk_C @ sk_A))),
% 0.20/0.56      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.56  thf('40', plain,
% 0.20/0.56      (((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['20', '23', '24', '39'])).
% 0.20/0.56  thf('41', plain,
% 0.20/0.56      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)
% 0.20/0.56         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf('42', plain,
% 0.20/0.56      ((m1_subset_1 @ sk_C @ 
% 0.20/0.56        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.56  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.56    (![A:$i,B:$i,C:$i]:
% 0.20/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.56       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.56  thf('43', plain,
% 0.20/0.56      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.56         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 0.20/0.56          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.20/0.56      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.56  thf('44', plain,
% 0.20/0.56      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.20/0.56      inference('sup-', [status(thm)], ['42', '43'])).
% 0.20/0.56  thf('45', plain,
% 0.20/0.56      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.20/0.56      inference('demod', [status(thm)], ['41', '44'])).
% 0.20/0.56  thf('46', plain, ($false),
% 0.20/0.56      inference('simplify_reflect-', [status(thm)], ['40', '45'])).
% 0.20/0.56  
% 0.20/0.56  % SZS output end Refutation
% 0.20/0.56  
% 0.20/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
