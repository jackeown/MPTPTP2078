%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A2ku1dR1Os

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:01 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 216 expanded)
%              Number of leaves         :   38 (  83 expanded)
%              Depth                    :   16
%              Number of atoms          :  618 (2791 expanded)
%              Number of equality atoms :   44 ( 156 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('0',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X8 @ X9 ) @ ( k2_relat_1 @ X8 ) )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X10: $i] :
      ( ( ( k9_relat_1 @ X10 @ ( k1_relat_1 @ X10 ) )
        = ( k2_relat_1 @ X10 ) )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf(t64_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_2])).

thf('2',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C_1 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    v1_funct_2 @ sk_D @ ( k1_tarski @ sk_A ) @ sk_B ),
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

thf('4',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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

thf('8',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('9',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('14',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('15',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['5','12','15'])).

thf('17',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ sk_C_1 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['2','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['5','12','15'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('21',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( ( k7_relset_1 @ X21 @ X22 @ X20 @ X23 )
        = ( k9_relat_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C_1 ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('24',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['5','12','15'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('26',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['24','26'])).

thf('28',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['24','26'])).

thf(t118_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) )
       => ( ( k9_relat_1 @ C @ ( k2_tarski @ A @ B ) )
          = ( k2_tarski @ ( k1_funct_1 @ C @ A ) @ ( k1_funct_1 @ C @ B ) ) ) ) ) )).

thf('29',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X12 ) )
      | ~ ( r2_hidden @ X13 @ ( k1_relat_1 @ X12 ) )
      | ( ( k9_relat_1 @ X12 @ ( k2_tarski @ X11 @ X13 ) )
        = ( k2_tarski @ ( k1_funct_1 @ X12 @ X11 ) @ ( k1_funct_1 @ X12 @ X13 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t118_funct_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k9_relat_1 @ sk_D @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('32',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('33',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_D @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['30','33','34'])).

thf('36',plain,
    ( ( k9_relat_1 @ sk_D @ ( k2_tarski @ sk_A @ sk_A ) )
    = ( k2_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) @ ( k1_funct_1 @ sk_D @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','35'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('37',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('38',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['5','12','15'])).

thf('39',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('40',plain,
    ( ( k9_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) )
    = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('41',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C_1 ) @ ( k9_relat_1 @ sk_D @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['23','40'])).

thf('42',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C_1 ) @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['1','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['31','32'])).

thf('44',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C_1 ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['0','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['31','32'])).

thf('47',plain,(
    $false ),
    inference(demod,[status(thm)],['45','46'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.A2ku1dR1Os
% 0.13/0.37  % Computer   : n019.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 13:13:53 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 0.23/0.51  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.23/0.51  % Solved by: fo/fo7.sh
% 0.23/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.23/0.51  % done 95 iterations in 0.071s
% 0.23/0.51  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.23/0.51  % SZS output start Refutation
% 0.23/0.51  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.23/0.51  thf(sk_B_type, type, sk_B: $i).
% 0.23/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.23/0.51  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.23/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.23/0.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.23/0.51  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.23/0.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.23/0.51  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.23/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.23/0.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.23/0.51  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.23/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.23/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.23/0.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.23/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.23/0.51  thf(sk_D_type, type, sk_D: $i).
% 0.23/0.51  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.23/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.23/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.23/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.23/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.23/0.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.23/0.51  thf(t144_relat_1, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( v1_relat_1 @ B ) =>
% 0.23/0.51       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.23/0.51  thf('0', plain,
% 0.23/0.51      (![X8 : $i, X9 : $i]:
% 0.23/0.51         ((r1_tarski @ (k9_relat_1 @ X8 @ X9) @ (k2_relat_1 @ X8))
% 0.23/0.51          | ~ (v1_relat_1 @ X8))),
% 0.23/0.51      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.23/0.51  thf(t146_relat_1, axiom,
% 0.23/0.51    (![A:$i]:
% 0.23/0.51     ( ( v1_relat_1 @ A ) =>
% 0.23/0.51       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.23/0.51  thf('1', plain,
% 0.23/0.51      (![X10 : $i]:
% 0.23/0.51         (((k9_relat_1 @ X10 @ (k1_relat_1 @ X10)) = (k2_relat_1 @ X10))
% 0.23/0.51          | ~ (v1_relat_1 @ X10))),
% 0.23/0.51      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.23/0.51  thf(t64_funct_2, conjecture,
% 0.23/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.51     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.23/0.51         ( m1_subset_1 @
% 0.23/0.51           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.23/0.51       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.23/0.51         ( r1_tarski @
% 0.23/0.51           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.23/0.51           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.23/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.23/0.51    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.51        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.23/0.51            ( m1_subset_1 @
% 0.23/0.51              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.23/0.51          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.23/0.51            ( r1_tarski @
% 0.23/0.51              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.23/0.51              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.23/0.51    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.23/0.51  thf('2', plain,
% 0.23/0.51      (~ (r1_tarski @ 
% 0.23/0.51          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C_1) @ 
% 0.23/0.51          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('3', plain, ((v1_funct_2 @ sk_D @ (k1_tarski @ sk_A) @ sk_B)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(d1_funct_2, axiom,
% 0.23/0.51    (![A:$i,B:$i,C:$i]:
% 0.23/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.51       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.23/0.51           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.23/0.51             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.23/0.51         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.23/0.51           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.23/0.51             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.23/0.51  thf(zf_stmt_1, axiom,
% 0.23/0.51    (![C:$i,B:$i,A:$i]:
% 0.23/0.51     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.23/0.51       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.23/0.51  thf('4', plain,
% 0.23/0.51      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.23/0.51         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 0.23/0.51          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 0.23/0.51          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.23/0.51  thf('5', plain,
% 0.23/0.51      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.23/0.51        | ((k1_tarski @ sk_A)
% 0.23/0.51            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['3', '4'])).
% 0.23/0.51  thf(zf_stmt_2, axiom,
% 0.23/0.51    (![B:$i,A:$i]:
% 0.23/0.51     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.23/0.51       ( zip_tseitin_0 @ B @ A ) ))).
% 0.23/0.51  thf('6', plain,
% 0.23/0.51      (![X24 : $i, X25 : $i]:
% 0.23/0.51         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.23/0.51  thf('7', plain,
% 0.23/0.51      ((m1_subset_1 @ sk_D @ 
% 0.23/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.23/0.51  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.23/0.51  thf(zf_stmt_5, axiom,
% 0.23/0.51    (![A:$i,B:$i,C:$i]:
% 0.23/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.51       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.23/0.51         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.23/0.51           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.23/0.51             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.23/0.51  thf('8', plain,
% 0.23/0.51      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.23/0.51         (~ (zip_tseitin_0 @ X29 @ X30)
% 0.23/0.51          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 0.23/0.51          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.23/0.51  thf('9', plain,
% 0.23/0.51      (((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))
% 0.23/0.51        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['7', '8'])).
% 0.23/0.51  thf('10', plain,
% 0.23/0.51      ((((sk_B) = (k1_xboole_0))
% 0.23/0.51        | (zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['6', '9'])).
% 0.23/0.51  thf('11', plain, (((sk_B) != (k1_xboole_0))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('12', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ (k1_tarski @ sk_A))),
% 0.23/0.51      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.23/0.51  thf('13', plain,
% 0.23/0.51      ((m1_subset_1 @ sk_D @ 
% 0.23/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(redefinition_k1_relset_1, axiom,
% 0.23/0.51    (![A:$i,B:$i,C:$i]:
% 0.23/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.51       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.23/0.51  thf('14', plain,
% 0.23/0.51      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.23/0.51         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 0.23/0.51          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.23/0.51      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.23/0.51  thf('15', plain,
% 0.23/0.51      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.23/0.51      inference('sup-', [status(thm)], ['13', '14'])).
% 0.23/0.51  thf('16', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.23/0.51      inference('demod', [status(thm)], ['5', '12', '15'])).
% 0.23/0.51  thf('17', plain,
% 0.23/0.51      (~ (r1_tarski @ 
% 0.23/0.51          (k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ sk_C_1) @ 
% 0.23/0.51          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.23/0.51      inference('demod', [status(thm)], ['2', '16'])).
% 0.23/0.51  thf('18', plain,
% 0.23/0.51      ((m1_subset_1 @ sk_D @ 
% 0.23/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('19', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.23/0.51      inference('demod', [status(thm)], ['5', '12', '15'])).
% 0.23/0.51  thf('20', plain,
% 0.23/0.51      ((m1_subset_1 @ sk_D @ 
% 0.23/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 0.23/0.51      inference('demod', [status(thm)], ['18', '19'])).
% 0.23/0.51  thf(redefinition_k7_relset_1, axiom,
% 0.23/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.23/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.51       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.23/0.51  thf('21', plain,
% 0.23/0.51      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.23/0.51         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.23/0.51          | ((k7_relset_1 @ X21 @ X22 @ X20 @ X23) = (k9_relat_1 @ X20 @ X23)))),
% 0.23/0.51      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.23/0.51  thf('22', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         ((k7_relset_1 @ (k1_relat_1 @ sk_D) @ sk_B @ sk_D @ X0)
% 0.23/0.51           = (k9_relat_1 @ sk_D @ X0))),
% 0.23/0.51      inference('sup-', [status(thm)], ['20', '21'])).
% 0.23/0.51  thf('23', plain,
% 0.23/0.51      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C_1) @ 
% 0.23/0.51          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.23/0.51      inference('demod', [status(thm)], ['17', '22'])).
% 0.23/0.51  thf('24', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.23/0.51      inference('demod', [status(thm)], ['5', '12', '15'])).
% 0.23/0.51  thf(d1_tarski, axiom,
% 0.23/0.51    (![A:$i,B:$i]:
% 0.23/0.51     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.23/0.51       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.23/0.51  thf('25', plain,
% 0.23/0.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.23/0.51         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.23/0.51      inference('cnf', [status(esa)], [d1_tarski])).
% 0.23/0.51  thf('26', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.23/0.51      inference('simplify', [status(thm)], ['25'])).
% 0.23/0.51  thf('27', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D))),
% 0.23/0.51      inference('sup+', [status(thm)], ['24', '26'])).
% 0.23/0.51  thf('28', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D))),
% 0.23/0.51      inference('sup+', [status(thm)], ['24', '26'])).
% 0.23/0.51  thf(t118_funct_1, axiom,
% 0.23/0.51    (![A:$i,B:$i,C:$i]:
% 0.23/0.51     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.23/0.51       ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.23/0.51           ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) ) =>
% 0.23/0.51         ( ( k9_relat_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 0.23/0.51           ( k2_tarski @ ( k1_funct_1 @ C @ A ) @ ( k1_funct_1 @ C @ B ) ) ) ) ))).
% 0.23/0.51  thf('29', plain,
% 0.23/0.51      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.23/0.51         (~ (r2_hidden @ X11 @ (k1_relat_1 @ X12))
% 0.23/0.51          | ~ (r2_hidden @ X13 @ (k1_relat_1 @ X12))
% 0.23/0.51          | ((k9_relat_1 @ X12 @ (k2_tarski @ X11 @ X13))
% 0.23/0.51              = (k2_tarski @ (k1_funct_1 @ X12 @ X11) @ 
% 0.23/0.51                 (k1_funct_1 @ X12 @ X13)))
% 0.23/0.51          | ~ (v1_funct_1 @ X12)
% 0.23/0.51          | ~ (v1_relat_1 @ X12))),
% 0.23/0.51      inference('cnf', [status(esa)], [t118_funct_1])).
% 0.23/0.51  thf('30', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (~ (v1_relat_1 @ sk_D)
% 0.23/0.51          | ~ (v1_funct_1 @ sk_D)
% 0.23/0.51          | ((k9_relat_1 @ sk_D @ (k2_tarski @ sk_A @ X0))
% 0.23/0.51              = (k2_tarski @ (k1_funct_1 @ sk_D @ sk_A) @ 
% 0.23/0.51                 (k1_funct_1 @ sk_D @ X0)))
% 0.23/0.51          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['28', '29'])).
% 0.23/0.51  thf('31', plain,
% 0.23/0.51      ((m1_subset_1 @ sk_D @ 
% 0.23/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf(cc1_relset_1, axiom,
% 0.23/0.51    (![A:$i,B:$i,C:$i]:
% 0.23/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.23/0.51       ( v1_relat_1 @ C ) ))).
% 0.23/0.51  thf('32', plain,
% 0.23/0.51      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.23/0.51         ((v1_relat_1 @ X14)
% 0.23/0.51          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.23/0.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.23/0.51  thf('33', plain, ((v1_relat_1 @ sk_D)),
% 0.23/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.23/0.51  thf('34', plain, ((v1_funct_1 @ sk_D)),
% 0.23/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.23/0.51  thf('35', plain,
% 0.23/0.51      (![X0 : $i]:
% 0.23/0.51         (((k9_relat_1 @ sk_D @ (k2_tarski @ sk_A @ X0))
% 0.23/0.51            = (k2_tarski @ (k1_funct_1 @ sk_D @ sk_A) @ 
% 0.23/0.51               (k1_funct_1 @ sk_D @ X0)))
% 0.23/0.51          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D)))),
% 0.23/0.51      inference('demod', [status(thm)], ['30', '33', '34'])).
% 0.23/0.51  thf('36', plain,
% 0.23/0.51      (((k9_relat_1 @ sk_D @ (k2_tarski @ sk_A @ sk_A))
% 0.23/0.51         = (k2_tarski @ (k1_funct_1 @ sk_D @ sk_A) @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.23/0.51      inference('sup-', [status(thm)], ['27', '35'])).
% 0.23/0.51  thf(t69_enumset1, axiom,
% 0.23/0.51    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.23/0.51  thf('37', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.23/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.23/0.51  thf('38', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D))),
% 0.23/0.51      inference('demod', [status(thm)], ['5', '12', '15'])).
% 0.23/0.51  thf('39', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.23/0.51      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.23/0.51  thf('40', plain,
% 0.23/0.51      (((k9_relat_1 @ sk_D @ (k1_relat_1 @ sk_D))
% 0.23/0.51         = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.23/0.51      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 0.23/0.51  thf('41', plain,
% 0.23/0.51      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C_1) @ 
% 0.23/0.51          (k9_relat_1 @ sk_D @ (k1_relat_1 @ sk_D)))),
% 0.23/0.51      inference('demod', [status(thm)], ['23', '40'])).
% 0.23/0.51  thf('42', plain,
% 0.23/0.51      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C_1) @ (k2_relat_1 @ sk_D))
% 0.23/0.51        | ~ (v1_relat_1 @ sk_D))),
% 0.23/0.51      inference('sup-', [status(thm)], ['1', '41'])).
% 0.23/0.51  thf('43', plain, ((v1_relat_1 @ sk_D)),
% 0.23/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.23/0.51  thf('44', plain,
% 0.23/0.51      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C_1) @ (k2_relat_1 @ sk_D))),
% 0.23/0.51      inference('demod', [status(thm)], ['42', '43'])).
% 0.23/0.51  thf('45', plain, (~ (v1_relat_1 @ sk_D)),
% 0.23/0.51      inference('sup-', [status(thm)], ['0', '44'])).
% 0.23/0.51  thf('46', plain, ((v1_relat_1 @ sk_D)),
% 0.23/0.51      inference('sup-', [status(thm)], ['31', '32'])).
% 0.23/0.51  thf('47', plain, ($false), inference('demod', [status(thm)], ['45', '46'])).
% 0.23/0.51  
% 0.23/0.51  % SZS output end Refutation
% 0.23/0.51  
% 0.23/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
