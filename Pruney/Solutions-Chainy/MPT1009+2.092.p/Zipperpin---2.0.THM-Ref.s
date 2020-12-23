%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JFZzjKugpi

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:01 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 222 expanded)
%              Number of leaves         :   38 (  85 expanded)
%              Depth                    :   16
%              Number of atoms          :  634 (2835 expanded)
%              Number of equality atoms :   46 ( 162 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('0',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X12 @ X13 ) @ ( k2_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X14: $i] :
      ( ( ( k9_relat_1 @ X14 @ ( k1_relat_1 @ X14 ) )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
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
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    v1_funct_2 @ sk_D_1 @ ( k1_tarski @ sk_A ) @ sk_B ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( v1_funct_2 @ X32 @ X30 @ X31 )
      | ( X30
        = ( k1_relset_1 @ X30 @ X31 @ X32 ) )
      | ~ ( zip_tseitin_1 @ X32 @ X31 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('5',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('6',plain,(
    ! [X28: $i,X29: $i] :
      ( ( zip_tseitin_0 @ X28 @ X29 )
      | ( X28 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('7',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( zip_tseitin_0 @ X33 @ X34 )
      | ( zip_tseitin_1 @ X35 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('9',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('14',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('15',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['5','12','15'])).

thf('17',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['2','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['5','12','15'])).

thf('20',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('21',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k7_relset_1 @ X25 @ X26 @ X24 @ X27 )
        = ( k9_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','22'])).

thf('24',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['5','12','15'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('25',plain,(
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

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('27',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['25','27'])).

thf('29',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['24','28'])).

thf('30',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['24','28'])).

thf(t118_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) )
       => ( ( k9_relat_1 @ C @ ( k2_tarski @ A @ B ) )
          = ( k2_tarski @ ( k1_funct_1 @ C @ A ) @ ( k1_funct_1 @ C @ B ) ) ) ) ) )).

thf('31',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X16 ) )
      | ~ ( r2_hidden @ X17 @ ( k1_relat_1 @ X16 ) )
      | ( ( k9_relat_1 @ X16 @ ( k2_tarski @ X15 @ X17 ) )
        = ( k2_tarski @ ( k1_funct_1 @ X16 @ X15 ) @ ( k1_funct_1 @ X16 @ X17 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t118_funct_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_1 )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ( ( k9_relat_1 @ sk_D_1 @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) @ ( k1_funct_1 @ sk_D_1 @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('34',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('35',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ sk_D_1 @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) @ ( k1_funct_1 @ sk_D_1 @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['32','35','36'])).

thf('38',plain,
    ( ( k9_relat_1 @ sk_D_1 @ ( k2_tarski @ sk_A @ sk_A ) )
    = ( k2_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['29','37'])).

thf('39',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('40',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['5','12','15'])).

thf('41',plain,(
    ! [X6: $i] :
      ( ( k2_tarski @ X6 @ X6 )
      = ( k1_tarski @ X6 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('42',plain,
    ( ( k9_relat_1 @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) )
    = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','39','40','41'])).

thf('43',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k9_relat_1 @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['23','42'])).

thf('44',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k2_relat_1 @ sk_D_1 ) )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('46',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k2_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['0','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['33','34'])).

thf('49',plain,(
    $false ),
    inference(demod,[status(thm)],['47','48'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.JFZzjKugpi
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:11:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.49/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.49/0.70  % Solved by: fo/fo7.sh
% 0.49/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.70  % done 193 iterations in 0.240s
% 0.49/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.49/0.70  % SZS output start Refutation
% 0.49/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.49/0.70  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.49/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.49/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.49/0.70  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.49/0.70  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.49/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.49/0.70  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.49/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.49/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.49/0.70  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.49/0.70  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.49/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.49/0.70  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.49/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.70  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.49/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.49/0.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.49/0.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.49/0.70  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.49/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.70  thf(t144_relat_1, axiom,
% 0.49/0.70    (![A:$i,B:$i]:
% 0.49/0.70     ( ( v1_relat_1 @ B ) =>
% 0.49/0.70       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.49/0.70  thf('0', plain,
% 0.49/0.70      (![X12 : $i, X13 : $i]:
% 0.49/0.70         ((r1_tarski @ (k9_relat_1 @ X12 @ X13) @ (k2_relat_1 @ X12))
% 0.49/0.70          | ~ (v1_relat_1 @ X12))),
% 0.49/0.70      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.49/0.70  thf(t146_relat_1, axiom,
% 0.49/0.70    (![A:$i]:
% 0.49/0.70     ( ( v1_relat_1 @ A ) =>
% 0.49/0.70       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.49/0.70  thf('1', plain,
% 0.49/0.70      (![X14 : $i]:
% 0.49/0.70         (((k9_relat_1 @ X14 @ (k1_relat_1 @ X14)) = (k2_relat_1 @ X14))
% 0.49/0.70          | ~ (v1_relat_1 @ X14))),
% 0.49/0.70      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.49/0.70  thf(t64_funct_2, conjecture,
% 0.49/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.70     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.49/0.70         ( m1_subset_1 @
% 0.49/0.70           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.49/0.70       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.49/0.70         ( r1_tarski @
% 0.49/0.70           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.49/0.70           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.49/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.70    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.70        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.49/0.70            ( m1_subset_1 @
% 0.49/0.70              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.49/0.70          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.49/0.70            ( r1_tarski @
% 0.49/0.70              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.49/0.70              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.49/0.70    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.49/0.70  thf('2', plain,
% 0.49/0.70      (~ (r1_tarski @ 
% 0.49/0.70          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ sk_C) @ 
% 0.49/0.70          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('3', plain, ((v1_funct_2 @ sk_D_1 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf(d1_funct_2, axiom,
% 0.49/0.70    (![A:$i,B:$i,C:$i]:
% 0.49/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.70       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.49/0.70           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.49/0.70             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.49/0.70         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.49/0.70           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.49/0.70             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.49/0.70  thf(zf_stmt_1, axiom,
% 0.49/0.70    (![C:$i,B:$i,A:$i]:
% 0.49/0.70     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.49/0.70       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.49/0.70  thf('4', plain,
% 0.49/0.70      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.49/0.70         (~ (v1_funct_2 @ X32 @ X30 @ X31)
% 0.49/0.70          | ((X30) = (k1_relset_1 @ X30 @ X31 @ X32))
% 0.49/0.70          | ~ (zip_tseitin_1 @ X32 @ X31 @ X30))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.49/0.70  thf('5', plain,
% 0.49/0.70      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.49/0.70        | ((k1_tarski @ sk_A)
% 0.49/0.70            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['3', '4'])).
% 0.49/0.70  thf(zf_stmt_2, axiom,
% 0.49/0.70    (![B:$i,A:$i]:
% 0.49/0.70     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.49/0.70       ( zip_tseitin_0 @ B @ A ) ))).
% 0.49/0.70  thf('6', plain,
% 0.49/0.70      (![X28 : $i, X29 : $i]:
% 0.49/0.70         ((zip_tseitin_0 @ X28 @ X29) | ((X28) = (k1_xboole_0)))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.49/0.70  thf('7', plain,
% 0.49/0.70      ((m1_subset_1 @ sk_D_1 @ 
% 0.49/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.49/0.70  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.49/0.70  thf(zf_stmt_5, axiom,
% 0.49/0.70    (![A:$i,B:$i,C:$i]:
% 0.49/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.70       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.49/0.70         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.49/0.70           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.49/0.70             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.49/0.70  thf('8', plain,
% 0.49/0.70      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.49/0.70         (~ (zip_tseitin_0 @ X33 @ X34)
% 0.49/0.70          | (zip_tseitin_1 @ X35 @ X33 @ X34)
% 0.49/0.70          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33))))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.49/0.70  thf('9', plain,
% 0.49/0.70      (((zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.49/0.70        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['7', '8'])).
% 0.49/0.70  thf('10', plain,
% 0.49/0.70      ((((sk_B) = (k1_xboole_0))
% 0.49/0.70        | (zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['6', '9'])).
% 0.49/0.70  thf('11', plain, (((sk_B) != (k1_xboole_0))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('12', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A))),
% 0.49/0.70      inference('simplify_reflect-', [status(thm)], ['10', '11'])).
% 0.49/0.70  thf('13', plain,
% 0.49/0.70      ((m1_subset_1 @ sk_D_1 @ 
% 0.49/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf(redefinition_k1_relset_1, axiom,
% 0.49/0.70    (![A:$i,B:$i,C:$i]:
% 0.49/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.70       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.49/0.70  thf('14', plain,
% 0.49/0.70      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.49/0.70         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 0.49/0.70          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.49/0.70      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.49/0.70  thf('15', plain,
% 0.49/0.70      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1)
% 0.49/0.70         = (k1_relat_1 @ sk_D_1))),
% 0.49/0.70      inference('sup-', [status(thm)], ['13', '14'])).
% 0.49/0.70  thf('16', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.49/0.70      inference('demod', [status(thm)], ['5', '12', '15'])).
% 0.49/0.70  thf('17', plain,
% 0.49/0.70      (~ (r1_tarski @ 
% 0.49/0.70          (k7_relset_1 @ (k1_relat_1 @ sk_D_1) @ sk_B @ sk_D_1 @ sk_C) @ 
% 0.49/0.70          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.49/0.70      inference('demod', [status(thm)], ['2', '16'])).
% 0.49/0.70  thf('18', plain,
% 0.49/0.70      ((m1_subset_1 @ sk_D_1 @ 
% 0.49/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('19', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.49/0.70      inference('demod', [status(thm)], ['5', '12', '15'])).
% 0.49/0.70  thf('20', plain,
% 0.49/0.70      ((m1_subset_1 @ sk_D_1 @ 
% 0.49/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ sk_B)))),
% 0.49/0.70      inference('demod', [status(thm)], ['18', '19'])).
% 0.49/0.70  thf(redefinition_k7_relset_1, axiom,
% 0.49/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.70       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.49/0.70  thf('21', plain,
% 0.49/0.70      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.49/0.70         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.49/0.70          | ((k7_relset_1 @ X25 @ X26 @ X24 @ X27) = (k9_relat_1 @ X24 @ X27)))),
% 0.49/0.70      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.49/0.70  thf('22', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         ((k7_relset_1 @ (k1_relat_1 @ sk_D_1) @ sk_B @ sk_D_1 @ X0)
% 0.49/0.70           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.49/0.70      inference('sup-', [status(thm)], ['20', '21'])).
% 0.49/0.70  thf('23', plain,
% 0.49/0.70      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ 
% 0.49/0.70          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.49/0.70      inference('demod', [status(thm)], ['17', '22'])).
% 0.49/0.70  thf('24', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.49/0.70      inference('demod', [status(thm)], ['5', '12', '15'])).
% 0.49/0.70  thf(t69_enumset1, axiom,
% 0.49/0.70    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.49/0.70  thf('25', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.49/0.70      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.49/0.70  thf(d2_tarski, axiom,
% 0.49/0.70    (![A:$i,B:$i,C:$i]:
% 0.49/0.70     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.49/0.70       ( ![D:$i]:
% 0.49/0.70         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.49/0.70  thf('26', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.70         (((X1) != (X0))
% 0.49/0.70          | (r2_hidden @ X1 @ X2)
% 0.49/0.70          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.49/0.70      inference('cnf', [status(esa)], [d2_tarski])).
% 0.49/0.70  thf('27', plain,
% 0.49/0.70      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['26'])).
% 0.49/0.70  thf('28', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.49/0.70      inference('sup+', [status(thm)], ['25', '27'])).
% 0.49/0.70  thf('29', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_1))),
% 0.49/0.70      inference('sup+', [status(thm)], ['24', '28'])).
% 0.49/0.70  thf('30', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_1))),
% 0.49/0.70      inference('sup+', [status(thm)], ['24', '28'])).
% 0.49/0.70  thf(t118_funct_1, axiom,
% 0.49/0.70    (![A:$i,B:$i,C:$i]:
% 0.49/0.70     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.49/0.70       ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.49/0.70           ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) ) =>
% 0.49/0.70         ( ( k9_relat_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 0.49/0.70           ( k2_tarski @ ( k1_funct_1 @ C @ A ) @ ( k1_funct_1 @ C @ B ) ) ) ) ))).
% 0.49/0.70  thf('31', plain,
% 0.49/0.70      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.49/0.70         (~ (r2_hidden @ X15 @ (k1_relat_1 @ X16))
% 0.49/0.70          | ~ (r2_hidden @ X17 @ (k1_relat_1 @ X16))
% 0.49/0.70          | ((k9_relat_1 @ X16 @ (k2_tarski @ X15 @ X17))
% 0.49/0.70              = (k2_tarski @ (k1_funct_1 @ X16 @ X15) @ 
% 0.49/0.70                 (k1_funct_1 @ X16 @ X17)))
% 0.49/0.70          | ~ (v1_funct_1 @ X16)
% 0.49/0.70          | ~ (v1_relat_1 @ X16))),
% 0.49/0.70      inference('cnf', [status(esa)], [t118_funct_1])).
% 0.49/0.70  thf('32', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (~ (v1_relat_1 @ sk_D_1)
% 0.49/0.70          | ~ (v1_funct_1 @ sk_D_1)
% 0.49/0.70          | ((k9_relat_1 @ sk_D_1 @ (k2_tarski @ sk_A @ X0))
% 0.49/0.70              = (k2_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A) @ 
% 0.49/0.70                 (k1_funct_1 @ sk_D_1 @ X0)))
% 0.49/0.70          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['30', '31'])).
% 0.49/0.70  thf('33', plain,
% 0.49/0.70      ((m1_subset_1 @ sk_D_1 @ 
% 0.49/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf(cc1_relset_1, axiom,
% 0.49/0.70    (![A:$i,B:$i,C:$i]:
% 0.49/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.70       ( v1_relat_1 @ C ) ))).
% 0.49/0.70  thf('34', plain,
% 0.49/0.70      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.49/0.70         ((v1_relat_1 @ X18)
% 0.49/0.70          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.49/0.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.49/0.70  thf('35', plain, ((v1_relat_1 @ sk_D_1)),
% 0.49/0.70      inference('sup-', [status(thm)], ['33', '34'])).
% 0.49/0.70  thf('36', plain, ((v1_funct_1 @ sk_D_1)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('37', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (((k9_relat_1 @ sk_D_1 @ (k2_tarski @ sk_A @ X0))
% 0.49/0.70            = (k2_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A) @ 
% 0.49/0.70               (k1_funct_1 @ sk_D_1 @ X0)))
% 0.49/0.70          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 0.49/0.70      inference('demod', [status(thm)], ['32', '35', '36'])).
% 0.49/0.70  thf('38', plain,
% 0.49/0.70      (((k9_relat_1 @ sk_D_1 @ (k2_tarski @ sk_A @ sk_A))
% 0.49/0.70         = (k2_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A) @ 
% 0.49/0.70            (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['29', '37'])).
% 0.49/0.70  thf('39', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.49/0.70      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.49/0.70  thf('40', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.49/0.70      inference('demod', [status(thm)], ['5', '12', '15'])).
% 0.49/0.70  thf('41', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.49/0.70      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.49/0.70  thf('42', plain,
% 0.49/0.70      (((k9_relat_1 @ sk_D_1 @ (k1_relat_1 @ sk_D_1))
% 0.49/0.70         = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.49/0.70      inference('demod', [status(thm)], ['38', '39', '40', '41'])).
% 0.49/0.70  thf('43', plain,
% 0.49/0.70      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ 
% 0.49/0.70          (k9_relat_1 @ sk_D_1 @ (k1_relat_1 @ sk_D_1)))),
% 0.49/0.70      inference('demod', [status(thm)], ['23', '42'])).
% 0.49/0.70  thf('44', plain,
% 0.49/0.70      ((~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ (k2_relat_1 @ sk_D_1))
% 0.49/0.70        | ~ (v1_relat_1 @ sk_D_1))),
% 0.49/0.70      inference('sup-', [status(thm)], ['1', '43'])).
% 0.49/0.70  thf('45', plain, ((v1_relat_1 @ sk_D_1)),
% 0.49/0.70      inference('sup-', [status(thm)], ['33', '34'])).
% 0.49/0.70  thf('46', plain,
% 0.49/0.70      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ (k2_relat_1 @ sk_D_1))),
% 0.49/0.70      inference('demod', [status(thm)], ['44', '45'])).
% 0.49/0.70  thf('47', plain, (~ (v1_relat_1 @ sk_D_1)),
% 0.49/0.70      inference('sup-', [status(thm)], ['0', '46'])).
% 0.49/0.70  thf('48', plain, ((v1_relat_1 @ sk_D_1)),
% 0.49/0.70      inference('sup-', [status(thm)], ['33', '34'])).
% 0.49/0.70  thf('49', plain, ($false), inference('demod', [status(thm)], ['47', '48'])).
% 0.49/0.70  
% 0.49/0.70  % SZS output end Refutation
% 0.49/0.70  
% 0.49/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
