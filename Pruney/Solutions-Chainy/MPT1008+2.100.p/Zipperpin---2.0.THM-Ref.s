%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QWnMkqYn1r

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:45 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 224 expanded)
%              Number of leaves         :   39 (  85 expanded)
%              Depth                    :   12
%              Number of atoms          :  654 (2887 expanded)
%              Number of equality atoms :   57 ( 224 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

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
    v1_funct_2 @ sk_C_1 @ ( k1_tarski @ sk_A ) @ sk_B ),
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
    ! [X56: $i,X57: $i,X58: $i] :
      ( ~ ( v1_funct_2 @ X58 @ X56 @ X57 )
      | ( X56
        = ( k1_relset_1 @ X56 @ X57 @ X58 ) )
      | ~ ( zip_tseitin_1 @ X58 @ X57 @ X56 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X54: $i,X55: $i] :
      ( ( zip_tseitin_0 @ X54 @ X55 )
      | ( X54 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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
    ! [X59: $i,X60: $i,X61: $i] :
      ( ~ ( zip_tseitin_0 @ X59 @ X60 )
      | ( zip_tseitin_1 @ X61 @ X59 @ X60 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X60 @ X59 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( ( k1_relset_1 @ X42 @ X43 @ X41 )
        = ( k1_relat_1 @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('14',plain,(
    ! [X35: $i,X36: $i] :
      ( ( ( k11_relat_1 @ X35 @ X36 )
        = ( k9_relat_1 @ X35 @ ( k1_tarski @ X36 ) ) )
      | ~ ( v1_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ sk_A )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_C_1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(t38_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( k7_relset_1 @ A @ B @ C @ A )
          = ( k2_relset_1 @ A @ B @ C ) )
        & ( ( k8_relset_1 @ A @ B @ C @ B )
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('19',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ( ( k7_relset_1 @ X51 @ X52 @ X53 @ X51 )
        = ( k2_relset_1 @ X51 @ X52 @ X53 ) )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[t38_relset_1])).

thf('20',plain,
    ( ( k7_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) )
    = ( k2_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('22',plain,(
    ! [X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) )
      | ( ( k7_relset_1 @ X48 @ X49 @ X47 @ X50 )
        = ( k9_relat_1 @ X47 @ X50 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B @ sk_C_1 @ X0 )
      = ( k9_relat_1 @ sk_C_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( ( k2_relset_1 @ X45 @ X46 @ X44 )
        = ( k2_relat_1 @ X44 ) )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('26',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('28',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_C_1 ) @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ( k9_relat_1 @ sk_C_1 @ ( k1_relat_1 @ sk_C_1 ) )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['20','23','28'])).

thf('30',plain,
    ( ( ( k11_relat_1 @ sk_C_1 @ sk_A )
      = ( k2_relat_1 @ sk_C_1 ) )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['15','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('32',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ( v1_relat_1 @ X33 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('34',plain,(
    ! [X37: $i,X38: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('35',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k11_relat_1 @ sk_C_1 @ sk_A )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['30','35'])).

thf('37',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('39',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('42',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup+',[status(thm)],['40','42'])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('44',plain,(
    ! [X39: $i,X40: $i] :
      ( ~ ( r2_hidden @ X39 @ ( k1_relat_1 @ X40 ) )
      | ( ( k11_relat_1 @ X40 @ X39 )
        = ( k1_tarski @ ( k1_funct_1 @ X40 @ X39 ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_relat_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('45',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k11_relat_1 @ sk_C_1 @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['33','34'])).

thf('47',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k11_relat_1 @ sk_C_1 @ sk_A )
    = ( k1_tarski @ ( k1_funct_1 @ sk_C_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != ( k11_relat_1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['39','48'])).

thf('50',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['36','49'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.QWnMkqYn1r
% 0.12/0.36  % Computer   : n014.cluster.edu
% 0.12/0.36  % Model      : x86_64 x86_64
% 0.12/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.36  % Memory     : 8042.1875MB
% 0.12/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.36  % CPULimit   : 60
% 0.12/0.36  % DateTime   : Tue Dec  1 20:17:52 EST 2020
% 0.12/0.36  % CPUTime    : 
% 0.12/0.36  % Running portfolio for 600 s
% 0.12/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.36  % Number of cores: 8
% 0.12/0.36  % Python version: Python 3.6.8
% 0.12/0.36  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 107 iterations in 0.102s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.57  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.39/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.57  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.39/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.39/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.39/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.39/0.57  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.39/0.57  thf(k8_relset_1_type, type, k8_relset_1: $i > $i > $i > $i > $i).
% 0.39/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.57  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.39/0.57  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.39/0.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.39/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.57  thf(t62_funct_2, conjecture,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.39/0.57         ( m1_subset_1 @
% 0.39/0.57           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.39/0.57       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.39/0.57         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.39/0.57           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.39/0.57        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.39/0.57            ( m1_subset_1 @
% 0.39/0.57              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.39/0.57          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.39/0.57            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.39/0.57              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.39/0.57  thf('0', plain, ((v1_funct_2 @ sk_C_1 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(d1_funct_2, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.57       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.39/0.57           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.39/0.57             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.39/0.57         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.57           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.39/0.57             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_1, axiom,
% 0.39/0.57    (![C:$i,B:$i,A:$i]:
% 0.39/0.57     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.39/0.57       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.39/0.57  thf('1', plain,
% 0.39/0.57      (![X56 : $i, X57 : $i, X58 : $i]:
% 0.39/0.57         (~ (v1_funct_2 @ X58 @ X56 @ X57)
% 0.39/0.57          | ((X56) = (k1_relset_1 @ X56 @ X57 @ X58))
% 0.39/0.57          | ~ (zip_tseitin_1 @ X58 @ X57 @ X56))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.57  thf('2', plain,
% 0.39/0.57      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.39/0.57        | ((k1_tarski @ sk_A)
% 0.39/0.57            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['0', '1'])).
% 0.39/0.57  thf(zf_stmt_2, axiom,
% 0.39/0.57    (![B:$i,A:$i]:
% 0.39/0.57     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.57       ( zip_tseitin_0 @ B @ A ) ))).
% 0.39/0.57  thf('3', plain,
% 0.39/0.57      (![X54 : $i, X55 : $i]:
% 0.39/0.57         ((zip_tseitin_0 @ X54 @ X55) | ((X54) = (k1_xboole_0)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.39/0.57  thf('4', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_C_1 @ 
% 0.39/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.39/0.57  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.39/0.57  thf(zf_stmt_5, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.57       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.39/0.57         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.39/0.57           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.39/0.57             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.39/0.57  thf('5', plain,
% 0.39/0.57      (![X59 : $i, X60 : $i, X61 : $i]:
% 0.39/0.57         (~ (zip_tseitin_0 @ X59 @ X60)
% 0.39/0.57          | (zip_tseitin_1 @ X61 @ X59 @ X60)
% 0.39/0.57          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X60 @ X59))))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.39/0.57  thf('6', plain,
% 0.39/0.57      (((zip_tseitin_1 @ sk_C_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.39/0.57        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['4', '5'])).
% 0.39/0.57  thf('7', plain,
% 0.39/0.57      ((((sk_B) = (k1_xboole_0))
% 0.39/0.57        | (zip_tseitin_1 @ sk_C_1 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['3', '6'])).
% 0.39/0.57  thf('8', plain, (((sk_B) != (k1_xboole_0))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('9', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B @ (k1_tarski @ sk_A))),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.39/0.57  thf('10', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_C_1 @ 
% 0.39/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(redefinition_k1_relset_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.57       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.39/0.57  thf('11', plain,
% 0.39/0.57      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.39/0.57         (((k1_relset_1 @ X42 @ X43 @ X41) = (k1_relat_1 @ X41))
% 0.39/0.57          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43))))),
% 0.39/0.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.39/0.57  thf('12', plain,
% 0.39/0.57      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 0.39/0.57         = (k1_relat_1 @ sk_C_1))),
% 0.39/0.57      inference('sup-', [status(thm)], ['10', '11'])).
% 0.39/0.57  thf('13', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.39/0.57      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.39/0.57  thf(d16_relat_1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ A ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.39/0.57  thf('14', plain,
% 0.39/0.57      (![X35 : $i, X36 : $i]:
% 0.39/0.57         (((k11_relat_1 @ X35 @ X36) = (k9_relat_1 @ X35 @ (k1_tarski @ X36)))
% 0.39/0.57          | ~ (v1_relat_1 @ X35))),
% 0.39/0.57      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.39/0.57  thf('15', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (((k11_relat_1 @ X0 @ sk_A)
% 0.39/0.57            = (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_C_1)))
% 0.39/0.57          | ~ (v1_relat_1 @ X0))),
% 0.39/0.57      inference('sup+', [status(thm)], ['13', '14'])).
% 0.39/0.57  thf('16', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_C_1 @ 
% 0.39/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('17', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.39/0.57      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.39/0.57  thf('18', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_C_1 @ 
% 0.39/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)))),
% 0.39/0.57      inference('demod', [status(thm)], ['16', '17'])).
% 0.39/0.57  thf(t38_relset_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.57       ( ( ( k7_relset_1 @ A @ B @ C @ A ) = ( k2_relset_1 @ A @ B @ C ) ) & 
% 0.39/0.57         ( ( k8_relset_1 @ A @ B @ C @ B ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.39/0.57  thf('19', plain,
% 0.39/0.57      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.39/0.57         (((k7_relset_1 @ X51 @ X52 @ X53 @ X51)
% 0.39/0.57            = (k2_relset_1 @ X51 @ X52 @ X53))
% 0.39/0.57          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52))))),
% 0.39/0.57      inference('cnf', [status(esa)], [t38_relset_1])).
% 0.39/0.57  thf('20', plain,
% 0.39/0.57      (((k7_relset_1 @ (k1_relat_1 @ sk_C_1) @ sk_B @ sk_C_1 @ 
% 0.39/0.57         (k1_relat_1 @ sk_C_1))
% 0.39/0.57         = (k2_relset_1 @ (k1_relat_1 @ sk_C_1) @ sk_B @ sk_C_1))),
% 0.39/0.57      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.57  thf('21', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_C_1 @ 
% 0.39/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_C_1) @ sk_B)))),
% 0.39/0.57      inference('demod', [status(thm)], ['16', '17'])).
% 0.39/0.57  thf(redefinition_k7_relset_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.57       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.39/0.57  thf('22', plain,
% 0.39/0.57      (![X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49)))
% 0.39/0.57          | ((k7_relset_1 @ X48 @ X49 @ X47 @ X50) = (k9_relat_1 @ X47 @ X50)))),
% 0.39/0.57      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.39/0.57  thf('23', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((k7_relset_1 @ (k1_relat_1 @ sk_C_1) @ sk_B @ sk_C_1 @ X0)
% 0.39/0.57           = (k9_relat_1 @ sk_C_1 @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['21', '22'])).
% 0.39/0.57  thf('24', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_C_1 @ 
% 0.39/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(redefinition_k2_relset_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.57       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.39/0.57  thf('25', plain,
% 0.39/0.57      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.39/0.57         (((k2_relset_1 @ X45 @ X46 @ X44) = (k2_relat_1 @ X44))
% 0.39/0.57          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46))))),
% 0.39/0.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.39/0.57  thf('26', plain,
% 0.39/0.57      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 0.39/0.57         = (k2_relat_1 @ sk_C_1))),
% 0.39/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.57  thf('27', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.39/0.57      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.39/0.57  thf('28', plain,
% 0.39/0.57      (((k2_relset_1 @ (k1_relat_1 @ sk_C_1) @ sk_B @ sk_C_1)
% 0.39/0.57         = (k2_relat_1 @ sk_C_1))),
% 0.39/0.57      inference('demod', [status(thm)], ['26', '27'])).
% 0.39/0.57  thf('29', plain,
% 0.39/0.57      (((k9_relat_1 @ sk_C_1 @ (k1_relat_1 @ sk_C_1)) = (k2_relat_1 @ sk_C_1))),
% 0.39/0.57      inference('demod', [status(thm)], ['20', '23', '28'])).
% 0.39/0.57  thf('30', plain,
% 0.39/0.57      ((((k11_relat_1 @ sk_C_1 @ sk_A) = (k2_relat_1 @ sk_C_1))
% 0.39/0.57        | ~ (v1_relat_1 @ sk_C_1))),
% 0.39/0.57      inference('sup+', [status(thm)], ['15', '29'])).
% 0.39/0.57  thf('31', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_C_1 @ 
% 0.39/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(cc2_relat_1, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ A ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.39/0.57  thf('32', plain,
% 0.39/0.57      (![X33 : $i, X34 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 0.39/0.57          | (v1_relat_1 @ X33)
% 0.39/0.57          | ~ (v1_relat_1 @ X34))),
% 0.39/0.57      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.39/0.57  thf('33', plain,
% 0.39/0.57      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.39/0.57        | (v1_relat_1 @ sk_C_1))),
% 0.39/0.57      inference('sup-', [status(thm)], ['31', '32'])).
% 0.39/0.57  thf(fc6_relat_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.39/0.57  thf('34', plain,
% 0.39/0.57      (![X37 : $i, X38 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X37 @ X38))),
% 0.39/0.57      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.39/0.57  thf('35', plain, ((v1_relat_1 @ sk_C_1)),
% 0.39/0.57      inference('demod', [status(thm)], ['33', '34'])).
% 0.39/0.57  thf('36', plain, (((k11_relat_1 @ sk_C_1 @ sk_A) = (k2_relat_1 @ sk_C_1))),
% 0.39/0.57      inference('demod', [status(thm)], ['30', '35'])).
% 0.39/0.57  thf('37', plain,
% 0.39/0.57      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 0.39/0.57         != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('38', plain,
% 0.39/0.57      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_1)
% 0.39/0.57         = (k2_relat_1 @ sk_C_1))),
% 0.39/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.39/0.57  thf('39', plain,
% 0.39/0.57      (((k2_relat_1 @ sk_C_1) != (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.39/0.57      inference('demod', [status(thm)], ['37', '38'])).
% 0.39/0.57  thf('40', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_1))),
% 0.39/0.57      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.39/0.57  thf(d1_tarski, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.39/0.57       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.39/0.57  thf('41', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.39/0.57      inference('cnf', [status(esa)], [d1_tarski])).
% 0.39/0.57  thf('42', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.39/0.57      inference('simplify', [status(thm)], ['41'])).
% 0.39/0.57  thf('43', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_1))),
% 0.39/0.57      inference('sup+', [status(thm)], ['40', '42'])).
% 0.39/0.57  thf(t117_funct_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.39/0.57       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.39/0.57         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.39/0.57  thf('44', plain,
% 0.39/0.57      (![X39 : $i, X40 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X39 @ (k1_relat_1 @ X40))
% 0.39/0.57          | ((k11_relat_1 @ X40 @ X39) = (k1_tarski @ (k1_funct_1 @ X40 @ X39)))
% 0.39/0.57          | ~ (v1_funct_1 @ X40)
% 0.39/0.57          | ~ (v1_relat_1 @ X40))),
% 0.39/0.57      inference('cnf', [status(esa)], [t117_funct_1])).
% 0.39/0.57  thf('45', plain,
% 0.39/0.57      ((~ (v1_relat_1 @ sk_C_1)
% 0.39/0.57        | ~ (v1_funct_1 @ sk_C_1)
% 0.39/0.57        | ((k11_relat_1 @ sk_C_1 @ sk_A)
% 0.39/0.57            = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['43', '44'])).
% 0.39/0.57  thf('46', plain, ((v1_relat_1 @ sk_C_1)),
% 0.39/0.57      inference('demod', [status(thm)], ['33', '34'])).
% 0.39/0.57  thf('47', plain, ((v1_funct_1 @ sk_C_1)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('48', plain,
% 0.39/0.57      (((k11_relat_1 @ sk_C_1 @ sk_A)
% 0.39/0.57         = (k1_tarski @ (k1_funct_1 @ sk_C_1 @ sk_A)))),
% 0.39/0.57      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.39/0.57  thf('49', plain, (((k2_relat_1 @ sk_C_1) != (k11_relat_1 @ sk_C_1 @ sk_A))),
% 0.39/0.57      inference('demod', [status(thm)], ['39', '48'])).
% 0.39/0.57  thf('50', plain, ($false),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['36', '49'])).
% 0.39/0.57  
% 0.39/0.57  % SZS output end Refutation
% 0.39/0.57  
% 0.41/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
