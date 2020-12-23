%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8j8nJgkQsS

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:44 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 204 expanded)
%              Number of leaves         :   49 (  84 expanded)
%              Depth                    :   11
%              Number of atoms          :  753 (2251 expanded)
%              Number of equality atoms :   68 ( 174 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('1',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ( X41
        = ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ~ ( zip_tseitin_2 @ X43 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ~ ( zip_tseitin_2 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('3',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_1 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_1 @ B @ A )
         => ( zip_tseitin_2 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( zip_tseitin_1 @ X44 @ X45 )
      | ( zip_tseitin_2 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_2 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    zip_tseitin_2 @ sk_C @ sk_B @ ( k1_tarski @ sk_A ) ),
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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k1_relset_1 @ X34 @ X35 @ X33 )
        = ( k1_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
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
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X13: $i,X14: $i] :
      ( ( k1_enumset1 @ X13 @ X13 @ X14 )
      = ( k2_tarski @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(d1_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( ( E != C )
              & ( E != B )
              & ( E != A ) ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [E: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ C @ B @ A )
    <=> ( ( E != A )
        & ( E != B )
        & ( E != C ) ) ) )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( D
        = ( k1_enumset1 @ A @ B @ C ) )
    <=> ! [E: $i] :
          ( ( r2_hidden @ E @ D )
        <=> ~ ( zip_tseitin_0 @ E @ C @ B @ A ) ) ) )).

thf('16',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 )
      | ( r2_hidden @ X5 @ X9 )
      | ( X9
       != ( k1_enumset1 @ X8 @ X7 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('17',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i] :
      ( ( r2_hidden @ X5 @ ( k1_enumset1 @ X8 @ X7 @ X6 ) )
      | ( zip_tseitin_0 @ X5 @ X6 @ X7 @ X8 ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( zip_tseitin_0 @ X2 @ X0 @ X1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['15','17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ~ ( zip_tseitin_0 @ X1 @ X2 @ X3 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('20',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ~ ( zip_tseitin_0 @ X0 @ X2 @ X3 @ X0 ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','21'])).

thf('23',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['13','22'])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('24',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X28 @ ( k1_relat_1 @ X29 ) )
      | ( ( k11_relat_1 @ X29 @ X28 )
        = ( k1_tarski @ ( k1_funct_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ( ( k11_relat_1 @ sk_C @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('27',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('29',plain,(
    ! [X22: $i,X23: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('30',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k11_relat_1 @ sk_C @ sk_A )
    = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('34',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v4_relat_1 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('35',plain,(
    v4_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('36',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X26
        = ( k7_relat_1 @ X26 @ X27 ) )
      | ~ ( v4_relat_1 @ X26 @ X27 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf('39',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('41',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('42',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X24 @ X25 ) )
        = ( k9_relat_1 @ X24 @ X25 ) )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('43',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('45',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf('47',plain,(
    ! [X12: $i] :
      ( ( k2_tarski @ X12 @ X12 )
      = ( k1_tarski @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('48',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k11_relat_1 @ X20 @ X21 )
        = ( k9_relat_1 @ X20 @ ( k1_tarski @ X21 ) ) )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = ( k9_relat_1 @ X1 @ ( k2_tarski @ X0 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k11_relat_1 @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k11_relat_1 @ sk_C @ X0 )
      = ( k9_relat_1 @ sk_C @ ( k1_tarski @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['45','50'])).

thf('52',plain,
    ( ( k11_relat_1 @ sk_C @ sk_A )
    = ( k9_relat_1 @ sk_C @ ( k1_relat_1 @ sk_C ) ) ),
    inference('sup+',[status(thm)],['44','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['28','29'])).

thf('54',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k11_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['43','52','53'])).

thf('55',plain,
    ( ( k2_relat_1 @ sk_C )
    = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','54'])).

thf('56',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('58',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k2_relset_1 @ X37 @ X38 @ X36 )
        = ( k2_relat_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('59',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['55','60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.8j8nJgkQsS
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:48:50 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.54  % Solved by: fo/fo7.sh
% 0.20/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.54  % done 114 iterations in 0.091s
% 0.20/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.54  % SZS output start Refutation
% 0.20/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.54  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.20/0.54  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.20/0.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.54  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.54  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.54  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.20/0.54  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.20/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.20/0.54  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.20/0.54  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.54  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.20/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.20/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.54  thf(t62_funct_2, conjecture,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.20/0.54         ( m1_subset_1 @
% 0.20/0.54           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.20/0.54       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.54         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.20/0.54           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.54    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.54        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.20/0.54            ( m1_subset_1 @
% 0.20/0.54              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.20/0.54          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.20/0.54            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.20/0.54              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.20/0.54    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.20/0.54  thf('0', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(d1_funct_2, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.54           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.20/0.54             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.54         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.54           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.20/0.54             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_1, axiom,
% 0.20/0.54    (![C:$i,B:$i,A:$i]:
% 0.20/0.54     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.20/0.54       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.54  thf('1', plain,
% 0.20/0.54      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.20/0.54         (~ (v1_funct_2 @ X43 @ X41 @ X42)
% 0.20/0.54          | ((X41) = (k1_relset_1 @ X41 @ X42 @ X43))
% 0.20/0.54          | ~ (zip_tseitin_2 @ X43 @ X42 @ X41))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.54  thf('2', plain,
% 0.20/0.54      ((~ (zip_tseitin_2 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.20/0.54        | ((k1_tarski @ sk_A)
% 0.20/0.54            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.54  thf(zf_stmt_2, axiom,
% 0.20/0.54    (![B:$i,A:$i]:
% 0.20/0.54     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.54       ( zip_tseitin_1 @ B @ A ) ))).
% 0.20/0.54  thf('3', plain,
% 0.20/0.54      (![X39 : $i, X40 : $i]:
% 0.20/0.54         ((zip_tseitin_1 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.54  thf('4', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C @ 
% 0.20/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.20/0.54  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $o).
% 0.20/0.54  thf(zf_stmt_5, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.20/0.54         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.54           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.54             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.20/0.54  thf('5', plain,
% 0.20/0.54      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.20/0.54         (~ (zip_tseitin_1 @ X44 @ X45)
% 0.20/0.54          | (zip_tseitin_2 @ X46 @ X44 @ X45)
% 0.20/0.54          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.54  thf('6', plain,
% 0.20/0.54      (((zip_tseitin_2 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 0.20/0.54        | ~ (zip_tseitin_1 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['4', '5'])).
% 0.20/0.54  thf('7', plain,
% 0.20/0.54      ((((sk_B) = (k1_xboole_0))
% 0.20/0.54        | (zip_tseitin_2 @ sk_C @ sk_B @ (k1_tarski @ sk_A)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['3', '6'])).
% 0.20/0.54  thf('8', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('9', plain, ((zip_tseitin_2 @ sk_C @ sk_B @ (k1_tarski @ sk_A))),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.20/0.54  thf('10', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C @ 
% 0.20/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.54  thf('11', plain,
% 0.20/0.54      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.20/0.54         (((k1_relset_1 @ X34 @ X35 @ X33) = (k1_relat_1 @ X33))
% 0.20/0.54          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.54  thf('12', plain,
% 0.20/0.54      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.20/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.20/0.54  thf('13', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.20/0.54      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.20/0.54  thf(t69_enumset1, axiom,
% 0.20/0.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.20/0.54  thf('14', plain,
% 0.20/0.54      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.20/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.54  thf(t70_enumset1, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.20/0.54  thf('15', plain,
% 0.20/0.54      (![X13 : $i, X14 : $i]:
% 0.20/0.54         ((k1_enumset1 @ X13 @ X13 @ X14) = (k2_tarski @ X13 @ X14))),
% 0.20/0.54      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.20/0.54  thf(d1_enumset1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.54     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.54       ( ![E:$i]:
% 0.20/0.54         ( ( r2_hidden @ E @ D ) <=>
% 0.20/0.54           ( ~( ( ( E ) != ( C ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( A ) ) ) ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.20/0.54  thf(zf_stmt_7, axiom,
% 0.20/0.54    (![E:$i,C:$i,B:$i,A:$i]:
% 0.20/0.54     ( ( zip_tseitin_0 @ E @ C @ B @ A ) <=>
% 0.20/0.54       ( ( ( E ) != ( A ) ) & ( ( E ) != ( B ) ) & ( ( E ) != ( C ) ) ) ))).
% 0.20/0.54  thf(zf_stmt_8, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.54     ( ( ( D ) = ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.20/0.54       ( ![E:$i]:
% 0.20/0.54         ( ( r2_hidden @ E @ D ) <=> ( ~( zip_tseitin_0 @ E @ C @ B @ A ) ) ) ) ))).
% 0.20/0.54  thf('16', plain,
% 0.20/0.54      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.54         ((zip_tseitin_0 @ X5 @ X6 @ X7 @ X8)
% 0.20/0.54          | (r2_hidden @ X5 @ X9)
% 0.20/0.54          | ((X9) != (k1_enumset1 @ X8 @ X7 @ X6)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.20/0.54  thf('17', plain,
% 0.20/0.54      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i]:
% 0.20/0.54         ((r2_hidden @ X5 @ (k1_enumset1 @ X8 @ X7 @ X6))
% 0.20/0.54          | (zip_tseitin_0 @ X5 @ X6 @ X7 @ X8))),
% 0.20/0.54      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.54  thf('18', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.54         ((r2_hidden @ X2 @ (k2_tarski @ X1 @ X0))
% 0.20/0.54          | (zip_tseitin_0 @ X2 @ X0 @ X1 @ X1))),
% 0.20/0.54      inference('sup+', [status(thm)], ['15', '17'])).
% 0.20/0.54  thf('19', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.54         (((X1) != (X0)) | ~ (zip_tseitin_0 @ X1 @ X2 @ X3 @ X0))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.20/0.54  thf('20', plain,
% 0.20/0.54      (![X0 : $i, X2 : $i, X3 : $i]: ~ (zip_tseitin_0 @ X0 @ X2 @ X3 @ X0)),
% 0.20/0.54      inference('simplify', [status(thm)], ['19'])).
% 0.20/0.54  thf('21', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X0 @ X1))),
% 0.20/0.54      inference('sup-', [status(thm)], ['18', '20'])).
% 0.20/0.54  thf('22', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.20/0.54      inference('sup+', [status(thm)], ['14', '21'])).
% 0.20/0.54  thf('23', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C))),
% 0.20/0.54      inference('sup+', [status(thm)], ['13', '22'])).
% 0.20/0.54  thf(t117_funct_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.54       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.20/0.54         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.20/0.54  thf('24', plain,
% 0.20/0.54      (![X28 : $i, X29 : $i]:
% 0.20/0.54         (~ (r2_hidden @ X28 @ (k1_relat_1 @ X29))
% 0.20/0.54          | ((k11_relat_1 @ X29 @ X28) = (k1_tarski @ (k1_funct_1 @ X29 @ X28)))
% 0.20/0.54          | ~ (v1_funct_1 @ X29)
% 0.20/0.54          | ~ (v1_relat_1 @ X29))),
% 0.20/0.54      inference('cnf', [status(esa)], [t117_funct_1])).
% 0.20/0.54  thf('25', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.54        | ~ (v1_funct_1 @ sk_C)
% 0.20/0.54        | ((k11_relat_1 @ sk_C @ sk_A)
% 0.20/0.54            = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.54  thf('26', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C @ 
% 0.20/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(cc2_relat_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.54  thf('27', plain,
% 0.20/0.54      (![X18 : $i, X19 : $i]:
% 0.20/0.54         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 0.20/0.54          | (v1_relat_1 @ X18)
% 0.20/0.54          | ~ (v1_relat_1 @ X19))),
% 0.20/0.54      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.54  thf('28', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.20/0.54        | (v1_relat_1 @ sk_C))),
% 0.20/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.54  thf(fc6_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.54  thf('29', plain,
% 0.20/0.54      (![X22 : $i, X23 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X22 @ X23))),
% 0.20/0.54      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.54  thf('30', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.54      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.54  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('32', plain,
% 0.20/0.54      (((k11_relat_1 @ sk_C @ sk_A) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['25', '30', '31'])).
% 0.20/0.54  thf('33', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C @ 
% 0.20/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(cc2_relset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.54  thf('34', plain,
% 0.20/0.54      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.20/0.54         ((v4_relat_1 @ X30 @ X31)
% 0.20/0.54          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.20/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.54  thf('35', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 0.20/0.54      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.54  thf(t209_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.54       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.20/0.54  thf('36', plain,
% 0.20/0.54      (![X26 : $i, X27 : $i]:
% 0.20/0.54         (((X26) = (k7_relat_1 @ X26 @ X27))
% 0.20/0.54          | ~ (v4_relat_1 @ X26 @ X27)
% 0.20/0.54          | ~ (v1_relat_1 @ X26))),
% 0.20/0.54      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.20/0.54  thf('37', plain,
% 0.20/0.54      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.54        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A))))),
% 0.20/0.54      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.54  thf('38', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.54      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.54  thf('39', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['37', '38'])).
% 0.20/0.54  thf('40', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.20/0.54      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.20/0.54  thf('41', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.20/0.54      inference('demod', [status(thm)], ['39', '40'])).
% 0.20/0.54  thf(t148_relat_1, axiom,
% 0.20/0.54    (![A:$i,B:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ B ) =>
% 0.20/0.54       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.20/0.54  thf('42', plain,
% 0.20/0.54      (![X24 : $i, X25 : $i]:
% 0.20/0.54         (((k2_relat_1 @ (k7_relat_1 @ X24 @ X25)) = (k9_relat_1 @ X24 @ X25))
% 0.20/0.54          | ~ (v1_relat_1 @ X24))),
% 0.20/0.54      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.20/0.54  thf('43', plain,
% 0.20/0.54      ((((k2_relat_1 @ sk_C) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))
% 0.20/0.54        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.54      inference('sup+', [status(thm)], ['41', '42'])).
% 0.20/0.54  thf('44', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 0.20/0.54      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.20/0.54  thf('45', plain,
% 0.20/0.54      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.20/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.54  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.54      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.54  thf('47', plain,
% 0.20/0.54      (![X12 : $i]: ((k2_tarski @ X12 @ X12) = (k1_tarski @ X12))),
% 0.20/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.20/0.54  thf(d16_relat_1, axiom,
% 0.20/0.54    (![A:$i]:
% 0.20/0.54     ( ( v1_relat_1 @ A ) =>
% 0.20/0.54       ( ![B:$i]:
% 0.20/0.54         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.20/0.54  thf('48', plain,
% 0.20/0.54      (![X20 : $i, X21 : $i]:
% 0.20/0.54         (((k11_relat_1 @ X20 @ X21) = (k9_relat_1 @ X20 @ (k1_tarski @ X21)))
% 0.20/0.54          | ~ (v1_relat_1 @ X20))),
% 0.20/0.54      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.20/0.54  thf('49', plain,
% 0.20/0.54      (![X0 : $i, X1 : $i]:
% 0.20/0.54         (((k11_relat_1 @ X1 @ X0) = (k9_relat_1 @ X1 @ (k2_tarski @ X0 @ X0)))
% 0.20/0.54          | ~ (v1_relat_1 @ X1))),
% 0.20/0.54      inference('sup+', [status(thm)], ['47', '48'])).
% 0.20/0.54  thf('50', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((k11_relat_1 @ sk_C @ X0)
% 0.20/0.54           = (k9_relat_1 @ sk_C @ (k2_tarski @ X0 @ X0)))),
% 0.20/0.54      inference('sup-', [status(thm)], ['46', '49'])).
% 0.20/0.54  thf('51', plain,
% 0.20/0.54      (![X0 : $i]:
% 0.20/0.54         ((k11_relat_1 @ sk_C @ X0) = (k9_relat_1 @ sk_C @ (k1_tarski @ X0)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['45', '50'])).
% 0.20/0.54  thf('52', plain,
% 0.20/0.54      (((k11_relat_1 @ sk_C @ sk_A) = (k9_relat_1 @ sk_C @ (k1_relat_1 @ sk_C)))),
% 0.20/0.54      inference('sup+', [status(thm)], ['44', '51'])).
% 0.20/0.54  thf('53', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.54      inference('demod', [status(thm)], ['28', '29'])).
% 0.20/0.54  thf('54', plain, (((k2_relat_1 @ sk_C) = (k11_relat_1 @ sk_C @ sk_A))),
% 0.20/0.54      inference('demod', [status(thm)], ['43', '52', '53'])).
% 0.20/0.54  thf('55', plain,
% 0.20/0.54      (((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['32', '54'])).
% 0.20/0.54  thf('56', plain,
% 0.20/0.54      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)
% 0.20/0.54         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf('57', plain,
% 0.20/0.54      ((m1_subset_1 @ sk_C @ 
% 0.20/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.20/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.54  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.54    (![A:$i,B:$i,C:$i]:
% 0.20/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.54       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.54  thf('58', plain,
% 0.20/0.54      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.20/0.54         (((k2_relset_1 @ X37 @ X38 @ X36) = (k2_relat_1 @ X36))
% 0.20/0.54          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.20/0.54      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.54  thf('59', plain,
% 0.20/0.54      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.20/0.54      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.54  thf('60', plain,
% 0.20/0.54      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 0.20/0.54      inference('demod', [status(thm)], ['56', '59'])).
% 0.20/0.54  thf('61', plain, ($false),
% 0.20/0.54      inference('simplify_reflect-', [status(thm)], ['55', '60'])).
% 0.20/0.54  
% 0.20/0.54  % SZS output end Refutation
% 0.20/0.54  
% 0.20/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
