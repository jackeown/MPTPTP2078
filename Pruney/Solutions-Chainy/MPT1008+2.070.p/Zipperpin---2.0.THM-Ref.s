%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4M3gAtNbzv

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:41 EST 2020

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 228 expanded)
%              Number of leaves         :   49 (  90 expanded)
%              Depth                    :   22
%              Number of atoms          : 1039 (2588 expanded)
%              Number of equality atoms :  112 ( 233 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_enumset1_type,type,(
    k2_enumset1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
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
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
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
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('14',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('15',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf('17',plain,
    ( ( ( k1_tarski @ sk_A )
      = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['13','16'])).

thf('18',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X39: $i] :
      ( ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X39 ) @ ( k2_relat_1 @ X39 ) ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('20',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('22',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v1_relat_1 @ X19 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('23',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['20','23','24'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('26',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X22 ) ) )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('27',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ ( k2_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('28',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_enumset1 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t142_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) )
    <=> ~ ( ( D != k1_xboole_0 )
          & ( D
           != ( k1_tarski @ A ) )
          & ( D
           != ( k1_tarski @ B ) )
          & ( D
           != ( k1_tarski @ C ) )
          & ( D
           != ( k2_tarski @ A @ B ) )
          & ( D
           != ( k2_tarski @ B @ C ) )
          & ( D
           != ( k2_tarski @ A @ C ) )
          & ( D
           != ( k1_enumset1 @ A @ B @ C ) ) ) ) )).

thf('30',plain,(
    ! [X8: $i,X9: $i,X10: $i,X12: $i] :
      ( ( r1_tarski @ X12 @ ( k1_enumset1 @ X8 @ X9 @ X10 ) )
      | ( X12
       != ( k1_tarski @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('31',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( r1_tarski @ ( k1_tarski @ X8 ) @ ( k1_enumset1 @ X8 @ X9 @ X10 ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['29','31'])).

thf('33',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('34',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ( v4_relat_1 @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ~ ( v1_relat_1 @ sk_C )
      | ( v4_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 )
      | ( v4_relat_1 @ sk_C @ X0 ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ sk_C @ ( k2_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,(
    v4_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ),
    inference('sup+',[status(thm)],['28','38'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15
        = ( k7_relat_1 @ X15 @ X16 ) )
      | ~ ( v4_relat_1 @ X15 @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('43',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf(t167_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) )).

thf('44',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ X17 @ ( k1_tarski @ X18 ) ) ) @ ( k1_tarski @ ( k1_funct_1 @ X17 @ X18 ) ) )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t167_funct_1])).

thf('45',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['21','22'])).

thf('47',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf(t71_enumset1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k2_enumset1 @ A @ A @ B @ C )
      = ( k1_enumset1 @ A @ B @ C ) ) )).

thf('49',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X4 @ X4 @ X5 @ X6 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('50',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_enumset1 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_enumset1 @ X1 @ X1 @ X1 @ X0 )
      = ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k2_enumset1 @ X0 @ X0 @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( k2_enumset1 @ X4 @ X4 @ X5 @ X6 )
      = ( k1_enumset1 @ X4 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t71_enumset1])).

thf('55',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X11
        = ( k1_enumset1 @ X8 @ X9 @ X10 ) )
      | ( X11
        = ( k2_tarski @ X8 @ X10 ) )
      | ( X11
        = ( k2_tarski @ X9 @ X10 ) )
      | ( X11
        = ( k2_tarski @ X8 @ X9 ) )
      | ( X11
        = ( k1_tarski @ X10 ) )
      | ( X11
        = ( k1_tarski @ X9 ) )
      | ( X11
        = ( k1_tarski @ X8 ) )
      | ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ ( k1_enumset1 @ X8 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X3 @ ( k2_enumset1 @ X2 @ X2 @ X1 @ X0 ) )
      | ( X3 = k1_xboole_0 )
      | ( X3
        = ( k1_tarski @ X2 ) )
      | ( X3
        = ( k1_tarski @ X1 ) )
      | ( X3
        = ( k1_tarski @ X0 ) )
      | ( X3
        = ( k2_tarski @ X2 @ X1 ) )
      | ( X3
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X3
        = ( k2_tarski @ X2 @ X0 ) )
      | ( X3
        = ( k1_enumset1 @ X2 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_enumset1 @ X0 @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_enumset1 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k2_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','60'])).

thf('62',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('63',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) )
    | ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C )
      = ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('67',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k2_relset_1 @ X29 @ X30 @ X28 )
        = ( k2_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('68',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ( k2_relat_1 @ sk_C )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','68'])).

thf('70',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['64','69'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('71',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('72',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('74',plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['71','74'])).

thf('76',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['27','70','75'])).

thf('77',plain,
    ( ( k1_tarski @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['17','76'])).

thf(fc2_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ A ) ) )).

thf('78',plain,(
    ! [X7: $i] :
      ~ ( v1_xboole_0 @ ( k1_tarski @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc2_xboole_0])).

thf('79',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['71','74'])).

thf('81',plain,(
    $false ),
    inference(demod,[status(thm)],['79','80'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.4M3gAtNbzv
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:45:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 1.07/1.30  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.07/1.30  % Solved by: fo/fo7.sh
% 1.07/1.30  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.07/1.30  % done 1260 iterations in 0.851s
% 1.07/1.30  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.07/1.30  % SZS output start Refutation
% 1.07/1.30  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.07/1.30  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.07/1.30  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.07/1.30  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.07/1.30  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 1.07/1.30  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.07/1.30  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.07/1.30  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 1.07/1.30  thf(sk_C_type, type, sk_C: $i).
% 1.07/1.30  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.07/1.30  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.07/1.30  thf(o_0_0_xboole_0_type, type, o_0_0_xboole_0: $i).
% 1.07/1.30  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.07/1.30  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.07/1.30  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.07/1.30  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.07/1.30  thf(k2_enumset1_type, type, k2_enumset1: $i > $i > $i > $i > $i).
% 1.07/1.30  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.07/1.30  thf(sk_A_type, type, sk_A: $i).
% 1.07/1.30  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.07/1.30  thf(sk_B_type, type, sk_B: $i).
% 1.07/1.30  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.07/1.30  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.07/1.30  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.07/1.30  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.07/1.30  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 1.07/1.30  thf(t62_funct_2, conjecture,
% 1.07/1.30    (![A:$i,B:$i,C:$i]:
% 1.07/1.30     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 1.07/1.30         ( m1_subset_1 @
% 1.07/1.30           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 1.07/1.30       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 1.07/1.30         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 1.07/1.30           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 1.07/1.30  thf(zf_stmt_0, negated_conjecture,
% 1.07/1.30    (~( ![A:$i,B:$i,C:$i]:
% 1.07/1.30        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 1.07/1.30            ( m1_subset_1 @
% 1.07/1.30              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 1.07/1.30          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 1.07/1.30            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 1.07/1.30              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 1.07/1.30    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 1.07/1.30  thf('0', plain, ((v1_funct_2 @ sk_C @ (k1_tarski @ sk_A) @ sk_B)),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf(d1_funct_2, axiom,
% 1.07/1.30    (![A:$i,B:$i,C:$i]:
% 1.07/1.30     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.30       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.07/1.30           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.07/1.30             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.07/1.30         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.07/1.30           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.07/1.30             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.07/1.30  thf(zf_stmt_1, axiom,
% 1.07/1.30    (![C:$i,B:$i,A:$i]:
% 1.07/1.30     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.07/1.30       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.07/1.30  thf('1', plain,
% 1.07/1.30      (![X33 : $i, X34 : $i, X35 : $i]:
% 1.07/1.30         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 1.07/1.30          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 1.07/1.30          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.07/1.30  thf('2', plain,
% 1.07/1.30      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 1.07/1.30        | ((k1_tarski @ sk_A)
% 1.07/1.30            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)))),
% 1.07/1.30      inference('sup-', [status(thm)], ['0', '1'])).
% 1.07/1.30  thf(zf_stmt_2, axiom,
% 1.07/1.30    (![B:$i,A:$i]:
% 1.07/1.30     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.07/1.30       ( zip_tseitin_0 @ B @ A ) ))).
% 1.07/1.30  thf('3', plain,
% 1.07/1.30      (![X31 : $i, X32 : $i]:
% 1.07/1.30         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.07/1.30  thf('4', plain,
% 1.07/1.30      ((m1_subset_1 @ sk_C @ 
% 1.07/1.30        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.07/1.30  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.07/1.30  thf(zf_stmt_5, axiom,
% 1.07/1.30    (![A:$i,B:$i,C:$i]:
% 1.07/1.30     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.30       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.07/1.30         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.07/1.30           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.07/1.30             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.07/1.30  thf('5', plain,
% 1.07/1.30      (![X36 : $i, X37 : $i, X38 : $i]:
% 1.07/1.30         (~ (zip_tseitin_0 @ X36 @ X37)
% 1.07/1.30          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 1.07/1.30          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.07/1.30  thf('6', plain,
% 1.07/1.30      (((zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))
% 1.07/1.30        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 1.07/1.30      inference('sup-', [status(thm)], ['4', '5'])).
% 1.07/1.30  thf('7', plain,
% 1.07/1.30      ((((sk_B) = (k1_xboole_0))
% 1.07/1.30        | (zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A)))),
% 1.07/1.30      inference('sup-', [status(thm)], ['3', '6'])).
% 1.07/1.30  thf('8', plain, (((sk_B) != (k1_xboole_0))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('9', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ (k1_tarski @ sk_A))),
% 1.07/1.30      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 1.07/1.30  thf('10', plain,
% 1.07/1.30      ((m1_subset_1 @ sk_C @ 
% 1.07/1.30        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf(redefinition_k1_relset_1, axiom,
% 1.07/1.30    (![A:$i,B:$i,C:$i]:
% 1.07/1.30     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.30       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.07/1.30  thf('11', plain,
% 1.07/1.30      (![X25 : $i, X26 : $i, X27 : $i]:
% 1.07/1.30         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 1.07/1.30          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 1.07/1.30      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.07/1.30  thf('12', plain,
% 1.07/1.30      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 1.07/1.30      inference('sup-', [status(thm)], ['10', '11'])).
% 1.07/1.30  thf('13', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.07/1.30      inference('demod', [status(thm)], ['2', '9', '12'])).
% 1.07/1.30  thf(l13_xboole_0, axiom,
% 1.07/1.30    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 1.07/1.30  thf('14', plain,
% 1.07/1.30      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.07/1.30      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.07/1.30  thf(t60_relat_1, axiom,
% 1.07/1.30    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 1.07/1.30     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.07/1.30  thf('15', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 1.07/1.30      inference('cnf', [status(esa)], [t60_relat_1])).
% 1.07/1.30  thf('16', plain,
% 1.07/1.30      (![X0 : $i]: (((k1_relat_1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.07/1.30      inference('sup+', [status(thm)], ['14', '15'])).
% 1.07/1.30  thf('17', plain,
% 1.07/1.30      ((((k1_tarski @ sk_A) = (k1_xboole_0)) | ~ (v1_xboole_0 @ sk_C))),
% 1.07/1.30      inference('sup+', [status(thm)], ['13', '16'])).
% 1.07/1.30  thf('18', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.07/1.30      inference('demod', [status(thm)], ['2', '9', '12'])).
% 1.07/1.30  thf(t3_funct_2, axiom,
% 1.07/1.30    (![A:$i]:
% 1.07/1.30     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.07/1.30       ( ( v1_funct_1 @ A ) & 
% 1.07/1.30         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 1.07/1.30         ( m1_subset_1 @
% 1.07/1.30           A @ 
% 1.07/1.30           ( k1_zfmisc_1 @
% 1.07/1.30             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 1.07/1.30  thf('19', plain,
% 1.07/1.30      (![X39 : $i]:
% 1.07/1.30         ((m1_subset_1 @ X39 @ 
% 1.07/1.30           (k1_zfmisc_1 @ 
% 1.07/1.30            (k2_zfmisc_1 @ (k1_relat_1 @ X39) @ (k2_relat_1 @ X39))))
% 1.07/1.30          | ~ (v1_funct_1 @ X39)
% 1.07/1.30          | ~ (v1_relat_1 @ X39))),
% 1.07/1.30      inference('cnf', [status(esa)], [t3_funct_2])).
% 1.07/1.30  thf('20', plain,
% 1.07/1.30      (((m1_subset_1 @ sk_C @ 
% 1.07/1.30         (k1_zfmisc_1 @ 
% 1.07/1.30          (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_C))))
% 1.07/1.30        | ~ (v1_relat_1 @ sk_C)
% 1.07/1.30        | ~ (v1_funct_1 @ sk_C))),
% 1.07/1.30      inference('sup+', [status(thm)], ['18', '19'])).
% 1.07/1.30  thf('21', plain,
% 1.07/1.30      ((m1_subset_1 @ sk_C @ 
% 1.07/1.30        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf(cc1_relset_1, axiom,
% 1.07/1.30    (![A:$i,B:$i,C:$i]:
% 1.07/1.30     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.30       ( v1_relat_1 @ C ) ))).
% 1.07/1.30  thf('22', plain,
% 1.07/1.30      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.07/1.30         ((v1_relat_1 @ X19)
% 1.07/1.30          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 1.07/1.30      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.07/1.30  thf('23', plain, ((v1_relat_1 @ sk_C)),
% 1.07/1.30      inference('sup-', [status(thm)], ['21', '22'])).
% 1.07/1.30  thf('24', plain, ((v1_funct_1 @ sk_C)),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('25', plain,
% 1.07/1.30      ((m1_subset_1 @ sk_C @ 
% 1.07/1.30        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_C))))),
% 1.07/1.30      inference('demod', [status(thm)], ['20', '23', '24'])).
% 1.07/1.30  thf(cc4_relset_1, axiom,
% 1.07/1.30    (![A:$i,B:$i]:
% 1.07/1.30     ( ( v1_xboole_0 @ A ) =>
% 1.07/1.30       ( ![C:$i]:
% 1.07/1.30         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 1.07/1.30           ( v1_xboole_0 @ C ) ) ) ))).
% 1.07/1.30  thf('26', plain,
% 1.07/1.30      (![X22 : $i, X23 : $i, X24 : $i]:
% 1.07/1.30         (~ (v1_xboole_0 @ X22)
% 1.07/1.30          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X22)))
% 1.07/1.30          | (v1_xboole_0 @ X23))),
% 1.07/1.30      inference('cnf', [status(esa)], [cc4_relset_1])).
% 1.07/1.30  thf('27', plain,
% 1.07/1.30      (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ (k2_relat_1 @ sk_C)))),
% 1.07/1.30      inference('sup-', [status(thm)], ['25', '26'])).
% 1.07/1.30  thf(t69_enumset1, axiom,
% 1.07/1.30    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 1.07/1.30  thf('28', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 1.07/1.30      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.07/1.30  thf(t70_enumset1, axiom,
% 1.07/1.30    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 1.07/1.30  thf('29', plain,
% 1.07/1.30      (![X2 : $i, X3 : $i]:
% 1.07/1.30         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 1.07/1.30      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.07/1.30  thf(t142_zfmisc_1, axiom,
% 1.07/1.30    (![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.30     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 1.07/1.30       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 1.07/1.30            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 1.07/1.30            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 1.07/1.30            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 1.07/1.30            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 1.07/1.30            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 1.07/1.30  thf('30', plain,
% 1.07/1.30      (![X8 : $i, X9 : $i, X10 : $i, X12 : $i]:
% 1.07/1.30         ((r1_tarski @ X12 @ (k1_enumset1 @ X8 @ X9 @ X10))
% 1.07/1.30          | ((X12) != (k1_tarski @ X8)))),
% 1.07/1.30      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 1.07/1.30  thf('31', plain,
% 1.07/1.30      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.07/1.30         (r1_tarski @ (k1_tarski @ X8) @ (k1_enumset1 @ X8 @ X9 @ X10))),
% 1.07/1.30      inference('simplify', [status(thm)], ['30'])).
% 1.07/1.30  thf('32', plain,
% 1.07/1.30      (![X0 : $i, X1 : $i]:
% 1.07/1.30         (r1_tarski @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))),
% 1.07/1.30      inference('sup+', [status(thm)], ['29', '31'])).
% 1.07/1.30  thf('33', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C))),
% 1.07/1.30      inference('demod', [status(thm)], ['2', '9', '12'])).
% 1.07/1.30  thf(d18_relat_1, axiom,
% 1.07/1.30    (![A:$i,B:$i]:
% 1.07/1.30     ( ( v1_relat_1 @ B ) =>
% 1.07/1.30       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.07/1.30  thf('34', plain,
% 1.07/1.30      (![X13 : $i, X14 : $i]:
% 1.07/1.30         (~ (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 1.07/1.30          | (v4_relat_1 @ X13 @ X14)
% 1.07/1.30          | ~ (v1_relat_1 @ X13))),
% 1.07/1.30      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.07/1.30  thf('35', plain,
% 1.07/1.30      (![X0 : $i]:
% 1.07/1.30         (~ (r1_tarski @ (k1_tarski @ sk_A) @ X0)
% 1.07/1.30          | ~ (v1_relat_1 @ sk_C)
% 1.07/1.30          | (v4_relat_1 @ sk_C @ X0))),
% 1.07/1.30      inference('sup-', [status(thm)], ['33', '34'])).
% 1.07/1.30  thf('36', plain, ((v1_relat_1 @ sk_C)),
% 1.07/1.30      inference('sup-', [status(thm)], ['21', '22'])).
% 1.07/1.30  thf('37', plain,
% 1.07/1.30      (![X0 : $i]:
% 1.07/1.30         (~ (r1_tarski @ (k1_tarski @ sk_A) @ X0) | (v4_relat_1 @ sk_C @ X0))),
% 1.07/1.30      inference('demod', [status(thm)], ['35', '36'])).
% 1.07/1.30  thf('38', plain, (![X0 : $i]: (v4_relat_1 @ sk_C @ (k2_tarski @ sk_A @ X0))),
% 1.07/1.30      inference('sup-', [status(thm)], ['32', '37'])).
% 1.07/1.30  thf('39', plain, ((v4_relat_1 @ sk_C @ (k1_tarski @ sk_A))),
% 1.07/1.30      inference('sup+', [status(thm)], ['28', '38'])).
% 1.07/1.30  thf(t209_relat_1, axiom,
% 1.07/1.30    (![A:$i,B:$i]:
% 1.07/1.30     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 1.07/1.30       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 1.07/1.30  thf('40', plain,
% 1.07/1.30      (![X15 : $i, X16 : $i]:
% 1.07/1.30         (((X15) = (k7_relat_1 @ X15 @ X16))
% 1.07/1.30          | ~ (v4_relat_1 @ X15 @ X16)
% 1.07/1.30          | ~ (v1_relat_1 @ X15))),
% 1.07/1.30      inference('cnf', [status(esa)], [t209_relat_1])).
% 1.07/1.30  thf('41', plain,
% 1.07/1.30      ((~ (v1_relat_1 @ sk_C)
% 1.07/1.30        | ((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A))))),
% 1.07/1.30      inference('sup-', [status(thm)], ['39', '40'])).
% 1.07/1.30  thf('42', plain, ((v1_relat_1 @ sk_C)),
% 1.07/1.30      inference('sup-', [status(thm)], ['21', '22'])).
% 1.07/1.30  thf('43', plain, (((sk_C) = (k7_relat_1 @ sk_C @ (k1_tarski @ sk_A)))),
% 1.07/1.30      inference('demod', [status(thm)], ['41', '42'])).
% 1.07/1.30  thf(t167_funct_1, axiom,
% 1.07/1.30    (![A:$i,B:$i]:
% 1.07/1.30     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.07/1.30       ( r1_tarski @
% 1.07/1.30         ( k2_relat_1 @ ( k7_relat_1 @ B @ ( k1_tarski @ A ) ) ) @ 
% 1.07/1.30         ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ))).
% 1.07/1.30  thf('44', plain,
% 1.07/1.30      (![X17 : $i, X18 : $i]:
% 1.07/1.30         ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ X17 @ (k1_tarski @ X18))) @ 
% 1.07/1.30           (k1_tarski @ (k1_funct_1 @ X17 @ X18)))
% 1.07/1.30          | ~ (v1_funct_1 @ X17)
% 1.07/1.30          | ~ (v1_relat_1 @ X17))),
% 1.07/1.30      inference('cnf', [status(esa)], [t167_funct_1])).
% 1.07/1.30  thf('45', plain,
% 1.07/1.30      (((r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 1.07/1.30         (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 1.07/1.30        | ~ (v1_relat_1 @ sk_C)
% 1.07/1.30        | ~ (v1_funct_1 @ sk_C))),
% 1.07/1.30      inference('sup+', [status(thm)], ['43', '44'])).
% 1.07/1.30  thf('46', plain, ((v1_relat_1 @ sk_C)),
% 1.07/1.30      inference('sup-', [status(thm)], ['21', '22'])).
% 1.07/1.30  thf('47', plain, ((v1_funct_1 @ sk_C)),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('48', plain,
% 1.07/1.30      ((r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 1.07/1.30        (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 1.07/1.30      inference('demod', [status(thm)], ['45', '46', '47'])).
% 1.07/1.30  thf(t71_enumset1, axiom,
% 1.07/1.30    (![A:$i,B:$i,C:$i]:
% 1.07/1.30     ( ( k2_enumset1 @ A @ A @ B @ C ) = ( k1_enumset1 @ A @ B @ C ) ))).
% 1.07/1.30  thf('49', plain,
% 1.07/1.30      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.07/1.30         ((k2_enumset1 @ X4 @ X4 @ X5 @ X6) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 1.07/1.30      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.07/1.30  thf('50', plain,
% 1.07/1.30      (![X2 : $i, X3 : $i]:
% 1.07/1.30         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 1.07/1.30      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.07/1.30  thf('51', plain,
% 1.07/1.30      (![X0 : $i, X1 : $i]:
% 1.07/1.30         ((k2_enumset1 @ X1 @ X1 @ X1 @ X0) = (k2_tarski @ X1 @ X0))),
% 1.07/1.30      inference('sup+', [status(thm)], ['49', '50'])).
% 1.07/1.30  thf('52', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 1.07/1.30      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.07/1.30  thf('53', plain,
% 1.07/1.30      (![X0 : $i]: ((k2_enumset1 @ X0 @ X0 @ X0 @ X0) = (k1_tarski @ X0))),
% 1.07/1.30      inference('sup+', [status(thm)], ['51', '52'])).
% 1.07/1.30  thf('54', plain,
% 1.07/1.30      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.07/1.30         ((k2_enumset1 @ X4 @ X4 @ X5 @ X6) = (k1_enumset1 @ X4 @ X5 @ X6))),
% 1.07/1.30      inference('cnf', [status(esa)], [t71_enumset1])).
% 1.07/1.30  thf('55', plain,
% 1.07/1.30      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 1.07/1.30         (((X11) = (k1_enumset1 @ X8 @ X9 @ X10))
% 1.07/1.30          | ((X11) = (k2_tarski @ X8 @ X10))
% 1.07/1.30          | ((X11) = (k2_tarski @ X9 @ X10))
% 1.07/1.30          | ((X11) = (k2_tarski @ X8 @ X9))
% 1.07/1.30          | ((X11) = (k1_tarski @ X10))
% 1.07/1.30          | ((X11) = (k1_tarski @ X9))
% 1.07/1.30          | ((X11) = (k1_tarski @ X8))
% 1.07/1.30          | ((X11) = (k1_xboole_0))
% 1.07/1.30          | ~ (r1_tarski @ X11 @ (k1_enumset1 @ X8 @ X9 @ X10)))),
% 1.07/1.30      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 1.07/1.30  thf('56', plain,
% 1.07/1.30      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.07/1.30         (~ (r1_tarski @ X3 @ (k2_enumset1 @ X2 @ X2 @ X1 @ X0))
% 1.07/1.30          | ((X3) = (k1_xboole_0))
% 1.07/1.30          | ((X3) = (k1_tarski @ X2))
% 1.07/1.30          | ((X3) = (k1_tarski @ X1))
% 1.07/1.30          | ((X3) = (k1_tarski @ X0))
% 1.07/1.30          | ((X3) = (k2_tarski @ X2 @ X1))
% 1.07/1.30          | ((X3) = (k2_tarski @ X1 @ X0))
% 1.07/1.30          | ((X3) = (k2_tarski @ X2 @ X0))
% 1.07/1.30          | ((X3) = (k1_enumset1 @ X2 @ X1 @ X0)))),
% 1.07/1.30      inference('sup-', [status(thm)], ['54', '55'])).
% 1.07/1.30  thf('57', plain,
% 1.07/1.30      (![X0 : $i, X1 : $i]:
% 1.07/1.30         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 1.07/1.30          | ((X1) = (k1_enumset1 @ X0 @ X0 @ X0))
% 1.07/1.30          | ((X1) = (k2_tarski @ X0 @ X0))
% 1.07/1.30          | ((X1) = (k2_tarski @ X0 @ X0))
% 1.07/1.30          | ((X1) = (k2_tarski @ X0 @ X0))
% 1.07/1.30          | ((X1) = (k1_tarski @ X0))
% 1.07/1.30          | ((X1) = (k1_tarski @ X0))
% 1.07/1.30          | ((X1) = (k1_tarski @ X0))
% 1.07/1.30          | ((X1) = (k1_xboole_0)))),
% 1.07/1.30      inference('sup-', [status(thm)], ['53', '56'])).
% 1.07/1.30  thf('58', plain,
% 1.07/1.30      (![X2 : $i, X3 : $i]:
% 1.07/1.30         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 1.07/1.30      inference('cnf', [status(esa)], [t70_enumset1])).
% 1.07/1.30  thf('59', plain,
% 1.07/1.30      (![X0 : $i, X1 : $i]:
% 1.07/1.30         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 1.07/1.30          | ((X1) = (k2_tarski @ X0 @ X0))
% 1.07/1.30          | ((X1) = (k2_tarski @ X0 @ X0))
% 1.07/1.30          | ((X1) = (k2_tarski @ X0 @ X0))
% 1.07/1.30          | ((X1) = (k2_tarski @ X0 @ X0))
% 1.07/1.30          | ((X1) = (k1_tarski @ X0))
% 1.07/1.30          | ((X1) = (k1_tarski @ X0))
% 1.07/1.30          | ((X1) = (k1_tarski @ X0))
% 1.07/1.30          | ((X1) = (k1_xboole_0)))),
% 1.07/1.30      inference('demod', [status(thm)], ['57', '58'])).
% 1.07/1.30  thf('60', plain,
% 1.07/1.30      (![X0 : $i, X1 : $i]:
% 1.07/1.30         (((X1) = (k1_xboole_0))
% 1.07/1.30          | ((X1) = (k1_tarski @ X0))
% 1.07/1.30          | ((X1) = (k2_tarski @ X0 @ X0))
% 1.07/1.30          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 1.07/1.30      inference('simplify', [status(thm)], ['59'])).
% 1.07/1.30  thf('61', plain,
% 1.07/1.30      ((((k2_relat_1 @ sk_C)
% 1.07/1.30          = (k2_tarski @ (k1_funct_1 @ sk_C @ sk_A) @ 
% 1.07/1.30             (k1_funct_1 @ sk_C @ sk_A)))
% 1.07/1.30        | ((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 1.07/1.30        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.07/1.30      inference('sup-', [status(thm)], ['48', '60'])).
% 1.07/1.30  thf('62', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 1.07/1.30      inference('cnf', [status(esa)], [t69_enumset1])).
% 1.07/1.30  thf('63', plain,
% 1.07/1.30      ((((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 1.07/1.30        | ((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))
% 1.07/1.30        | ((k2_relat_1 @ sk_C) = (k1_xboole_0)))),
% 1.07/1.30      inference('demod', [status(thm)], ['61', '62'])).
% 1.07/1.30  thf('64', plain,
% 1.07/1.30      ((((k2_relat_1 @ sk_C) = (k1_xboole_0))
% 1.07/1.30        | ((k2_relat_1 @ sk_C) = (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A))))),
% 1.07/1.30      inference('simplify', [status(thm)], ['63'])).
% 1.07/1.30  thf('65', plain,
% 1.07/1.30      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C)
% 1.07/1.30         != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf('66', plain,
% 1.07/1.30      ((m1_subset_1 @ sk_C @ 
% 1.07/1.30        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 1.07/1.30      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.30  thf(redefinition_k2_relset_1, axiom,
% 1.07/1.30    (![A:$i,B:$i,C:$i]:
% 1.07/1.30     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.30       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.07/1.30  thf('67', plain,
% 1.07/1.30      (![X28 : $i, X29 : $i, X30 : $i]:
% 1.07/1.30         (((k2_relset_1 @ X29 @ X30 @ X28) = (k2_relat_1 @ X28))
% 1.07/1.30          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.07/1.30      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.07/1.30  thf('68', plain,
% 1.07/1.30      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 1.07/1.30      inference('sup-', [status(thm)], ['66', '67'])).
% 1.07/1.30  thf('69', plain,
% 1.07/1.30      (((k2_relat_1 @ sk_C) != (k1_tarski @ (k1_funct_1 @ sk_C @ sk_A)))),
% 1.07/1.30      inference('demod', [status(thm)], ['65', '68'])).
% 1.07/1.30  thf('70', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 1.07/1.30      inference('simplify_reflect-', [status(thm)], ['64', '69'])).
% 1.07/1.30  thf(dt_o_0_0_xboole_0, axiom, (v1_xboole_0 @ o_0_0_xboole_0)).
% 1.07/1.30  thf('71', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 1.07/1.30      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 1.07/1.30  thf('72', plain, ((v1_xboole_0 @ o_0_0_xboole_0)),
% 1.07/1.30      inference('cnf', [status(esa)], [dt_o_0_0_xboole_0])).
% 1.07/1.30  thf('73', plain,
% 1.07/1.30      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.07/1.30      inference('cnf', [status(esa)], [l13_xboole_0])).
% 1.07/1.30  thf('74', plain, (((o_0_0_xboole_0) = (k1_xboole_0))),
% 1.07/1.30      inference('sup-', [status(thm)], ['72', '73'])).
% 1.07/1.30  thf('75', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.07/1.30      inference('demod', [status(thm)], ['71', '74'])).
% 1.07/1.30  thf('76', plain, ((v1_xboole_0 @ sk_C)),
% 1.07/1.30      inference('demod', [status(thm)], ['27', '70', '75'])).
% 1.07/1.30  thf('77', plain, (((k1_tarski @ sk_A) = (k1_xboole_0))),
% 1.07/1.30      inference('demod', [status(thm)], ['17', '76'])).
% 1.07/1.30  thf(fc2_xboole_0, axiom, (![A:$i]: ( ~( v1_xboole_0 @ ( k1_tarski @ A ) ) ))).
% 1.07/1.30  thf('78', plain, (![X7 : $i]: ~ (v1_xboole_0 @ (k1_tarski @ X7))),
% 1.07/1.30      inference('cnf', [status(esa)], [fc2_xboole_0])).
% 1.07/1.30  thf('79', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 1.07/1.30      inference('sup-', [status(thm)], ['77', '78'])).
% 1.07/1.30  thf('80', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.07/1.30      inference('demod', [status(thm)], ['71', '74'])).
% 1.07/1.30  thf('81', plain, ($false), inference('demod', [status(thm)], ['79', '80'])).
% 1.07/1.30  
% 1.07/1.30  % SZS output end Refutation
% 1.07/1.30  
% 1.15/1.31  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
