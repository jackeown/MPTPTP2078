%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9b2cy9pv3y

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:11 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 221 expanded)
%              Number of leaves         :   43 (  86 expanded)
%              Depth                    :   14
%              Number of atoms          :  764 (2720 expanded)
%              Number of equality atoms :   49 ( 138 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('0',plain,(
    ! [X43: $i] :
      ( ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X43 ) @ ( k2_relat_1 @ X43 ) ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('1',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k7_relset_1 @ X32 @ X33 @ X31 @ X34 )
        = ( k9_relat_1 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k7_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 )
        = ( k9_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    ! [X43: $i] :
      ( ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X43 ) @ ( k2_relat_1 @ X43 ) ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('4',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X25 @ X26 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k7_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('6',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 @ X1 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','7'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['8'])).

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

thf('10',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ( X37
        = ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('17',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('23',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['13','20','23'])).

thf('25',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['10','24'])).

thf('26',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['13','20','23'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('27',plain,(
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

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k2_tarski @ X3 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('29',plain,(
    ! [X0: $i,X3: $i] :
      ( r2_hidden @ X0 @ ( k2_tarski @ X3 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['27','29'])).

thf('31',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['26','30'])).

thf(t117_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
       => ( ( k11_relat_1 @ B @ A )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('32',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ ( k1_relat_1 @ X23 ) )
      | ( ( k11_relat_1 @ X23 @ X22 )
        = ( k1_tarski @ ( k1_funct_1 @ X23 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t117_funct_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( ( k11_relat_1 @ sk_D_1 @ sk_A )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('35',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('37',plain,(
    ! [X19: $i,X20: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('38',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('40',plain,(
    ! [X21: $i] :
      ( ( ( k9_relat_1 @ X21 @ ( k1_relat_1 @ X21 ) )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('41',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['13','20','23'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('42',plain,(
    ! [X17: $i,X18: $i] :
      ( ( ( k11_relat_1 @ X17 @ X18 )
        = ( k9_relat_1 @ X17 @ ( k1_tarski @ X18 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k11_relat_1 @ X0 @ sk_A )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( ( k11_relat_1 @ sk_D_1 @ sk_A )
      = ( k2_relat_1 @ sk_D_1 ) )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['40','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['36','37'])).

thf('46',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['36','37'])).

thf('47',plain,
    ( ( k11_relat_1 @ sk_D_1 @ sk_A )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( k2_relat_1 @ sk_D_1 )
    = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['33','38','39','47'])).

thf('49',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B @ sk_D_1 @ sk_C ) @ ( k2_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['25','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['13','20','23'])).

thf('52',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k7_relset_1 @ X32 @ X33 @ X31 @ X34 )
        = ( k9_relat_1 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_relat_1 @ sk_D_1 ) @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k2_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['49','54'])).

thf('56',plain,
    ( ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['9','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['36','37'])).

thf('59',plain,(
    $false ),
    inference(demod,[status(thm)],['56','57','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9b2cy9pv3y
% 0.11/0.32  % Computer   : n019.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 13:53:52 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.32  % Running portfolio for 600 s
% 0.11/0.32  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.11/0.33  % Number of cores: 8
% 0.11/0.33  % Python version: Python 3.6.8
% 0.11/0.33  % Running in FO mode
% 0.41/0.63  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.63  % Solved by: fo/fo7.sh
% 0.41/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.63  % done 171 iterations in 0.198s
% 0.41/0.63  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.63  % SZS output start Refutation
% 0.41/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.63  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.63  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.41/0.63  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.41/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.63  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.41/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.63  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.41/0.63  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.41/0.63  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.41/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.41/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.63  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 0.41/0.63  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.41/0.63  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.41/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.63  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.41/0.63  thf(t3_funct_2, axiom,
% 0.41/0.63    (![A:$i]:
% 0.41/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.41/0.63       ( ( v1_funct_1 @ A ) & 
% 0.41/0.63         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.41/0.63         ( m1_subset_1 @
% 0.41/0.63           A @ 
% 0.41/0.63           ( k1_zfmisc_1 @
% 0.41/0.63             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.41/0.63  thf('0', plain,
% 0.41/0.63      (![X43 : $i]:
% 0.41/0.63         ((m1_subset_1 @ X43 @ 
% 0.41/0.63           (k1_zfmisc_1 @ 
% 0.41/0.63            (k2_zfmisc_1 @ (k1_relat_1 @ X43) @ (k2_relat_1 @ X43))))
% 0.41/0.63          | ~ (v1_funct_1 @ X43)
% 0.41/0.63          | ~ (v1_relat_1 @ X43))),
% 0.41/0.63      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.41/0.63  thf(redefinition_k7_relset_1, axiom,
% 0.41/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.63       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.41/0.63  thf('1', plain,
% 0.41/0.63      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.41/0.63         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.41/0.63          | ((k7_relset_1 @ X32 @ X33 @ X31 @ X34) = (k9_relat_1 @ X31 @ X34)))),
% 0.41/0.63      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.41/0.63  thf('2', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]:
% 0.41/0.63         (~ (v1_relat_1 @ X0)
% 0.41/0.63          | ~ (v1_funct_1 @ X0)
% 0.41/0.63          | ((k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1)
% 0.41/0.63              = (k9_relat_1 @ X0 @ X1)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['0', '1'])).
% 0.41/0.63  thf('3', plain,
% 0.41/0.63      (![X43 : $i]:
% 0.41/0.63         ((m1_subset_1 @ X43 @ 
% 0.41/0.63           (k1_zfmisc_1 @ 
% 0.41/0.63            (k2_zfmisc_1 @ (k1_relat_1 @ X43) @ (k2_relat_1 @ X43))))
% 0.41/0.63          | ~ (v1_funct_1 @ X43)
% 0.41/0.63          | ~ (v1_relat_1 @ X43))),
% 0.41/0.63      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.41/0.63  thf(dt_k7_relset_1, axiom,
% 0.41/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.63       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.41/0.63  thf('4', plain,
% 0.41/0.63      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.41/0.63         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.41/0.63          | (m1_subset_1 @ (k7_relset_1 @ X25 @ X26 @ X24 @ X27) @ 
% 0.41/0.63             (k1_zfmisc_1 @ X26)))),
% 0.41/0.63      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.41/0.63  thf('5', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]:
% 0.41/0.63         (~ (v1_relat_1 @ X0)
% 0.41/0.63          | ~ (v1_funct_1 @ X0)
% 0.41/0.63          | (m1_subset_1 @ 
% 0.41/0.63             (k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1) @ 
% 0.41/0.63             (k1_zfmisc_1 @ (k2_relat_1 @ X0))))),
% 0.41/0.63      inference('sup-', [status(thm)], ['3', '4'])).
% 0.41/0.63  thf(t3_subset, axiom,
% 0.41/0.63    (![A:$i,B:$i]:
% 0.41/0.63     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.41/0.63  thf('6', plain,
% 0.41/0.63      (![X12 : $i, X13 : $i]:
% 0.41/0.63         ((r1_tarski @ X12 @ X13) | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13)))),
% 0.41/0.63      inference('cnf', [status(esa)], [t3_subset])).
% 0.41/0.63  thf('7', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]:
% 0.41/0.63         (~ (v1_funct_1 @ X0)
% 0.41/0.63          | ~ (v1_relat_1 @ X0)
% 0.41/0.63          | (r1_tarski @ 
% 0.41/0.63             (k7_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0 @ X1) @ 
% 0.41/0.63             (k2_relat_1 @ X0)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['5', '6'])).
% 0.41/0.63  thf('8', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]:
% 0.41/0.63         ((r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1))
% 0.41/0.63          | ~ (v1_funct_1 @ X1)
% 0.41/0.63          | ~ (v1_relat_1 @ X1)
% 0.41/0.63          | ~ (v1_relat_1 @ X1)
% 0.41/0.63          | ~ (v1_funct_1 @ X1))),
% 0.41/0.63      inference('sup+', [status(thm)], ['2', '7'])).
% 0.41/0.63  thf('9', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i]:
% 0.41/0.63         (~ (v1_relat_1 @ X1)
% 0.41/0.63          | ~ (v1_funct_1 @ X1)
% 0.41/0.63          | (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X1)))),
% 0.41/0.63      inference('simplify', [status(thm)], ['8'])).
% 0.41/0.63  thf(t64_funct_2, conjecture,
% 0.41/0.63    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.63     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.41/0.63         ( m1_subset_1 @
% 0.41/0.63           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.41/0.63       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.41/0.63         ( r1_tarski @
% 0.41/0.63           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.41/0.63           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.41/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.63    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.63        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.41/0.63            ( m1_subset_1 @
% 0.41/0.63              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.41/0.63          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.41/0.63            ( r1_tarski @
% 0.41/0.63              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.41/0.63              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.41/0.63    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.41/0.63  thf('10', plain,
% 0.41/0.63      (~ (r1_tarski @ 
% 0.41/0.63          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ sk_C) @ 
% 0.41/0.63          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('11', plain, ((v1_funct_2 @ sk_D_1 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf(d1_funct_2, axiom,
% 0.41/0.63    (![A:$i,B:$i,C:$i]:
% 0.41/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.63       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.41/0.63           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.41/0.63             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.41/0.63         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.41/0.63           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.41/0.63             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.41/0.63  thf(zf_stmt_1, axiom,
% 0.41/0.63    (![C:$i,B:$i,A:$i]:
% 0.41/0.63     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.41/0.63       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.41/0.63  thf('12', plain,
% 0.41/0.63      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.41/0.63         (~ (v1_funct_2 @ X39 @ X37 @ X38)
% 0.41/0.63          | ((X37) = (k1_relset_1 @ X37 @ X38 @ X39))
% 0.41/0.63          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.63  thf('13', plain,
% 0.41/0.63      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.41/0.63        | ((k1_tarski @ sk_A)
% 0.41/0.63            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['11', '12'])).
% 0.41/0.63  thf(zf_stmt_2, axiom,
% 0.41/0.63    (![B:$i,A:$i]:
% 0.41/0.63     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.41/0.63       ( zip_tseitin_0 @ B @ A ) ))).
% 0.41/0.63  thf('14', plain,
% 0.41/0.63      (![X35 : $i, X36 : $i]:
% 0.41/0.63         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.41/0.63  thf('15', plain,
% 0.41/0.63      ((m1_subset_1 @ sk_D_1 @ 
% 0.41/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.41/0.63  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.41/0.63  thf(zf_stmt_5, axiom,
% 0.41/0.63    (![A:$i,B:$i,C:$i]:
% 0.41/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.63       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.41/0.63         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.41/0.63           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.41/0.63             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.41/0.63  thf('16', plain,
% 0.41/0.63      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.41/0.63         (~ (zip_tseitin_0 @ X40 @ X41)
% 0.41/0.63          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 0.41/0.63          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.41/0.63  thf('17', plain,
% 0.41/0.63      (((zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A))
% 0.41/0.63        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['15', '16'])).
% 0.41/0.63  thf('18', plain,
% 0.41/0.63      ((((sk_B) = (k1_xboole_0))
% 0.41/0.63        | (zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.41/0.63      inference('sup-', [status(thm)], ['14', '17'])).
% 0.41/0.63  thf('19', plain, (((sk_B) != (k1_xboole_0))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('20', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_B @ (k1_tarski @ sk_A))),
% 0.41/0.63      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.41/0.63  thf('21', plain,
% 0.41/0.63      ((m1_subset_1 @ sk_D_1 @ 
% 0.41/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf(redefinition_k1_relset_1, axiom,
% 0.41/0.63    (![A:$i,B:$i,C:$i]:
% 0.41/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.63       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.41/0.63  thf('22', plain,
% 0.41/0.63      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.41/0.63         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 0.41/0.63          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.41/0.63      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.41/0.63  thf('23', plain,
% 0.41/0.63      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1)
% 0.41/0.63         = (k1_relat_1 @ sk_D_1))),
% 0.41/0.63      inference('sup-', [status(thm)], ['21', '22'])).
% 0.41/0.63  thf('24', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.41/0.63      inference('demod', [status(thm)], ['13', '20', '23'])).
% 0.41/0.63  thf('25', plain,
% 0.41/0.63      (~ (r1_tarski @ 
% 0.41/0.63          (k7_relset_1 @ (k1_relat_1 @ sk_D_1) @ sk_B @ sk_D_1 @ sk_C) @ 
% 0.41/0.63          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.41/0.63      inference('demod', [status(thm)], ['10', '24'])).
% 0.41/0.63  thf('26', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.41/0.63      inference('demod', [status(thm)], ['13', '20', '23'])).
% 0.41/0.63  thf(t69_enumset1, axiom,
% 0.41/0.63    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.41/0.63  thf('27', plain, (![X6 : $i]: ((k2_tarski @ X6 @ X6) = (k1_tarski @ X6))),
% 0.41/0.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.41/0.63  thf(d2_tarski, axiom,
% 0.41/0.63    (![A:$i,B:$i,C:$i]:
% 0.41/0.63     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.41/0.63       ( ![D:$i]:
% 0.41/0.63         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.41/0.63  thf('28', plain,
% 0.41/0.63      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.41/0.63         (((X1) != (X0))
% 0.41/0.63          | (r2_hidden @ X1 @ X2)
% 0.41/0.63          | ((X2) != (k2_tarski @ X3 @ X0)))),
% 0.41/0.63      inference('cnf', [status(esa)], [d2_tarski])).
% 0.41/0.63  thf('29', plain,
% 0.41/0.63      (![X0 : $i, X3 : $i]: (r2_hidden @ X0 @ (k2_tarski @ X3 @ X0))),
% 0.41/0.63      inference('simplify', [status(thm)], ['28'])).
% 0.41/0.63  thf('30', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.41/0.63      inference('sup+', [status(thm)], ['27', '29'])).
% 0.41/0.63  thf('31', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_1))),
% 0.41/0.63      inference('sup+', [status(thm)], ['26', '30'])).
% 0.41/0.63  thf(t117_funct_1, axiom,
% 0.41/0.63    (![A:$i,B:$i]:
% 0.41/0.63     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.41/0.63       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) =>
% 0.41/0.63         ( ( k11_relat_1 @ B @ A ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.41/0.63  thf('32', plain,
% 0.41/0.63      (![X22 : $i, X23 : $i]:
% 0.41/0.63         (~ (r2_hidden @ X22 @ (k1_relat_1 @ X23))
% 0.41/0.63          | ((k11_relat_1 @ X23 @ X22) = (k1_tarski @ (k1_funct_1 @ X23 @ X22)))
% 0.41/0.63          | ~ (v1_funct_1 @ X23)
% 0.41/0.63          | ~ (v1_relat_1 @ X23))),
% 0.41/0.63      inference('cnf', [status(esa)], [t117_funct_1])).
% 0.41/0.63  thf('33', plain,
% 0.41/0.63      ((~ (v1_relat_1 @ sk_D_1)
% 0.41/0.63        | ~ (v1_funct_1 @ sk_D_1)
% 0.41/0.63        | ((k11_relat_1 @ sk_D_1 @ sk_A)
% 0.41/0.63            = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A))))),
% 0.41/0.63      inference('sup-', [status(thm)], ['31', '32'])).
% 0.41/0.63  thf('34', plain,
% 0.41/0.63      ((m1_subset_1 @ sk_D_1 @ 
% 0.41/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf(cc2_relat_1, axiom,
% 0.41/0.63    (![A:$i]:
% 0.41/0.63     ( ( v1_relat_1 @ A ) =>
% 0.41/0.63       ( ![B:$i]:
% 0.41/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.41/0.63  thf('35', plain,
% 0.41/0.63      (![X15 : $i, X16 : $i]:
% 0.41/0.63         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.41/0.63          | (v1_relat_1 @ X15)
% 0.41/0.63          | ~ (v1_relat_1 @ X16))),
% 0.41/0.63      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.41/0.63  thf('36', plain,
% 0.41/0.63      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.41/0.63        | (v1_relat_1 @ sk_D_1))),
% 0.41/0.63      inference('sup-', [status(thm)], ['34', '35'])).
% 0.41/0.63  thf(fc6_relat_1, axiom,
% 0.41/0.63    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.41/0.63  thf('37', plain,
% 0.41/0.63      (![X19 : $i, X20 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X19 @ X20))),
% 0.41/0.63      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.41/0.63  thf('38', plain, ((v1_relat_1 @ sk_D_1)),
% 0.41/0.63      inference('demod', [status(thm)], ['36', '37'])).
% 0.41/0.63  thf('39', plain, ((v1_funct_1 @ sk_D_1)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf(t146_relat_1, axiom,
% 0.41/0.63    (![A:$i]:
% 0.41/0.63     ( ( v1_relat_1 @ A ) =>
% 0.41/0.63       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.41/0.63  thf('40', plain,
% 0.41/0.63      (![X21 : $i]:
% 0.41/0.63         (((k9_relat_1 @ X21 @ (k1_relat_1 @ X21)) = (k2_relat_1 @ X21))
% 0.41/0.63          | ~ (v1_relat_1 @ X21))),
% 0.41/0.63      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.41/0.63  thf('41', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.41/0.63      inference('demod', [status(thm)], ['13', '20', '23'])).
% 0.41/0.63  thf(d16_relat_1, axiom,
% 0.41/0.63    (![A:$i]:
% 0.41/0.63     ( ( v1_relat_1 @ A ) =>
% 0.41/0.63       ( ![B:$i]:
% 0.41/0.63         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 0.41/0.63  thf('42', plain,
% 0.41/0.63      (![X17 : $i, X18 : $i]:
% 0.41/0.63         (((k11_relat_1 @ X17 @ X18) = (k9_relat_1 @ X17 @ (k1_tarski @ X18)))
% 0.41/0.63          | ~ (v1_relat_1 @ X17))),
% 0.41/0.63      inference('cnf', [status(esa)], [d16_relat_1])).
% 0.41/0.63  thf('43', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         (((k11_relat_1 @ X0 @ sk_A)
% 0.41/0.63            = (k9_relat_1 @ X0 @ (k1_relat_1 @ sk_D_1)))
% 0.41/0.63          | ~ (v1_relat_1 @ X0))),
% 0.41/0.63      inference('sup+', [status(thm)], ['41', '42'])).
% 0.41/0.63  thf('44', plain,
% 0.41/0.63      ((((k11_relat_1 @ sk_D_1 @ sk_A) = (k2_relat_1 @ sk_D_1))
% 0.41/0.63        | ~ (v1_relat_1 @ sk_D_1)
% 0.41/0.63        | ~ (v1_relat_1 @ sk_D_1))),
% 0.41/0.63      inference('sup+', [status(thm)], ['40', '43'])).
% 0.41/0.63  thf('45', plain, ((v1_relat_1 @ sk_D_1)),
% 0.41/0.63      inference('demod', [status(thm)], ['36', '37'])).
% 0.41/0.63  thf('46', plain, ((v1_relat_1 @ sk_D_1)),
% 0.41/0.63      inference('demod', [status(thm)], ['36', '37'])).
% 0.41/0.63  thf('47', plain, (((k11_relat_1 @ sk_D_1 @ sk_A) = (k2_relat_1 @ sk_D_1))),
% 0.41/0.63      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.41/0.63  thf('48', plain,
% 0.41/0.63      (((k2_relat_1 @ sk_D_1) = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.41/0.63      inference('demod', [status(thm)], ['33', '38', '39', '47'])).
% 0.41/0.63  thf('49', plain,
% 0.41/0.63      (~ (r1_tarski @ 
% 0.41/0.63          (k7_relset_1 @ (k1_relat_1 @ sk_D_1) @ sk_B @ sk_D_1 @ sk_C) @ 
% 0.41/0.63          (k2_relat_1 @ sk_D_1))),
% 0.41/0.63      inference('demod', [status(thm)], ['25', '48'])).
% 0.41/0.63  thf('50', plain,
% 0.41/0.63      ((m1_subset_1 @ sk_D_1 @ 
% 0.41/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('51', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.41/0.63      inference('demod', [status(thm)], ['13', '20', '23'])).
% 0.41/0.63  thf('52', plain,
% 0.41/0.63      ((m1_subset_1 @ sk_D_1 @ 
% 0.41/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D_1) @ sk_B)))),
% 0.41/0.63      inference('demod', [status(thm)], ['50', '51'])).
% 0.41/0.63  thf('53', plain,
% 0.41/0.63      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.41/0.63         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.41/0.63          | ((k7_relset_1 @ X32 @ X33 @ X31 @ X34) = (k9_relat_1 @ X31 @ X34)))),
% 0.41/0.63      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.41/0.63  thf('54', plain,
% 0.41/0.63      (![X0 : $i]:
% 0.41/0.63         ((k7_relset_1 @ (k1_relat_1 @ sk_D_1) @ sk_B @ sk_D_1 @ X0)
% 0.41/0.63           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.41/0.63      inference('sup-', [status(thm)], ['52', '53'])).
% 0.41/0.63  thf('55', plain,
% 0.41/0.63      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ (k2_relat_1 @ sk_D_1))),
% 0.41/0.63      inference('demod', [status(thm)], ['49', '54'])).
% 0.41/0.63  thf('56', plain, ((~ (v1_funct_1 @ sk_D_1) | ~ (v1_relat_1 @ sk_D_1))),
% 0.41/0.63      inference('sup-', [status(thm)], ['9', '55'])).
% 0.41/0.63  thf('57', plain, ((v1_funct_1 @ sk_D_1)),
% 0.41/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.63  thf('58', plain, ((v1_relat_1 @ sk_D_1)),
% 0.41/0.63      inference('demod', [status(thm)], ['36', '37'])).
% 0.41/0.63  thf('59', plain, ($false),
% 0.41/0.63      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.41/0.63  
% 0.41/0.63  % SZS output end Refutation
% 0.41/0.63  
% 0.49/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
