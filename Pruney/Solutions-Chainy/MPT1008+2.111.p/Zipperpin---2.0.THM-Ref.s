%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9caK9JpSiL

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:47 EST 2020

% Result     : Theorem 0.45s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 509 expanded)
%              Number of leaves         :   36 ( 166 expanded)
%              Depth                    :   27
%              Number of atoms          : 1078 (7066 expanded)
%              Number of equality atoms :  113 ( 608 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

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
    v1_funct_2 @ sk_C_2 @ ( k1_tarski @ sk_A ) @ sk_B ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_2 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ( ( k1_tarski @ sk_A )
      = ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('3',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('4',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('6',plain,
    ( ( zip_tseitin_1 @ sk_C_2 @ sk_B @ ( k1_tarski @ sk_A ) )
    | ~ ( zip_tseitin_0 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C_2 @ sk_B @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    zip_tseitin_1 @ sk_C_2 @ sk_B @ ( k1_tarski @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k1_relset_1 @ X20 @ X21 @ X19 )
        = ( k1_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf(d1_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ( C = A ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X1 != X0 )
      | ( r2_hidden @ X1 @ X2 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('15',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('16',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['13','15'])).

thf('17',plain,(
    r2_hidden @ sk_A @ ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['13','15'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('18',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

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

thf('19',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X12 @ X13 ) @ X12 )
      | ( r2_hidden @ ( sk_D @ X12 @ X13 ) @ ( k1_relat_1 @ X13 ) )
      | ( X12
        = ( k2_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('20',plain,
    ( ( k1_tarski @ sk_A )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['2','9','12'])).

thf('21',plain,(
    ! [X0: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ X2 )
      | ( X3 = X0 )
      | ( X2
       != ( k1_tarski @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d1_tarski])).

thf('22',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ X0 )
      | ( ( sk_D @ X0 @ sk_C_2 )
        = sk_A ) ) ),
    inference('sup-',[status(thm)],['19','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('26',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('28',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('29',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ X0 )
      | ( ( sk_D @ X0 @ sk_C_2 )
        = sk_A ) ) ),
    inference(demod,[status(thm)],['24','29','30'])).

thf('32',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ ( k1_tarski @ X0 ) @ sk_C_2 )
        = sk_A )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_C_2 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( ( sk_D @ ( k2_tarski @ X0 @ X0 ) @ sk_C_2 )
        = sk_A )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ sk_C_2 )
        = X0 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup+',[status(thm)],['18','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( r2_hidden @ ( sk_C_1 @ X0 @ sk_C_2 ) @ X0 )
      | ( ( sk_D @ X0 @ sk_C_2 )
        = sk_A ) ) ),
    inference(demod,[status(thm)],['24','29','30'])).

thf('36',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X12 @ X13 ) @ X12 )
      | ( ( sk_C_1 @ X12 @ X13 )
       != ( k1_funct_1 @ X13 @ X14 ) )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X13 ) )
      | ( X12
        = ( k2_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ X0 @ sk_C_2 )
        = sk_A )
      | ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_C_1 @ X0 @ sk_C_2 )
       != ( k1_funct_1 @ sk_C_2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['27','28'])).

thf('39',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_D @ X0 @ sk_C_2 )
        = sk_A )
      | ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_C_1 @ X0 @ sk_C_2 )
       != ( k1_funct_1 @ sk_C_2 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( sk_C_1 @ X0 @ sk_C_2 )
       != ( k1_funct_1 @ sk_C_2 @ X1 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( X0
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( ( sk_D @ X0 @ sk_C_2 )
        = sk_A ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0
       != ( k1_funct_1 @ sk_C_2 @ X1 ) )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( ( sk_D @ ( k2_tarski @ X0 @ X0 ) @ sk_C_2 )
        = sk_A )
      | ( ( sk_D @ ( k1_tarski @ X0 ) @ sk_C_2 )
        = sk_A )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['34','41'])).

thf('43',plain,(
    ! [X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ X1 ) ) @ sk_C_2 )
        = sk_A )
      | ( ( sk_D @ ( k2_tarski @ ( k1_funct_1 @ sk_C_2 @ X1 ) @ ( k1_funct_1 @ sk_C_2 @ X1 ) ) @ sk_C_2 )
        = sk_A )
      | ( ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ X1 ) )
        = ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X5: $i] :
      ( ( k2_tarski @ X5 @ X5 )
      = ( k1_tarski @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('45',plain,(
    ! [X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ X1 ) ) @ sk_C_2 )
        = sk_A )
      | ( ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ X1 ) ) @ sk_C_2 )
        = sk_A )
      | ( ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ X1 ) )
        = ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X1: $i] :
      ( ( ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ X1 ) )
        = ( k2_relat_1 @ sk_C_2 ) )
      | ( ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ X1 ) ) @ sk_C_2 )
        = sk_A )
      | ~ ( r2_hidden @ X1 @ ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ( ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) @ sk_C_2 )
      = sk_A )
    | ( ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) )
      = ( k2_relat_1 @ sk_C_2 ) ) ),
    inference('sup-',[status(thm)],['17','46'])).

thf('48',plain,(
    ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_2 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('50',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k2_relset_1 @ X23 @ X24 @ X22 )
        = ( k2_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('51',plain,
    ( ( k2_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,
    ( ( sk_D @ ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) @ sk_C_2 )
    = sk_A ),
    inference('simplify_reflect-',[status(thm)],['47','52'])).

thf('54',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X12 @ X13 ) @ X12 )
      | ( ( sk_C_1 @ X12 @ X13 )
        = ( k1_funct_1 @ X13 @ ( sk_D @ X12 @ X13 ) ) )
      | ( X12
        = ( k2_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('55',plain,(
    ! [X0: $i,X3: $i] :
      ( ( X3 = X0 )
      | ~ ( r2_hidden @ X3 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ( ( k1_tarski @ X0 )
        = ( k2_relat_1 @ X1 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ X1 )
        = ( k1_funct_1 @ X1 @ ( sk_D @ ( k1_tarski @ X0 ) @ X1 ) ) )
      | ( ( sk_C_1 @ ( k1_tarski @ X0 ) @ X1 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( ( sk_C_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) @ sk_C_2 )
      = ( k1_funct_1 @ sk_C_2 @ sk_A ) )
    | ( ( sk_C_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) @ sk_C_2 )
      = ( k1_funct_1 @ sk_C_2 @ sk_A ) )
    | ( ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) )
      = ( k2_relat_1 @ sk_C_2 ) )
    | ~ ( v1_funct_1 @ sk_C_2 )
    | ~ ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup+',[status(thm)],['53','56'])).

thf('58',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['27','28'])).

thf('60',plain,
    ( ( ( sk_C_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) @ sk_C_2 )
      = ( k1_funct_1 @ sk_C_2 @ sk_A ) )
    | ( ( sk_C_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) @ sk_C_2 )
      = ( k1_funct_1 @ sk_C_2 @ sk_A ) )
    | ( ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) )
      = ( k2_relat_1 @ sk_C_2 ) ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf('61',plain,
    ( ( ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) )
      = ( k2_relat_1 @ sk_C_2 ) )
    | ( ( sk_C_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) @ sk_C_2 )
      = ( k1_funct_1 @ sk_C_2 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('63',plain,
    ( ( sk_C_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) @ sk_C_2 )
    = ( k1_funct_1 @ sk_C_2 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ ( sk_C_1 @ X12 @ X13 ) @ X12 )
      | ( ( sk_C_1 @ X12 @ X13 )
       != ( k1_funct_1 @ X13 @ X14 ) )
      | ~ ( r2_hidden @ X14 @ ( k1_relat_1 @ X13 ) )
      | ( X12
        = ( k2_relat_1 @ X13 ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( k1_funct_1 @ sk_C_2 @ sk_A ) @ ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_C_2 )
      | ~ ( v1_funct_1 @ sk_C_2 )
      | ( ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) )
        = ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( sk_C_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) @ sk_C_2 )
       != ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference(simplify,[status(thm)],['14'])).

thf('67',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['27','28'])).

thf('68',plain,(
    v1_funct_1 @ sk_C_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( sk_C_1 @ ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) @ sk_C_2 )
    = ( k1_funct_1 @ sk_C_2 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['61','62'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) )
        = ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( k1_funct_1 @ sk_C_2 @ sk_A )
       != ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['65','66','67','68','69'])).

thf('71',plain,(
    ( k2_relat_1 @ sk_C_2 )
 != ( k1_tarski @ ( k1_funct_1 @ sk_C_2 @ sk_A ) ) ),
    inference(demod,[status(thm)],['48','51'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( ( k1_funct_1 @ sk_C_2 @ sk_A )
       != ( k1_funct_1 @ sk_C_2 @ X0 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) )
      | ( X0 = sk_A ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('74',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    $false ),
    inference('sup-',[status(thm)],['16','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9caK9JpSiL
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:25:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.45/0.63  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.45/0.63  % Solved by: fo/fo7.sh
% 0.45/0.63  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.45/0.63  % done 153 iterations in 0.204s
% 0.45/0.63  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.45/0.63  % SZS output start Refutation
% 0.45/0.63  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.45/0.63  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.45/0.63  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.45/0.63  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.45/0.63  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.45/0.63  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.45/0.63  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.45/0.63  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.45/0.63  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.45/0.63  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.45/0.63  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.45/0.63  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.45/0.63  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.45/0.63  thf(sk_B_type, type, sk_B: $i).
% 0.45/0.63  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.45/0.63  thf(sk_A_type, type, sk_A: $i).
% 0.45/0.63  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.45/0.63  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.45/0.63  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.45/0.63  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.45/0.63  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.45/0.63  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.45/0.63  thf(t62_funct_2, conjecture,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.45/0.63         ( m1_subset_1 @
% 0.45/0.63           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.45/0.63       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.45/0.63         ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.45/0.63           ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.45/0.63  thf(zf_stmt_0, negated_conjecture,
% 0.45/0.63    (~( ![A:$i,B:$i,C:$i]:
% 0.45/0.63        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ ( k1_tarski @ A ) @ B ) & 
% 0.45/0.63            ( m1_subset_1 @
% 0.45/0.63              C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.45/0.63          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.45/0.63            ( ( k2_relset_1 @ ( k1_tarski @ A ) @ B @ C ) =
% 0.45/0.63              ( k1_tarski @ ( k1_funct_1 @ C @ A ) ) ) ) ) )),
% 0.45/0.63    inference('cnf.neg', [status(esa)], [t62_funct_2])).
% 0.45/0.63  thf('0', plain, ((v1_funct_2 @ sk_C_2 @ (k1_tarski @ sk_A) @ sk_B)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(d1_funct_2, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.63       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.63           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.45/0.63             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.45/0.63         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.63           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.45/0.63             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.45/0.63  thf(zf_stmt_1, axiom,
% 0.45/0.63    (![C:$i,B:$i,A:$i]:
% 0.45/0.63     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.45/0.63       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.45/0.63  thf('1', plain,
% 0.45/0.63      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.45/0.63         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 0.45/0.63          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 0.45/0.63          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.45/0.63  thf('2', plain,
% 0.45/0.63      ((~ (zip_tseitin_1 @ sk_C_2 @ sk_B @ (k1_tarski @ sk_A))
% 0.45/0.63        | ((k1_tarski @ sk_A)
% 0.45/0.63            = (k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_2)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['0', '1'])).
% 0.45/0.63  thf(zf_stmt_2, axiom,
% 0.45/0.63    (![B:$i,A:$i]:
% 0.45/0.63     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.45/0.63       ( zip_tseitin_0 @ B @ A ) ))).
% 0.45/0.63  thf('3', plain,
% 0.45/0.63      (![X25 : $i, X26 : $i]:
% 0.45/0.63         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.45/0.63  thf('4', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_C_2 @ 
% 0.45/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.45/0.63  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.45/0.63  thf(zf_stmt_5, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.63       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.45/0.63         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.45/0.63           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.45/0.63             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.45/0.63  thf('5', plain,
% 0.45/0.63      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.45/0.63         (~ (zip_tseitin_0 @ X30 @ X31)
% 0.45/0.63          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 0.45/0.63          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.45/0.63  thf('6', plain,
% 0.45/0.63      (((zip_tseitin_1 @ sk_C_2 @ sk_B @ (k1_tarski @ sk_A))
% 0.45/0.63        | ~ (zip_tseitin_0 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['4', '5'])).
% 0.45/0.63  thf('7', plain,
% 0.45/0.63      ((((sk_B) = (k1_xboole_0))
% 0.45/0.63        | (zip_tseitin_1 @ sk_C_2 @ sk_B @ (k1_tarski @ sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['3', '6'])).
% 0.45/0.63  thf('8', plain, (((sk_B) != (k1_xboole_0))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('9', plain, ((zip_tseitin_1 @ sk_C_2 @ sk_B @ (k1_tarski @ sk_A))),
% 0.45/0.63      inference('simplify_reflect-', [status(thm)], ['7', '8'])).
% 0.45/0.63  thf('10', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_C_2 @ 
% 0.45/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(redefinition_k1_relset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.63       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.45/0.63  thf('11', plain,
% 0.45/0.63      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.45/0.63         (((k1_relset_1 @ X20 @ X21 @ X19) = (k1_relat_1 @ X19))
% 0.45/0.63          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.45/0.63      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.45/0.63  thf('12', plain,
% 0.45/0.63      (((k1_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_2)
% 0.45/0.63         = (k1_relat_1 @ sk_C_2))),
% 0.45/0.63      inference('sup-', [status(thm)], ['10', '11'])).
% 0.45/0.63  thf('13', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))),
% 0.45/0.63      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.45/0.63  thf(d1_tarski, axiom,
% 0.45/0.63    (![A:$i,B:$i]:
% 0.45/0.63     ( ( ( B ) = ( k1_tarski @ A ) ) <=>
% 0.45/0.63       ( ![C:$i]: ( ( r2_hidden @ C @ B ) <=> ( ( C ) = ( A ) ) ) ) ))).
% 0.45/0.63  thf('14', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.45/0.63         (((X1) != (X0)) | (r2_hidden @ X1 @ X2) | ((X2) != (k1_tarski @ X0)))),
% 0.45/0.63      inference('cnf', [status(esa)], [d1_tarski])).
% 0.45/0.63  thf('15', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.45/0.63      inference('simplify', [status(thm)], ['14'])).
% 0.45/0.63  thf('16', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_2))),
% 0.45/0.63      inference('sup+', [status(thm)], ['13', '15'])).
% 0.45/0.63  thf('17', plain, ((r2_hidden @ sk_A @ (k1_relat_1 @ sk_C_2))),
% 0.45/0.63      inference('sup+', [status(thm)], ['13', '15'])).
% 0.45/0.63  thf(t69_enumset1, axiom,
% 0.45/0.63    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.45/0.63  thf('18', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.45/0.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.63  thf(d5_funct_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.45/0.63           ( ![C:$i]:
% 0.45/0.63             ( ( r2_hidden @ C @ B ) <=>
% 0.45/0.63               ( ?[D:$i]:
% 0.45/0.63                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.45/0.63                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.45/0.63  thf('19', plain,
% 0.45/0.63      (![X12 : $i, X13 : $i]:
% 0.45/0.63         ((r2_hidden @ (sk_C_1 @ X12 @ X13) @ X12)
% 0.45/0.63          | (r2_hidden @ (sk_D @ X12 @ X13) @ (k1_relat_1 @ X13))
% 0.45/0.63          | ((X12) = (k2_relat_1 @ X13))
% 0.45/0.63          | ~ (v1_funct_1 @ X13)
% 0.45/0.63          | ~ (v1_relat_1 @ X13))),
% 0.45/0.63      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.45/0.63  thf('20', plain, (((k1_tarski @ sk_A) = (k1_relat_1 @ sk_C_2))),
% 0.45/0.63      inference('demod', [status(thm)], ['2', '9', '12'])).
% 0.45/0.63  thf('21', plain,
% 0.45/0.63      (![X0 : $i, X2 : $i, X3 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X3 @ X2) | ((X3) = (X0)) | ((X2) != (k1_tarski @ X0)))),
% 0.45/0.63      inference('cnf', [status(esa)], [d1_tarski])).
% 0.45/0.63  thf('22', plain,
% 0.45/0.63      (![X0 : $i, X3 : $i]:
% 0.45/0.63         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.45/0.63      inference('simplify', [status(thm)], ['21'])).
% 0.45/0.63  thf('23', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2)) | ((X0) = (sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['20', '22'])).
% 0.45/0.63  thf('24', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ sk_C_2)
% 0.45/0.63          | ~ (v1_funct_1 @ sk_C_2)
% 0.45/0.63          | ((X0) = (k2_relat_1 @ sk_C_2))
% 0.45/0.63          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ X0)
% 0.45/0.63          | ((sk_D @ X0 @ sk_C_2) = (sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['19', '23'])).
% 0.45/0.63  thf('25', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_C_2 @ 
% 0.45/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(cc2_relat_1, axiom,
% 0.45/0.63    (![A:$i]:
% 0.45/0.63     ( ( v1_relat_1 @ A ) =>
% 0.45/0.63       ( ![B:$i]:
% 0.45/0.63         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.45/0.63  thf('26', plain,
% 0.45/0.63      (![X8 : $i, X9 : $i]:
% 0.45/0.63         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.45/0.63          | (v1_relat_1 @ X8)
% 0.45/0.63          | ~ (v1_relat_1 @ X9))),
% 0.45/0.63      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.45/0.63  thf('27', plain,
% 0.45/0.63      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.45/0.63        | (v1_relat_1 @ sk_C_2))),
% 0.45/0.63      inference('sup-', [status(thm)], ['25', '26'])).
% 0.45/0.63  thf(fc6_relat_1, axiom,
% 0.45/0.63    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.45/0.63  thf('28', plain,
% 0.45/0.63      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.45/0.63      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.45/0.63  thf('29', plain, ((v1_relat_1 @ sk_C_2)),
% 0.45/0.63      inference('demod', [status(thm)], ['27', '28'])).
% 0.45/0.63  thf('30', plain, ((v1_funct_1 @ sk_C_2)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('31', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (((X0) = (k2_relat_1 @ sk_C_2))
% 0.45/0.63          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ X0)
% 0.45/0.63          | ((sk_D @ X0 @ sk_C_2) = (sk_A)))),
% 0.45/0.63      inference('demod', [status(thm)], ['24', '29', '30'])).
% 0.45/0.63  thf('32', plain,
% 0.45/0.63      (![X0 : $i, X3 : $i]:
% 0.45/0.63         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.45/0.63      inference('simplify', [status(thm)], ['21'])).
% 0.45/0.63  thf('33', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (((sk_D @ (k1_tarski @ X0) @ sk_C_2) = (sk_A))
% 0.45/0.63          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_C_2))
% 0.45/0.63          | ((sk_C_1 @ (k1_tarski @ X0) @ sk_C_2) = (X0)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['31', '32'])).
% 0.45/0.63  thf('34', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (((sk_D @ (k2_tarski @ X0 @ X0) @ sk_C_2) = (sk_A))
% 0.45/0.63          | ((sk_C_1 @ (k1_tarski @ X0) @ sk_C_2) = (X0))
% 0.45/0.63          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_C_2)))),
% 0.45/0.63      inference('sup+', [status(thm)], ['18', '33'])).
% 0.45/0.63  thf('35', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (((X0) = (k2_relat_1 @ sk_C_2))
% 0.45/0.63          | (r2_hidden @ (sk_C_1 @ X0 @ sk_C_2) @ X0)
% 0.45/0.63          | ((sk_D @ X0 @ sk_C_2) = (sk_A)))),
% 0.45/0.63      inference('demod', [status(thm)], ['24', '29', '30'])).
% 0.45/0.63  thf('36', plain,
% 0.45/0.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.63         (~ (r2_hidden @ (sk_C_1 @ X12 @ X13) @ X12)
% 0.45/0.63          | ((sk_C_1 @ X12 @ X13) != (k1_funct_1 @ X13 @ X14))
% 0.45/0.63          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X13))
% 0.45/0.63          | ((X12) = (k2_relat_1 @ X13))
% 0.45/0.63          | ~ (v1_funct_1 @ X13)
% 0.45/0.63          | ~ (v1_relat_1 @ X13))),
% 0.45/0.63      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.45/0.63  thf('37', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (((sk_D @ X0 @ sk_C_2) = (sk_A))
% 0.45/0.63          | ((X0) = (k2_relat_1 @ sk_C_2))
% 0.45/0.63          | ~ (v1_relat_1 @ sk_C_2)
% 0.45/0.63          | ~ (v1_funct_1 @ sk_C_2)
% 0.45/0.63          | ((X0) = (k2_relat_1 @ sk_C_2))
% 0.45/0.63          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_C_2))
% 0.45/0.63          | ((sk_C_1 @ X0 @ sk_C_2) != (k1_funct_1 @ sk_C_2 @ X1)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['35', '36'])).
% 0.45/0.63  thf('38', plain, ((v1_relat_1 @ sk_C_2)),
% 0.45/0.63      inference('demod', [status(thm)], ['27', '28'])).
% 0.45/0.63  thf('39', plain, ((v1_funct_1 @ sk_C_2)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('40', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (((sk_D @ X0 @ sk_C_2) = (sk_A))
% 0.45/0.63          | ((X0) = (k2_relat_1 @ sk_C_2))
% 0.45/0.63          | ((X0) = (k2_relat_1 @ sk_C_2))
% 0.45/0.63          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_C_2))
% 0.45/0.63          | ((sk_C_1 @ X0 @ sk_C_2) != (k1_funct_1 @ sk_C_2 @ X1)))),
% 0.45/0.63      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.45/0.63  thf('41', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (((sk_C_1 @ X0 @ sk_C_2) != (k1_funct_1 @ sk_C_2 @ X1))
% 0.45/0.63          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_C_2))
% 0.45/0.63          | ((X0) = (k2_relat_1 @ sk_C_2))
% 0.45/0.63          | ((sk_D @ X0 @ sk_C_2) = (sk_A)))),
% 0.45/0.63      inference('simplify', [status(thm)], ['40'])).
% 0.45/0.63  thf('42', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (((X0) != (k1_funct_1 @ sk_C_2 @ X1))
% 0.45/0.63          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_C_2))
% 0.45/0.63          | ((sk_D @ (k2_tarski @ X0 @ X0) @ sk_C_2) = (sk_A))
% 0.45/0.63          | ((sk_D @ (k1_tarski @ X0) @ sk_C_2) = (sk_A))
% 0.45/0.63          | ((k1_tarski @ X0) = (k2_relat_1 @ sk_C_2))
% 0.45/0.63          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_C_2)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['34', '41'])).
% 0.45/0.63  thf('43', plain,
% 0.45/0.63      (![X1 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_C_2))
% 0.45/0.63          | ((sk_D @ (k1_tarski @ (k1_funct_1 @ sk_C_2 @ X1)) @ sk_C_2)
% 0.45/0.63              = (sk_A))
% 0.45/0.63          | ((sk_D @ 
% 0.45/0.63              (k2_tarski @ (k1_funct_1 @ sk_C_2 @ X1) @ 
% 0.45/0.63               (k1_funct_1 @ sk_C_2 @ X1)) @ 
% 0.45/0.63              sk_C_2) = (sk_A))
% 0.45/0.63          | ((k1_tarski @ (k1_funct_1 @ sk_C_2 @ X1)) = (k2_relat_1 @ sk_C_2)))),
% 0.45/0.63      inference('simplify', [status(thm)], ['42'])).
% 0.45/0.63  thf('44', plain, (![X5 : $i]: ((k2_tarski @ X5 @ X5) = (k1_tarski @ X5))),
% 0.45/0.63      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.45/0.63  thf('45', plain,
% 0.45/0.63      (![X1 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_C_2))
% 0.45/0.63          | ((sk_D @ (k1_tarski @ (k1_funct_1 @ sk_C_2 @ X1)) @ sk_C_2)
% 0.45/0.63              = (sk_A))
% 0.45/0.63          | ((sk_D @ (k1_tarski @ (k1_funct_1 @ sk_C_2 @ X1)) @ sk_C_2)
% 0.45/0.63              = (sk_A))
% 0.45/0.63          | ((k1_tarski @ (k1_funct_1 @ sk_C_2 @ X1)) = (k2_relat_1 @ sk_C_2)))),
% 0.45/0.63      inference('demod', [status(thm)], ['43', '44'])).
% 0.45/0.63  thf('46', plain,
% 0.45/0.63      (![X1 : $i]:
% 0.45/0.63         (((k1_tarski @ (k1_funct_1 @ sk_C_2 @ X1)) = (k2_relat_1 @ sk_C_2))
% 0.45/0.63          | ((sk_D @ (k1_tarski @ (k1_funct_1 @ sk_C_2 @ X1)) @ sk_C_2)
% 0.45/0.63              = (sk_A))
% 0.45/0.63          | ~ (r2_hidden @ X1 @ (k1_relat_1 @ sk_C_2)))),
% 0.45/0.63      inference('simplify', [status(thm)], ['45'])).
% 0.45/0.63  thf('47', plain,
% 0.45/0.63      ((((sk_D @ (k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)) @ sk_C_2) = (sk_A))
% 0.45/0.63        | ((k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)) = (k2_relat_1 @ sk_C_2)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['17', '46'])).
% 0.45/0.63  thf('48', plain,
% 0.45/0.63      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_2)
% 0.45/0.63         != (k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('49', plain,
% 0.45/0.63      ((m1_subset_1 @ sk_C_2 @ 
% 0.45/0.63        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf(redefinition_k2_relset_1, axiom,
% 0.45/0.63    (![A:$i,B:$i,C:$i]:
% 0.45/0.63     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.45/0.63       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.45/0.63  thf('50', plain,
% 0.45/0.63      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.45/0.63         (((k2_relset_1 @ X23 @ X24 @ X22) = (k2_relat_1 @ X22))
% 0.45/0.63          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.45/0.63      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.45/0.63  thf('51', plain,
% 0.45/0.63      (((k2_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_C_2)
% 0.45/0.63         = (k2_relat_1 @ sk_C_2))),
% 0.45/0.63      inference('sup-', [status(thm)], ['49', '50'])).
% 0.45/0.63  thf('52', plain,
% 0.45/0.63      (((k2_relat_1 @ sk_C_2) != (k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)))),
% 0.45/0.63      inference('demod', [status(thm)], ['48', '51'])).
% 0.45/0.63  thf('53', plain,
% 0.45/0.63      (((sk_D @ (k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)) @ sk_C_2) = (sk_A))),
% 0.45/0.63      inference('simplify_reflect-', [status(thm)], ['47', '52'])).
% 0.45/0.63  thf('54', plain,
% 0.45/0.63      (![X12 : $i, X13 : $i]:
% 0.45/0.63         ((r2_hidden @ (sk_C_1 @ X12 @ X13) @ X12)
% 0.45/0.63          | ((sk_C_1 @ X12 @ X13) = (k1_funct_1 @ X13 @ (sk_D @ X12 @ X13)))
% 0.45/0.63          | ((X12) = (k2_relat_1 @ X13))
% 0.45/0.63          | ~ (v1_funct_1 @ X13)
% 0.45/0.63          | ~ (v1_relat_1 @ X13))),
% 0.45/0.63      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.45/0.63  thf('55', plain,
% 0.45/0.63      (![X0 : $i, X3 : $i]:
% 0.45/0.63         (((X3) = (X0)) | ~ (r2_hidden @ X3 @ (k1_tarski @ X0)))),
% 0.45/0.63      inference('simplify', [status(thm)], ['21'])).
% 0.45/0.63  thf('56', plain,
% 0.45/0.63      (![X0 : $i, X1 : $i]:
% 0.45/0.63         (~ (v1_relat_1 @ X1)
% 0.45/0.63          | ~ (v1_funct_1 @ X1)
% 0.45/0.63          | ((k1_tarski @ X0) = (k2_relat_1 @ X1))
% 0.45/0.63          | ((sk_C_1 @ (k1_tarski @ X0) @ X1)
% 0.45/0.63              = (k1_funct_1 @ X1 @ (sk_D @ (k1_tarski @ X0) @ X1)))
% 0.45/0.63          | ((sk_C_1 @ (k1_tarski @ X0) @ X1) = (X0)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['54', '55'])).
% 0.45/0.63  thf('57', plain,
% 0.45/0.63      ((((sk_C_1 @ (k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)) @ sk_C_2)
% 0.45/0.63          = (k1_funct_1 @ sk_C_2 @ sk_A))
% 0.45/0.63        | ((sk_C_1 @ (k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)) @ sk_C_2)
% 0.45/0.63            = (k1_funct_1 @ sk_C_2 @ sk_A))
% 0.45/0.63        | ((k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)) = (k2_relat_1 @ sk_C_2))
% 0.45/0.63        | ~ (v1_funct_1 @ sk_C_2)
% 0.45/0.63        | ~ (v1_relat_1 @ sk_C_2))),
% 0.45/0.63      inference('sup+', [status(thm)], ['53', '56'])).
% 0.45/0.63  thf('58', plain, ((v1_funct_1 @ sk_C_2)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('59', plain, ((v1_relat_1 @ sk_C_2)),
% 0.45/0.63      inference('demod', [status(thm)], ['27', '28'])).
% 0.45/0.63  thf('60', plain,
% 0.45/0.63      ((((sk_C_1 @ (k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)) @ sk_C_2)
% 0.45/0.63          = (k1_funct_1 @ sk_C_2 @ sk_A))
% 0.45/0.63        | ((sk_C_1 @ (k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)) @ sk_C_2)
% 0.45/0.63            = (k1_funct_1 @ sk_C_2 @ sk_A))
% 0.45/0.63        | ((k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)) = (k2_relat_1 @ sk_C_2)))),
% 0.45/0.63      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.45/0.63  thf('61', plain,
% 0.45/0.63      ((((k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)) = (k2_relat_1 @ sk_C_2))
% 0.45/0.63        | ((sk_C_1 @ (k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)) @ sk_C_2)
% 0.45/0.63            = (k1_funct_1 @ sk_C_2 @ sk_A)))),
% 0.45/0.63      inference('simplify', [status(thm)], ['60'])).
% 0.45/0.63  thf('62', plain,
% 0.45/0.63      (((k2_relat_1 @ sk_C_2) != (k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)))),
% 0.45/0.63      inference('demod', [status(thm)], ['48', '51'])).
% 0.45/0.63  thf('63', plain,
% 0.45/0.63      (((sk_C_1 @ (k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)) @ sk_C_2)
% 0.45/0.63         = (k1_funct_1 @ sk_C_2 @ sk_A))),
% 0.45/0.63      inference('simplify_reflect-', [status(thm)], ['61', '62'])).
% 0.45/0.63  thf('64', plain,
% 0.45/0.63      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.45/0.63         (~ (r2_hidden @ (sk_C_1 @ X12 @ X13) @ X12)
% 0.45/0.63          | ((sk_C_1 @ X12 @ X13) != (k1_funct_1 @ X13 @ X14))
% 0.45/0.63          | ~ (r2_hidden @ X14 @ (k1_relat_1 @ X13))
% 0.45/0.63          | ((X12) = (k2_relat_1 @ X13))
% 0.45/0.63          | ~ (v1_funct_1 @ X13)
% 0.45/0.63          | ~ (v1_relat_1 @ X13))),
% 0.45/0.63      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.45/0.63  thf('65', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (r2_hidden @ (k1_funct_1 @ sk_C_2 @ sk_A) @ 
% 0.45/0.63             (k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)))
% 0.45/0.63          | ~ (v1_relat_1 @ sk_C_2)
% 0.45/0.63          | ~ (v1_funct_1 @ sk_C_2)
% 0.45/0.63          | ((k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)) = (k2_relat_1 @ sk_C_2))
% 0.45/0.63          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))
% 0.45/0.63          | ((sk_C_1 @ (k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)) @ sk_C_2)
% 0.45/0.63              != (k1_funct_1 @ sk_C_2 @ X0)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['63', '64'])).
% 0.45/0.63  thf('66', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.45/0.63      inference('simplify', [status(thm)], ['14'])).
% 0.45/0.63  thf('67', plain, ((v1_relat_1 @ sk_C_2)),
% 0.45/0.63      inference('demod', [status(thm)], ['27', '28'])).
% 0.45/0.63  thf('68', plain, ((v1_funct_1 @ sk_C_2)),
% 0.45/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.63  thf('69', plain,
% 0.45/0.63      (((sk_C_1 @ (k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)) @ sk_C_2)
% 0.45/0.63         = (k1_funct_1 @ sk_C_2 @ sk_A))),
% 0.45/0.63      inference('simplify_reflect-', [status(thm)], ['61', '62'])).
% 0.45/0.63  thf('70', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (((k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)) = (k2_relat_1 @ sk_C_2))
% 0.45/0.63          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))
% 0.45/0.63          | ((k1_funct_1 @ sk_C_2 @ sk_A) != (k1_funct_1 @ sk_C_2 @ X0)))),
% 0.45/0.63      inference('demod', [status(thm)], ['65', '66', '67', '68', '69'])).
% 0.45/0.63  thf('71', plain,
% 0.45/0.63      (((k2_relat_1 @ sk_C_2) != (k1_tarski @ (k1_funct_1 @ sk_C_2 @ sk_A)))),
% 0.45/0.63      inference('demod', [status(thm)], ['48', '51'])).
% 0.45/0.63  thf('72', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))
% 0.45/0.63          | ((k1_funct_1 @ sk_C_2 @ sk_A) != (k1_funct_1 @ sk_C_2 @ X0)))),
% 0.45/0.63      inference('simplify_reflect-', [status(thm)], ['70', '71'])).
% 0.45/0.63  thf('73', plain,
% 0.45/0.63      (![X0 : $i]:
% 0.45/0.63         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2)) | ((X0) = (sk_A)))),
% 0.45/0.63      inference('sup-', [status(thm)], ['20', '22'])).
% 0.45/0.63  thf('74', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2))),
% 0.45/0.63      inference('clc', [status(thm)], ['72', '73'])).
% 0.45/0.63  thf('75', plain, ($false), inference('sup-', [status(thm)], ['16', '74'])).
% 0.45/0.63  
% 0.45/0.63  % SZS output end Refutation
% 0.45/0.63  
% 0.46/0.64  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
