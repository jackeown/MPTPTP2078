%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.edFgu91KZf

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:50 EST 2020

% Result     : Theorem 0.37s
% Output     : Refutation 0.37s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 219 expanded)
%              Number of leaves         :   46 (  87 expanded)
%              Depth                    :   21
%              Number of atoms          :  920 (2824 expanded)
%              Number of equality atoms :   67 ( 193 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(t65_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) )
          = A ) ) ) )).

thf('0',plain,(
    ! [X15: $i] :
      ( ~ ( v2_funct_1 @ X15 )
      | ( ( k2_funct_1 @ ( k2_funct_1 @ X15 ) )
        = X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t65_funct_1])).

thf(t32_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ D )
          & ( r2_hidden @ C @ A ) )
       => ( ( B = k1_xboole_0 )
          | ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) )
            = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( v2_funct_1 @ D )
            & ( r2_hidden @ C @ A ) )
         => ( ( B = k1_xboole_0 )
            | ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) )
              = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t32_funct_2])).

thf('1',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('2',plain,(
    ! [X8: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(fc6_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) )
        & ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('3',plain,(
    ! [X9: $i] :
      ( ( v2_funct_1 @ ( k2_funct_1 @ X9 ) )
      | ~ ( v2_funct_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_funct_1])).

thf('4',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('5',plain,(
    ! [X8: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('6',plain,(
    ! [X12: $i] :
      ( ~ ( v2_funct_1 @ X12 )
      | ( ( k2_relat_1 @ X12 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X3: $i] :
      ( ( ( k9_relat_1 @ X3 @ ( k1_relat_1 @ X3 ) )
        = ( k2_relat_1 @ X3 ) )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
        = ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ( X27
        = ( k1_relset_1 @ X27 @ X28 @ X29 ) )
      | ~ ( zip_tseitin_1 @ X29 @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('14',plain,(
    ! [X25: $i,X26: $i] :
      ( ( zip_tseitin_0 @ X25 @ X26 )
      | ( X25 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( zip_tseitin_0 @ X30 @ X31 )
      | ( zip_tseitin_1 @ X32 @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('17',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('22',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( ( k1_relset_1 @ X23 @ X24 @ X22 )
        = ( k1_relat_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('23',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['13','20','23'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('26',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['25'])).

thf(t177_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v2_funct_1 @ A )
            & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) )
         => ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) )
            = B ) ) ) )).

thf('27',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_tarski @ X10 @ ( k1_relat_1 @ X11 ) )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X11 ) @ ( k9_relat_1 @ X11 @ X10 ) )
        = X10 )
      | ~ ( v2_funct_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t177_funct_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k9_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( ( ( k9_relat_1 @ ( k2_funct_1 @ sk_D ) @ ( k9_relat_1 @ sk_D @ sk_A ) )
      = ( k1_relat_1 @ sk_D ) )
    | ~ ( v2_funct_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['24','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('31',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( v4_relat_1 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('32',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X6: $i,X7: $i] :
      ( ( X6
        = ( k7_relat_1 @ X6 @ X7 ) )
      | ~ ( v4_relat_1 @ X6 @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('36',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('37',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['34','37'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) )
        = ( k9_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('40',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k9_relat_1 @ sk_D @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['35','36'])).

thf('42',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k9_relat_1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['13','20','23'])).

thf('44',plain,(
    v2_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['35','36'])).

thf('47',plain,
    ( ( k9_relat_1 @ ( k2_funct_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) )
    = sk_A ),
    inference(demod,[status(thm)],['29','42','43','44','45','46'])).

thf('48',plain,
    ( ( ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) )
      = sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['10','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['35','36'])).

thf('50',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v2_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( k2_relat_1 @ ( k2_funct_1 @ sk_D ) )
    = sk_A ),
    inference(demod,[status(thm)],['48','49','50','51'])).

thf(t57_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( v2_funct_1 @ B )
          & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) )
       => ( ( A
            = ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) )
          & ( A
            = ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ) )).

thf('53',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v2_funct_1 @ X13 )
      | ~ ( r2_hidden @ X14 @ ( k2_relat_1 @ X13 ) )
      | ( X14
        = ( k1_funct_1 @ X13 @ ( k1_funct_1 @ ( k2_funct_1 @ X13 ) @ X14 ) ) )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t57_funct_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_D ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
      | ( X0
        = ( k1_funct_1 @ ( k2_funct_1 @ sk_D ) @ ( k1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) @ X0 ) ) )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_D ) )
      | ( X0
        = ( k1_funct_1 @ ( k2_funct_1 @ sk_D ) @ ( k1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','54'])).

thf('56',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['35','36'])).

thf('57',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ ( k2_funct_1 @ sk_D ) )
      | ( X0
        = ( k1_funct_1 @ ( k2_funct_1 @ sk_D ) @ ( k1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) @ X0 ) ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v2_funct_1 @ sk_D )
      | ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
      | ( X0
        = ( k1_funct_1 @ ( k2_funct_1 @ sk_D ) @ ( k1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['3','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['35','36'])).

thf('61',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v2_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_D ) )
      | ( X0
        = ( k1_funct_1 @ ( k2_funct_1 @ sk_D ) @ ( k1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['59','60','61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( X0
        = ( k1_funct_1 @ ( k2_funct_1 @ sk_D ) @ ( k1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','63'])).

thf('65',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['35','36'])).

thf('66',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k1_funct_1 @ ( k2_funct_1 @ sk_D ) @ ( k1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,
    ( sk_C
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_D ) @ ( k1_funct_1 @ ( k2_funct_1 @ ( k2_funct_1 @ sk_D ) ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['1','67'])).

thf('69',plain,
    ( ( sk_C
      = ( k1_funct_1 @ ( k2_funct_1 @ sk_D ) @ ( k1_funct_1 @ sk_D @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v2_funct_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['0','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['35','36'])).

thf('71',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v2_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( sk_C
    = ( k1_funct_1 @ ( k2_funct_1 @ sk_D ) @ ( k1_funct_1 @ sk_D @ sk_C ) ) ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,(
    ( k1_funct_1 @ ( k2_funct_1 @ sk_D ) @ ( k1_funct_1 @ sk_D @ sk_C ) )
 != sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['73','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.edFgu91KZf
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 20:41:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.36  % Running portfolio for 600 s
% 0.14/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.36  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.37/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.37/0.62  % Solved by: fo/fo7.sh
% 0.37/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.37/0.62  % done 137 iterations in 0.143s
% 0.37/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.37/0.62  % SZS output start Refutation
% 0.37/0.62  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.37/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.37/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.37/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.37/0.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.37/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.37/0.62  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.37/0.62  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.37/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.37/0.62  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.37/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.37/0.62  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.37/0.62  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.37/0.62  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.37/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.37/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.37/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.37/0.62  thf(sk_D_type, type, sk_D: $i).
% 0.37/0.62  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.37/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.37/0.62  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.37/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.37/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.37/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.37/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.37/0.62  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.37/0.62  thf(t65_funct_1, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.62       ( ( v2_funct_1 @ A ) => ( ( k2_funct_1 @ ( k2_funct_1 @ A ) ) = ( A ) ) ) ))).
% 0.37/0.62  thf('0', plain,
% 0.37/0.62      (![X15 : $i]:
% 0.37/0.62         (~ (v2_funct_1 @ X15)
% 0.37/0.62          | ((k2_funct_1 @ (k2_funct_1 @ X15)) = (X15))
% 0.37/0.62          | ~ (v1_funct_1 @ X15)
% 0.37/0.62          | ~ (v1_relat_1 @ X15))),
% 0.37/0.62      inference('cnf', [status(esa)], [t65_funct_1])).
% 0.37/0.62  thf(t32_funct_2, conjecture,
% 0.37/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.62     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.37/0.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.62       ( ( ( v2_funct_1 @ D ) & ( r2_hidden @ C @ A ) ) =>
% 0.37/0.62         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.37/0.62           ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) ) =
% 0.37/0.62             ( C ) ) ) ) ))).
% 0.37/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.37/0.62    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.37/0.62        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.37/0.62            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.37/0.62          ( ( ( v2_funct_1 @ D ) & ( r2_hidden @ C @ A ) ) =>
% 0.37/0.62            ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.37/0.62              ( ( k1_funct_1 @ ( k2_funct_1 @ D ) @ ( k1_funct_1 @ D @ C ) ) =
% 0.37/0.62                ( C ) ) ) ) ) )),
% 0.37/0.62    inference('cnf.neg', [status(esa)], [t32_funct_2])).
% 0.37/0.62  thf('1', plain, ((r2_hidden @ sk_C @ sk_A)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(dt_k2_funct_1, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.62       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.37/0.62         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.37/0.62  thf('2', plain,
% 0.37/0.62      (![X8 : $i]:
% 0.37/0.62         ((v1_funct_1 @ (k2_funct_1 @ X8))
% 0.37/0.62          | ~ (v1_funct_1 @ X8)
% 0.37/0.62          | ~ (v1_relat_1 @ X8))),
% 0.37/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.37/0.62  thf(fc6_funct_1, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) =>
% 0.37/0.62       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 0.37/0.62         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) & 
% 0.37/0.62         ( v2_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 0.37/0.62  thf('3', plain,
% 0.37/0.62      (![X9 : $i]:
% 0.37/0.62         ((v2_funct_1 @ (k2_funct_1 @ X9))
% 0.37/0.62          | ~ (v2_funct_1 @ X9)
% 0.37/0.62          | ~ (v1_funct_1 @ X9)
% 0.37/0.62          | ~ (v1_relat_1 @ X9))),
% 0.37/0.62      inference('cnf', [status(esa)], [fc6_funct_1])).
% 0.37/0.62  thf('4', plain,
% 0.37/0.62      (![X8 : $i]:
% 0.37/0.62         ((v1_relat_1 @ (k2_funct_1 @ X8))
% 0.37/0.62          | ~ (v1_funct_1 @ X8)
% 0.37/0.62          | ~ (v1_relat_1 @ X8))),
% 0.37/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.37/0.62  thf('5', plain,
% 0.37/0.62      (![X8 : $i]:
% 0.37/0.62         ((v1_relat_1 @ (k2_funct_1 @ X8))
% 0.37/0.62          | ~ (v1_funct_1 @ X8)
% 0.37/0.62          | ~ (v1_relat_1 @ X8))),
% 0.37/0.62      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 0.37/0.62  thf(t55_funct_1, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.62       ( ( v2_funct_1 @ A ) =>
% 0.37/0.62         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 0.37/0.62           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.37/0.62  thf('6', plain,
% 0.37/0.62      (![X12 : $i]:
% 0.37/0.62         (~ (v2_funct_1 @ X12)
% 0.37/0.62          | ((k2_relat_1 @ X12) = (k1_relat_1 @ (k2_funct_1 @ X12)))
% 0.37/0.62          | ~ (v1_funct_1 @ X12)
% 0.37/0.62          | ~ (v1_relat_1 @ X12))),
% 0.37/0.62      inference('cnf', [status(esa)], [t55_funct_1])).
% 0.37/0.62  thf(t146_relat_1, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( v1_relat_1 @ A ) =>
% 0.37/0.62       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.37/0.62  thf('7', plain,
% 0.37/0.62      (![X3 : $i]:
% 0.37/0.62         (((k9_relat_1 @ X3 @ (k1_relat_1 @ X3)) = (k2_relat_1 @ X3))
% 0.37/0.62          | ~ (v1_relat_1 @ X3))),
% 0.37/0.62      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.37/0.62  thf('8', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.37/0.62            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.37/0.62          | ~ (v1_relat_1 @ X0)
% 0.37/0.62          | ~ (v1_funct_1 @ X0)
% 0.37/0.62          | ~ (v2_funct_1 @ X0)
% 0.37/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 0.37/0.62      inference('sup+', [status(thm)], ['6', '7'])).
% 0.37/0.62  thf('9', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (v1_relat_1 @ X0)
% 0.37/0.62          | ~ (v1_funct_1 @ X0)
% 0.37/0.62          | ~ (v2_funct_1 @ X0)
% 0.37/0.62          | ~ (v1_funct_1 @ X0)
% 0.37/0.62          | ~ (v1_relat_1 @ X0)
% 0.37/0.62          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.37/0.62              = (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 0.37/0.62      inference('sup-', [status(thm)], ['5', '8'])).
% 0.37/0.62  thf('10', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (((k9_relat_1 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0))
% 0.37/0.62            = (k2_relat_1 @ (k2_funct_1 @ X0)))
% 0.37/0.62          | ~ (v2_funct_1 @ X0)
% 0.37/0.62          | ~ (v1_funct_1 @ X0)
% 0.37/0.62          | ~ (v1_relat_1 @ X0))),
% 0.37/0.62      inference('simplify', [status(thm)], ['9'])).
% 0.37/0.62  thf('11', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(d1_funct_2, axiom,
% 0.37/0.62    (![A:$i,B:$i,C:$i]:
% 0.37/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.62       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.37/0.62           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.37/0.62             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.37/0.62         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.62           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.37/0.62             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.37/0.62  thf(zf_stmt_1, axiom,
% 0.37/0.62    (![C:$i,B:$i,A:$i]:
% 0.37/0.62     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.37/0.62       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.37/0.62  thf('12', plain,
% 0.37/0.62      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.37/0.62         (~ (v1_funct_2 @ X29 @ X27 @ X28)
% 0.37/0.62          | ((X27) = (k1_relset_1 @ X27 @ X28 @ X29))
% 0.37/0.62          | ~ (zip_tseitin_1 @ X29 @ X28 @ X27))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.37/0.62  thf('13', plain,
% 0.37/0.62      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.37/0.62        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['11', '12'])).
% 0.37/0.62  thf(zf_stmt_2, axiom,
% 0.37/0.62    (![B:$i,A:$i]:
% 0.37/0.62     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.37/0.62       ( zip_tseitin_0 @ B @ A ) ))).
% 0.37/0.62  thf('14', plain,
% 0.37/0.62      (![X25 : $i, X26 : $i]:
% 0.37/0.62         ((zip_tseitin_0 @ X25 @ X26) | ((X25) = (k1_xboole_0)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.37/0.62  thf('15', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.37/0.62  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.37/0.62  thf(zf_stmt_5, axiom,
% 0.37/0.62    (![A:$i,B:$i,C:$i]:
% 0.37/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.62       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.37/0.62         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.37/0.62           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.37/0.62             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.37/0.62  thf('16', plain,
% 0.37/0.62      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.37/0.62         (~ (zip_tseitin_0 @ X30 @ X31)
% 0.37/0.62          | (zip_tseitin_1 @ X32 @ X30 @ X31)
% 0.37/0.62          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X30))))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.37/0.62  thf('17', plain,
% 0.37/0.62      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['15', '16'])).
% 0.37/0.62  thf('18', plain,
% 0.37/0.62      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['14', '17'])).
% 0.37/0.62  thf('19', plain, (((sk_B) != (k1_xboole_0))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('20', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 0.37/0.62      inference('simplify_reflect-', [status(thm)], ['18', '19'])).
% 0.37/0.62  thf('21', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(redefinition_k1_relset_1, axiom,
% 0.37/0.62    (![A:$i,B:$i,C:$i]:
% 0.37/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.62       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.37/0.62  thf('22', plain,
% 0.37/0.62      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.37/0.62         (((k1_relset_1 @ X23 @ X24 @ X22) = (k1_relat_1 @ X22))
% 0.37/0.62          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.37/0.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.37/0.62  thf('23', plain,
% 0.37/0.62      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.37/0.62      inference('sup-', [status(thm)], ['21', '22'])).
% 0.37/0.62  thf('24', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.37/0.62      inference('demod', [status(thm)], ['13', '20', '23'])).
% 0.37/0.62  thf(d10_xboole_0, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.37/0.62  thf('25', plain,
% 0.37/0.62      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.37/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.37/0.62  thf('26', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.37/0.62      inference('simplify', [status(thm)], ['25'])).
% 0.37/0.62  thf(t177_funct_1, axiom,
% 0.37/0.62    (![A:$i]:
% 0.37/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.37/0.62       ( ![B:$i]:
% 0.37/0.62         ( ( ( v2_funct_1 @ A ) & ( r1_tarski @ B @ ( k1_relat_1 @ A ) ) ) =>
% 0.37/0.62           ( ( k9_relat_1 @ ( k2_funct_1 @ A ) @ ( k9_relat_1 @ A @ B ) ) =
% 0.37/0.62             ( B ) ) ) ) ))).
% 0.37/0.62  thf('27', plain,
% 0.37/0.62      (![X10 : $i, X11 : $i]:
% 0.37/0.62         (~ (r1_tarski @ X10 @ (k1_relat_1 @ X11))
% 0.37/0.62          | ((k9_relat_1 @ (k2_funct_1 @ X11) @ (k9_relat_1 @ X11 @ X10))
% 0.37/0.62              = (X10))
% 0.37/0.62          | ~ (v2_funct_1 @ X11)
% 0.37/0.62          | ~ (v1_funct_1 @ X11)
% 0.37/0.62          | ~ (v1_relat_1 @ X11))),
% 0.37/0.62      inference('cnf', [status(esa)], [t177_funct_1])).
% 0.37/0.62  thf('28', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (v1_relat_1 @ X0)
% 0.37/0.62          | ~ (v1_funct_1 @ X0)
% 0.37/0.62          | ~ (v2_funct_1 @ X0)
% 0.37/0.62          | ((k9_relat_1 @ (k2_funct_1 @ X0) @ 
% 0.37/0.62              (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))) = (k1_relat_1 @ X0)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['26', '27'])).
% 0.37/0.62  thf('29', plain,
% 0.37/0.62      ((((k9_relat_1 @ (k2_funct_1 @ sk_D) @ (k9_relat_1 @ sk_D @ sk_A))
% 0.37/0.62          = (k1_relat_1 @ sk_D))
% 0.37/0.62        | ~ (v2_funct_1 @ sk_D)
% 0.37/0.62        | ~ (v1_funct_1 @ sk_D)
% 0.37/0.62        | ~ (v1_relat_1 @ sk_D))),
% 0.37/0.62      inference('sup+', [status(thm)], ['24', '28'])).
% 0.37/0.62  thf('30', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(cc2_relset_1, axiom,
% 0.37/0.62    (![A:$i,B:$i,C:$i]:
% 0.37/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.62       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.37/0.62  thf('31', plain,
% 0.37/0.62      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.37/0.62         ((v4_relat_1 @ X19 @ X20)
% 0.37/0.62          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.37/0.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.37/0.62  thf('32', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 0.37/0.62      inference('sup-', [status(thm)], ['30', '31'])).
% 0.37/0.62  thf(t209_relat_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.37/0.62       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.37/0.62  thf('33', plain,
% 0.37/0.62      (![X6 : $i, X7 : $i]:
% 0.37/0.62         (((X6) = (k7_relat_1 @ X6 @ X7))
% 0.37/0.62          | ~ (v4_relat_1 @ X6 @ X7)
% 0.37/0.62          | ~ (v1_relat_1 @ X6))),
% 0.37/0.62      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.37/0.62  thf('34', plain,
% 0.37/0.62      ((~ (v1_relat_1 @ sk_D) | ((sk_D) = (k7_relat_1 @ sk_D @ sk_A)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['32', '33'])).
% 0.37/0.62  thf('35', plain,
% 0.37/0.62      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf(cc1_relset_1, axiom,
% 0.37/0.62    (![A:$i,B:$i,C:$i]:
% 0.37/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.37/0.62       ( v1_relat_1 @ C ) ))).
% 0.37/0.62  thf('36', plain,
% 0.37/0.62      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.37/0.62         ((v1_relat_1 @ X16)
% 0.37/0.62          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.37/0.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.37/0.62  thf('37', plain, ((v1_relat_1 @ sk_D)),
% 0.37/0.62      inference('sup-', [status(thm)], ['35', '36'])).
% 0.37/0.62  thf('38', plain, (((sk_D) = (k7_relat_1 @ sk_D @ sk_A))),
% 0.37/0.62      inference('demod', [status(thm)], ['34', '37'])).
% 0.37/0.62  thf(t148_relat_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( v1_relat_1 @ B ) =>
% 0.37/0.62       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.37/0.62  thf('39', plain,
% 0.37/0.62      (![X4 : $i, X5 : $i]:
% 0.37/0.62         (((k2_relat_1 @ (k7_relat_1 @ X4 @ X5)) = (k9_relat_1 @ X4 @ X5))
% 0.37/0.62          | ~ (v1_relat_1 @ X4))),
% 0.37/0.62      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.37/0.62  thf('40', plain,
% 0.37/0.62      ((((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ sk_A))
% 0.37/0.62        | ~ (v1_relat_1 @ sk_D))),
% 0.37/0.62      inference('sup+', [status(thm)], ['38', '39'])).
% 0.37/0.62  thf('41', plain, ((v1_relat_1 @ sk_D)),
% 0.37/0.62      inference('sup-', [status(thm)], ['35', '36'])).
% 0.37/0.62  thf('42', plain, (((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ sk_A))),
% 0.37/0.62      inference('demod', [status(thm)], ['40', '41'])).
% 0.37/0.62  thf('43', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.37/0.62      inference('demod', [status(thm)], ['13', '20', '23'])).
% 0.37/0.62  thf('44', plain, ((v2_funct_1 @ sk_D)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('45', plain, ((v1_funct_1 @ sk_D)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('46', plain, ((v1_relat_1 @ sk_D)),
% 0.37/0.62      inference('sup-', [status(thm)], ['35', '36'])).
% 0.37/0.62  thf('47', plain,
% 0.37/0.62      (((k9_relat_1 @ (k2_funct_1 @ sk_D) @ (k2_relat_1 @ sk_D)) = (sk_A))),
% 0.37/0.62      inference('demod', [status(thm)], ['29', '42', '43', '44', '45', '46'])).
% 0.37/0.62  thf('48', plain,
% 0.37/0.62      ((((k2_relat_1 @ (k2_funct_1 @ sk_D)) = (sk_A))
% 0.37/0.62        | ~ (v1_relat_1 @ sk_D)
% 0.37/0.62        | ~ (v1_funct_1 @ sk_D)
% 0.37/0.62        | ~ (v2_funct_1 @ sk_D))),
% 0.37/0.62      inference('sup+', [status(thm)], ['10', '47'])).
% 0.37/0.62  thf('49', plain, ((v1_relat_1 @ sk_D)),
% 0.37/0.62      inference('sup-', [status(thm)], ['35', '36'])).
% 0.37/0.62  thf('50', plain, ((v1_funct_1 @ sk_D)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('51', plain, ((v2_funct_1 @ sk_D)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('52', plain, (((k2_relat_1 @ (k2_funct_1 @ sk_D)) = (sk_A))),
% 0.37/0.62      inference('demod', [status(thm)], ['48', '49', '50', '51'])).
% 0.37/0.62  thf(t57_funct_1, axiom,
% 0.37/0.62    (![A:$i,B:$i]:
% 0.37/0.62     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.37/0.62       ( ( ( v2_funct_1 @ B ) & ( r2_hidden @ A @ ( k2_relat_1 @ B ) ) ) =>
% 0.37/0.62         ( ( ( A ) =
% 0.37/0.62             ( k1_funct_1 @ B @ ( k1_funct_1 @ ( k2_funct_1 @ B ) @ A ) ) ) & 
% 0.37/0.62           ( ( A ) =
% 0.37/0.62             ( k1_funct_1 @ ( k5_relat_1 @ ( k2_funct_1 @ B ) @ B ) @ A ) ) ) ) ))).
% 0.37/0.62  thf('53', plain,
% 0.37/0.62      (![X13 : $i, X14 : $i]:
% 0.37/0.62         (~ (v2_funct_1 @ X13)
% 0.37/0.62          | ~ (r2_hidden @ X14 @ (k2_relat_1 @ X13))
% 0.37/0.62          | ((X14)
% 0.37/0.62              = (k1_funct_1 @ X13 @ (k1_funct_1 @ (k2_funct_1 @ X13) @ X14)))
% 0.37/0.62          | ~ (v1_funct_1 @ X13)
% 0.37/0.62          | ~ (v1_relat_1 @ X13))),
% 0.37/0.62      inference('cnf', [status(esa)], [t57_funct_1])).
% 0.37/0.62  thf('54', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (r2_hidden @ X0 @ sk_A)
% 0.37/0.62          | ~ (v1_relat_1 @ (k2_funct_1 @ sk_D))
% 0.37/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 0.37/0.62          | ((X0)
% 0.37/0.62              = (k1_funct_1 @ (k2_funct_1 @ sk_D) @ 
% 0.37/0.62                 (k1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_D)) @ X0)))
% 0.37/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ sk_D)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['52', '53'])).
% 0.37/0.62  thf('55', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (v1_relat_1 @ sk_D)
% 0.37/0.62          | ~ (v1_funct_1 @ sk_D)
% 0.37/0.62          | ~ (v2_funct_1 @ (k2_funct_1 @ sk_D))
% 0.37/0.62          | ((X0)
% 0.37/0.62              = (k1_funct_1 @ (k2_funct_1 @ sk_D) @ 
% 0.37/0.62                 (k1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_D)) @ X0)))
% 0.37/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 0.37/0.62          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['4', '54'])).
% 0.37/0.62  thf('56', plain, ((v1_relat_1 @ sk_D)),
% 0.37/0.62      inference('sup-', [status(thm)], ['35', '36'])).
% 0.37/0.62  thf('57', plain, ((v1_funct_1 @ sk_D)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('58', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (v2_funct_1 @ (k2_funct_1 @ sk_D))
% 0.37/0.62          | ((X0)
% 0.37/0.62              = (k1_funct_1 @ (k2_funct_1 @ sk_D) @ 
% 0.37/0.62                 (k1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_D)) @ X0)))
% 0.37/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 0.37/0.62          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.37/0.62      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.37/0.62  thf('59', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (v1_relat_1 @ sk_D)
% 0.37/0.62          | ~ (v1_funct_1 @ sk_D)
% 0.37/0.62          | ~ (v2_funct_1 @ sk_D)
% 0.37/0.62          | ~ (r2_hidden @ X0 @ sk_A)
% 0.37/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 0.37/0.62          | ((X0)
% 0.37/0.62              = (k1_funct_1 @ (k2_funct_1 @ sk_D) @ 
% 0.37/0.62                 (k1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_D)) @ X0))))),
% 0.37/0.62      inference('sup-', [status(thm)], ['3', '58'])).
% 0.37/0.62  thf('60', plain, ((v1_relat_1 @ sk_D)),
% 0.37/0.62      inference('sup-', [status(thm)], ['35', '36'])).
% 0.37/0.62  thf('61', plain, ((v1_funct_1 @ sk_D)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('62', plain, ((v2_funct_1 @ sk_D)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('63', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (r2_hidden @ X0 @ sk_A)
% 0.37/0.62          | ~ (v1_funct_1 @ (k2_funct_1 @ sk_D))
% 0.37/0.62          | ((X0)
% 0.37/0.62              = (k1_funct_1 @ (k2_funct_1 @ sk_D) @ 
% 0.37/0.62                 (k1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_D)) @ X0))))),
% 0.37/0.62      inference('demod', [status(thm)], ['59', '60', '61', '62'])).
% 0.37/0.62  thf('64', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (~ (v1_relat_1 @ sk_D)
% 0.37/0.62          | ~ (v1_funct_1 @ sk_D)
% 0.37/0.62          | ((X0)
% 0.37/0.62              = (k1_funct_1 @ (k2_funct_1 @ sk_D) @ 
% 0.37/0.62                 (k1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_D)) @ X0)))
% 0.37/0.62          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.37/0.62      inference('sup-', [status(thm)], ['2', '63'])).
% 0.37/0.62  thf('65', plain, ((v1_relat_1 @ sk_D)),
% 0.37/0.62      inference('sup-', [status(thm)], ['35', '36'])).
% 0.37/0.62  thf('66', plain, ((v1_funct_1 @ sk_D)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('67', plain,
% 0.37/0.62      (![X0 : $i]:
% 0.37/0.62         (((X0)
% 0.37/0.62            = (k1_funct_1 @ (k2_funct_1 @ sk_D) @ 
% 0.37/0.62               (k1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_D)) @ X0)))
% 0.37/0.62          | ~ (r2_hidden @ X0 @ sk_A))),
% 0.37/0.62      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.37/0.62  thf('68', plain,
% 0.37/0.62      (((sk_C)
% 0.37/0.62         = (k1_funct_1 @ (k2_funct_1 @ sk_D) @ 
% 0.37/0.62            (k1_funct_1 @ (k2_funct_1 @ (k2_funct_1 @ sk_D)) @ sk_C)))),
% 0.37/0.62      inference('sup-', [status(thm)], ['1', '67'])).
% 0.37/0.62  thf('69', plain,
% 0.37/0.62      ((((sk_C)
% 0.37/0.62          = (k1_funct_1 @ (k2_funct_1 @ sk_D) @ (k1_funct_1 @ sk_D @ sk_C)))
% 0.37/0.62        | ~ (v1_relat_1 @ sk_D)
% 0.37/0.62        | ~ (v1_funct_1 @ sk_D)
% 0.37/0.62        | ~ (v2_funct_1 @ sk_D))),
% 0.37/0.62      inference('sup+', [status(thm)], ['0', '68'])).
% 0.37/0.62  thf('70', plain, ((v1_relat_1 @ sk_D)),
% 0.37/0.62      inference('sup-', [status(thm)], ['35', '36'])).
% 0.37/0.62  thf('71', plain, ((v1_funct_1 @ sk_D)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('72', plain, ((v2_funct_1 @ sk_D)),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('73', plain,
% 0.37/0.62      (((sk_C)
% 0.37/0.62         = (k1_funct_1 @ (k2_funct_1 @ sk_D) @ (k1_funct_1 @ sk_D @ sk_C)))),
% 0.37/0.62      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 0.37/0.62  thf('74', plain,
% 0.37/0.62      (((k1_funct_1 @ (k2_funct_1 @ sk_D) @ (k1_funct_1 @ sk_D @ sk_C))
% 0.37/0.62         != (sk_C))),
% 0.37/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.37/0.62  thf('75', plain, ($false),
% 0.37/0.62      inference('simplify_reflect-', [status(thm)], ['73', '74'])).
% 0.37/0.62  
% 0.37/0.62  % SZS output end Refutation
% 0.37/0.62  
% 0.37/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
