%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.i1Ih0eNfuH

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:47 EST 2020

% Result     : Theorem 2.22s
% Output     : Refutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :  333 (65072 expanded)
%              Number of leaves         :   40 (18920 expanded)
%              Depth                    :   39
%              Number of atoms          : 2734 (946647 expanded)
%              Number of equality atoms :  169 (48969 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t31_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( v2_funct_1 @ C )
            & ( ( k2_relset_1 @ A @ B @ C )
              = B ) )
         => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
            & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
            & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t31_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('2',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('4',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('5',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('9',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_C @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ sk_C @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( zip_tseitin_0 @ sk_B @ X1 ) ) ),
    inference('sup+',[status(thm)],['2','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( r1_tarski @ sk_C @ sk_B ) ) ),
    inference(eq_fact,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['3','5'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('17',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v5_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X1 )
      | ( v5_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

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

thf('22',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('23',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ sk_C @ X0 )
      | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('27',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('30',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ sk_C @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('33',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v5_relat_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('36',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('38',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('39',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('41',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('42',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( r1_tarski @ sk_B @ X0 ) ) ),
    inference(demod,[status(thm)],['34','39','44'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('46',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ~ ( r1_tarski @ X0 @ sk_B )
      | ( X0 = sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B @ X0 )
      | ( sk_C = sk_B )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['12','47'])).

thf('49',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('50',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
    | ( sk_C = sk_B )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('52',plain,
    ( ( sk_C = sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf(t55_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v2_funct_1 @ A )
       => ( ( ( k2_relat_1 @ A )
            = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) )
          & ( ( k1_relat_1 @ A )
            = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ) )).

thf('53',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k1_relat_1 @ X16 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('54',plain,
    ( ( sk_C = sk_B )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf(dt_k2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ ( k2_funct_1 @ A ) )
        & ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ) )).

thf('55',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('56',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('57',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k1_relat_1 @ X16 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('59',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ( v5_relat_1 @ X11 @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['57','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v5_relat_1 @ ( k2_funct_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v5_relat_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['55','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A )
    | ( sk_C = sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['54','68'])).

thf('70',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A )
    | ( sk_C = sk_B ) ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('75',plain,
    ( ( sk_C = sk_B )
    | ~ ( r1_tarski @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_A
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( sk_A
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_C = sk_B ) ),
    inference('sup-',[status(thm)],['53','75'])).

thf('77',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('78',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) )
    | ( sk_A
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_C = sk_B ) ),
    inference(demod,[status(thm)],['76','77','78','79'])).

thf('81',plain,
    ( ~ ( r1_tarski @ sk_A @ sk_A )
    | ( sk_C = sk_B )
    | ( sk_C = sk_B )
    | ( sk_A
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['52','80'])).

thf('82',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('83',plain,
    ( ( sk_C = sk_B )
    | ( sk_C = sk_B )
    | ( sk_A
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( sk_A
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
    | ( sk_C = sk_B ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X15: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('86',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('87',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_relat_1 @ X16 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('88',plain,(
    ! [X34: $i] :
      ( ( v1_funct_2 @ X34 @ ( k1_relat_1 @ X34 ) @ ( k2_relat_1 @ X34 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['86','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['85','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ ( k2_relat_1 @ sk_C ) @ sk_A )
    | ( sk_C = sk_B )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['84','93'])).

thf('95',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['42','43'])).

thf('96',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('97',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,
    ( ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ( sk_C = sk_B ) ),
    inference(demod,[status(thm)],['94','95','96','97','98'])).

thf('100',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('101',plain,
    ( ( sk_C = sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['1','101'])).

thf('103',plain,
    ( ( sk_C = sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('104',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('105',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('106',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('108',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_B ) )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['103','108'])).

thf('110',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k1_relat_1 @ X16 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ ( k2_funct_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['112'])).

thf('114',plain,
    ( ( ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ ( k2_relat_1 @ sk_B ) @ sk_A )
      | ( sk_B = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v2_funct_1 @ sk_B ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['109','113'])).

thf('115',plain,
    ( ( sk_C = sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('116',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['42','43'])).

thf('117',plain,
    ( ( ( k2_relat_1 @ sk_B )
      = sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['115','116'])).

thf('118',plain,
    ( ( sk_C = sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('119',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('120',plain,
    ( ( v1_relat_1 @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['118','119'])).

thf('121',plain,
    ( ( sk_C = sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('122',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,
    ( ( v1_funct_1 @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( sk_C = sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('125',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,
    ( ( v2_funct_1 @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_B @ sk_A )
      | ( sk_B = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['114','117','120','123','126'])).

thf('128',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_B ) @ sk_B @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['1','101'])).

thf('129',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('130',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('131',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ k1_xboole_0 @ sk_A )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['102','129','130'])).

thf('132',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('133',plain,(
    ! [X15: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('134',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('135',plain,
    ( ( ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C ) )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ~ ( v1_relat_1 @ sk_C )
   <= ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['135','136'])).

thf('138',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['132','137'])).

thf('139',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('140',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k1_relat_1 @ X16 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('141',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_relat_1 @ X16 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('142',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('143',plain,(
    ! [X15: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('144',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('145',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('146',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['144','145'])).

thf('147',plain,(
    ! [X34: $i] :
      ( ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X34 ) @ ( k2_relat_1 @ X34 ) ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('148',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_0 @ ( k1_relat_1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['146','147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['144','145'])).

thf('150',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,
    ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('155',plain,
    ( ( ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['153','154'])).

thf('156',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
        | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) )
        | ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['148','155'])).

thf('157',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) )
        | ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['143','156'])).

thf('158',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('159',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ! [X0: $i] :
        ( ( sk_A
          = ( k1_relat_1 @ sk_C ) )
        | ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        | ~ ( v1_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_relat_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['142','160'])).

thf('162',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('163',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ ( k1_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['161','162','163'])).

thf('165',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ ( k2_relat_1 @ sk_C ) @ X0 )
        | ~ ( v1_relat_1 @ sk_C )
        | ~ ( v1_funct_1 @ sk_C )
        | ~ ( v2_funct_1 @ sk_C )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['141','164'])).

thf('166',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['42','43'])).

thf('167',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('168',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('169',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_0 @ sk_B @ X0 )
        | ( sk_A
          = ( k1_relat_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['165','166','167','168','169'])).

thf('171',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('172',plain,
    ( ( ( sk_A
        = ( k1_relat_1 @ sk_C ) )
      | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('174',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['172','173'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ~ ( v2_funct_1 @ X0 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['67'])).

thf('176',plain,
    ( ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['174','175'])).

thf('177',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('178',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) @ sk_A )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['176','177','178','179'])).

thf('181',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('182',plain,
    ( ( ~ ( r1_tarski @ sk_A @ ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
      | ( sk_A
        = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['180','181'])).

thf('183',plain,
    ( ( ~ ( r1_tarski @ sk_A @ ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C )
      | ( sk_A
        = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['140','182'])).

thf('184',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['172','173'])).

thf('185',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('186',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('187',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ( sk_A
      = ( k2_relat_1 @ ( k2_funct_1 @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['183','184','185','186','187','188'])).

thf('190',plain,(
    ! [X15: $i] :
      ( ( v1_funct_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('191',plain,(
    ! [X15: $i] :
      ( ( v1_relat_1 @ ( k2_funct_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_funct_1])).

thf('192',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k2_relat_1 @ X16 )
        = ( k1_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('193',plain,(
    ! [X34: $i] :
      ( ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X34 ) @ ( k2_relat_1 @ X34 ) ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('194',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['192','193'])).

thf('195',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['191','194'])).

thf('196',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['190','196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['197'])).

thf('199',plain,
    ( ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ sk_C ) @ sk_A ) ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v2_funct_1 @ sk_C ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['189','198'])).

thf('200',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['42','43'])).

thf('201',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('202',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('203',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['199','200','201','202','203'])).

thf('205',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['139','204'])).

thf('206',plain,
    ( ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A )
    | ~ ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) ) ),
    inference(split,[status(esa)],['0'])).

thf('207',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['138','205','206'])).

thf('208',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ k1_xboole_0 ) @ k1_xboole_0 @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['131','207'])).

thf('209',plain,
    ( ( sk_C = sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('210',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_B )
      = sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['209','210'])).

thf('212',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('213',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('214',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['58'])).

thf('215',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('216',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['4'])).

thf('218',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('219',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k2_relset_1 @ X0 @ k1_xboole_0 @ X1 )
        = ( k2_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['217','218'])).

thf('220',plain,(
    ! [X0: $i] :
      ( ( k2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['216','219'])).

thf('221',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('222',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['211','212','213','220','221'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_funct_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_relat_1 @ X0 ) @ ( k2_relat_1 @ ( k2_funct_1 @ X0 ) ) ) ) )
      | ~ ( v2_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['197'])).

thf('224',plain,
    ( ( ( m1_subset_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ ( k2_relat_1 @ ( k2_funct_1 @ k1_xboole_0 ) ) ) ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_funct_1 @ k1_xboole_0 )
      | ~ ( v2_funct_1 @ k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['222','223'])).

thf('225',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('226',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('227',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('228',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['226','227'])).

thf('229',plain,
    ( ( v1_funct_1 @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['121','122'])).

thf('230',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('231',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['229','230'])).

thf('232',plain,
    ( ( v2_funct_1 @ sk_B )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup+',[status(thm)],['124','125'])).

thf('233',plain,
    ( ( sk_B = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(clc,[status(thm)],['127','128'])).

thf('234',plain,
    ( ( v2_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['232','233'])).

thf('235',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['224','225','228','231','234'])).

thf('236',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('237',plain,
    ( ( r1_tarski @ ( k2_funct_1 @ k1_xboole_0 ) @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['235','236'])).

thf('238',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['138','205','206'])).

thf('239',plain,(
    r1_tarski @ ( k2_funct_1 @ k1_xboole_0 ) @ k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['237','238'])).

thf('240',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['211','212','213','220','221'])).

thf('241',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('242',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('243',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v5_relat_1 @ X17 @ X19 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('244',plain,(
    ! [X0: $i,X1: $i] :
      ( v5_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['242','243'])).

thf('245',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup+',[status(thm)],['241','244'])).

thf('246',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v5_relat_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('247',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['245','246'])).

thf('248',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['226','227'])).

thf('249',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['247','248'])).

thf('250',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('251',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k2_relat_1 @ k1_xboole_0 ) )
      | ( X0
        = ( k2_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['249','250'])).

thf('252',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
        | ( X0
          = ( k2_relat_1 @ k1_xboole_0 ) ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['240','251'])).

thf('253',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['211','212','213','220','221'])).

thf('254',plain,
    ( ! [X0: $i] :
        ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
        | ( X0 = k1_xboole_0 ) )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['252','253'])).

thf('255',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['138','205','206'])).

thf('256',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(simpl_trail,[status(thm)],['254','255'])).

thf('257',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['239','256'])).

thf('258',plain,(
    ~ ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['208','257'])).

thf('259',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('260',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('261',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('262',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ X1 )
        = ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['260','261'])).

thf('263',plain,(
    ! [X0: $i] :
      ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      = ( k1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['259','262'])).

thf('264',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( X28
       != ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('265',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_relat_1 @ k1_xboole_0 ) )
      | ~ ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['263','264'])).

thf('266',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('267',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['16'])).

thf('268',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('269',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['267','268'])).

thf('270',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X27 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('271',plain,(
    ! [X26: $i] :
      ( zip_tseitin_0 @ X26 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['270'])).

thf('272',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['269','271'])).

thf('273',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['266','272'])).

thf('274',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
       != ( k1_relat_1 @ k1_xboole_0 ) )
      | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['265','273'])).

thf('275',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['239','256'])).

thf('276',plain,(
    ! [X16: $i] :
      ( ~ ( v2_funct_1 @ X16 )
      | ( ( k1_relat_1 @ X16 )
        = ( k2_relat_1 @ ( k2_funct_1 @ X16 ) ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t55_funct_1])).

thf('277',plain,
    ( ( ( k1_relat_1 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ~ ( v1_funct_1 @ k1_xboole_0 )
    | ~ ( v2_funct_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['275','276'])).

thf('278',plain,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['211','212','213','220','221'])).

thf('279',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['138','205','206'])).

thf('280',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['278','279'])).

thf('281',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['226','227'])).

thf('282',plain,
    ( ( v1_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['229','230'])).

thf('283',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['138','205','206'])).

thf('284',plain,(
    v1_funct_1 @ k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['282','283'])).

thf('285',plain,
    ( ( v2_funct_1 @ k1_xboole_0 )
   <= ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['232','233'])).

thf('286',plain,(
    ~ ( v1_funct_2 @ ( k2_funct_1 @ sk_C ) @ sk_B @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['138','205','206'])).

thf('287',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['285','286'])).

thf('288',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['277','280','281','284','287'])).

thf('289',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['274','288'])).

thf('290',plain,(
    ! [X0: $i] :
      ( v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['289'])).

thf('291',plain,(
    $false ),
    inference(demod,[status(thm)],['258','290'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.i1Ih0eNfuH
% 0.13/0.36  % Computer   : n016.cluster.edu
% 0.13/0.36  % Model      : x86_64 x86_64
% 0.13/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.36  % Memory     : 8042.1875MB
% 0.13/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.36  % CPULimit   : 60
% 0.13/0.36  % DateTime   : Tue Dec  1 17:26:19 EST 2020
% 0.13/0.36  % CPUTime    : 
% 0.13/0.36  % Running portfolio for 600 s
% 0.13/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.37  % Running in FO mode
% 2.22/2.46  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.22/2.46  % Solved by: fo/fo7.sh
% 2.22/2.46  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.22/2.46  % done 3004 iterations in 1.996s
% 2.22/2.46  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.22/2.46  % SZS output start Refutation
% 2.22/2.46  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.22/2.46  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.22/2.46  thf(sk_C_type, type, sk_C: $i).
% 2.22/2.46  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.22/2.46  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.22/2.46  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.22/2.46  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 2.22/2.46  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.22/2.46  thf(sk_A_type, type, sk_A: $i).
% 2.22/2.46  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.22/2.46  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.22/2.46  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.22/2.46  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.22/2.46  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.22/2.46  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.22/2.46  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.22/2.46  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.22/2.46  thf(sk_B_type, type, sk_B: $i).
% 2.22/2.46  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.22/2.46  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.22/2.46  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.22/2.46  thf(t31_funct_2, conjecture,
% 2.22/2.46    (![A:$i,B:$i,C:$i]:
% 2.22/2.46     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.22/2.46         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.22/2.46       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 2.22/2.46         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 2.22/2.46           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 2.22/2.46           ( m1_subset_1 @
% 2.22/2.46             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 2.22/2.46  thf(zf_stmt_0, negated_conjecture,
% 2.22/2.46    (~( ![A:$i,B:$i,C:$i]:
% 2.22/2.46        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.22/2.46            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.22/2.46          ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 2.22/2.46            ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 2.22/2.46              ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 2.22/2.46              ( m1_subset_1 @
% 2.22/2.46                ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )),
% 2.22/2.46    inference('cnf.neg', [status(esa)], [t31_funct_2])).
% 2.22/2.46  thf('0', plain,
% 2.22/2.46      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.22/2.46        | ~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)
% 2.22/2.46        | ~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.46             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.46  thf('1', plain,
% 2.22/2.46      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 2.22/2.46         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.46      inference('split', [status(esa)], ['0'])).
% 2.22/2.46  thf(d1_funct_2, axiom,
% 2.22/2.46    (![A:$i,B:$i,C:$i]:
% 2.22/2.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.22/2.46       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.22/2.46           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.22/2.46             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.22/2.46         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.22/2.46           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.22/2.46             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.22/2.46  thf(zf_stmt_1, axiom,
% 2.22/2.46    (![B:$i,A:$i]:
% 2.22/2.46     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.22/2.46       ( zip_tseitin_0 @ B @ A ) ))).
% 2.22/2.46  thf('2', plain,
% 2.22/2.46      (![X26 : $i, X27 : $i]:
% 2.22/2.46         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.22/2.46  thf('3', plain,
% 2.22/2.46      (![X26 : $i, X27 : $i]:
% 2.22/2.46         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.22/2.46  thf(t113_zfmisc_1, axiom,
% 2.22/2.46    (![A:$i,B:$i]:
% 2.22/2.46     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.22/2.46       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.22/2.46  thf('4', plain,
% 2.22/2.46      (![X4 : $i, X5 : $i]:
% 2.22/2.46         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 2.22/2.46      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.22/2.46  thf('5', plain,
% 2.22/2.46      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 2.22/2.46      inference('simplify', [status(thm)], ['4'])).
% 2.22/2.46  thf('6', plain,
% 2.22/2.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.22/2.46         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 2.22/2.46      inference('sup+', [status(thm)], ['3', '5'])).
% 2.22/2.46  thf('7', plain,
% 2.22/2.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.46  thf(t3_subset, axiom,
% 2.22/2.46    (![A:$i,B:$i]:
% 2.22/2.46     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.22/2.46  thf('8', plain,
% 2.22/2.46      (![X6 : $i, X7 : $i]:
% 2.22/2.46         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 2.22/2.46      inference('cnf', [status(esa)], [t3_subset])).
% 2.22/2.46  thf('9', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B))),
% 2.22/2.46      inference('sup-', [status(thm)], ['7', '8'])).
% 2.22/2.46  thf('10', plain,
% 2.22/2.46      (![X0 : $i]:
% 2.22/2.46         ((r1_tarski @ sk_C @ k1_xboole_0) | (zip_tseitin_0 @ sk_B @ X0))),
% 2.22/2.46      inference('sup+', [status(thm)], ['6', '9'])).
% 2.22/2.46  thf('11', plain,
% 2.22/2.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.22/2.46         ((r1_tarski @ sk_C @ X0)
% 2.22/2.46          | (zip_tseitin_0 @ X0 @ X2)
% 2.22/2.46          | (zip_tseitin_0 @ sk_B @ X1))),
% 2.22/2.46      inference('sup+', [status(thm)], ['2', '10'])).
% 2.22/2.46  thf('12', plain,
% 2.22/2.46      (![X0 : $i]: ((zip_tseitin_0 @ sk_B @ X0) | (r1_tarski @ sk_C @ sk_B))),
% 2.22/2.46      inference('eq_fact', [status(thm)], ['11'])).
% 2.22/2.46  thf('13', plain,
% 2.22/2.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.22/2.46         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 2.22/2.46      inference('sup+', [status(thm)], ['3', '5'])).
% 2.22/2.46  thf('14', plain,
% 2.22/2.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.46  thf('15', plain,
% 2.22/2.46      (![X0 : $i]:
% 2.22/2.46         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.22/2.46          | (zip_tseitin_0 @ sk_B @ X0))),
% 2.22/2.46      inference('sup+', [status(thm)], ['13', '14'])).
% 2.22/2.46  thf('16', plain,
% 2.22/2.46      (![X4 : $i, X5 : $i]:
% 2.22/2.46         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 2.22/2.46      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.22/2.46  thf('17', plain,
% 2.22/2.46      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 2.22/2.46      inference('simplify', [status(thm)], ['16'])).
% 2.22/2.46  thf(cc2_relset_1, axiom,
% 2.22/2.46    (![A:$i,B:$i,C:$i]:
% 2.22/2.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.22/2.46       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.22/2.46  thf('18', plain,
% 2.22/2.46      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.22/2.46         ((v5_relat_1 @ X17 @ X19)
% 2.22/2.46          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 2.22/2.46      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.22/2.46  thf('19', plain,
% 2.22/2.46      (![X0 : $i, X1 : $i]:
% 2.22/2.46         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.22/2.46          | (v5_relat_1 @ X1 @ X0))),
% 2.22/2.46      inference('sup-', [status(thm)], ['17', '18'])).
% 2.22/2.46  thf('20', plain,
% 2.22/2.46      (![X0 : $i, X1 : $i]:
% 2.22/2.46         ((zip_tseitin_0 @ sk_B @ X1) | (v5_relat_1 @ sk_C @ X0))),
% 2.22/2.46      inference('sup-', [status(thm)], ['15', '19'])).
% 2.22/2.46  thf('21', plain,
% 2.22/2.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.46  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.22/2.46  thf(zf_stmt_3, axiom,
% 2.22/2.46    (![C:$i,B:$i,A:$i]:
% 2.22/2.46     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.22/2.46       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.22/2.46  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.22/2.46  thf(zf_stmt_5, axiom,
% 2.22/2.46    (![A:$i,B:$i,C:$i]:
% 2.22/2.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.22/2.46       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.22/2.46         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.22/2.46           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.22/2.46             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.22/2.46  thf('22', plain,
% 2.22/2.46      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.22/2.46         (~ (zip_tseitin_0 @ X31 @ X32)
% 2.22/2.46          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 2.22/2.46          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.22/2.46  thf('23', plain,
% 2.22/2.46      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 2.22/2.46      inference('sup-', [status(thm)], ['21', '22'])).
% 2.22/2.46  thf('24', plain,
% 2.22/2.46      (![X0 : $i]:
% 2.22/2.46         ((v5_relat_1 @ sk_C @ X0) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 2.22/2.46      inference('sup-', [status(thm)], ['20', '23'])).
% 2.22/2.46  thf('25', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.46  thf('26', plain,
% 2.22/2.46      (![X28 : $i, X29 : $i, X30 : $i]:
% 2.22/2.46         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 2.22/2.46          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 2.22/2.46          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.22/2.46  thf('27', plain,
% 2.22/2.46      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 2.22/2.46        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 2.22/2.46      inference('sup-', [status(thm)], ['25', '26'])).
% 2.22/2.46  thf('28', plain,
% 2.22/2.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.46  thf(redefinition_k1_relset_1, axiom,
% 2.22/2.46    (![A:$i,B:$i,C:$i]:
% 2.22/2.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.22/2.46       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.22/2.46  thf('29', plain,
% 2.22/2.46      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.22/2.46         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 2.22/2.46          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 2.22/2.46      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.22/2.46  thf('30', plain,
% 2.22/2.46      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 2.22/2.46      inference('sup-', [status(thm)], ['28', '29'])).
% 2.22/2.46  thf('31', plain,
% 2.22/2.46      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 2.22/2.46      inference('demod', [status(thm)], ['27', '30'])).
% 2.22/2.46  thf('32', plain,
% 2.22/2.46      (![X0 : $i]: ((v5_relat_1 @ sk_C @ X0) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 2.22/2.46      inference('sup-', [status(thm)], ['24', '31'])).
% 2.22/2.46  thf(d19_relat_1, axiom,
% 2.22/2.46    (![A:$i,B:$i]:
% 2.22/2.46     ( ( v1_relat_1 @ B ) =>
% 2.22/2.46       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 2.22/2.46  thf('33', plain,
% 2.22/2.46      (![X11 : $i, X12 : $i]:
% 2.22/2.46         (~ (v5_relat_1 @ X11 @ X12)
% 2.22/2.46          | (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 2.22/2.46          | ~ (v1_relat_1 @ X11))),
% 2.22/2.46      inference('cnf', [status(esa)], [d19_relat_1])).
% 2.22/2.46  thf('34', plain,
% 2.22/2.46      (![X0 : $i]:
% 2.22/2.46         (((sk_A) = (k1_relat_1 @ sk_C))
% 2.22/2.46          | ~ (v1_relat_1 @ sk_C)
% 2.22/2.46          | (r1_tarski @ (k2_relat_1 @ sk_C) @ X0))),
% 2.22/2.46      inference('sup-', [status(thm)], ['32', '33'])).
% 2.22/2.46  thf('35', plain,
% 2.22/2.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.46  thf(cc2_relat_1, axiom,
% 2.22/2.46    (![A:$i]:
% 2.22/2.46     ( ( v1_relat_1 @ A ) =>
% 2.22/2.46       ( ![B:$i]:
% 2.22/2.46         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.22/2.46  thf('36', plain,
% 2.22/2.46      (![X9 : $i, X10 : $i]:
% 2.22/2.46         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 2.22/2.46          | (v1_relat_1 @ X9)
% 2.22/2.46          | ~ (v1_relat_1 @ X10))),
% 2.22/2.46      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.22/2.46  thf('37', plain,
% 2.22/2.46      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 2.22/2.46      inference('sup-', [status(thm)], ['35', '36'])).
% 2.22/2.46  thf(fc6_relat_1, axiom,
% 2.22/2.46    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.22/2.46  thf('38', plain,
% 2.22/2.46      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 2.22/2.46      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.22/2.46  thf('39', plain, ((v1_relat_1 @ sk_C)),
% 2.22/2.46      inference('demod', [status(thm)], ['37', '38'])).
% 2.22/2.46  thf('40', plain,
% 2.22/2.46      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.46  thf(redefinition_k2_relset_1, axiom,
% 2.22/2.46    (![A:$i,B:$i,C:$i]:
% 2.22/2.46     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.22/2.46       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.22/2.46  thf('41', plain,
% 2.22/2.46      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.22/2.46         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 2.22/2.46          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 2.22/2.46      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.22/2.46  thf('42', plain,
% 2.22/2.46      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 2.22/2.46      inference('sup-', [status(thm)], ['40', '41'])).
% 2.22/2.46  thf('43', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.46  thf('44', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.22/2.46      inference('sup+', [status(thm)], ['42', '43'])).
% 2.22/2.46  thf('45', plain,
% 2.22/2.46      (![X0 : $i]: (((sk_A) = (k1_relat_1 @ sk_C)) | (r1_tarski @ sk_B @ X0))),
% 2.22/2.46      inference('demod', [status(thm)], ['34', '39', '44'])).
% 2.22/2.46  thf(d10_xboole_0, axiom,
% 2.22/2.46    (![A:$i,B:$i]:
% 2.22/2.46     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.22/2.46  thf('46', plain,
% 2.22/2.46      (![X0 : $i, X2 : $i]:
% 2.22/2.46         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.22/2.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.22/2.46  thf('47', plain,
% 2.22/2.46      (![X0 : $i]:
% 2.22/2.46         (((sk_A) = (k1_relat_1 @ sk_C))
% 2.22/2.46          | ~ (r1_tarski @ X0 @ sk_B)
% 2.22/2.46          | ((X0) = (sk_B)))),
% 2.22/2.46      inference('sup-', [status(thm)], ['45', '46'])).
% 2.22/2.46  thf('48', plain,
% 2.22/2.46      (![X0 : $i]:
% 2.22/2.46         ((zip_tseitin_0 @ sk_B @ X0)
% 2.22/2.46          | ((sk_C) = (sk_B))
% 2.22/2.46          | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 2.22/2.46      inference('sup-', [status(thm)], ['12', '47'])).
% 2.22/2.46  thf('49', plain,
% 2.22/2.46      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 2.22/2.46      inference('sup-', [status(thm)], ['21', '22'])).
% 2.22/2.46  thf('50', plain,
% 2.22/2.46      ((((sk_A) = (k1_relat_1 @ sk_C))
% 2.22/2.46        | ((sk_C) = (sk_B))
% 2.22/2.46        | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 2.22/2.46      inference('sup-', [status(thm)], ['48', '49'])).
% 2.22/2.46  thf('51', plain,
% 2.22/2.46      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 2.22/2.46      inference('demod', [status(thm)], ['27', '30'])).
% 2.22/2.46  thf('52', plain, ((((sk_C) = (sk_B)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 2.22/2.46      inference('clc', [status(thm)], ['50', '51'])).
% 2.22/2.46  thf(t55_funct_1, axiom,
% 2.22/2.46    (![A:$i]:
% 2.22/2.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.22/2.46       ( ( v2_funct_1 @ A ) =>
% 2.22/2.46         ( ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ ( k2_funct_1 @ A ) ) ) & 
% 2.22/2.46           ( ( k1_relat_1 @ A ) = ( k2_relat_1 @ ( k2_funct_1 @ A ) ) ) ) ) ))).
% 2.22/2.46  thf('53', plain,
% 2.22/2.46      (![X16 : $i]:
% 2.22/2.46         (~ (v2_funct_1 @ X16)
% 2.22/2.46          | ((k1_relat_1 @ X16) = (k2_relat_1 @ (k2_funct_1 @ X16)))
% 2.22/2.46          | ~ (v1_funct_1 @ X16)
% 2.22/2.46          | ~ (v1_relat_1 @ X16))),
% 2.22/2.46      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.22/2.46  thf('54', plain, ((((sk_C) = (sk_B)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 2.22/2.46      inference('clc', [status(thm)], ['50', '51'])).
% 2.22/2.46  thf(dt_k2_funct_1, axiom,
% 2.22/2.46    (![A:$i]:
% 2.22/2.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.22/2.46       ( ( v1_relat_1 @ ( k2_funct_1 @ A ) ) & 
% 2.22/2.46         ( v1_funct_1 @ ( k2_funct_1 @ A ) ) ) ))).
% 2.22/2.46  thf('55', plain,
% 2.22/2.46      (![X15 : $i]:
% 2.22/2.46         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 2.22/2.46          | ~ (v1_funct_1 @ X15)
% 2.22/2.46          | ~ (v1_relat_1 @ X15))),
% 2.22/2.46      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.22/2.46  thf('56', plain,
% 2.22/2.46      (![X15 : $i]:
% 2.22/2.46         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 2.22/2.46          | ~ (v1_funct_1 @ X15)
% 2.22/2.46          | ~ (v1_relat_1 @ X15))),
% 2.22/2.46      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.22/2.46  thf('57', plain,
% 2.22/2.46      (![X16 : $i]:
% 2.22/2.46         (~ (v2_funct_1 @ X16)
% 2.22/2.46          | ((k1_relat_1 @ X16) = (k2_relat_1 @ (k2_funct_1 @ X16)))
% 2.22/2.46          | ~ (v1_funct_1 @ X16)
% 2.22/2.46          | ~ (v1_relat_1 @ X16))),
% 2.22/2.46      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.22/2.46  thf('58', plain,
% 2.22/2.46      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 2.22/2.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.22/2.46  thf('59', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.22/2.46      inference('simplify', [status(thm)], ['58'])).
% 2.22/2.46  thf('60', plain,
% 2.22/2.46      (![X11 : $i, X12 : $i]:
% 2.22/2.46         (~ (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 2.22/2.46          | (v5_relat_1 @ X11 @ X12)
% 2.22/2.46          | ~ (v1_relat_1 @ X11))),
% 2.22/2.46      inference('cnf', [status(esa)], [d19_relat_1])).
% 2.22/2.46  thf('61', plain,
% 2.22/2.46      (![X0 : $i]:
% 2.22/2.46         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 2.22/2.46      inference('sup-', [status(thm)], ['59', '60'])).
% 2.22/2.46  thf('62', plain,
% 2.22/2.46      (![X0 : $i]:
% 2.22/2.46         ((v5_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 2.22/2.46          | ~ (v1_relat_1 @ X0)
% 2.22/2.46          | ~ (v1_funct_1 @ X0)
% 2.22/2.46          | ~ (v2_funct_1 @ X0)
% 2.22/2.46          | ~ (v1_relat_1 @ (k2_funct_1 @ X0)))),
% 2.22/2.46      inference('sup+', [status(thm)], ['57', '61'])).
% 2.22/2.46  thf('63', plain,
% 2.22/2.46      (![X0 : $i]:
% 2.22/2.46         (~ (v1_relat_1 @ X0)
% 2.22/2.46          | ~ (v1_funct_1 @ X0)
% 2.22/2.46          | ~ (v2_funct_1 @ X0)
% 2.22/2.46          | ~ (v1_funct_1 @ X0)
% 2.22/2.46          | ~ (v1_relat_1 @ X0)
% 2.22/2.46          | (v5_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0)))),
% 2.22/2.46      inference('sup-', [status(thm)], ['56', '62'])).
% 2.22/2.46  thf('64', plain,
% 2.22/2.46      (![X0 : $i]:
% 2.22/2.46         ((v5_relat_1 @ (k2_funct_1 @ X0) @ (k1_relat_1 @ X0))
% 2.22/2.46          | ~ (v2_funct_1 @ X0)
% 2.22/2.46          | ~ (v1_funct_1 @ X0)
% 2.22/2.46          | ~ (v1_relat_1 @ X0))),
% 2.22/2.46      inference('simplify', [status(thm)], ['63'])).
% 2.22/2.46  thf('65', plain,
% 2.22/2.46      (![X11 : $i, X12 : $i]:
% 2.22/2.46         (~ (v5_relat_1 @ X11 @ X12)
% 2.22/2.46          | (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 2.22/2.46          | ~ (v1_relat_1 @ X11))),
% 2.22/2.46      inference('cnf', [status(esa)], [d19_relat_1])).
% 2.22/2.46  thf('66', plain,
% 2.22/2.46      (![X0 : $i]:
% 2.22/2.46         (~ (v1_relat_1 @ X0)
% 2.22/2.46          | ~ (v1_funct_1 @ X0)
% 2.22/2.46          | ~ (v2_funct_1 @ X0)
% 2.22/2.46          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.22/2.46          | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 2.22/2.46      inference('sup-', [status(thm)], ['64', '65'])).
% 2.22/2.46  thf('67', plain,
% 2.22/2.46      (![X0 : $i]:
% 2.22/2.46         (~ (v1_relat_1 @ X0)
% 2.22/2.46          | ~ (v1_funct_1 @ X0)
% 2.22/2.46          | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 2.22/2.46          | ~ (v2_funct_1 @ X0)
% 2.22/2.46          | ~ (v1_funct_1 @ X0)
% 2.22/2.46          | ~ (v1_relat_1 @ X0))),
% 2.22/2.46      inference('sup-', [status(thm)], ['55', '66'])).
% 2.22/2.46  thf('68', plain,
% 2.22/2.46      (![X0 : $i]:
% 2.22/2.46         (~ (v2_funct_1 @ X0)
% 2.22/2.46          | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 2.22/2.46          | ~ (v1_funct_1 @ X0)
% 2.22/2.46          | ~ (v1_relat_1 @ X0))),
% 2.22/2.46      inference('simplify', [status(thm)], ['67'])).
% 2.22/2.46  thf('69', plain,
% 2.22/2.46      (((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)
% 2.22/2.46        | ((sk_C) = (sk_B))
% 2.22/2.46        | ~ (v1_relat_1 @ sk_C)
% 2.22/2.46        | ~ (v1_funct_1 @ sk_C)
% 2.22/2.46        | ~ (v2_funct_1 @ sk_C))),
% 2.22/2.46      inference('sup+', [status(thm)], ['54', '68'])).
% 2.22/2.46  thf('70', plain, ((v1_relat_1 @ sk_C)),
% 2.22/2.46      inference('demod', [status(thm)], ['37', '38'])).
% 2.22/2.46  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.46  thf('72', plain, ((v2_funct_1 @ sk_C)),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.46  thf('73', plain,
% 2.22/2.46      (((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)
% 2.22/2.46        | ((sk_C) = (sk_B)))),
% 2.22/2.46      inference('demod', [status(thm)], ['69', '70', '71', '72'])).
% 2.22/2.46  thf('74', plain,
% 2.22/2.46      (![X0 : $i, X2 : $i]:
% 2.22/2.46         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.22/2.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.22/2.46  thf('75', plain,
% 2.22/2.46      ((((sk_C) = (sk_B))
% 2.22/2.46        | ~ (r1_tarski @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.22/2.46        | ((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 2.22/2.46      inference('sup-', [status(thm)], ['73', '74'])).
% 2.22/2.46  thf('76', plain,
% 2.22/2.46      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))
% 2.22/2.46        | ~ (v1_relat_1 @ sk_C)
% 2.22/2.46        | ~ (v1_funct_1 @ sk_C)
% 2.22/2.46        | ~ (v2_funct_1 @ sk_C)
% 2.22/2.46        | ((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.22/2.46        | ((sk_C) = (sk_B)))),
% 2.22/2.46      inference('sup-', [status(thm)], ['53', '75'])).
% 2.22/2.46  thf('77', plain, ((v1_relat_1 @ sk_C)),
% 2.22/2.46      inference('demod', [status(thm)], ['37', '38'])).
% 2.22/2.46  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.46  thf('79', plain, ((v2_funct_1 @ sk_C)),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.46  thf('80', plain,
% 2.22/2.46      ((~ (r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))
% 2.22/2.46        | ((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.22/2.46        | ((sk_C) = (sk_B)))),
% 2.22/2.46      inference('demod', [status(thm)], ['76', '77', '78', '79'])).
% 2.22/2.46  thf('81', plain,
% 2.22/2.46      ((~ (r1_tarski @ sk_A @ sk_A)
% 2.22/2.46        | ((sk_C) = (sk_B))
% 2.22/2.46        | ((sk_C) = (sk_B))
% 2.22/2.46        | ((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 2.22/2.46      inference('sup-', [status(thm)], ['52', '80'])).
% 2.22/2.46  thf('82', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.22/2.46      inference('simplify', [status(thm)], ['58'])).
% 2.22/2.46  thf('83', plain,
% 2.22/2.46      ((((sk_C) = (sk_B))
% 2.22/2.46        | ((sk_C) = (sk_B))
% 2.22/2.46        | ((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))),
% 2.22/2.46      inference('demod', [status(thm)], ['81', '82'])).
% 2.22/2.46  thf('84', plain,
% 2.22/2.46      ((((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))) | ((sk_C) = (sk_B)))),
% 2.22/2.46      inference('simplify', [status(thm)], ['83'])).
% 2.22/2.46  thf('85', plain,
% 2.22/2.46      (![X15 : $i]:
% 2.22/2.46         ((v1_funct_1 @ (k2_funct_1 @ X15))
% 2.22/2.46          | ~ (v1_funct_1 @ X15)
% 2.22/2.46          | ~ (v1_relat_1 @ X15))),
% 2.22/2.46      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.22/2.46  thf('86', plain,
% 2.22/2.46      (![X15 : $i]:
% 2.22/2.46         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 2.22/2.46          | ~ (v1_funct_1 @ X15)
% 2.22/2.46          | ~ (v1_relat_1 @ X15))),
% 2.22/2.46      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.22/2.46  thf('87', plain,
% 2.22/2.46      (![X16 : $i]:
% 2.22/2.46         (~ (v2_funct_1 @ X16)
% 2.22/2.46          | ((k2_relat_1 @ X16) = (k1_relat_1 @ (k2_funct_1 @ X16)))
% 2.22/2.46          | ~ (v1_funct_1 @ X16)
% 2.22/2.46          | ~ (v1_relat_1 @ X16))),
% 2.22/2.46      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.22/2.46  thf(t3_funct_2, axiom,
% 2.22/2.46    (![A:$i]:
% 2.22/2.46     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 2.22/2.46       ( ( v1_funct_1 @ A ) & 
% 2.22/2.46         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 2.22/2.46         ( m1_subset_1 @
% 2.22/2.46           A @ 
% 2.22/2.46           ( k1_zfmisc_1 @
% 2.22/2.46             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 2.22/2.46  thf('88', plain,
% 2.22/2.46      (![X34 : $i]:
% 2.22/2.46         ((v1_funct_2 @ X34 @ (k1_relat_1 @ X34) @ (k2_relat_1 @ X34))
% 2.22/2.46          | ~ (v1_funct_1 @ X34)
% 2.22/2.46          | ~ (v1_relat_1 @ X34))),
% 2.22/2.46      inference('cnf', [status(esa)], [t3_funct_2])).
% 2.22/2.46  thf('89', plain,
% 2.22/2.46      (![X0 : $i]:
% 2.22/2.46         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.22/2.46           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.22/2.46          | ~ (v1_relat_1 @ X0)
% 2.22/2.46          | ~ (v1_funct_1 @ X0)
% 2.22/2.46          | ~ (v2_funct_1 @ X0)
% 2.22/2.46          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.22/2.46          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 2.22/2.46      inference('sup+', [status(thm)], ['87', '88'])).
% 2.22/2.46  thf('90', plain,
% 2.22/2.46      (![X0 : $i]:
% 2.22/2.46         (~ (v1_relat_1 @ X0)
% 2.22/2.46          | ~ (v1_funct_1 @ X0)
% 2.22/2.46          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.22/2.46          | ~ (v2_funct_1 @ X0)
% 2.22/2.46          | ~ (v1_funct_1 @ X0)
% 2.22/2.46          | ~ (v1_relat_1 @ X0)
% 2.22/2.46          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.22/2.46             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 2.22/2.46      inference('sup-', [status(thm)], ['86', '89'])).
% 2.22/2.46  thf('91', plain,
% 2.22/2.46      (![X0 : $i]:
% 2.22/2.46         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.22/2.46           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.22/2.46          | ~ (v2_funct_1 @ X0)
% 2.22/2.46          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.22/2.46          | ~ (v1_funct_1 @ X0)
% 2.22/2.46          | ~ (v1_relat_1 @ X0))),
% 2.22/2.46      inference('simplify', [status(thm)], ['90'])).
% 2.22/2.46  thf('92', plain,
% 2.22/2.46      (![X0 : $i]:
% 2.22/2.46         (~ (v1_relat_1 @ X0)
% 2.22/2.46          | ~ (v1_funct_1 @ X0)
% 2.22/2.46          | ~ (v1_relat_1 @ X0)
% 2.22/2.46          | ~ (v1_funct_1 @ X0)
% 2.22/2.46          | ~ (v2_funct_1 @ X0)
% 2.22/2.46          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.22/2.46             (k2_relat_1 @ (k2_funct_1 @ X0))))),
% 2.22/2.46      inference('sup-', [status(thm)], ['85', '91'])).
% 2.22/2.46  thf('93', plain,
% 2.22/2.46      (![X0 : $i]:
% 2.22/2.46         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.22/2.46           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.22/2.46          | ~ (v2_funct_1 @ X0)
% 2.22/2.46          | ~ (v1_funct_1 @ X0)
% 2.22/2.46          | ~ (v1_relat_1 @ X0))),
% 2.22/2.46      inference('simplify', [status(thm)], ['92'])).
% 2.22/2.46  thf('94', plain,
% 2.22/2.46      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ (k2_relat_1 @ sk_C) @ sk_A)
% 2.22/2.46        | ((sk_C) = (sk_B))
% 2.22/2.46        | ~ (v1_relat_1 @ sk_C)
% 2.22/2.46        | ~ (v1_funct_1 @ sk_C)
% 2.22/2.46        | ~ (v2_funct_1 @ sk_C))),
% 2.22/2.46      inference('sup+', [status(thm)], ['84', '93'])).
% 2.22/2.46  thf('95', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.22/2.46      inference('sup+', [status(thm)], ['42', '43'])).
% 2.22/2.46  thf('96', plain, ((v1_relat_1 @ sk_C)),
% 2.22/2.46      inference('demod', [status(thm)], ['37', '38'])).
% 2.22/2.46  thf('97', plain, ((v1_funct_1 @ sk_C)),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.46  thf('98', plain, ((v2_funct_1 @ sk_C)),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.46  thf('99', plain,
% 2.22/2.46      (((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A) | ((sk_C) = (sk_B)))),
% 2.22/2.46      inference('demod', [status(thm)], ['94', '95', '96', '97', '98'])).
% 2.22/2.46  thf('100', plain,
% 2.22/2.46      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))
% 2.22/2.46         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.46      inference('split', [status(esa)], ['0'])).
% 2.22/2.46  thf('101', plain,
% 2.22/2.46      ((((sk_C) = (sk_B)))
% 2.22/2.46         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.46      inference('sup-', [status(thm)], ['99', '100'])).
% 2.22/2.46  thf('102', plain,
% 2.22/2.46      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_B @ sk_A))
% 2.22/2.46         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.46      inference('demod', [status(thm)], ['1', '101'])).
% 2.22/2.46  thf('103', plain,
% 2.22/2.46      ((((sk_C) = (sk_B)))
% 2.22/2.46         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.46      inference('sup-', [status(thm)], ['99', '100'])).
% 2.22/2.46  thf('104', plain,
% 2.22/2.46      (![X26 : $i, X27 : $i]:
% 2.22/2.46         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.22/2.46  thf('105', plain,
% 2.22/2.46      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 2.22/2.46      inference('sup-', [status(thm)], ['21', '22'])).
% 2.22/2.46  thf('106', plain,
% 2.22/2.46      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 2.22/2.46      inference('sup-', [status(thm)], ['104', '105'])).
% 2.22/2.46  thf('107', plain,
% 2.22/2.46      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 2.22/2.46      inference('demod', [status(thm)], ['27', '30'])).
% 2.22/2.46  thf('108', plain,
% 2.22/2.46      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 2.22/2.46      inference('sup-', [status(thm)], ['106', '107'])).
% 2.22/2.46  thf('109', plain,
% 2.22/2.46      (((((sk_A) = (k1_relat_1 @ sk_B)) | ((sk_B) = (k1_xboole_0))))
% 2.22/2.46         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.46      inference('sup+', [status(thm)], ['103', '108'])).
% 2.22/2.46  thf('110', plain,
% 2.22/2.46      (![X16 : $i]:
% 2.22/2.46         (~ (v2_funct_1 @ X16)
% 2.22/2.46          | ((k1_relat_1 @ X16) = (k2_relat_1 @ (k2_funct_1 @ X16)))
% 2.22/2.46          | ~ (v1_funct_1 @ X16)
% 2.22/2.46          | ~ (v1_relat_1 @ X16))),
% 2.22/2.46      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.22/2.46  thf('111', plain,
% 2.22/2.46      (![X0 : $i]:
% 2.22/2.46         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.22/2.46           (k2_relat_1 @ (k2_funct_1 @ X0)))
% 2.22/2.46          | ~ (v2_funct_1 @ X0)
% 2.22/2.46          | ~ (v1_funct_1 @ X0)
% 2.22/2.46          | ~ (v1_relat_1 @ X0))),
% 2.22/2.46      inference('simplify', [status(thm)], ['92'])).
% 2.22/2.46  thf('112', plain,
% 2.22/2.46      (![X0 : $i]:
% 2.22/2.46         ((v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.22/2.46           (k1_relat_1 @ X0))
% 2.22/2.46          | ~ (v1_relat_1 @ X0)
% 2.22/2.46          | ~ (v1_funct_1 @ X0)
% 2.22/2.46          | ~ (v2_funct_1 @ X0)
% 2.22/2.46          | ~ (v1_relat_1 @ X0)
% 2.22/2.46          | ~ (v1_funct_1 @ X0)
% 2.22/2.46          | ~ (v2_funct_1 @ X0))),
% 2.22/2.46      inference('sup+', [status(thm)], ['110', '111'])).
% 2.22/2.46  thf('113', plain,
% 2.22/2.46      (![X0 : $i]:
% 2.22/2.46         (~ (v2_funct_1 @ X0)
% 2.22/2.46          | ~ (v1_funct_1 @ X0)
% 2.22/2.46          | ~ (v1_relat_1 @ X0)
% 2.22/2.46          | (v1_funct_2 @ (k2_funct_1 @ X0) @ (k2_relat_1 @ X0) @ 
% 2.22/2.46             (k1_relat_1 @ X0)))),
% 2.22/2.46      inference('simplify', [status(thm)], ['112'])).
% 2.22/2.46  thf('114', plain,
% 2.22/2.46      ((((v1_funct_2 @ (k2_funct_1 @ sk_B) @ (k2_relat_1 @ sk_B) @ sk_A)
% 2.22/2.46         | ((sk_B) = (k1_xboole_0))
% 2.22/2.46         | ~ (v1_relat_1 @ sk_B)
% 2.22/2.46         | ~ (v1_funct_1 @ sk_B)
% 2.22/2.46         | ~ (v2_funct_1 @ sk_B)))
% 2.22/2.46         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.46      inference('sup+', [status(thm)], ['109', '113'])).
% 2.22/2.46  thf('115', plain,
% 2.22/2.46      ((((sk_C) = (sk_B)))
% 2.22/2.46         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.46      inference('sup-', [status(thm)], ['99', '100'])).
% 2.22/2.46  thf('116', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.22/2.46      inference('sup+', [status(thm)], ['42', '43'])).
% 2.22/2.46  thf('117', plain,
% 2.22/2.46      ((((k2_relat_1 @ sk_B) = (sk_B)))
% 2.22/2.46         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.46      inference('sup+', [status(thm)], ['115', '116'])).
% 2.22/2.46  thf('118', plain,
% 2.22/2.46      ((((sk_C) = (sk_B)))
% 2.22/2.46         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.46      inference('sup-', [status(thm)], ['99', '100'])).
% 2.22/2.46  thf('119', plain, ((v1_relat_1 @ sk_C)),
% 2.22/2.46      inference('demod', [status(thm)], ['37', '38'])).
% 2.22/2.46  thf('120', plain,
% 2.22/2.46      (((v1_relat_1 @ sk_B))
% 2.22/2.46         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.46      inference('sup+', [status(thm)], ['118', '119'])).
% 2.22/2.46  thf('121', plain,
% 2.22/2.46      ((((sk_C) = (sk_B)))
% 2.22/2.46         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.46      inference('sup-', [status(thm)], ['99', '100'])).
% 2.22/2.46  thf('122', plain, ((v1_funct_1 @ sk_C)),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.46  thf('123', plain,
% 2.22/2.46      (((v1_funct_1 @ sk_B))
% 2.22/2.46         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.46      inference('sup+', [status(thm)], ['121', '122'])).
% 2.22/2.46  thf('124', plain,
% 2.22/2.46      ((((sk_C) = (sk_B)))
% 2.22/2.46         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.46      inference('sup-', [status(thm)], ['99', '100'])).
% 2.22/2.46  thf('125', plain, ((v2_funct_1 @ sk_C)),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.46  thf('126', plain,
% 2.22/2.46      (((v2_funct_1 @ sk_B))
% 2.22/2.46         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.46      inference('sup+', [status(thm)], ['124', '125'])).
% 2.22/2.46  thf('127', plain,
% 2.22/2.46      ((((v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_B @ sk_A)
% 2.22/2.46         | ((sk_B) = (k1_xboole_0))))
% 2.22/2.46         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.46      inference('demod', [status(thm)], ['114', '117', '120', '123', '126'])).
% 2.22/2.46  thf('128', plain,
% 2.22/2.46      ((~ (v1_funct_2 @ (k2_funct_1 @ sk_B) @ sk_B @ sk_A))
% 2.22/2.46         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.46      inference('demod', [status(thm)], ['1', '101'])).
% 2.22/2.46  thf('129', plain,
% 2.22/2.46      ((((sk_B) = (k1_xboole_0)))
% 2.22/2.46         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.46      inference('clc', [status(thm)], ['127', '128'])).
% 2.22/2.46  thf('130', plain,
% 2.22/2.46      ((((sk_B) = (k1_xboole_0)))
% 2.22/2.46         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.46      inference('clc', [status(thm)], ['127', '128'])).
% 2.22/2.46  thf('131', plain,
% 2.22/2.46      ((~ (v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0 @ sk_A))
% 2.22/2.46         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.46      inference('demod', [status(thm)], ['102', '129', '130'])).
% 2.22/2.46  thf('132', plain, ((v1_relat_1 @ sk_C)),
% 2.22/2.46      inference('demod', [status(thm)], ['37', '38'])).
% 2.22/2.46  thf('133', plain,
% 2.22/2.46      (![X15 : $i]:
% 2.22/2.46         ((v1_funct_1 @ (k2_funct_1 @ X15))
% 2.22/2.46          | ~ (v1_funct_1 @ X15)
% 2.22/2.46          | ~ (v1_relat_1 @ X15))),
% 2.22/2.46      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.22/2.46  thf('134', plain,
% 2.22/2.46      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C)))
% 2.22/2.46         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 2.22/2.46      inference('split', [status(esa)], ['0'])).
% 2.22/2.46  thf('135', plain,
% 2.22/2.46      (((~ (v1_relat_1 @ sk_C) | ~ (v1_funct_1 @ sk_C)))
% 2.22/2.46         <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 2.22/2.46      inference('sup-', [status(thm)], ['133', '134'])).
% 2.22/2.46  thf('136', plain, ((v1_funct_1 @ sk_C)),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.46  thf('137', plain,
% 2.22/2.46      ((~ (v1_relat_1 @ sk_C)) <= (~ ((v1_funct_1 @ (k2_funct_1 @ sk_C))))),
% 2.22/2.46      inference('demod', [status(thm)], ['135', '136'])).
% 2.22/2.46  thf('138', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.22/2.46      inference('sup-', [status(thm)], ['132', '137'])).
% 2.22/2.46  thf('139', plain,
% 2.22/2.46      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.46           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 2.22/2.46         <= (~
% 2.22/2.46             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.46               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.22/2.46      inference('split', [status(esa)], ['0'])).
% 2.22/2.46  thf('140', plain,
% 2.22/2.46      (![X16 : $i]:
% 2.22/2.46         (~ (v2_funct_1 @ X16)
% 2.22/2.46          | ((k1_relat_1 @ X16) = (k2_relat_1 @ (k2_funct_1 @ X16)))
% 2.22/2.46          | ~ (v1_funct_1 @ X16)
% 2.22/2.46          | ~ (v1_relat_1 @ X16))),
% 2.22/2.46      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.22/2.46  thf('141', plain,
% 2.22/2.46      (![X16 : $i]:
% 2.22/2.46         (~ (v2_funct_1 @ X16)
% 2.22/2.46          | ((k2_relat_1 @ X16) = (k1_relat_1 @ (k2_funct_1 @ X16)))
% 2.22/2.46          | ~ (v1_funct_1 @ X16)
% 2.22/2.46          | ~ (v1_relat_1 @ X16))),
% 2.22/2.46      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.22/2.46  thf('142', plain,
% 2.22/2.46      (![X15 : $i]:
% 2.22/2.46         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 2.22/2.46          | ~ (v1_funct_1 @ X15)
% 2.22/2.46          | ~ (v1_relat_1 @ X15))),
% 2.22/2.46      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.22/2.46  thf('143', plain,
% 2.22/2.46      (![X15 : $i]:
% 2.22/2.46         ((v1_funct_1 @ (k2_funct_1 @ X15))
% 2.22/2.46          | ~ (v1_funct_1 @ X15)
% 2.22/2.46          | ~ (v1_relat_1 @ X15))),
% 2.22/2.46      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.22/2.46  thf('144', plain,
% 2.22/2.46      (![X26 : $i, X27 : $i]:
% 2.22/2.46         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.22/2.46  thf('145', plain,
% 2.22/2.46      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 2.22/2.46      inference('simplify', [status(thm)], ['16'])).
% 2.22/2.46  thf('146', plain,
% 2.22/2.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.22/2.46         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 2.22/2.46      inference('sup+', [status(thm)], ['144', '145'])).
% 2.22/2.46  thf('147', plain,
% 2.22/2.46      (![X34 : $i]:
% 2.22/2.46         ((m1_subset_1 @ X34 @ 
% 2.22/2.46           (k1_zfmisc_1 @ 
% 2.22/2.46            (k2_zfmisc_1 @ (k1_relat_1 @ X34) @ (k2_relat_1 @ X34))))
% 2.22/2.46          | ~ (v1_funct_1 @ X34)
% 2.22/2.46          | ~ (v1_relat_1 @ X34))),
% 2.22/2.46      inference('cnf', [status(esa)], [t3_funct_2])).
% 2.22/2.46  thf('148', plain,
% 2.22/2.46      (![X0 : $i, X1 : $i]:
% 2.22/2.46         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.22/2.46          | (zip_tseitin_0 @ (k1_relat_1 @ X0) @ X1)
% 2.22/2.46          | ~ (v1_relat_1 @ X0)
% 2.22/2.46          | ~ (v1_funct_1 @ X0))),
% 2.22/2.46      inference('sup+', [status(thm)], ['146', '147'])).
% 2.22/2.46  thf('149', plain,
% 2.22/2.46      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.22/2.46         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 2.22/2.46      inference('sup+', [status(thm)], ['144', '145'])).
% 2.22/2.46  thf('150', plain,
% 2.22/2.46      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 2.22/2.46      inference('sup-', [status(thm)], ['21', '22'])).
% 2.22/2.46  thf('151', plain,
% 2.22/2.46      (![X0 : $i]:
% 2.22/2.46         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 2.22/2.46          | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 2.22/2.46      inference('sup-', [status(thm)], ['149', '150'])).
% 2.22/2.46  thf('152', plain,
% 2.22/2.46      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 2.22/2.46      inference('demod', [status(thm)], ['27', '30'])).
% 2.22/2.46  thf('153', plain,
% 2.22/2.46      (![X0 : $i]:
% 2.22/2.46         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 2.22/2.46          | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 2.22/2.46      inference('sup-', [status(thm)], ['151', '152'])).
% 2.22/2.46  thf('154', plain,
% 2.22/2.46      ((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.46           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 2.22/2.46         <= (~
% 2.22/2.46             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.46               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.22/2.46      inference('split', [status(esa)], ['0'])).
% 2.22/2.46  thf('155', plain,
% 2.22/2.46      (((~ (m1_subset_1 @ (k2_funct_1 @ sk_C) @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.22/2.46         | ((sk_A) = (k1_relat_1 @ sk_C))))
% 2.22/2.46         <= (~
% 2.22/2.46             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.46               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.22/2.46      inference('sup-', [status(thm)], ['153', '154'])).
% 2.22/2.46  thf('156', plain,
% 2.22/2.46      ((![X0 : $i]:
% 2.22/2.46          (~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 2.22/2.46           | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))
% 2.22/2.46           | (zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 2.22/2.46           | ((sk_A) = (k1_relat_1 @ sk_C))))
% 2.22/2.46         <= (~
% 2.22/2.46             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.46               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.22/2.46      inference('sup-', [status(thm)], ['148', '155'])).
% 2.22/2.46  thf('157', plain,
% 2.22/2.46      ((![X0 : $i]:
% 2.22/2.46          (~ (v1_relat_1 @ sk_C)
% 2.22/2.46           | ~ (v1_funct_1 @ sk_C)
% 2.22/2.46           | ((sk_A) = (k1_relat_1 @ sk_C))
% 2.22/2.46           | (zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 2.22/2.46           | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))))
% 2.22/2.46         <= (~
% 2.22/2.46             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.46               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.22/2.46      inference('sup-', [status(thm)], ['143', '156'])).
% 2.22/2.46  thf('158', plain, ((v1_relat_1 @ sk_C)),
% 2.22/2.46      inference('demod', [status(thm)], ['37', '38'])).
% 2.22/2.46  thf('159', plain, ((v1_funct_1 @ sk_C)),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.46  thf('160', plain,
% 2.22/2.46      ((![X0 : $i]:
% 2.22/2.46          (((sk_A) = (k1_relat_1 @ sk_C))
% 2.22/2.46           | (zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 2.22/2.46           | ~ (v1_relat_1 @ (k2_funct_1 @ sk_C))))
% 2.22/2.46         <= (~
% 2.22/2.46             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.46               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.22/2.46      inference('demod', [status(thm)], ['157', '158', '159'])).
% 2.22/2.46  thf('161', plain,
% 2.22/2.46      ((![X0 : $i]:
% 2.22/2.46          (~ (v1_relat_1 @ sk_C)
% 2.22/2.46           | ~ (v1_funct_1 @ sk_C)
% 2.22/2.46           | (zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 2.22/2.46           | ((sk_A) = (k1_relat_1 @ sk_C))))
% 2.22/2.46         <= (~
% 2.22/2.46             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.46               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.22/2.46      inference('sup-', [status(thm)], ['142', '160'])).
% 2.22/2.46  thf('162', plain, ((v1_relat_1 @ sk_C)),
% 2.22/2.46      inference('demod', [status(thm)], ['37', '38'])).
% 2.22/2.46  thf('163', plain, ((v1_funct_1 @ sk_C)),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.46  thf('164', plain,
% 2.22/2.46      ((![X0 : $i]:
% 2.22/2.46          ((zip_tseitin_0 @ (k1_relat_1 @ (k2_funct_1 @ sk_C)) @ X0)
% 2.22/2.46           | ((sk_A) = (k1_relat_1 @ sk_C))))
% 2.22/2.46         <= (~
% 2.22/2.46             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.46               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.22/2.46      inference('demod', [status(thm)], ['161', '162', '163'])).
% 2.22/2.46  thf('165', plain,
% 2.22/2.46      ((![X0 : $i]:
% 2.22/2.46          ((zip_tseitin_0 @ (k2_relat_1 @ sk_C) @ X0)
% 2.22/2.46           | ~ (v1_relat_1 @ sk_C)
% 2.22/2.46           | ~ (v1_funct_1 @ sk_C)
% 2.22/2.46           | ~ (v2_funct_1 @ sk_C)
% 2.22/2.46           | ((sk_A) = (k1_relat_1 @ sk_C))))
% 2.22/2.46         <= (~
% 2.22/2.46             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.46               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.22/2.46      inference('sup+', [status(thm)], ['141', '164'])).
% 2.22/2.46  thf('166', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.22/2.46      inference('sup+', [status(thm)], ['42', '43'])).
% 2.22/2.46  thf('167', plain, ((v1_relat_1 @ sk_C)),
% 2.22/2.46      inference('demod', [status(thm)], ['37', '38'])).
% 2.22/2.46  thf('168', plain, ((v1_funct_1 @ sk_C)),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.46  thf('169', plain, ((v2_funct_1 @ sk_C)),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.46  thf('170', plain,
% 2.22/2.46      ((![X0 : $i]:
% 2.22/2.46          ((zip_tseitin_0 @ sk_B @ X0) | ((sk_A) = (k1_relat_1 @ sk_C))))
% 2.22/2.46         <= (~
% 2.22/2.46             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.46               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.22/2.46      inference('demod', [status(thm)], ['165', '166', '167', '168', '169'])).
% 2.22/2.46  thf('171', plain,
% 2.22/2.46      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 2.22/2.46      inference('sup-', [status(thm)], ['21', '22'])).
% 2.22/2.46  thf('172', plain,
% 2.22/2.46      (((((sk_A) = (k1_relat_1 @ sk_C)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)))
% 2.22/2.46         <= (~
% 2.22/2.46             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.46               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.22/2.46      inference('sup-', [status(thm)], ['170', '171'])).
% 2.22/2.46  thf('173', plain,
% 2.22/2.46      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 2.22/2.46      inference('demod', [status(thm)], ['27', '30'])).
% 2.22/2.46  thf('174', plain,
% 2.22/2.46      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 2.22/2.46         <= (~
% 2.22/2.46             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.46               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.22/2.46      inference('clc', [status(thm)], ['172', '173'])).
% 2.22/2.46  thf('175', plain,
% 2.22/2.46      (![X0 : $i]:
% 2.22/2.46         (~ (v2_funct_1 @ X0)
% 2.22/2.46          | (r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ X0)) @ (k1_relat_1 @ X0))
% 2.22/2.46          | ~ (v1_funct_1 @ X0)
% 2.22/2.46          | ~ (v1_relat_1 @ X0))),
% 2.22/2.46      inference('simplify', [status(thm)], ['67'])).
% 2.22/2.46  thf('176', plain,
% 2.22/2.46      ((((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A)
% 2.22/2.46         | ~ (v1_relat_1 @ sk_C)
% 2.22/2.46         | ~ (v1_funct_1 @ sk_C)
% 2.22/2.46         | ~ (v2_funct_1 @ sk_C)))
% 2.22/2.46         <= (~
% 2.22/2.46             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.46               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.22/2.46      inference('sup+', [status(thm)], ['174', '175'])).
% 2.22/2.46  thf('177', plain, ((v1_relat_1 @ sk_C)),
% 2.22/2.46      inference('demod', [status(thm)], ['37', '38'])).
% 2.22/2.46  thf('178', plain, ((v1_funct_1 @ sk_C)),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.46  thf('179', plain, ((v2_funct_1 @ sk_C)),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.46  thf('180', plain,
% 2.22/2.46      (((r1_tarski @ (k2_relat_1 @ (k2_funct_1 @ sk_C)) @ sk_A))
% 2.22/2.46         <= (~
% 2.22/2.46             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.46               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.22/2.46      inference('demod', [status(thm)], ['176', '177', '178', '179'])).
% 2.22/2.46  thf('181', plain,
% 2.22/2.46      (![X0 : $i, X2 : $i]:
% 2.22/2.46         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.22/2.46      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.22/2.46  thf('182', plain,
% 2.22/2.46      (((~ (r1_tarski @ sk_A @ (k2_relat_1 @ (k2_funct_1 @ sk_C)))
% 2.22/2.46         | ((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))))
% 2.22/2.46         <= (~
% 2.22/2.46             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.46               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.22/2.46      inference('sup-', [status(thm)], ['180', '181'])).
% 2.22/2.46  thf('183', plain,
% 2.22/2.46      (((~ (r1_tarski @ sk_A @ (k1_relat_1 @ sk_C))
% 2.22/2.46         | ~ (v1_relat_1 @ sk_C)
% 2.22/2.46         | ~ (v1_funct_1 @ sk_C)
% 2.22/2.46         | ~ (v2_funct_1 @ sk_C)
% 2.22/2.46         | ((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C)))))
% 2.22/2.46         <= (~
% 2.22/2.46             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.46               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.22/2.46      inference('sup-', [status(thm)], ['140', '182'])).
% 2.22/2.46  thf('184', plain,
% 2.22/2.46      ((((sk_A) = (k1_relat_1 @ sk_C)))
% 2.22/2.46         <= (~
% 2.22/2.46             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.46               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.22/2.46      inference('clc', [status(thm)], ['172', '173'])).
% 2.22/2.46  thf('185', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.22/2.46      inference('simplify', [status(thm)], ['58'])).
% 2.22/2.46  thf('186', plain, ((v1_relat_1 @ sk_C)),
% 2.22/2.46      inference('demod', [status(thm)], ['37', '38'])).
% 2.22/2.46  thf('187', plain, ((v1_funct_1 @ sk_C)),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.46  thf('188', plain, ((v2_funct_1 @ sk_C)),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.46  thf('189', plain,
% 2.22/2.46      ((((sk_A) = (k2_relat_1 @ (k2_funct_1 @ sk_C))))
% 2.22/2.46         <= (~
% 2.22/2.46             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.46               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.22/2.46      inference('demod', [status(thm)],
% 2.22/2.46                ['183', '184', '185', '186', '187', '188'])).
% 2.22/2.46  thf('190', plain,
% 2.22/2.46      (![X15 : $i]:
% 2.22/2.46         ((v1_funct_1 @ (k2_funct_1 @ X15))
% 2.22/2.46          | ~ (v1_funct_1 @ X15)
% 2.22/2.46          | ~ (v1_relat_1 @ X15))),
% 2.22/2.46      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.22/2.46  thf('191', plain,
% 2.22/2.46      (![X15 : $i]:
% 2.22/2.46         ((v1_relat_1 @ (k2_funct_1 @ X15))
% 2.22/2.46          | ~ (v1_funct_1 @ X15)
% 2.22/2.46          | ~ (v1_relat_1 @ X15))),
% 2.22/2.46      inference('cnf', [status(esa)], [dt_k2_funct_1])).
% 2.22/2.46  thf('192', plain,
% 2.22/2.46      (![X16 : $i]:
% 2.22/2.46         (~ (v2_funct_1 @ X16)
% 2.22/2.46          | ((k2_relat_1 @ X16) = (k1_relat_1 @ (k2_funct_1 @ X16)))
% 2.22/2.46          | ~ (v1_funct_1 @ X16)
% 2.22/2.46          | ~ (v1_relat_1 @ X16))),
% 2.22/2.46      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.22/2.46  thf('193', plain,
% 2.22/2.46      (![X34 : $i]:
% 2.22/2.46         ((m1_subset_1 @ X34 @ 
% 2.22/2.46           (k1_zfmisc_1 @ 
% 2.22/2.46            (k2_zfmisc_1 @ (k1_relat_1 @ X34) @ (k2_relat_1 @ X34))))
% 2.22/2.46          | ~ (v1_funct_1 @ X34)
% 2.22/2.46          | ~ (v1_relat_1 @ X34))),
% 2.22/2.46      inference('cnf', [status(esa)], [t3_funct_2])).
% 2.22/2.46  thf('194', plain,
% 2.22/2.46      (![X0 : $i]:
% 2.22/2.46         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.22/2.46           (k1_zfmisc_1 @ 
% 2.22/2.46            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 2.22/2.46          | ~ (v1_relat_1 @ X0)
% 2.22/2.46          | ~ (v1_funct_1 @ X0)
% 2.22/2.46          | ~ (v2_funct_1 @ X0)
% 2.22/2.46          | ~ (v1_relat_1 @ (k2_funct_1 @ X0))
% 2.22/2.46          | ~ (v1_funct_1 @ (k2_funct_1 @ X0)))),
% 2.22/2.46      inference('sup+', [status(thm)], ['192', '193'])).
% 2.22/2.46  thf('195', plain,
% 2.22/2.46      (![X0 : $i]:
% 2.22/2.46         (~ (v1_relat_1 @ X0)
% 2.22/2.46          | ~ (v1_funct_1 @ X0)
% 2.22/2.46          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.22/2.46          | ~ (v2_funct_1 @ X0)
% 2.22/2.46          | ~ (v1_funct_1 @ X0)
% 2.22/2.46          | ~ (v1_relat_1 @ X0)
% 2.22/2.46          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.22/2.46             (k1_zfmisc_1 @ 
% 2.22/2.46              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 2.22/2.46               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 2.22/2.46      inference('sup-', [status(thm)], ['191', '194'])).
% 2.22/2.46  thf('196', plain,
% 2.22/2.46      (![X0 : $i]:
% 2.22/2.46         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.22/2.46           (k1_zfmisc_1 @ 
% 2.22/2.46            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 2.22/2.46          | ~ (v2_funct_1 @ X0)
% 2.22/2.46          | ~ (v1_funct_1 @ (k2_funct_1 @ X0))
% 2.22/2.46          | ~ (v1_funct_1 @ X0)
% 2.22/2.46          | ~ (v1_relat_1 @ X0))),
% 2.22/2.46      inference('simplify', [status(thm)], ['195'])).
% 2.22/2.46  thf('197', plain,
% 2.22/2.46      (![X0 : $i]:
% 2.22/2.46         (~ (v1_relat_1 @ X0)
% 2.22/2.46          | ~ (v1_funct_1 @ X0)
% 2.22/2.46          | ~ (v1_relat_1 @ X0)
% 2.22/2.46          | ~ (v1_funct_1 @ X0)
% 2.22/2.46          | ~ (v2_funct_1 @ X0)
% 2.22/2.46          | (m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.22/2.46             (k1_zfmisc_1 @ 
% 2.22/2.46              (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ 
% 2.22/2.46               (k2_relat_1 @ (k2_funct_1 @ X0))))))),
% 2.22/2.46      inference('sup-', [status(thm)], ['190', '196'])).
% 2.22/2.46  thf('198', plain,
% 2.22/2.46      (![X0 : $i]:
% 2.22/2.46         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.22/2.46           (k1_zfmisc_1 @ 
% 2.22/2.46            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 2.22/2.46          | ~ (v2_funct_1 @ X0)
% 2.22/2.46          | ~ (v1_funct_1 @ X0)
% 2.22/2.46          | ~ (v1_relat_1 @ X0))),
% 2.22/2.46      inference('simplify', [status(thm)], ['197'])).
% 2.22/2.46  thf('199', plain,
% 2.22/2.46      ((((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.46          (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_relat_1 @ sk_C) @ sk_A)))
% 2.22/2.46         | ~ (v1_relat_1 @ sk_C)
% 2.22/2.46         | ~ (v1_funct_1 @ sk_C)
% 2.22/2.46         | ~ (v2_funct_1 @ sk_C)))
% 2.22/2.46         <= (~
% 2.22/2.46             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.46               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.22/2.46      inference('sup+', [status(thm)], ['189', '198'])).
% 2.22/2.46  thf('200', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 2.22/2.46      inference('sup+', [status(thm)], ['42', '43'])).
% 2.22/2.46  thf('201', plain, ((v1_relat_1 @ sk_C)),
% 2.22/2.46      inference('demod', [status(thm)], ['37', '38'])).
% 2.22/2.46  thf('202', plain, ((v1_funct_1 @ sk_C)),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.46  thf('203', plain, ((v2_funct_1 @ sk_C)),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.46  thf('204', plain,
% 2.22/2.46      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.46         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))
% 2.22/2.46         <= (~
% 2.22/2.46             ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.46               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))))),
% 2.22/2.46      inference('demod', [status(thm)], ['199', '200', '201', '202', '203'])).
% 2.22/2.46  thf('205', plain,
% 2.22/2.46      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.46         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A))))),
% 2.22/2.46      inference('demod', [status(thm)], ['139', '204'])).
% 2.22/2.46  thf('206', plain,
% 2.22/2.46      (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)) | 
% 2.22/2.46       ~
% 2.22/2.46       ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 2.22/2.46         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))) | 
% 2.22/2.46       ~ ((v1_funct_1 @ (k2_funct_1 @ sk_C)))),
% 2.22/2.46      inference('split', [status(esa)], ['0'])).
% 2.22/2.46  thf('207', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 2.22/2.46      inference('sat_resolution*', [status(thm)], ['138', '205', '206'])).
% 2.22/2.46  thf('208', plain,
% 2.22/2.46      (~ (v1_funct_2 @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0 @ sk_A)),
% 2.22/2.46      inference('simpl_trail', [status(thm)], ['131', '207'])).
% 2.22/2.46  thf('209', plain,
% 2.22/2.46      ((((sk_C) = (sk_B)))
% 2.22/2.46         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.46      inference('sup-', [status(thm)], ['99', '100'])).
% 2.22/2.46  thf('210', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 2.22/2.46      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.22/2.47  thf('211', plain,
% 2.22/2.47      ((((k2_relset_1 @ sk_A @ sk_B @ sk_B) = (sk_B)))
% 2.22/2.47         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.47      inference('sup+', [status(thm)], ['209', '210'])).
% 2.22/2.47  thf('212', plain,
% 2.22/2.47      ((((sk_B) = (k1_xboole_0)))
% 2.22/2.47         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.47      inference('clc', [status(thm)], ['127', '128'])).
% 2.22/2.47  thf('213', plain,
% 2.22/2.47      ((((sk_B) = (k1_xboole_0)))
% 2.22/2.47         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.47      inference('clc', [status(thm)], ['127', '128'])).
% 2.22/2.47  thf('214', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 2.22/2.47      inference('simplify', [status(thm)], ['58'])).
% 2.22/2.47  thf('215', plain,
% 2.22/2.47      (![X6 : $i, X8 : $i]:
% 2.22/2.47         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 2.22/2.47      inference('cnf', [status(esa)], [t3_subset])).
% 2.22/2.47  thf('216', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.22/2.47      inference('sup-', [status(thm)], ['214', '215'])).
% 2.22/2.47  thf('217', plain,
% 2.22/2.47      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 2.22/2.47      inference('simplify', [status(thm)], ['4'])).
% 2.22/2.47  thf('218', plain,
% 2.22/2.47      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.22/2.47         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 2.22/2.47          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 2.22/2.47      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.22/2.47  thf('219', plain,
% 2.22/2.47      (![X0 : $i, X1 : $i]:
% 2.22/2.47         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.22/2.47          | ((k2_relset_1 @ X0 @ k1_xboole_0 @ X1) = (k2_relat_1 @ X1)))),
% 2.22/2.47      inference('sup-', [status(thm)], ['217', '218'])).
% 2.22/2.47  thf('220', plain,
% 2.22/2.47      (![X0 : $i]:
% 2.22/2.47         ((k2_relset_1 @ X0 @ k1_xboole_0 @ k1_xboole_0)
% 2.22/2.47           = (k2_relat_1 @ k1_xboole_0))),
% 2.22/2.47      inference('sup-', [status(thm)], ['216', '219'])).
% 2.22/2.47  thf('221', plain,
% 2.22/2.47      ((((sk_B) = (k1_xboole_0)))
% 2.22/2.47         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.47      inference('clc', [status(thm)], ['127', '128'])).
% 2.22/2.47  thf('222', plain,
% 2.22/2.47      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 2.22/2.47         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.47      inference('demod', [status(thm)], ['211', '212', '213', '220', '221'])).
% 2.22/2.47  thf('223', plain,
% 2.22/2.47      (![X0 : $i]:
% 2.22/2.47         ((m1_subset_1 @ (k2_funct_1 @ X0) @ 
% 2.22/2.47           (k1_zfmisc_1 @ 
% 2.22/2.47            (k2_zfmisc_1 @ (k2_relat_1 @ X0) @ (k2_relat_1 @ (k2_funct_1 @ X0)))))
% 2.22/2.47          | ~ (v2_funct_1 @ X0)
% 2.22/2.47          | ~ (v1_funct_1 @ X0)
% 2.22/2.47          | ~ (v1_relat_1 @ X0))),
% 2.22/2.47      inference('simplify', [status(thm)], ['197'])).
% 2.22/2.47  thf('224', plain,
% 2.22/2.47      ((((m1_subset_1 @ (k2_funct_1 @ k1_xboole_0) @ 
% 2.22/2.47          (k1_zfmisc_1 @ 
% 2.22/2.47           (k2_zfmisc_1 @ k1_xboole_0 @ 
% 2.22/2.47            (k2_relat_1 @ (k2_funct_1 @ k1_xboole_0)))))
% 2.22/2.47         | ~ (v1_relat_1 @ k1_xboole_0)
% 2.22/2.47         | ~ (v1_funct_1 @ k1_xboole_0)
% 2.22/2.47         | ~ (v2_funct_1 @ k1_xboole_0)))
% 2.22/2.47         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.47      inference('sup+', [status(thm)], ['222', '223'])).
% 2.22/2.47  thf('225', plain,
% 2.22/2.47      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 2.22/2.47      inference('simplify', [status(thm)], ['16'])).
% 2.22/2.47  thf('226', plain,
% 2.22/2.47      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 2.22/2.47      inference('simplify', [status(thm)], ['16'])).
% 2.22/2.47  thf('227', plain,
% 2.22/2.47      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 2.22/2.47      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.22/2.47  thf('228', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.22/2.47      inference('sup+', [status(thm)], ['226', '227'])).
% 2.22/2.47  thf('229', plain,
% 2.22/2.47      (((v1_funct_1 @ sk_B))
% 2.22/2.47         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.47      inference('sup+', [status(thm)], ['121', '122'])).
% 2.22/2.47  thf('230', plain,
% 2.22/2.47      ((((sk_B) = (k1_xboole_0)))
% 2.22/2.47         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.47      inference('clc', [status(thm)], ['127', '128'])).
% 2.22/2.47  thf('231', plain,
% 2.22/2.47      (((v1_funct_1 @ k1_xboole_0))
% 2.22/2.47         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.47      inference('demod', [status(thm)], ['229', '230'])).
% 2.22/2.47  thf('232', plain,
% 2.22/2.47      (((v2_funct_1 @ sk_B))
% 2.22/2.47         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.47      inference('sup+', [status(thm)], ['124', '125'])).
% 2.22/2.47  thf('233', plain,
% 2.22/2.47      ((((sk_B) = (k1_xboole_0)))
% 2.22/2.47         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.47      inference('clc', [status(thm)], ['127', '128'])).
% 2.22/2.47  thf('234', plain,
% 2.22/2.47      (((v2_funct_1 @ k1_xboole_0))
% 2.22/2.47         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.47      inference('demod', [status(thm)], ['232', '233'])).
% 2.22/2.47  thf('235', plain,
% 2.22/2.47      (((m1_subset_1 @ (k2_funct_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0)))
% 2.22/2.47         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.47      inference('demod', [status(thm)], ['224', '225', '228', '231', '234'])).
% 2.22/2.47  thf('236', plain,
% 2.22/2.47      (![X6 : $i, X7 : $i]:
% 2.22/2.47         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 2.22/2.47      inference('cnf', [status(esa)], [t3_subset])).
% 2.22/2.47  thf('237', plain,
% 2.22/2.47      (((r1_tarski @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0))
% 2.22/2.47         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.47      inference('sup-', [status(thm)], ['235', '236'])).
% 2.22/2.47  thf('238', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 2.22/2.47      inference('sat_resolution*', [status(thm)], ['138', '205', '206'])).
% 2.22/2.47  thf('239', plain, ((r1_tarski @ (k2_funct_1 @ k1_xboole_0) @ k1_xboole_0)),
% 2.22/2.47      inference('simpl_trail', [status(thm)], ['237', '238'])).
% 2.22/2.47  thf('240', plain,
% 2.22/2.47      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 2.22/2.47         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.47      inference('demod', [status(thm)], ['211', '212', '213', '220', '221'])).
% 2.22/2.47  thf('241', plain,
% 2.22/2.47      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 2.22/2.47      inference('simplify', [status(thm)], ['16'])).
% 2.22/2.47  thf('242', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.22/2.47      inference('sup-', [status(thm)], ['214', '215'])).
% 2.22/2.47  thf('243', plain,
% 2.22/2.47      (![X17 : $i, X18 : $i, X19 : $i]:
% 2.22/2.47         ((v5_relat_1 @ X17 @ X19)
% 2.22/2.47          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 2.22/2.47      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.22/2.47  thf('244', plain,
% 2.22/2.47      (![X0 : $i, X1 : $i]: (v5_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X0)),
% 2.22/2.47      inference('sup-', [status(thm)], ['242', '243'])).
% 2.22/2.47  thf('245', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 2.22/2.47      inference('sup+', [status(thm)], ['241', '244'])).
% 2.22/2.47  thf('246', plain,
% 2.22/2.47      (![X11 : $i, X12 : $i]:
% 2.22/2.47         (~ (v5_relat_1 @ X11 @ X12)
% 2.22/2.47          | (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 2.22/2.47          | ~ (v1_relat_1 @ X11))),
% 2.22/2.47      inference('cnf', [status(esa)], [d19_relat_1])).
% 2.22/2.47  thf('247', plain,
% 2.22/2.47      (![X0 : $i]:
% 2.22/2.47         (~ (v1_relat_1 @ k1_xboole_0)
% 2.22/2.47          | (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0))),
% 2.22/2.47      inference('sup-', [status(thm)], ['245', '246'])).
% 2.22/2.47  thf('248', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.22/2.47      inference('sup+', [status(thm)], ['226', '227'])).
% 2.22/2.47  thf('249', plain,
% 2.22/2.47      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)),
% 2.22/2.47      inference('demod', [status(thm)], ['247', '248'])).
% 2.22/2.47  thf('250', plain,
% 2.22/2.47      (![X0 : $i, X2 : $i]:
% 2.22/2.47         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 2.22/2.47      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.22/2.47  thf('251', plain,
% 2.22/2.47      (![X0 : $i]:
% 2.22/2.47         (~ (r1_tarski @ X0 @ (k2_relat_1 @ k1_xboole_0))
% 2.22/2.47          | ((X0) = (k2_relat_1 @ k1_xboole_0)))),
% 2.22/2.47      inference('sup-', [status(thm)], ['249', '250'])).
% 2.22/2.47  thf('252', plain,
% 2.22/2.47      ((![X0 : $i]:
% 2.22/2.47          (~ (r1_tarski @ X0 @ k1_xboole_0)
% 2.22/2.47           | ((X0) = (k2_relat_1 @ k1_xboole_0))))
% 2.22/2.47         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.47      inference('sup-', [status(thm)], ['240', '251'])).
% 2.22/2.47  thf('253', plain,
% 2.22/2.47      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 2.22/2.47         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.47      inference('demod', [status(thm)], ['211', '212', '213', '220', '221'])).
% 2.22/2.47  thf('254', plain,
% 2.22/2.47      ((![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0))))
% 2.22/2.47         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.47      inference('demod', [status(thm)], ['252', '253'])).
% 2.22/2.47  thf('255', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 2.22/2.47      inference('sat_resolution*', [status(thm)], ['138', '205', '206'])).
% 2.22/2.47  thf('256', plain,
% 2.22/2.47      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 2.22/2.47      inference('simpl_trail', [status(thm)], ['254', '255'])).
% 2.22/2.47  thf('257', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.22/2.47      inference('sup-', [status(thm)], ['239', '256'])).
% 2.22/2.47  thf('258', plain, (~ (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ sk_A)),
% 2.22/2.47      inference('demod', [status(thm)], ['208', '257'])).
% 2.22/2.47  thf('259', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.22/2.47      inference('sup-', [status(thm)], ['214', '215'])).
% 2.22/2.47  thf('260', plain,
% 2.22/2.47      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 2.22/2.47      inference('simplify', [status(thm)], ['16'])).
% 2.22/2.47  thf('261', plain,
% 2.22/2.47      (![X20 : $i, X21 : $i, X22 : $i]:
% 2.22/2.47         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 2.22/2.47          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 2.22/2.47      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.22/2.47  thf('262', plain,
% 2.22/2.47      (![X0 : $i, X1 : $i]:
% 2.22/2.47         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.22/2.47          | ((k1_relset_1 @ k1_xboole_0 @ X0 @ X1) = (k1_relat_1 @ X1)))),
% 2.22/2.47      inference('sup-', [status(thm)], ['260', '261'])).
% 2.22/2.47  thf('263', plain,
% 2.22/2.47      (![X0 : $i]:
% 2.22/2.47         ((k1_relset_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 2.22/2.47           = (k1_relat_1 @ k1_xboole_0))),
% 2.22/2.47      inference('sup-', [status(thm)], ['259', '262'])).
% 2.22/2.47  thf('264', plain,
% 2.22/2.47      (![X28 : $i, X29 : $i, X30 : $i]:
% 2.22/2.47         (((X28) != (k1_relset_1 @ X28 @ X29 @ X30))
% 2.22/2.47          | (v1_funct_2 @ X30 @ X28 @ X29)
% 2.22/2.47          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 2.22/2.47      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.22/2.47  thf('265', plain,
% 2.22/2.47      (![X0 : $i]:
% 2.22/2.47         (((k1_xboole_0) != (k1_relat_1 @ k1_xboole_0))
% 2.22/2.47          | ~ (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)
% 2.22/2.47          | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0))),
% 2.22/2.47      inference('sup-', [status(thm)], ['263', '264'])).
% 2.22/2.47  thf('266', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.22/2.47      inference('sup-', [status(thm)], ['214', '215'])).
% 2.22/2.47  thf('267', plain,
% 2.22/2.47      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 2.22/2.47      inference('simplify', [status(thm)], ['16'])).
% 2.22/2.47  thf('268', plain,
% 2.22/2.47      (![X31 : $i, X32 : $i, X33 : $i]:
% 2.22/2.47         (~ (zip_tseitin_0 @ X31 @ X32)
% 2.22/2.47          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 2.22/2.47          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 2.22/2.47      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.22/2.47  thf('269', plain,
% 2.22/2.47      (![X0 : $i, X1 : $i]:
% 2.22/2.47         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.22/2.47          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 2.22/2.47          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 2.22/2.47      inference('sup-', [status(thm)], ['267', '268'])).
% 2.22/2.47  thf('270', plain,
% 2.22/2.47      (![X26 : $i, X27 : $i]:
% 2.22/2.47         ((zip_tseitin_0 @ X26 @ X27) | ((X27) != (k1_xboole_0)))),
% 2.22/2.47      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.22/2.47  thf('271', plain, (![X26 : $i]: (zip_tseitin_0 @ X26 @ k1_xboole_0)),
% 2.22/2.47      inference('simplify', [status(thm)], ['270'])).
% 2.22/2.47  thf('272', plain,
% 2.22/2.47      (![X0 : $i, X1 : $i]:
% 2.22/2.47         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.22/2.47          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 2.22/2.47      inference('demod', [status(thm)], ['269', '271'])).
% 2.22/2.47  thf('273', plain,
% 2.22/2.47      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 2.22/2.47      inference('sup-', [status(thm)], ['266', '272'])).
% 2.22/2.47  thf('274', plain,
% 2.22/2.47      (![X0 : $i]:
% 2.22/2.47         (((k1_xboole_0) != (k1_relat_1 @ k1_xboole_0))
% 2.22/2.47          | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0))),
% 2.22/2.47      inference('demod', [status(thm)], ['265', '273'])).
% 2.22/2.47  thf('275', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.22/2.47      inference('sup-', [status(thm)], ['239', '256'])).
% 2.22/2.47  thf('276', plain,
% 2.22/2.47      (![X16 : $i]:
% 2.22/2.47         (~ (v2_funct_1 @ X16)
% 2.22/2.47          | ((k1_relat_1 @ X16) = (k2_relat_1 @ (k2_funct_1 @ X16)))
% 2.22/2.47          | ~ (v1_funct_1 @ X16)
% 2.22/2.47          | ~ (v1_relat_1 @ X16))),
% 2.22/2.47      inference('cnf', [status(esa)], [t55_funct_1])).
% 2.22/2.47  thf('277', plain,
% 2.22/2.47      ((((k1_relat_1 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 2.22/2.47        | ~ (v1_relat_1 @ k1_xboole_0)
% 2.22/2.47        | ~ (v1_funct_1 @ k1_xboole_0)
% 2.22/2.47        | ~ (v2_funct_1 @ k1_xboole_0))),
% 2.22/2.47      inference('sup+', [status(thm)], ['275', '276'])).
% 2.22/2.47  thf('278', plain,
% 2.22/2.47      ((((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))
% 2.22/2.47         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.47      inference('demod', [status(thm)], ['211', '212', '213', '220', '221'])).
% 2.22/2.47  thf('279', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 2.22/2.47      inference('sat_resolution*', [status(thm)], ['138', '205', '206'])).
% 2.22/2.47  thf('280', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.22/2.47      inference('simpl_trail', [status(thm)], ['278', '279'])).
% 2.22/2.47  thf('281', plain, ((v1_relat_1 @ k1_xboole_0)),
% 2.22/2.47      inference('sup+', [status(thm)], ['226', '227'])).
% 2.22/2.47  thf('282', plain,
% 2.22/2.47      (((v1_funct_1 @ k1_xboole_0))
% 2.22/2.47         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.47      inference('demod', [status(thm)], ['229', '230'])).
% 2.22/2.47  thf('283', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 2.22/2.47      inference('sat_resolution*', [status(thm)], ['138', '205', '206'])).
% 2.22/2.47  thf('284', plain, ((v1_funct_1 @ k1_xboole_0)),
% 2.22/2.47      inference('simpl_trail', [status(thm)], ['282', '283'])).
% 2.22/2.47  thf('285', plain,
% 2.22/2.47      (((v2_funct_1 @ k1_xboole_0))
% 2.22/2.47         <= (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A)))),
% 2.22/2.47      inference('demod', [status(thm)], ['232', '233'])).
% 2.22/2.47  thf('286', plain, (~ ((v1_funct_2 @ (k2_funct_1 @ sk_C) @ sk_B @ sk_A))),
% 2.22/2.47      inference('sat_resolution*', [status(thm)], ['138', '205', '206'])).
% 2.22/2.47  thf('287', plain, ((v2_funct_1 @ k1_xboole_0)),
% 2.22/2.47      inference('simpl_trail', [status(thm)], ['285', '286'])).
% 2.22/2.47  thf('288', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.22/2.47      inference('demod', [status(thm)], ['277', '280', '281', '284', '287'])).
% 2.22/2.47  thf('289', plain,
% 2.22/2.47      (![X0 : $i]:
% 2.22/2.47         (((k1_xboole_0) != (k1_xboole_0))
% 2.22/2.47          | (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0))),
% 2.22/2.47      inference('demod', [status(thm)], ['274', '288'])).
% 2.22/2.47  thf('290', plain,
% 2.22/2.47      (![X0 : $i]: (v1_funct_2 @ k1_xboole_0 @ k1_xboole_0 @ X0)),
% 2.22/2.47      inference('simplify', [status(thm)], ['289'])).
% 2.22/2.47  thf('291', plain, ($false), inference('demod', [status(thm)], ['258', '290'])).
% 2.22/2.47  
% 2.22/2.47  % SZS output end Refutation
% 2.22/2.47  
% 2.22/2.47  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
