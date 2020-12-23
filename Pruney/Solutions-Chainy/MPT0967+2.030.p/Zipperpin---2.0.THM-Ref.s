%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KcS4EY9VwE

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:15 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  149 ( 876 expanded)
%              Number of leaves         :   34 ( 237 expanded)
%              Depth                    :   24
%              Number of atoms          : 1103 (12790 expanded)
%              Number of equality atoms :  110 (1202 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t9_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r1_tarski @ B @ C )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( r1_tarski @ B @ C )
         => ( ( ( B = k1_xboole_0 )
              & ( A != k1_xboole_0 ) )
            | ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ C )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t9_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('4',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v5_relat_1 @ X15 @ X17 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('8',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('9',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v5_relat_1 @ X11 @ X12 )
      | ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['10','15'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['5','18'])).

thf(t4_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X29 ) @ X30 )
      | ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X29 ) @ X30 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('23',plain,(
    v1_funct_1 @ sk_D ),
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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('24',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('25',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('26',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['24','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('29',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('30',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('34',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('36',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('37',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k2_zfmisc_1 @ sk_B @ X0 )
        = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['31','38'])).

thf('40',plain,(
    ! [X3: $i,X4: $i] :
      ( ( X3 = k1_xboole_0 )
      | ( X4 = k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X4 @ X3 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_B = k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['43'])).

thf('45',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('46',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['43'])).

thf('47',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf('50',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('51',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ X1 )
        = ( k1_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ! [X0: $i] :
        ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D )
        = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('54',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['43'])).

thf('55',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('58',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ! [X0: $i] :
        ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D )
        = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['49','52'])).

thf('60',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['46','47'])).

thf('62',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('63',plain,
    ( ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ sk_B @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X22 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('65',plain,(
    ! [X21: $i] :
      ( zip_tseitin_0 @ X21 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['63','65'])).

thf('67',plain,
    ( ( k1_xboole_0
      = ( k1_relat_1 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['60','66'])).

thf('68',plain,
    ( ! [X0: $i] :
        ( ( k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D )
        = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','67'])).

thf('69',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( X23
       != ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('70',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ~ ( zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0 )
        | ( v1_funct_2 @ sk_D @ k1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf('72',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('73',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X21: $i] :
      ( zip_tseitin_0 @ X21 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf('76',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,
    ( ! [X0: $i] :
        ( zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['71','76'])).

thf('78',plain,
    ( ! [X0: $i] :
        ( ( k1_xboole_0 != k1_xboole_0 )
        | ( v1_funct_2 @ sk_D @ k1_xboole_0 @ X0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','77'])).

thf('79',plain,
    ( ! [X0: $i] :
        ( v1_funct_2 @ sk_D @ k1_xboole_0 @ X0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['43'])).

thf('81',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('82',plain,
    ( ~ ( v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C )
   <= ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ( sk_A != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','82'])).

thf('84',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf('85',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['25'])).

thf('86',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['43'])).

thf('87',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('88',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_C ) ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      & ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['85','88'])).

thf('90',plain,
    ( ( sk_A != k1_xboole_0 )
    | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['84','89'])).

thf('91',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('92',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['43'])).

thf('93',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['4','83','90','91','92'])).

thf('94',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['44','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['42','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['42','94'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( sk_A
        = ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup+',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D ) )
      | ( X1 = X0 ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(condensation,[status(thm)],['98'])).

thf('100',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(demod,[status(thm)],['21','22','23','99'])).

thf('101',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('102',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['0'])).

thf('104',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['4','102','103'])).

thf('105',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','104'])).

thf('106',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['5','18'])).

thf('107',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X29 ) @ X30 )
      | ( v1_funct_2 @ X29 @ ( k1_relat_1 @ X29 ) @ X30 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t4_funct_2])).

thf('108',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_funct_2 @ sk_D @ ( k1_relat_1 @ sk_D ) @ sk_C ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['13','14'])).

thf('110',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(condensation,[status(thm)],['98'])).

thf('112',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_C ),
    inference(demod,[status(thm)],['108','109','110','111'])).

thf('113',plain,(
    $false ),
    inference(demod,[status(thm)],['105','112'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.KcS4EY9VwE
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:26:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.60/0.78  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.60/0.78  % Solved by: fo/fo7.sh
% 0.60/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.78  % done 266 iterations in 0.306s
% 0.60/0.78  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.60/0.78  % SZS output start Refutation
% 0.60/0.78  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.60/0.78  thf(sk_D_type, type, sk_D: $i).
% 0.60/0.78  thf(sk_C_type, type, sk_C: $i).
% 0.60/0.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.60/0.78  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.60/0.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.60/0.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.78  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.78  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.60/0.78  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.60/0.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.78  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.60/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.78  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.60/0.78  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.60/0.78  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.60/0.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.78  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.60/0.78  thf(t9_funct_2, conjecture,
% 0.60/0.78    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.78     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.60/0.78         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.60/0.78       ( ( r1_tarski @ B @ C ) =>
% 0.60/0.78         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.60/0.78           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.60/0.78             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.60/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.78    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.78        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.60/0.78            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.60/0.78          ( ( r1_tarski @ B @ C ) =>
% 0.60/0.78            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.60/0.78              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.60/0.78                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.60/0.78    inference('cnf.neg', [status(esa)], [t9_funct_2])).
% 0.60/0.78  thf('0', plain,
% 0.60/0.78      ((~ (v1_funct_1 @ sk_D)
% 0.60/0.78        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.60/0.78        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('1', plain,
% 0.60/0.78      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.60/0.78         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.60/0.78      inference('split', [status(esa)], ['0'])).
% 0.60/0.78  thf('2', plain, ((v1_funct_1 @ sk_D)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('3', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.60/0.78      inference('split', [status(esa)], ['0'])).
% 0.60/0.78  thf('4', plain, (((v1_funct_1 @ sk_D))),
% 0.60/0.78      inference('sup-', [status(thm)], ['2', '3'])).
% 0.60/0.78  thf('5', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('6', plain,
% 0.60/0.78      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf(cc2_relset_1, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i]:
% 0.60/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.78       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.60/0.78  thf('7', plain,
% 0.60/0.78      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.60/0.78         ((v5_relat_1 @ X15 @ X17)
% 0.60/0.78          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.60/0.78      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.60/0.78  thf('8', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 0.60/0.78      inference('sup-', [status(thm)], ['6', '7'])).
% 0.60/0.78  thf(d19_relat_1, axiom,
% 0.60/0.78    (![A:$i,B:$i]:
% 0.60/0.78     ( ( v1_relat_1 @ B ) =>
% 0.60/0.78       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.60/0.78  thf('9', plain,
% 0.60/0.78      (![X11 : $i, X12 : $i]:
% 0.60/0.78         (~ (v5_relat_1 @ X11 @ X12)
% 0.60/0.78          | (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 0.60/0.78          | ~ (v1_relat_1 @ X11))),
% 0.60/0.78      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.60/0.78  thf('10', plain,
% 0.60/0.78      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 0.60/0.78      inference('sup-', [status(thm)], ['8', '9'])).
% 0.60/0.78  thf('11', plain,
% 0.60/0.78      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf(cc2_relat_1, axiom,
% 0.60/0.78    (![A:$i]:
% 0.60/0.78     ( ( v1_relat_1 @ A ) =>
% 0.60/0.78       ( ![B:$i]:
% 0.60/0.78         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.60/0.78  thf('12', plain,
% 0.60/0.78      (![X9 : $i, X10 : $i]:
% 0.60/0.78         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.60/0.78          | (v1_relat_1 @ X9)
% 0.60/0.78          | ~ (v1_relat_1 @ X10))),
% 0.60/0.78      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.60/0.78  thf('13', plain,
% 0.60/0.78      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D))),
% 0.60/0.78      inference('sup-', [status(thm)], ['11', '12'])).
% 0.60/0.78  thf(fc6_relat_1, axiom,
% 0.60/0.78    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.60/0.78  thf('14', plain,
% 0.60/0.78      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 0.60/0.78      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.60/0.78  thf('15', plain, ((v1_relat_1 @ sk_D)),
% 0.60/0.78      inference('demod', [status(thm)], ['13', '14'])).
% 0.60/0.78  thf('16', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 0.60/0.78      inference('demod', [status(thm)], ['10', '15'])).
% 0.60/0.78  thf(t1_xboole_1, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i]:
% 0.60/0.78     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.60/0.78       ( r1_tarski @ A @ C ) ))).
% 0.60/0.78  thf('17', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.78         (~ (r1_tarski @ X0 @ X1)
% 0.60/0.78          | ~ (r1_tarski @ X1 @ X2)
% 0.60/0.78          | (r1_tarski @ X0 @ X2))),
% 0.60/0.78      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.60/0.78  thf('18', plain,
% 0.60/0.78      (![X0 : $i]:
% 0.60/0.78         ((r1_tarski @ (k2_relat_1 @ sk_D) @ X0) | ~ (r1_tarski @ sk_B @ X0))),
% 0.60/0.78      inference('sup-', [status(thm)], ['16', '17'])).
% 0.60/0.78  thf('19', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.60/0.78      inference('sup-', [status(thm)], ['5', '18'])).
% 0.60/0.78  thf(t4_funct_2, axiom,
% 0.60/0.78    (![A:$i,B:$i]:
% 0.60/0.78     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.60/0.78       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.60/0.78         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.60/0.78           ( m1_subset_1 @
% 0.60/0.78             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.60/0.78  thf('20', plain,
% 0.60/0.78      (![X29 : $i, X30 : $i]:
% 0.60/0.78         (~ (r1_tarski @ (k2_relat_1 @ X29) @ X30)
% 0.60/0.78          | (m1_subset_1 @ X29 @ 
% 0.60/0.78             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X29) @ X30)))
% 0.60/0.78          | ~ (v1_funct_1 @ X29)
% 0.60/0.78          | ~ (v1_relat_1 @ X29))),
% 0.60/0.78      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.60/0.78  thf('21', plain,
% 0.60/0.78      ((~ (v1_relat_1 @ sk_D)
% 0.60/0.78        | ~ (v1_funct_1 @ sk_D)
% 0.60/0.78        | (m1_subset_1 @ sk_D @ 
% 0.60/0.78           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_C))))),
% 0.60/0.78      inference('sup-', [status(thm)], ['19', '20'])).
% 0.60/0.78  thf('22', plain, ((v1_relat_1 @ sk_D)),
% 0.60/0.78      inference('demod', [status(thm)], ['13', '14'])).
% 0.60/0.78  thf('23', plain, ((v1_funct_1 @ sk_D)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf(d1_funct_2, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i]:
% 0.60/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.78       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.60/0.78           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.60/0.78             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.60/0.78         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.60/0.78           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.60/0.78             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.60/0.78  thf(zf_stmt_1, axiom,
% 0.60/0.78    (![B:$i,A:$i]:
% 0.60/0.78     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.60/0.78       ( zip_tseitin_0 @ B @ A ) ))).
% 0.60/0.78  thf('24', plain,
% 0.60/0.78      (![X21 : $i, X22 : $i]:
% 0.60/0.78         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.60/0.78  thf(t113_zfmisc_1, axiom,
% 0.60/0.78    (![A:$i,B:$i]:
% 0.60/0.78     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.60/0.78       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.60/0.78  thf('25', plain,
% 0.60/0.78      (![X4 : $i, X5 : $i]:
% 0.60/0.78         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.60/0.78      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.60/0.78  thf('26', plain,
% 0.60/0.78      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.60/0.78      inference('simplify', [status(thm)], ['25'])).
% 0.60/0.78  thf('27', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.78         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 0.60/0.78      inference('sup+', [status(thm)], ['24', '26'])).
% 0.60/0.78  thf('28', plain,
% 0.60/0.78      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.60/0.78  thf(zf_stmt_3, axiom,
% 0.60/0.78    (![C:$i,B:$i,A:$i]:
% 0.60/0.78     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.60/0.78       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.60/0.78  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.60/0.78  thf(zf_stmt_5, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i]:
% 0.60/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.78       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.60/0.78         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.60/0.78           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.60/0.78             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.60/0.78  thf('29', plain,
% 0.60/0.78      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.60/0.78         (~ (zip_tseitin_0 @ X26 @ X27)
% 0.60/0.78          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 0.60/0.78          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.60/0.78  thf('30', plain,
% 0.60/0.78      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.60/0.78      inference('sup-', [status(thm)], ['28', '29'])).
% 0.60/0.78  thf('31', plain,
% 0.60/0.78      (![X0 : $i]:
% 0.60/0.78         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 0.60/0.78          | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.60/0.78      inference('sup-', [status(thm)], ['27', '30'])).
% 0.60/0.78  thf('32', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('33', plain,
% 0.60/0.78      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.60/0.78         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.60/0.78          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 0.60/0.78          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.78  thf('34', plain,
% 0.60/0.78      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.60/0.78        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.60/0.78      inference('sup-', [status(thm)], ['32', '33'])).
% 0.60/0.78  thf('35', plain,
% 0.60/0.78      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf(redefinition_k1_relset_1, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i]:
% 0.60/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.78       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.60/0.78  thf('36', plain,
% 0.60/0.78      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.60/0.78         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 0.60/0.78          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.60/0.78      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.60/0.78  thf('37', plain,
% 0.60/0.78      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.60/0.78      inference('sup-', [status(thm)], ['35', '36'])).
% 0.60/0.78  thf('38', plain,
% 0.60/0.78      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.60/0.78      inference('demod', [status(thm)], ['34', '37'])).
% 0.60/0.78  thf('39', plain,
% 0.60/0.78      (![X0 : $i]:
% 0.60/0.78         (((k2_zfmisc_1 @ sk_B @ X0) = (k1_xboole_0))
% 0.60/0.78          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.60/0.78      inference('sup-', [status(thm)], ['31', '38'])).
% 0.60/0.78  thf('40', plain,
% 0.60/0.78      (![X3 : $i, X4 : $i]:
% 0.60/0.78         (((X3) = (k1_xboole_0))
% 0.60/0.78          | ((X4) = (k1_xboole_0))
% 0.60/0.78          | ((k2_zfmisc_1 @ X4 @ X3) != (k1_xboole_0)))),
% 0.60/0.78      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.60/0.78  thf('41', plain,
% 0.60/0.78      (![X0 : $i]:
% 0.60/0.78         (((k1_xboole_0) != (k1_xboole_0))
% 0.60/0.78          | ((sk_A) = (k1_relat_1 @ sk_D))
% 0.60/0.78          | ((sk_B) = (k1_xboole_0))
% 0.60/0.78          | ((X0) = (k1_xboole_0)))),
% 0.60/0.78      inference('sup-', [status(thm)], ['39', '40'])).
% 0.60/0.78  thf('42', plain,
% 0.60/0.78      (![X0 : $i]:
% 0.60/0.78         (((X0) = (k1_xboole_0))
% 0.60/0.78          | ((sk_B) = (k1_xboole_0))
% 0.60/0.78          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.60/0.78      inference('simplify', [status(thm)], ['41'])).
% 0.60/0.78  thf('43', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('44', plain,
% 0.60/0.78      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.60/0.78      inference('split', [status(esa)], ['43'])).
% 0.60/0.78  thf('45', plain,
% 0.60/0.78      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.60/0.78      inference('simplify', [status(thm)], ['25'])).
% 0.60/0.78  thf('46', plain,
% 0.60/0.78      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.60/0.78      inference('split', [status(esa)], ['43'])).
% 0.60/0.78  thf('47', plain,
% 0.60/0.78      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('48', plain,
% 0.60/0.78      (((m1_subset_1 @ sk_D @ 
% 0.60/0.78         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.60/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.60/0.78      inference('sup+', [status(thm)], ['46', '47'])).
% 0.60/0.78  thf('49', plain,
% 0.60/0.78      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.60/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.60/0.78      inference('sup+', [status(thm)], ['45', '48'])).
% 0.60/0.78  thf('50', plain,
% 0.60/0.78      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.60/0.78      inference('simplify', [status(thm)], ['25'])).
% 0.60/0.78  thf('51', plain,
% 0.60/0.78      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.60/0.78         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 0.60/0.78          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.60/0.78      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.60/0.78  thf('52', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.60/0.78          | ((k1_relset_1 @ k1_xboole_0 @ X0 @ X1) = (k1_relat_1 @ X1)))),
% 0.60/0.78      inference('sup-', [status(thm)], ['50', '51'])).
% 0.60/0.78  thf('53', plain,
% 0.60/0.78      ((![X0 : $i]:
% 0.60/0.78          ((k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D) = (k1_relat_1 @ sk_D)))
% 0.60/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.60/0.78      inference('sup-', [status(thm)], ['49', '52'])).
% 0.60/0.78  thf('54', plain,
% 0.60/0.78      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.60/0.78      inference('split', [status(esa)], ['43'])).
% 0.60/0.78  thf('55', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('56', plain,
% 0.60/0.78      (((v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_B))
% 0.60/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.60/0.78      inference('sup+', [status(thm)], ['54', '55'])).
% 0.60/0.78  thf('57', plain,
% 0.60/0.78      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.60/0.78         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 0.60/0.78          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 0.60/0.78          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.78  thf('58', plain,
% 0.60/0.78      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 0.60/0.78         | ((k1_xboole_0) = (k1_relset_1 @ k1_xboole_0 @ sk_B @ sk_D))))
% 0.60/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.60/0.78      inference('sup-', [status(thm)], ['56', '57'])).
% 0.60/0.78  thf('59', plain,
% 0.60/0.78      ((![X0 : $i]:
% 0.60/0.78          ((k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D) = (k1_relat_1 @ sk_D)))
% 0.60/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.60/0.78      inference('sup-', [status(thm)], ['49', '52'])).
% 0.60/0.78  thf('60', plain,
% 0.60/0.78      (((~ (zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 0.60/0.78         | ((k1_xboole_0) = (k1_relat_1 @ sk_D))))
% 0.60/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.60/0.78      inference('demod', [status(thm)], ['58', '59'])).
% 0.60/0.78  thf('61', plain,
% 0.60/0.78      (((m1_subset_1 @ sk_D @ 
% 0.60/0.78         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.60/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.60/0.78      inference('sup+', [status(thm)], ['46', '47'])).
% 0.60/0.78  thf('62', plain,
% 0.60/0.78      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.60/0.78         (~ (zip_tseitin_0 @ X26 @ X27)
% 0.60/0.78          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 0.60/0.78          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.60/0.78  thf('63', plain,
% 0.60/0.78      ((((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0)
% 0.60/0.78         | ~ (zip_tseitin_0 @ sk_B @ k1_xboole_0)))
% 0.60/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.60/0.78      inference('sup-', [status(thm)], ['61', '62'])).
% 0.60/0.78  thf('64', plain,
% 0.60/0.78      (![X21 : $i, X22 : $i]:
% 0.60/0.78         ((zip_tseitin_0 @ X21 @ X22) | ((X22) != (k1_xboole_0)))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.60/0.78  thf('65', plain, (![X21 : $i]: (zip_tseitin_0 @ X21 @ k1_xboole_0)),
% 0.60/0.78      inference('simplify', [status(thm)], ['64'])).
% 0.60/0.78  thf('66', plain,
% 0.60/0.78      (((zip_tseitin_1 @ sk_D @ sk_B @ k1_xboole_0))
% 0.60/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.60/0.78      inference('demod', [status(thm)], ['63', '65'])).
% 0.60/0.78  thf('67', plain,
% 0.60/0.78      ((((k1_xboole_0) = (k1_relat_1 @ sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.60/0.78      inference('demod', [status(thm)], ['60', '66'])).
% 0.60/0.78  thf('68', plain,
% 0.60/0.78      ((![X0 : $i]: ((k1_relset_1 @ k1_xboole_0 @ X0 @ sk_D) = (k1_xboole_0)))
% 0.60/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.60/0.78      inference('demod', [status(thm)], ['53', '67'])).
% 0.60/0.78  thf('69', plain,
% 0.60/0.78      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.60/0.78         (((X23) != (k1_relset_1 @ X23 @ X24 @ X25))
% 0.60/0.78          | (v1_funct_2 @ X25 @ X23 @ X24)
% 0.60/0.78          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.78  thf('70', plain,
% 0.60/0.78      ((![X0 : $i]:
% 0.60/0.78          (((k1_xboole_0) != (k1_xboole_0))
% 0.60/0.78           | ~ (zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0)
% 0.60/0.78           | (v1_funct_2 @ sk_D @ k1_xboole_0 @ X0)))
% 0.60/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.60/0.78      inference('sup-', [status(thm)], ['68', '69'])).
% 0.60/0.78  thf('71', plain,
% 0.60/0.78      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.60/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.60/0.78      inference('sup+', [status(thm)], ['45', '48'])).
% 0.60/0.78  thf('72', plain,
% 0.60/0.78      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.60/0.78      inference('simplify', [status(thm)], ['25'])).
% 0.60/0.78  thf('73', plain,
% 0.60/0.78      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.60/0.78         (~ (zip_tseitin_0 @ X26 @ X27)
% 0.60/0.78          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 0.60/0.78          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.60/0.78  thf('74', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.60/0.78          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0)
% 0.60/0.78          | ~ (zip_tseitin_0 @ X0 @ k1_xboole_0))),
% 0.60/0.78      inference('sup-', [status(thm)], ['72', '73'])).
% 0.60/0.78  thf('75', plain, (![X21 : $i]: (zip_tseitin_0 @ X21 @ k1_xboole_0)),
% 0.60/0.78      inference('simplify', [status(thm)], ['64'])).
% 0.60/0.78  thf('76', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.60/0.78          | (zip_tseitin_1 @ X1 @ X0 @ k1_xboole_0))),
% 0.60/0.78      inference('demod', [status(thm)], ['74', '75'])).
% 0.60/0.78  thf('77', plain,
% 0.60/0.78      ((![X0 : $i]: (zip_tseitin_1 @ sk_D @ X0 @ k1_xboole_0))
% 0.60/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.60/0.78      inference('sup-', [status(thm)], ['71', '76'])).
% 0.60/0.78  thf('78', plain,
% 0.60/0.78      ((![X0 : $i]:
% 0.60/0.78          (((k1_xboole_0) != (k1_xboole_0))
% 0.60/0.78           | (v1_funct_2 @ sk_D @ k1_xboole_0 @ X0)))
% 0.60/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.60/0.78      inference('demod', [status(thm)], ['70', '77'])).
% 0.60/0.78  thf('79', plain,
% 0.60/0.78      ((![X0 : $i]: (v1_funct_2 @ sk_D @ k1_xboole_0 @ X0))
% 0.60/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.60/0.78      inference('simplify', [status(thm)], ['78'])).
% 0.60/0.78  thf('80', plain,
% 0.60/0.78      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.60/0.78      inference('split', [status(esa)], ['43'])).
% 0.60/0.78  thf('81', plain,
% 0.60/0.78      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.60/0.78         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.60/0.78      inference('split', [status(esa)], ['0'])).
% 0.60/0.78  thf('82', plain,
% 0.60/0.78      ((~ (v1_funct_2 @ sk_D @ k1_xboole_0 @ sk_C))
% 0.60/0.78         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) & (((sk_A) = (k1_xboole_0))))),
% 0.60/0.78      inference('sup-', [status(thm)], ['80', '81'])).
% 0.60/0.78  thf('83', plain,
% 0.60/0.78      (((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ (((sk_A) = (k1_xboole_0)))),
% 0.60/0.78      inference('sup-', [status(thm)], ['79', '82'])).
% 0.60/0.78  thf('84', plain,
% 0.60/0.78      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.60/0.78         <= ((((sk_A) = (k1_xboole_0))))),
% 0.60/0.78      inference('sup+', [status(thm)], ['45', '48'])).
% 0.60/0.78  thf('85', plain,
% 0.60/0.78      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.60/0.78      inference('simplify', [status(thm)], ['25'])).
% 0.60/0.78  thf('86', plain,
% 0.60/0.78      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.60/0.78      inference('split', [status(esa)], ['43'])).
% 0.60/0.78  thf('87', plain,
% 0.60/0.78      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.60/0.78         <= (~
% 0.60/0.78             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.60/0.78      inference('split', [status(esa)], ['0'])).
% 0.60/0.78  thf('88', plain,
% 0.60/0.78      ((~ (m1_subset_1 @ sk_D @ 
% 0.60/0.78           (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_C))))
% 0.60/0.78         <= (~
% 0.60/0.78             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 0.60/0.78             (((sk_A) = (k1_xboole_0))))),
% 0.60/0.78      inference('sup-', [status(thm)], ['86', '87'])).
% 0.60/0.78  thf('89', plain,
% 0.60/0.78      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.60/0.78         <= (~
% 0.60/0.78             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) & 
% 0.60/0.78             (((sk_A) = (k1_xboole_0))))),
% 0.60/0.78      inference('sup-', [status(thm)], ['85', '88'])).
% 0.60/0.78  thf('90', plain,
% 0.60/0.78      (~ (((sk_A) = (k1_xboole_0))) | 
% 0.60/0.78       ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.60/0.78      inference('sup-', [status(thm)], ['84', '89'])).
% 0.60/0.78  thf('91', plain,
% 0.60/0.78      (~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.60/0.78       ~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | ~ ((v1_funct_1 @ sk_D))),
% 0.60/0.78      inference('split', [status(esa)], ['0'])).
% 0.60/0.78  thf('92', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.60/0.78      inference('split', [status(esa)], ['43'])).
% 0.60/0.78  thf('93', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.60/0.78      inference('sat_resolution*', [status(thm)], ['4', '83', '90', '91', '92'])).
% 0.60/0.78  thf('94', plain, (((sk_B) != (k1_xboole_0))),
% 0.60/0.78      inference('simpl_trail', [status(thm)], ['44', '93'])).
% 0.60/0.78  thf('95', plain,
% 0.60/0.78      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.60/0.78      inference('simplify_reflect-', [status(thm)], ['42', '94'])).
% 0.60/0.78  thf('96', plain,
% 0.60/0.78      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.60/0.78      inference('simplify_reflect-', [status(thm)], ['42', '94'])).
% 0.60/0.78  thf('97', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         (((X1) = (X0))
% 0.60/0.78          | ((sk_A) = (k1_relat_1 @ sk_D))
% 0.60/0.78          | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.60/0.78      inference('sup+', [status(thm)], ['95', '96'])).
% 0.60/0.78  thf('98', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]: (((sk_A) = (k1_relat_1 @ sk_D)) | ((X1) = (X0)))),
% 0.60/0.78      inference('simplify', [status(thm)], ['97'])).
% 0.60/0.78  thf('99', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.60/0.78      inference('condensation', [status(thm)], ['98'])).
% 0.60/0.78  thf('100', plain,
% 0.60/0.78      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.60/0.78      inference('demod', [status(thm)], ['21', '22', '23', '99'])).
% 0.60/0.78  thf('101', plain,
% 0.60/0.78      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.60/0.78         <= (~
% 0.60/0.78             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.60/0.78      inference('split', [status(esa)], ['0'])).
% 0.60/0.78  thf('102', plain,
% 0.60/0.78      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.60/0.78      inference('sup-', [status(thm)], ['100', '101'])).
% 0.60/0.78  thf('103', plain,
% 0.60/0.78      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | 
% 0.60/0.78       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.60/0.78       ~ ((v1_funct_1 @ sk_D))),
% 0.60/0.78      inference('split', [status(esa)], ['0'])).
% 0.60/0.78  thf('104', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.60/0.78      inference('sat_resolution*', [status(thm)], ['4', '102', '103'])).
% 0.60/0.78  thf('105', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.60/0.78      inference('simpl_trail', [status(thm)], ['1', '104'])).
% 0.60/0.78  thf('106', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.60/0.78      inference('sup-', [status(thm)], ['5', '18'])).
% 0.60/0.78  thf('107', plain,
% 0.60/0.78      (![X29 : $i, X30 : $i]:
% 0.60/0.78         (~ (r1_tarski @ (k2_relat_1 @ X29) @ X30)
% 0.60/0.78          | (v1_funct_2 @ X29 @ (k1_relat_1 @ X29) @ X30)
% 0.60/0.78          | ~ (v1_funct_1 @ X29)
% 0.60/0.78          | ~ (v1_relat_1 @ X29))),
% 0.60/0.78      inference('cnf', [status(esa)], [t4_funct_2])).
% 0.60/0.78  thf('108', plain,
% 0.60/0.78      ((~ (v1_relat_1 @ sk_D)
% 0.60/0.78        | ~ (v1_funct_1 @ sk_D)
% 0.60/0.78        | (v1_funct_2 @ sk_D @ (k1_relat_1 @ sk_D) @ sk_C))),
% 0.60/0.78      inference('sup-', [status(thm)], ['106', '107'])).
% 0.60/0.78  thf('109', plain, ((v1_relat_1 @ sk_D)),
% 0.60/0.78      inference('demod', [status(thm)], ['13', '14'])).
% 0.60/0.78  thf('110', plain, ((v1_funct_1 @ sk_D)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('111', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.60/0.78      inference('condensation', [status(thm)], ['98'])).
% 0.60/0.78  thf('112', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.60/0.78      inference('demod', [status(thm)], ['108', '109', '110', '111'])).
% 0.60/0.78  thf('113', plain, ($false), inference('demod', [status(thm)], ['105', '112'])).
% 0.60/0.78  
% 0.60/0.78  % SZS output end Refutation
% 0.60/0.78  
% 0.60/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
