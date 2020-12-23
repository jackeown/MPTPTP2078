%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9OTKNDbaCq

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:13 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  146 ( 670 expanded)
%              Number of leaves         :   37 ( 205 expanded)
%              Depth                    :   21
%              Number of atoms          :  968 (8814 expanded)
%              Number of equality atoms :   76 ( 496 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf('0',plain,(
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

thf('1',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('2',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('4',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('5',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['2','5'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,(
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

thf('9',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','10'])).

thf('12',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X31 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('15',plain,(
    ! [X30: $i] :
      ( zip_tseitin_0 @ X30 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('16',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('17',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1 )
      | ~ ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('20',plain,(
    ! [X5: $i,X6: $i] :
      ( ( ( k2_zfmisc_1 @ X5 @ X6 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('21',plain,(
    ! [X6: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X6 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['21','24'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('26',plain,(
    ! [X8: $i,X9: $i] :
      ( ( r1_tarski @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('27',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('28',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('29',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('32',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v5_relat_1 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('33',plain,(
    v5_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['31','32'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('34',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v5_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k2_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('37',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('38',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_B ),
    inference(demod,[status(thm)],['35','38'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 )
      | ~ ( r1_tarski @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_C ),
    inference('sup-',[status(thm)],['30','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('45',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['43','44'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('46',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v4_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['36','37'])).

thf('49',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['47','48'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('50',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X27 ) @ X28 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X27 ) @ X29 )
      | ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['36','37'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['42','53'])).

thf('55',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('56',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( X32
       != ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ~ ( zip_tseitin_1 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('58',plain,
    ( ( sk_A
     != ( k1_relat_1 @ sk_D ) )
    | ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
   <= ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(split,[status(esa)],['59'])).

thf('61',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ~ ( v1_funct_1 @ sk_D )
   <= ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['59'])).

thf('63',plain,(
    v1_funct_1 @ sk_D ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['42','53'])).

thf('65',plain,
    ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(split,[status(esa)],['59'])).

thf('66',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference(split,[status(esa)],['59'])).

thf('68',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['63','66','67'])).

thf('69',plain,(
    ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['60','68'])).

thf('70',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ( sk_A
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(clc,[status(thm)],['58','69'])).

thf('71',plain,
    ( ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ sk_C @ sk_A )
      | ( sk_A
       != ( k1_relat_1 @ sk_D ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','70'])).

thf('72',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('73',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('74',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('75',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('76',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v4_relat_1 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('77',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v4_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k1_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('81',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('82',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['79','82'])).

thf('84',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('85',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ sk_C @ k1_xboole_0 )
      | ( k1_xboole_0 != k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72','73','74','85'])).

thf('87',plain,
    ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    sk_A != k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','87'])).

thf('89',plain,
    ( ( sk_B != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['12'])).

thf('90',plain,(
    sk_B != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['88','89'])).

thf('91',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['13','90'])).

thf('92',plain,(
    zip_tseitin_1 @ sk_D @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['11','91'])).

thf('93',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['6','92'])).

thf('94',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ( sk_A
     != ( k1_relat_1 @ sk_D ) ) ),
    inference(clc,[status(thm)],['58','69'])).

thf('95',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_0 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('97',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( r1_tarski @ X3 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('98',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( sk_B = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['95','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['42','53'])).

thf('101',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_0 @ X35 @ X36 )
      | ( zip_tseitin_1 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('102',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['99','102'])).

thf('104',plain,(
    sk_B != k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['13','90'])).

thf('105',plain,(
    zip_tseitin_1 @ sk_D @ sk_C @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['103','104'])).

thf('106',plain,(
    sk_A
 != ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['94','105'])).

thf('107',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['93','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9OTKNDbaCq
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:50:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.41/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.61  % Solved by: fo/fo7.sh
% 0.41/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.61  % done 289 iterations in 0.158s
% 0.41/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.61  % SZS output start Refutation
% 0.41/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.61  thf(sk_D_type, type, sk_D: $i).
% 0.41/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.61  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.41/0.61  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.61  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.61  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.41/0.61  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.41/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.61  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.41/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.61  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.41/0.61  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.41/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.61  thf(t9_funct_2, conjecture,
% 0.41/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.61     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.41/0.61         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.61       ( ( r1_tarski @ B @ C ) =>
% 0.41/0.61         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.41/0.61           ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.41/0.61             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ))).
% 0.41/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.61    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.61        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.41/0.61            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.61          ( ( r1_tarski @ B @ C ) =>
% 0.41/0.61            ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.41/0.61              ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ C ) & 
% 0.41/0.61                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) ) ) )),
% 0.41/0.61    inference('cnf.neg', [status(esa)], [t9_funct_2])).
% 0.41/0.61  thf('0', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(d1_funct_2, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.61       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.41/0.61           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.41/0.61             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.41/0.61         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.41/0.61           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.41/0.61             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.41/0.61  thf(zf_stmt_1, axiom,
% 0.41/0.61    (![C:$i,B:$i,A:$i]:
% 0.41/0.61     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.41/0.61       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.41/0.61  thf('1', plain,
% 0.41/0.61      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.41/0.61         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 0.41/0.61          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 0.41/0.61          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.61  thf('2', plain,
% 0.41/0.61      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A)
% 0.41/0.61        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['0', '1'])).
% 0.41/0.61  thf('3', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(redefinition_k1_relset_1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.61       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.41/0.61  thf('4', plain,
% 0.41/0.61      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.41/0.61         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 0.41/0.61          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.41/0.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.41/0.61  thf('5', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.41/0.61      inference('sup-', [status(thm)], ['3', '4'])).
% 0.41/0.61  thf('6', plain,
% 0.41/0.61      ((~ (zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 0.41/0.61      inference('demod', [status(thm)], ['2', '5'])).
% 0.41/0.61  thf(zf_stmt_2, axiom,
% 0.41/0.61    (![B:$i,A:$i]:
% 0.41/0.61     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.41/0.61       ( zip_tseitin_0 @ B @ A ) ))).
% 0.41/0.61  thf('7', plain,
% 0.41/0.61      (![X30 : $i, X31 : $i]:
% 0.41/0.61         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.41/0.61  thf('8', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.41/0.61  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.41/0.61  thf(zf_stmt_5, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.61       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.41/0.61         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.41/0.61           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.41/0.61             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.41/0.61  thf('9', plain,
% 0.41/0.61      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.41/0.61         (~ (zip_tseitin_0 @ X35 @ X36)
% 0.41/0.61          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 0.41/0.61          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.41/0.61  thf('10', plain,
% 0.41/0.61      (((zip_tseitin_1 @ sk_D @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['8', '9'])).
% 0.41/0.61  thf('11', plain,
% 0.41/0.61      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_B @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['7', '10'])).
% 0.41/0.61  thf('12', plain, ((((sk_B) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('13', plain,
% 0.41/0.61      ((((sk_B) != (k1_xboole_0))) <= (~ (((sk_B) = (k1_xboole_0))))),
% 0.41/0.61      inference('split', [status(esa)], ['12'])).
% 0.41/0.61  thf('14', plain,
% 0.41/0.61      (![X30 : $i, X31 : $i]:
% 0.41/0.61         ((zip_tseitin_0 @ X30 @ X31) | ((X31) != (k1_xboole_0)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.41/0.61  thf('15', plain, (![X30 : $i]: (zip_tseitin_0 @ X30 @ k1_xboole_0)),
% 0.41/0.61      inference('simplify', [status(thm)], ['14'])).
% 0.41/0.61  thf(t4_subset_1, axiom,
% 0.41/0.61    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.41/0.61  thf('16', plain,
% 0.41/0.61      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.41/0.61      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.41/0.61  thf('17', plain,
% 0.41/0.61      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.41/0.61         (~ (zip_tseitin_0 @ X35 @ X36)
% 0.41/0.61          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 0.41/0.61          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.41/0.61  thf('18', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i]:
% 0.41/0.61         ((zip_tseitin_1 @ k1_xboole_0 @ X0 @ X1) | ~ (zip_tseitin_0 @ X0 @ X1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['16', '17'])).
% 0.41/0.61  thf('19', plain,
% 0.41/0.61      (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.41/0.61      inference('sup-', [status(thm)], ['15', '18'])).
% 0.41/0.61  thf(t113_zfmisc_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.41/0.61       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.41/0.61  thf('20', plain,
% 0.41/0.61      (![X5 : $i, X6 : $i]:
% 0.41/0.61         (((k2_zfmisc_1 @ X5 @ X6) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.41/0.61      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.41/0.61  thf('21', plain,
% 0.41/0.61      (![X6 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X6) = (k1_xboole_0))),
% 0.41/0.61      inference('simplify', [status(thm)], ['20'])).
% 0.41/0.61  thf('22', plain,
% 0.41/0.61      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('split', [status(esa)], ['12'])).
% 0.41/0.61  thf('23', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('24', plain,
% 0.41/0.61      (((m1_subset_1 @ sk_D @ 
% 0.41/0.61         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B))))
% 0.41/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('sup+', [status(thm)], ['22', '23'])).
% 0.41/0.61  thf('25', plain,
% 0.41/0.61      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.41/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('sup+', [status(thm)], ['21', '24'])).
% 0.41/0.61  thf(t3_subset, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.41/0.61  thf('26', plain,
% 0.41/0.61      (![X8 : $i, X9 : $i]:
% 0.41/0.61         ((r1_tarski @ X8 @ X9) | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.41/0.61      inference('cnf', [status(esa)], [t3_subset])).
% 0.41/0.61  thf('27', plain,
% 0.41/0.61      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['25', '26'])).
% 0.41/0.61  thf(t3_xboole_1, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.41/0.61  thf('28', plain,
% 0.41/0.61      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.41/0.61      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.41/0.61  thf('29', plain,
% 0.41/0.61      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['27', '28'])).
% 0.41/0.61  thf('30', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('31', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(cc2_relset_1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.61       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.41/0.61  thf('32', plain,
% 0.41/0.61      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.41/0.61         ((v5_relat_1 @ X21 @ X23)
% 0.41/0.61          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.41/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.41/0.61  thf('33', plain, ((v5_relat_1 @ sk_D @ sk_B)),
% 0.41/0.61      inference('sup-', [status(thm)], ['31', '32'])).
% 0.41/0.61  thf(d19_relat_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( v1_relat_1 @ B ) =>
% 0.41/0.61       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.41/0.61  thf('34', plain,
% 0.41/0.61      (![X16 : $i, X17 : $i]:
% 0.41/0.61         (~ (v5_relat_1 @ X16 @ X17)
% 0.41/0.61          | (r1_tarski @ (k2_relat_1 @ X16) @ X17)
% 0.41/0.61          | ~ (v1_relat_1 @ X16))),
% 0.41/0.61      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.41/0.61  thf('35', plain,
% 0.41/0.61      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B))),
% 0.41/0.61      inference('sup-', [status(thm)], ['33', '34'])).
% 0.41/0.61  thf('36', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(cc1_relset_1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.61       ( v1_relat_1 @ C ) ))).
% 0.41/0.61  thf('37', plain,
% 0.41/0.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.41/0.61         ((v1_relat_1 @ X18)
% 0.41/0.61          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.41/0.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.41/0.61  thf('38', plain, ((v1_relat_1 @ sk_D)),
% 0.41/0.61      inference('sup-', [status(thm)], ['36', '37'])).
% 0.41/0.61  thf('39', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_B)),
% 0.41/0.61      inference('demod', [status(thm)], ['35', '38'])).
% 0.41/0.61  thf(t1_xboole_1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.41/0.61       ( r1_tarski @ A @ C ) ))).
% 0.41/0.61  thf('40', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         (~ (r1_tarski @ X0 @ X1)
% 0.41/0.61          | ~ (r1_tarski @ X1 @ X2)
% 0.41/0.61          | (r1_tarski @ X0 @ X2))),
% 0.41/0.61      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.41/0.61  thf('41', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((r1_tarski @ (k2_relat_1 @ sk_D) @ X0) | ~ (r1_tarski @ sk_B @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['39', '40'])).
% 0.41/0.61  thf('42', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_C)),
% 0.41/0.61      inference('sup-', [status(thm)], ['30', '41'])).
% 0.41/0.61  thf('43', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('44', plain,
% 0.41/0.61      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.41/0.61         ((v4_relat_1 @ X21 @ X22)
% 0.41/0.61          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.41/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.41/0.61  thf('45', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 0.41/0.61      inference('sup-', [status(thm)], ['43', '44'])).
% 0.41/0.61  thf(d18_relat_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( v1_relat_1 @ B ) =>
% 0.41/0.61       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.41/0.61  thf('46', plain,
% 0.41/0.61      (![X14 : $i, X15 : $i]:
% 0.41/0.61         (~ (v4_relat_1 @ X14 @ X15)
% 0.41/0.61          | (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 0.41/0.61          | ~ (v1_relat_1 @ X14))),
% 0.41/0.61      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.41/0.61  thf('47', plain,
% 0.41/0.61      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['45', '46'])).
% 0.41/0.61  thf('48', plain, ((v1_relat_1 @ sk_D)),
% 0.41/0.61      inference('sup-', [status(thm)], ['36', '37'])).
% 0.41/0.61  thf('49', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ sk_A)),
% 0.41/0.61      inference('demod', [status(thm)], ['47', '48'])).
% 0.41/0.61  thf(t11_relset_1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( v1_relat_1 @ C ) =>
% 0.41/0.61       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.41/0.61           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.41/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.41/0.61  thf('50', plain,
% 0.41/0.61      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.41/0.61         (~ (r1_tarski @ (k1_relat_1 @ X27) @ X28)
% 0.41/0.61          | ~ (r1_tarski @ (k2_relat_1 @ X27) @ X29)
% 0.41/0.61          | (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.41/0.61          | ~ (v1_relat_1 @ X27))),
% 0.41/0.61      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.41/0.61  thf('51', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (v1_relat_1 @ sk_D)
% 0.41/0.61          | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.41/0.61          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['49', '50'])).
% 0.41/0.61  thf('52', plain, ((v1_relat_1 @ sk_D)),
% 0.41/0.61      inference('sup-', [status(thm)], ['36', '37'])).
% 0.41/0.61  thf('53', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.41/0.61          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 0.41/0.61      inference('demod', [status(thm)], ['51', '52'])).
% 0.41/0.61  thf('54', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['42', '53'])).
% 0.41/0.61  thf('55', plain,
% 0.41/0.61      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.41/0.61         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 0.41/0.61          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.41/0.61      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.41/0.61  thf('56', plain,
% 0.41/0.61      (((k1_relset_1 @ sk_A @ sk_C @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.41/0.61      inference('sup-', [status(thm)], ['54', '55'])).
% 0.41/0.61  thf('57', plain,
% 0.41/0.61      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.41/0.61         (((X32) != (k1_relset_1 @ X32 @ X33 @ X34))
% 0.41/0.61          | (v1_funct_2 @ X34 @ X32 @ X33)
% 0.41/0.61          | ~ (zip_tseitin_1 @ X34 @ X33 @ X32))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.61  thf('58', plain,
% 0.41/0.61      ((((sk_A) != (k1_relat_1 @ sk_D))
% 0.41/0.61        | ~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)
% 0.41/0.61        | (v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.41/0.61      inference('sup-', [status(thm)], ['56', '57'])).
% 0.41/0.61  thf('59', plain,
% 0.41/0.61      ((~ (v1_funct_1 @ sk_D)
% 0.41/0.61        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)
% 0.41/0.61        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('60', plain,
% 0.41/0.61      ((~ (v1_funct_2 @ sk_D @ sk_A @ sk_C))
% 0.41/0.61         <= (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)))),
% 0.41/0.61      inference('split', [status(esa)], ['59'])).
% 0.41/0.61  thf('61', plain, ((v1_funct_1 @ sk_D)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('62', plain, ((~ (v1_funct_1 @ sk_D)) <= (~ ((v1_funct_1 @ sk_D)))),
% 0.41/0.61      inference('split', [status(esa)], ['59'])).
% 0.41/0.61  thf('63', plain, (((v1_funct_1 @ sk_D))),
% 0.41/0.61      inference('sup-', [status(thm)], ['61', '62'])).
% 0.41/0.61  thf('64', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['42', '53'])).
% 0.41/0.61  thf('65', plain,
% 0.41/0.61      ((~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))
% 0.41/0.61         <= (~
% 0.41/0.61             ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))))),
% 0.41/0.61      inference('split', [status(esa)], ['59'])).
% 0.41/0.61  thf('66', plain,
% 0.41/0.61      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['64', '65'])).
% 0.41/0.61  thf('67', plain,
% 0.41/0.61      (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C)) | 
% 0.41/0.61       ~ ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))) | 
% 0.41/0.61       ~ ((v1_funct_1 @ sk_D))),
% 0.41/0.61      inference('split', [status(esa)], ['59'])).
% 0.41/0.61  thf('68', plain, (~ ((v1_funct_2 @ sk_D @ sk_A @ sk_C))),
% 0.41/0.61      inference('sat_resolution*', [status(thm)], ['63', '66', '67'])).
% 0.41/0.61  thf('69', plain, (~ (v1_funct_2 @ sk_D @ sk_A @ sk_C)),
% 0.41/0.61      inference('simpl_trail', [status(thm)], ['60', '68'])).
% 0.41/0.61  thf('70', plain,
% 0.41/0.61      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)
% 0.41/0.61        | ((sk_A) != (k1_relat_1 @ sk_D)))),
% 0.41/0.61      inference('clc', [status(thm)], ['58', '69'])).
% 0.41/0.61  thf('71', plain,
% 0.41/0.61      (((~ (zip_tseitin_1 @ k1_xboole_0 @ sk_C @ sk_A)
% 0.41/0.61         | ((sk_A) != (k1_relat_1 @ sk_D)))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['29', '70'])).
% 0.41/0.61  thf('72', plain,
% 0.41/0.61      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('split', [status(esa)], ['12'])).
% 0.41/0.61  thf('73', plain,
% 0.41/0.61      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('split', [status(esa)], ['12'])).
% 0.41/0.61  thf('74', plain,
% 0.41/0.61      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['27', '28'])).
% 0.41/0.61  thf('75', plain,
% 0.41/0.61      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.41/0.61      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.41/0.61  thf('76', plain,
% 0.41/0.61      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.41/0.61         ((v4_relat_1 @ X21 @ X22)
% 0.41/0.61          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.41/0.61      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.41/0.61  thf('77', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 0.41/0.61      inference('sup-', [status(thm)], ['75', '76'])).
% 0.41/0.61  thf('78', plain,
% 0.41/0.61      (![X14 : $i, X15 : $i]:
% 0.41/0.61         (~ (v4_relat_1 @ X14 @ X15)
% 0.41/0.61          | (r1_tarski @ (k1_relat_1 @ X14) @ X15)
% 0.41/0.61          | ~ (v1_relat_1 @ X14))),
% 0.41/0.61      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.41/0.61  thf('79', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (v1_relat_1 @ k1_xboole_0)
% 0.41/0.61          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['77', '78'])).
% 0.41/0.61  thf('80', plain,
% 0.41/0.61      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.41/0.61      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.41/0.61  thf('81', plain,
% 0.41/0.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.41/0.61         ((v1_relat_1 @ X18)
% 0.41/0.61          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.41/0.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.41/0.61  thf('82', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.41/0.61      inference('sup-', [status(thm)], ['80', '81'])).
% 0.41/0.61  thf('83', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.41/0.61      inference('demod', [status(thm)], ['79', '82'])).
% 0.41/0.61  thf('84', plain,
% 0.41/0.61      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.41/0.61      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.41/0.61  thf('85', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['83', '84'])).
% 0.41/0.61  thf('86', plain,
% 0.41/0.61      (((~ (zip_tseitin_1 @ k1_xboole_0 @ sk_C @ k1_xboole_0)
% 0.41/0.61         | ((k1_xboole_0) != (k1_xboole_0)))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('demod', [status(thm)], ['71', '72', '73', '74', '85'])).
% 0.41/0.61  thf('87', plain,
% 0.41/0.61      ((~ (zip_tseitin_1 @ k1_xboole_0 @ sk_C @ k1_xboole_0))
% 0.41/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('simplify', [status(thm)], ['86'])).
% 0.41/0.61  thf('88', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['19', '87'])).
% 0.41/0.61  thf('89', plain, (~ (((sk_B) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.41/0.61      inference('split', [status(esa)], ['12'])).
% 0.41/0.61  thf('90', plain, (~ (((sk_B) = (k1_xboole_0)))),
% 0.41/0.61      inference('sat_resolution*', [status(thm)], ['88', '89'])).
% 0.41/0.61  thf('91', plain, (((sk_B) != (k1_xboole_0))),
% 0.41/0.61      inference('simpl_trail', [status(thm)], ['13', '90'])).
% 0.41/0.61  thf('92', plain, ((zip_tseitin_1 @ sk_D @ sk_B @ sk_A)),
% 0.41/0.61      inference('simplify_reflect-', [status(thm)], ['11', '91'])).
% 0.41/0.61  thf('93', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 0.41/0.61      inference('demod', [status(thm)], ['6', '92'])).
% 0.41/0.61  thf('94', plain,
% 0.41/0.61      ((~ (zip_tseitin_1 @ sk_D @ sk_C @ sk_A)
% 0.41/0.61        | ((sk_A) != (k1_relat_1 @ sk_D)))),
% 0.41/0.61      inference('clc', [status(thm)], ['58', '69'])).
% 0.41/0.61  thf('95', plain, ((r1_tarski @ sk_B @ sk_C)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('96', plain,
% 0.41/0.61      (![X30 : $i, X31 : $i]:
% 0.41/0.61         ((zip_tseitin_0 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.41/0.61  thf('97', plain,
% 0.41/0.61      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (r1_tarski @ X3 @ k1_xboole_0))),
% 0.41/0.61      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.41/0.61  thf('98', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         (~ (r1_tarski @ X1 @ X0)
% 0.41/0.61          | (zip_tseitin_0 @ X0 @ X2)
% 0.41/0.61          | ((X1) = (k1_xboole_0)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['96', '97'])).
% 0.41/0.61  thf('99', plain,
% 0.41/0.61      (![X0 : $i]: (((sk_B) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_C @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['95', '98'])).
% 0.41/0.61  thf('100', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.41/0.61      inference('sup-', [status(thm)], ['42', '53'])).
% 0.41/0.61  thf('101', plain,
% 0.41/0.61      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.41/0.61         (~ (zip_tseitin_0 @ X35 @ X36)
% 0.41/0.61          | (zip_tseitin_1 @ X37 @ X35 @ X36)
% 0.41/0.61          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.41/0.61  thf('102', plain,
% 0.41/0.61      (((zip_tseitin_1 @ sk_D @ sk_C @ sk_A) | ~ (zip_tseitin_0 @ sk_C @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['100', '101'])).
% 0.41/0.61  thf('103', plain,
% 0.41/0.61      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_C @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['99', '102'])).
% 0.41/0.61  thf('104', plain, (((sk_B) != (k1_xboole_0))),
% 0.41/0.61      inference('simpl_trail', [status(thm)], ['13', '90'])).
% 0.41/0.61  thf('105', plain, ((zip_tseitin_1 @ sk_D @ sk_C @ sk_A)),
% 0.41/0.61      inference('simplify_reflect-', [status(thm)], ['103', '104'])).
% 0.41/0.61  thf('106', plain, (((sk_A) != (k1_relat_1 @ sk_D))),
% 0.41/0.61      inference('demod', [status(thm)], ['94', '105'])).
% 0.41/0.61  thf('107', plain, ($false),
% 0.41/0.61      inference('simplify_reflect-', [status(thm)], ['93', '106'])).
% 0.41/0.61  
% 0.41/0.61  % SZS output end Refutation
% 0.41/0.61  
% 0.41/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
