%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aqygB727ff

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:34 EST 2020

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :  148 (1291 expanded)
%              Number of leaves         :   46 ( 396 expanded)
%              Depth                    :   29
%              Number of atoms          : 1054 (18628 expanded)
%              Number of equality atoms :   77 ( 783 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t115_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
            & ! [F: $i] :
                ~ ( ( r2_hidden @ F @ A )
                  & ( r2_hidden @ F @ C )
                  & ( E
                    = ( k1_funct_1 @ D @ F ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
              & ! [F: $i] :
                  ~ ( ( r2_hidden @ F @ A )
                    & ( r2_hidden @ F @ C )
                    & ( E
                      = ( k1_funct_1 @ D @ F ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t115_funct_2])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('2',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_1 @ X38 @ X39 )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

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

thf('4',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( zip_tseitin_1 @ X43 @ X44 )
      | ( zip_tseitin_2 @ X45 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('5',plain,
    ( ( zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('7',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ( X40
        = ( k1_relset_1 @ X40 @ X41 @ X42 ) )
      | ~ ( zip_tseitin_2 @ X42 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('9',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X33 @ X31 )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('14',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['6','13'])).

thf('15',plain,(
    r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('17',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( ( k7_relset_1 @ X35 @ X36 @ X34 @ X37 )
        = ( k9_relat_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ sk_C ) ),
    inference(demod,[status(thm)],['15','18'])).

thf(d12_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_funct_1 @ A )
        & ( v1_relat_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) )
                  & ( r2_hidden @ E @ B )
                  & ( D
                    = ( k1_funct_1 @ A @ E ) ) ) ) ) ) )).

thf(zf_stmt_6,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( D
          = ( k1_funct_1 @ A @ E ) )
        & ( r2_hidden @ E @ B )
        & ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ) )).

thf(zf_stmt_8,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i,C: $i] :
          ( ( C
            = ( k9_relat_1 @ A @ B ) )
        <=> ! [D: $i] :
              ( ( r2_hidden @ D @ C )
            <=> ? [E: $i] :
                  ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) )).

thf('20',plain,(
    ! [X21: $i,X22: $i,X24: $i,X25: $i] :
      ( ( X24
       != ( k9_relat_1 @ X22 @ X21 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X25 @ X21 @ X22 ) @ X25 @ X21 @ X22 )
      | ~ ( r2_hidden @ X25 @ X24 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('21',plain,(
    ! [X21: $i,X22: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( r2_hidden @ X25 @ ( k9_relat_1 @ X22 @ X21 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X25 @ X21 @ X22 ) @ X25 @ X21 @ X22 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,
    ( ( zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_E_2 @ sk_C @ sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('27',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('28',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_E_2 @ sk_C @ sk_D_2 ),
    inference(demod,[status(thm)],['22','23','28'])).

thf('30',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X16 @ ( k1_relat_1 @ X15 ) )
      | ~ ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('31',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['14','31'])).

thf('33',plain,(
    ! [X46: $i] :
      ( ~ ( r2_hidden @ X46 @ sk_A )
      | ~ ( r2_hidden @ X46 @ sk_C )
      | ( sk_E_2
       != ( k1_funct_1 @ sk_D_2 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E_2
     != ( k1_funct_1 @ sk_D_2 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) ) )
    | ~ ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_E_2 @ sk_C @ sk_D_2 ),
    inference(demod,[status(thm)],['22','23','28'])).

thf('36',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( X17
        = ( k1_funct_1 @ X15 @ X16 ) )
      | ~ ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('37',plain,
    ( sk_E_2
    = ( k1_funct_1 @ sk_D_2 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_E_2 @ sk_C @ sk_D_2 ),
    inference(demod,[status(thm)],['22','23','28'])).

thf('39',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ X16 @ X18 )
      | ~ ( zip_tseitin_0 @ X16 @ X17 @ X18 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('40',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_C ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E_2 != sk_E_2 ) ),
    inference(demod,[status(thm)],['34','37','40'])).

thf('42',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['1','42'])).

thf('44',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( X43 != k1_xboole_0 )
      | ( X44 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X45 @ X44 @ X43 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('45',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X45 @ X44 @ k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ( X44 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_2 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['41'])).

thf('49',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','49'])).

thf('51',plain,(
    r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ sk_C ) ),
    inference(demod,[status(thm)],['15','18'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('52',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k9_relat_1 @ X14 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X14 @ X12 @ X13 ) @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('53',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_2 ) @ sk_E_2 ) @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference(demod,[status(thm)],['26','27'])).

thf('55',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_2 ) @ sk_E_2 ) @ sk_D_2 ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_1 @ X38 @ X39 )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('57',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('58',plain,(
    ! [X1: $i,X3: $i] :
      ( ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X3 ) )
      | ~ ( r1_tarski @ X1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('59',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('60',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ X3 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['56','61'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_1 @ sk_D_2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ k1_xboole_0 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['50','63'])).

thf('65',plain,
    ( ( zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('66',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['41'])).

thf('67',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['41'])).

thf('68',plain,
    ( ( zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ sk_A )
    | ~ ( zip_tseitin_1 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['64','68'])).

thf('70',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['9','12'])).

thf('71',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['41'])).

thf('72',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_A )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X46: $i] :
      ( ~ ( r2_hidden @ X46 @ sk_A )
      | ~ ( r2_hidden @ X46 @ sk_C )
      | ( sk_E_2
       != ( k1_funct_1 @ sk_D_2 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_E_2
       != ( k1_funct_1 @ sk_D_2 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) ) )
      | ~ ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( sk_E_2
    = ( k1_funct_1 @ sk_D_2 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('79',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_C ),
    inference('sup-',[status(thm)],['38','39'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_E_2 != sk_E_2 ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['80'])).

thf('82',plain,
    ( ( zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ sk_A )
    | ~ ( zip_tseitin_1 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_1 @ X38 @ X39 )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('85',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_1 @ X38 @ X39 )
      | ( X39 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('86',plain,(
    ! [X38: $i] :
      ( zip_tseitin_1 @ X38 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['84','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ X0 @ X0 ) ),
    inference(eq_fact,[status(thm)],['87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['83','88'])).

thf('90',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_A )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X46: $i] :
      ( ~ ( r2_hidden @ X46 @ sk_A )
      | ~ ( r2_hidden @ X46 @ sk_C )
      | ( sk_E_2
       != ( k1_funct_1 @ sk_D_2 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_E_2
       != ( k1_funct_1 @ sk_D_2 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) ) )
      | ~ ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( sk_E_2
    = ( k1_funct_1 @ sk_D_2 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('97',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_C ),
    inference('sup-',[status(thm)],['38','39'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( sk_E_2 != sk_E_2 ) ) ),
    inference(demod,[status(thm)],['95','96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    $false ),
    inference('sup-',[status(thm)],['0','99'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.aqygB727ff
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:10:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.71/0.91  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.71/0.91  % Solved by: fo/fo7.sh
% 0.71/0.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.71/0.91  % done 463 iterations in 0.457s
% 0.71/0.91  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.71/0.91  % SZS output start Refutation
% 0.71/0.91  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.71/0.91  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.71/0.91  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.71/0.91  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.71/0.91  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.71/0.91  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.71/0.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.71/0.91  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.71/0.91  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.71/0.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.71/0.91  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.71/0.91  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.71/0.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.71/0.91  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.71/0.91  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.71/0.91  thf(sk_A_type, type, sk_A: $i).
% 0.71/0.91  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.71/0.91  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.71/0.91  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.71/0.91  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.71/0.91  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.71/0.91  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.71/0.91  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.71/0.91  thf(sk_B_type, type, sk_B: $i).
% 0.71/0.91  thf(sk_C_type, type, sk_C: $i).
% 0.71/0.91  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.71/0.91  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.71/0.91  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.71/0.91      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.71/0.91  thf(t115_funct_2, conjecture,
% 0.71/0.91    (![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.91     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.71/0.91         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.71/0.91       ( ![E:$i]:
% 0.71/0.91         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.71/0.91              ( ![F:$i]:
% 0.71/0.91                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.71/0.91                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.71/0.91  thf(zf_stmt_0, negated_conjecture,
% 0.71/0.91    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.91        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.71/0.91            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.71/0.91          ( ![E:$i]:
% 0.71/0.91            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.71/0.91                 ( ![F:$i]:
% 0.71/0.91                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.71/0.91                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 0.71/0.91    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 0.71/0.91  thf('1', plain,
% 0.71/0.91      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf(d1_funct_2, axiom,
% 0.71/0.91    (![A:$i,B:$i,C:$i]:
% 0.71/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.91       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.71/0.91           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.71/0.91             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.71/0.91         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.71/0.91           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.71/0.91             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.71/0.91  thf(zf_stmt_1, axiom,
% 0.71/0.91    (![B:$i,A:$i]:
% 0.71/0.91     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.71/0.91       ( zip_tseitin_1 @ B @ A ) ))).
% 0.71/0.91  thf('2', plain,
% 0.71/0.91      (![X38 : $i, X39 : $i]:
% 0.71/0.91         ((zip_tseitin_1 @ X38 @ X39) | ((X38) = (k1_xboole_0)))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.71/0.91  thf('3', plain,
% 0.71/0.91      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.71/0.91  thf(zf_stmt_3, axiom,
% 0.71/0.91    (![C:$i,B:$i,A:$i]:
% 0.71/0.91     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.71/0.91       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.71/0.91  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $o).
% 0.71/0.91  thf(zf_stmt_5, axiom,
% 0.71/0.91    (![A:$i,B:$i,C:$i]:
% 0.71/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.91       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.71/0.91         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.71/0.91           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.71/0.91             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.71/0.91  thf('4', plain,
% 0.71/0.91      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.71/0.91         (~ (zip_tseitin_1 @ X43 @ X44)
% 0.71/0.91          | (zip_tseitin_2 @ X45 @ X43 @ X44)
% 0.71/0.91          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43))))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.71/0.91  thf('5', plain,
% 0.71/0.91      (((zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A)
% 0.71/0.91        | ~ (zip_tseitin_1 @ sk_B @ sk_A))),
% 0.71/0.91      inference('sup-', [status(thm)], ['3', '4'])).
% 0.71/0.91  thf('6', plain,
% 0.71/0.91      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A))),
% 0.71/0.91      inference('sup-', [status(thm)], ['2', '5'])).
% 0.71/0.91  thf('7', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('8', plain,
% 0.71/0.91      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.71/0.91         (~ (v1_funct_2 @ X42 @ X40 @ X41)
% 0.71/0.91          | ((X40) = (k1_relset_1 @ X40 @ X41 @ X42))
% 0.71/0.91          | ~ (zip_tseitin_2 @ X42 @ X41 @ X40))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.71/0.91  thf('9', plain,
% 0.71/0.91      ((~ (zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A)
% 0.71/0.91        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_2)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['7', '8'])).
% 0.71/0.91  thf('10', plain,
% 0.71/0.91      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf(redefinition_k1_relset_1, axiom,
% 0.71/0.91    (![A:$i,B:$i,C:$i]:
% 0.71/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.91       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.71/0.91  thf('11', plain,
% 0.71/0.91      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.71/0.91         (((k1_relset_1 @ X32 @ X33 @ X31) = (k1_relat_1 @ X31))
% 0.71/0.91          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.71/0.91      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.71/0.91  thf('12', plain,
% 0.71/0.91      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 0.71/0.91      inference('sup-', [status(thm)], ['10', '11'])).
% 0.71/0.91  thf('13', plain,
% 0.71/0.91      ((~ (zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A)
% 0.71/0.91        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.71/0.91      inference('demod', [status(thm)], ['9', '12'])).
% 0.71/0.91  thf('14', plain,
% 0.71/0.91      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['6', '13'])).
% 0.71/0.91  thf('15', plain,
% 0.71/0.91      ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('16', plain,
% 0.71/0.91      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf(redefinition_k7_relset_1, axiom,
% 0.71/0.91    (![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.91       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.71/0.91  thf('17', plain,
% 0.71/0.91      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.71/0.91         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.71/0.91          | ((k7_relset_1 @ X35 @ X36 @ X34 @ X37) = (k9_relat_1 @ X34 @ X37)))),
% 0.71/0.91      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.71/0.91  thf('18', plain,
% 0.71/0.91      (![X0 : $i]:
% 0.71/0.91         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0)
% 0.71/0.91           = (k9_relat_1 @ sk_D_2 @ X0))),
% 0.71/0.91      inference('sup-', [status(thm)], ['16', '17'])).
% 0.71/0.91  thf('19', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.71/0.91      inference('demod', [status(thm)], ['15', '18'])).
% 0.71/0.91  thf(d12_funct_1, axiom,
% 0.71/0.91    (![A:$i]:
% 0.71/0.91     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.71/0.91       ( ![B:$i,C:$i]:
% 0.71/0.91         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.71/0.91           ( ![D:$i]:
% 0.71/0.91             ( ( r2_hidden @ D @ C ) <=>
% 0.71/0.91               ( ?[E:$i]:
% 0.71/0.91                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 0.71/0.91                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 0.71/0.91  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.71/0.91  thf(zf_stmt_7, axiom,
% 0.71/0.91    (![E:$i,D:$i,B:$i,A:$i]:
% 0.71/0.91     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.71/0.91       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 0.71/0.91         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 0.71/0.91  thf(zf_stmt_8, axiom,
% 0.71/0.91    (![A:$i]:
% 0.71/0.91     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.71/0.91       ( ![B:$i,C:$i]:
% 0.71/0.91         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.71/0.91           ( ![D:$i]:
% 0.71/0.91             ( ( r2_hidden @ D @ C ) <=>
% 0.71/0.91               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 0.71/0.91  thf('20', plain,
% 0.71/0.91      (![X21 : $i, X22 : $i, X24 : $i, X25 : $i]:
% 0.71/0.91         (((X24) != (k9_relat_1 @ X22 @ X21))
% 0.71/0.91          | (zip_tseitin_0 @ (sk_E_1 @ X25 @ X21 @ X22) @ X25 @ X21 @ X22)
% 0.71/0.91          | ~ (r2_hidden @ X25 @ X24)
% 0.71/0.91          | ~ (v1_funct_1 @ X22)
% 0.71/0.91          | ~ (v1_relat_1 @ X22))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.71/0.91  thf('21', plain,
% 0.71/0.91      (![X21 : $i, X22 : $i, X25 : $i]:
% 0.71/0.91         (~ (v1_relat_1 @ X22)
% 0.71/0.91          | ~ (v1_funct_1 @ X22)
% 0.71/0.91          | ~ (r2_hidden @ X25 @ (k9_relat_1 @ X22 @ X21))
% 0.71/0.91          | (zip_tseitin_0 @ (sk_E_1 @ X25 @ X21 @ X22) @ X25 @ X21 @ X22))),
% 0.71/0.91      inference('simplify', [status(thm)], ['20'])).
% 0.71/0.91  thf('22', plain,
% 0.71/0.91      (((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_E_2 @ sk_C @ 
% 0.71/0.91         sk_D_2)
% 0.71/0.91        | ~ (v1_funct_1 @ sk_D_2)
% 0.71/0.91        | ~ (v1_relat_1 @ sk_D_2))),
% 0.71/0.91      inference('sup-', [status(thm)], ['19', '21'])).
% 0.71/0.91  thf('23', plain, ((v1_funct_1 @ sk_D_2)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('24', plain,
% 0.71/0.91      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf(cc2_relat_1, axiom,
% 0.71/0.91    (![A:$i]:
% 0.71/0.91     ( ( v1_relat_1 @ A ) =>
% 0.71/0.91       ( ![B:$i]:
% 0.71/0.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.71/0.91  thf('25', plain,
% 0.71/0.91      (![X7 : $i, X8 : $i]:
% 0.71/0.91         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.71/0.91          | (v1_relat_1 @ X7)
% 0.71/0.91          | ~ (v1_relat_1 @ X8))),
% 0.71/0.91      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.71/0.91  thf('26', plain,
% 0.71/0.91      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_2))),
% 0.71/0.91      inference('sup-', [status(thm)], ['24', '25'])).
% 0.71/0.91  thf(fc6_relat_1, axiom,
% 0.71/0.91    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.71/0.91  thf('27', plain,
% 0.71/0.91      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.71/0.91      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.71/0.91  thf('28', plain, ((v1_relat_1 @ sk_D_2)),
% 0.71/0.91      inference('demod', [status(thm)], ['26', '27'])).
% 0.71/0.91  thf('29', plain,
% 0.71/0.91      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_E_2 @ sk_C @ 
% 0.71/0.91        sk_D_2)),
% 0.71/0.91      inference('demod', [status(thm)], ['22', '23', '28'])).
% 0.71/0.91  thf('30', plain,
% 0.71/0.91      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.71/0.91         ((r2_hidden @ X16 @ (k1_relat_1 @ X15))
% 0.71/0.91          | ~ (zip_tseitin_0 @ X16 @ X17 @ X18 @ X15))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.71/0.91  thf('31', plain,
% 0.71/0.91      ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ (k1_relat_1 @ sk_D_2))),
% 0.71/0.91      inference('sup-', [status(thm)], ['29', '30'])).
% 0.71/0.91  thf('32', plain,
% 0.71/0.91      (((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_A)
% 0.71/0.91        | ((sk_B) = (k1_xboole_0)))),
% 0.71/0.91      inference('sup+', [status(thm)], ['14', '31'])).
% 0.71/0.91  thf('33', plain,
% 0.71/0.91      (![X46 : $i]:
% 0.71/0.91         (~ (r2_hidden @ X46 @ sk_A)
% 0.71/0.91          | ~ (r2_hidden @ X46 @ sk_C)
% 0.71/0.91          | ((sk_E_2) != (k1_funct_1 @ sk_D_2 @ X46)))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('34', plain,
% 0.71/0.91      ((((sk_B) = (k1_xboole_0))
% 0.71/0.91        | ((sk_E_2)
% 0.71/0.91            != (k1_funct_1 @ sk_D_2 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2)))
% 0.71/0.91        | ~ (r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_C))),
% 0.71/0.91      inference('sup-', [status(thm)], ['32', '33'])).
% 0.71/0.91  thf('35', plain,
% 0.71/0.91      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_E_2 @ sk_C @ 
% 0.71/0.91        sk_D_2)),
% 0.71/0.91      inference('demod', [status(thm)], ['22', '23', '28'])).
% 0.71/0.91  thf('36', plain,
% 0.71/0.91      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.71/0.91         (((X17) = (k1_funct_1 @ X15 @ X16))
% 0.71/0.91          | ~ (zip_tseitin_0 @ X16 @ X17 @ X18 @ X15))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.71/0.91  thf('37', plain,
% 0.71/0.91      (((sk_E_2) = (k1_funct_1 @ sk_D_2 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['35', '36'])).
% 0.71/0.91  thf('38', plain,
% 0.71/0.91      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_E_2 @ sk_C @ 
% 0.71/0.91        sk_D_2)),
% 0.71/0.91      inference('demod', [status(thm)], ['22', '23', '28'])).
% 0.71/0.91  thf('39', plain,
% 0.71/0.91      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.71/0.91         ((r2_hidden @ X16 @ X18) | ~ (zip_tseitin_0 @ X16 @ X17 @ X18 @ X15))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.71/0.91  thf('40', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_C)),
% 0.71/0.91      inference('sup-', [status(thm)], ['38', '39'])).
% 0.71/0.91  thf('41', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_E_2) != (sk_E_2)))),
% 0.71/0.91      inference('demod', [status(thm)], ['34', '37', '40'])).
% 0.71/0.91  thf('42', plain, (((sk_B) = (k1_xboole_0))),
% 0.71/0.91      inference('simplify', [status(thm)], ['41'])).
% 0.71/0.91  thf('43', plain,
% 0.71/0.91      ((m1_subset_1 @ sk_D_2 @ 
% 0.71/0.91        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.71/0.91      inference('demod', [status(thm)], ['1', '42'])).
% 0.71/0.91  thf('44', plain,
% 0.71/0.91      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.71/0.91         (((X43) != (k1_xboole_0))
% 0.71/0.91          | ((X44) = (k1_xboole_0))
% 0.71/0.91          | ((X45) = (k1_xboole_0))
% 0.71/0.91          | ~ (v1_funct_2 @ X45 @ X44 @ X43)
% 0.71/0.91          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43))))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.71/0.91  thf('45', plain,
% 0.71/0.91      (![X44 : $i, X45 : $i]:
% 0.71/0.91         (~ (m1_subset_1 @ X45 @ 
% 0.71/0.91             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ k1_xboole_0)))
% 0.71/0.91          | ~ (v1_funct_2 @ X45 @ X44 @ k1_xboole_0)
% 0.71/0.91          | ((X45) = (k1_xboole_0))
% 0.71/0.91          | ((X44) = (k1_xboole_0)))),
% 0.71/0.91      inference('simplify', [status(thm)], ['44'])).
% 0.71/0.91  thf('46', plain,
% 0.71/0.91      ((((sk_A) = (k1_xboole_0))
% 0.71/0.91        | ((sk_D_2) = (k1_xboole_0))
% 0.71/0.91        | ~ (v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0))),
% 0.71/0.91      inference('sup-', [status(thm)], ['43', '45'])).
% 0.71/0.91  thf('47', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B)),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('48', plain, (((sk_B) = (k1_xboole_0))),
% 0.71/0.91      inference('simplify', [status(thm)], ['41'])).
% 0.71/0.91  thf('49', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0)),
% 0.71/0.91      inference('demod', [status(thm)], ['47', '48'])).
% 0.71/0.91  thf('50', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_D_2) = (k1_xboole_0)))),
% 0.71/0.91      inference('demod', [status(thm)], ['46', '49'])).
% 0.71/0.91  thf('51', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.71/0.91      inference('demod', [status(thm)], ['15', '18'])).
% 0.71/0.91  thf(t143_relat_1, axiom,
% 0.71/0.91    (![A:$i,B:$i,C:$i]:
% 0.71/0.91     ( ( v1_relat_1 @ C ) =>
% 0.71/0.91       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.71/0.91         ( ?[D:$i]:
% 0.71/0.91           ( ( r2_hidden @ D @ B ) & 
% 0.71/0.91             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.71/0.91             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.71/0.91  thf('52', plain,
% 0.71/0.91      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.71/0.91         (~ (r2_hidden @ X13 @ (k9_relat_1 @ X14 @ X12))
% 0.71/0.91          | (r2_hidden @ (k4_tarski @ (sk_D @ X14 @ X12 @ X13) @ X13) @ X14)
% 0.71/0.91          | ~ (v1_relat_1 @ X14))),
% 0.71/0.91      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.71/0.91  thf('53', plain,
% 0.71/0.91      ((~ (v1_relat_1 @ sk_D_2)
% 0.71/0.91        | (r2_hidden @ 
% 0.71/0.91           (k4_tarski @ (sk_D @ sk_D_2 @ sk_C @ sk_E_2) @ sk_E_2) @ sk_D_2))),
% 0.71/0.91      inference('sup-', [status(thm)], ['51', '52'])).
% 0.71/0.91  thf('54', plain, ((v1_relat_1 @ sk_D_2)),
% 0.71/0.91      inference('demod', [status(thm)], ['26', '27'])).
% 0.71/0.91  thf('55', plain,
% 0.71/0.91      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_2 @ sk_C @ sk_E_2) @ sk_E_2) @ 
% 0.71/0.91        sk_D_2)),
% 0.71/0.91      inference('demod', [status(thm)], ['53', '54'])).
% 0.71/0.91  thf('56', plain,
% 0.71/0.91      (![X38 : $i, X39 : $i]:
% 0.71/0.91         ((zip_tseitin_1 @ X38 @ X39) | ((X38) = (k1_xboole_0)))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.71/0.91  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.71/0.91  thf('57', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.71/0.91      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.71/0.91  thf(t3_subset, axiom,
% 0.71/0.91    (![A:$i,B:$i]:
% 0.71/0.91     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.71/0.91  thf('58', plain,
% 0.71/0.91      (![X1 : $i, X3 : $i]:
% 0.71/0.91         ((m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X3)) | ~ (r1_tarski @ X1 @ X3))),
% 0.71/0.91      inference('cnf', [status(esa)], [t3_subset])).
% 0.71/0.91  thf('59', plain,
% 0.71/0.91      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.71/0.91      inference('sup-', [status(thm)], ['57', '58'])).
% 0.71/0.91  thf(t5_subset, axiom,
% 0.71/0.91    (![A:$i,B:$i,C:$i]:
% 0.71/0.91     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.71/0.91          ( v1_xboole_0 @ C ) ) ))).
% 0.71/0.91  thf('60', plain,
% 0.71/0.91      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.71/0.91         (~ (r2_hidden @ X4 @ X5)
% 0.71/0.91          | ~ (v1_xboole_0 @ X6)
% 0.71/0.91          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.71/0.91      inference('cnf', [status(esa)], [t5_subset])).
% 0.71/0.91  thf('61', plain,
% 0.71/0.91      (![X0 : $i, X1 : $i]:
% 0.71/0.91         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.71/0.91      inference('sup-', [status(thm)], ['59', '60'])).
% 0.71/0.91  thf('62', plain,
% 0.71/0.91      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.71/0.91         (~ (r2_hidden @ X1 @ X0)
% 0.71/0.91          | (zip_tseitin_1 @ X0 @ X3)
% 0.71/0.91          | ~ (v1_xboole_0 @ X2))),
% 0.71/0.91      inference('sup-', [status(thm)], ['56', '61'])).
% 0.71/0.91  thf('63', plain,
% 0.71/0.91      (![X0 : $i, X1 : $i]:
% 0.71/0.91         (~ (v1_xboole_0 @ X0) | (zip_tseitin_1 @ sk_D_2 @ X1))),
% 0.71/0.91      inference('sup-', [status(thm)], ['55', '62'])).
% 0.71/0.91  thf('64', plain,
% 0.71/0.91      (![X0 : $i, X1 : $i]:
% 0.71/0.91         ((zip_tseitin_1 @ k1_xboole_0 @ X0)
% 0.71/0.91          | ((sk_A) = (k1_xboole_0))
% 0.71/0.91          | ~ (v1_xboole_0 @ X1))),
% 0.71/0.91      inference('sup+', [status(thm)], ['50', '63'])).
% 0.71/0.91  thf('65', plain,
% 0.71/0.91      (((zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A)
% 0.71/0.91        | ~ (zip_tseitin_1 @ sk_B @ sk_A))),
% 0.71/0.91      inference('sup-', [status(thm)], ['3', '4'])).
% 0.71/0.91  thf('66', plain, (((sk_B) = (k1_xboole_0))),
% 0.71/0.91      inference('simplify', [status(thm)], ['41'])).
% 0.71/0.91  thf('67', plain, (((sk_B) = (k1_xboole_0))),
% 0.71/0.91      inference('simplify', [status(thm)], ['41'])).
% 0.71/0.91  thf('68', plain,
% 0.71/0.91      (((zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ sk_A)
% 0.71/0.91        | ~ (zip_tseitin_1 @ k1_xboole_0 @ sk_A))),
% 0.71/0.91      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.71/0.91  thf('69', plain,
% 0.71/0.91      (![X0 : $i]:
% 0.71/0.91         (~ (v1_xboole_0 @ X0)
% 0.71/0.91          | ((sk_A) = (k1_xboole_0))
% 0.71/0.91          | (zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ sk_A))),
% 0.71/0.91      inference('sup-', [status(thm)], ['64', '68'])).
% 0.71/0.91  thf('70', plain,
% 0.71/0.91      ((~ (zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A)
% 0.71/0.91        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.71/0.91      inference('demod', [status(thm)], ['9', '12'])).
% 0.71/0.91  thf('71', plain, (((sk_B) = (k1_xboole_0))),
% 0.71/0.91      inference('simplify', [status(thm)], ['41'])).
% 0.71/0.91  thf('72', plain,
% 0.71/0.91      ((~ (zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ sk_A)
% 0.71/0.91        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.71/0.91      inference('demod', [status(thm)], ['70', '71'])).
% 0.71/0.91  thf('73', plain,
% 0.71/0.91      (![X0 : $i]:
% 0.71/0.91         (((sk_A) = (k1_xboole_0))
% 0.71/0.91          | ~ (v1_xboole_0 @ X0)
% 0.71/0.91          | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['69', '72'])).
% 0.71/0.91  thf('74', plain,
% 0.71/0.91      ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ (k1_relat_1 @ sk_D_2))),
% 0.71/0.91      inference('sup-', [status(thm)], ['29', '30'])).
% 0.71/0.91  thf('75', plain,
% 0.71/0.91      (![X0 : $i]:
% 0.71/0.91         ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_A)
% 0.71/0.91          | ~ (v1_xboole_0 @ X0)
% 0.71/0.91          | ((sk_A) = (k1_xboole_0)))),
% 0.71/0.91      inference('sup+', [status(thm)], ['73', '74'])).
% 0.71/0.91  thf('76', plain,
% 0.71/0.91      (![X46 : $i]:
% 0.71/0.91         (~ (r2_hidden @ X46 @ sk_A)
% 0.71/0.91          | ~ (r2_hidden @ X46 @ sk_C)
% 0.71/0.91          | ((sk_E_2) != (k1_funct_1 @ sk_D_2 @ X46)))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('77', plain,
% 0.71/0.91      (![X0 : $i]:
% 0.71/0.91         (((sk_A) = (k1_xboole_0))
% 0.71/0.91          | ~ (v1_xboole_0 @ X0)
% 0.71/0.91          | ((sk_E_2)
% 0.71/0.91              != (k1_funct_1 @ sk_D_2 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2)))
% 0.71/0.91          | ~ (r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_C))),
% 0.71/0.91      inference('sup-', [status(thm)], ['75', '76'])).
% 0.71/0.91  thf('78', plain,
% 0.71/0.91      (((sk_E_2) = (k1_funct_1 @ sk_D_2 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['35', '36'])).
% 0.71/0.91  thf('79', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_C)),
% 0.71/0.91      inference('sup-', [status(thm)], ['38', '39'])).
% 0.71/0.91  thf('80', plain,
% 0.71/0.91      (![X0 : $i]:
% 0.71/0.91         (((sk_A) = (k1_xboole_0))
% 0.71/0.91          | ~ (v1_xboole_0 @ X0)
% 0.71/0.91          | ((sk_E_2) != (sk_E_2)))),
% 0.71/0.91      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.71/0.91  thf('81', plain,
% 0.71/0.91      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((sk_A) = (k1_xboole_0)))),
% 0.71/0.91      inference('simplify', [status(thm)], ['80'])).
% 0.71/0.91  thf('82', plain,
% 0.71/0.91      (((zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ sk_A)
% 0.71/0.91        | ~ (zip_tseitin_1 @ k1_xboole_0 @ sk_A))),
% 0.71/0.91      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.71/0.91  thf('83', plain,
% 0.71/0.91      (![X0 : $i]:
% 0.71/0.91         (~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.71/0.91          | ~ (v1_xboole_0 @ X0)
% 0.71/0.91          | (zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ sk_A))),
% 0.71/0.91      inference('sup-', [status(thm)], ['81', '82'])).
% 0.71/0.91  thf('84', plain,
% 0.71/0.91      (![X38 : $i, X39 : $i]:
% 0.71/0.91         ((zip_tseitin_1 @ X38 @ X39) | ((X38) = (k1_xboole_0)))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.71/0.91  thf('85', plain,
% 0.71/0.91      (![X38 : $i, X39 : $i]:
% 0.71/0.91         ((zip_tseitin_1 @ X38 @ X39) | ((X39) != (k1_xboole_0)))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.71/0.91  thf('86', plain, (![X38 : $i]: (zip_tseitin_1 @ X38 @ k1_xboole_0)),
% 0.71/0.91      inference('simplify', [status(thm)], ['85'])).
% 0.71/0.91  thf('87', plain,
% 0.71/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.91         ((zip_tseitin_1 @ X1 @ X0) | (zip_tseitin_1 @ X0 @ X2))),
% 0.71/0.91      inference('sup+', [status(thm)], ['84', '86'])).
% 0.71/0.91  thf('88', plain, (![X0 : $i]: (zip_tseitin_1 @ X0 @ X0)),
% 0.71/0.91      inference('eq_fact', [status(thm)], ['87'])).
% 0.71/0.91  thf('89', plain,
% 0.71/0.91      (![X0 : $i]:
% 0.71/0.91         (~ (v1_xboole_0 @ X0) | (zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ sk_A))),
% 0.71/0.91      inference('demod', [status(thm)], ['83', '88'])).
% 0.71/0.91  thf('90', plain,
% 0.71/0.91      ((~ (zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ sk_A)
% 0.71/0.91        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.71/0.91      inference('demod', [status(thm)], ['70', '71'])).
% 0.71/0.91  thf('91', plain,
% 0.71/0.91      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['89', '90'])).
% 0.71/0.91  thf('92', plain,
% 0.71/0.91      ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ (k1_relat_1 @ sk_D_2))),
% 0.71/0.91      inference('sup-', [status(thm)], ['29', '30'])).
% 0.71/0.91  thf('93', plain,
% 0.71/0.91      (![X0 : $i]:
% 0.71/0.91         ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_A)
% 0.71/0.91          | ~ (v1_xboole_0 @ X0))),
% 0.71/0.91      inference('sup+', [status(thm)], ['91', '92'])).
% 0.71/0.91  thf('94', plain,
% 0.71/0.91      (![X46 : $i]:
% 0.71/0.91         (~ (r2_hidden @ X46 @ sk_A)
% 0.71/0.91          | ~ (r2_hidden @ X46 @ sk_C)
% 0.71/0.91          | ((sk_E_2) != (k1_funct_1 @ sk_D_2 @ X46)))),
% 0.71/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.91  thf('95', plain,
% 0.71/0.91      (![X0 : $i]:
% 0.71/0.91         (~ (v1_xboole_0 @ X0)
% 0.71/0.91          | ((sk_E_2)
% 0.71/0.91              != (k1_funct_1 @ sk_D_2 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2)))
% 0.71/0.91          | ~ (r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_C))),
% 0.71/0.91      inference('sup-', [status(thm)], ['93', '94'])).
% 0.71/0.91  thf('96', plain,
% 0.71/0.91      (((sk_E_2) = (k1_funct_1 @ sk_D_2 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2)))),
% 0.71/0.91      inference('sup-', [status(thm)], ['35', '36'])).
% 0.71/0.91  thf('97', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_C)),
% 0.71/0.91      inference('sup-', [status(thm)], ['38', '39'])).
% 0.71/0.91  thf('98', plain,
% 0.71/0.91      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((sk_E_2) != (sk_E_2)))),
% 0.71/0.91      inference('demod', [status(thm)], ['95', '96', '97'])).
% 0.71/0.91  thf('99', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 0.71/0.91      inference('simplify', [status(thm)], ['98'])).
% 0.71/0.91  thf('100', plain, ($false), inference('sup-', [status(thm)], ['0', '99'])).
% 0.71/0.91  
% 0.71/0.91  % SZS output end Refutation
% 0.71/0.91  
% 0.71/0.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
