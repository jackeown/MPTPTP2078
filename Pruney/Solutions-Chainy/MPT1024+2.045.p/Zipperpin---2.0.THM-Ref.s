%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FdbJXBNhyq

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:40 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.67s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 173 expanded)
%              Number of leaves         :   45 (  72 expanded)
%              Depth                    :   12
%              Number of atoms          :  707 (2087 expanded)
%              Number of equality atoms :   37 (  83 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

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

thf('0',plain,(
    r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( ( k7_relset_1 @ X34 @ X35 @ X33 @ X36 )
        = ( k9_relat_1 @ X33 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

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

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( D
          = ( k1_funct_1 @ A @ E ) )
        & ( r2_hidden @ E @ B )
        & ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ) )).

thf(zf_stmt_3,axiom,(
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

thf('5',plain,(
    ! [X17: $i,X18: $i,X20: $i,X21: $i] :
      ( ( X20
       != ( k9_relat_1 @ X18 @ X17 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X21 @ X17 @ X18 ) @ X21 @ X17 @ X18 )
      | ~ ( r2_hidden @ X21 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X17: $i,X18: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X18 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( r2_hidden @ X21 @ ( k9_relat_1 @ X18 @ X17 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X21 @ X17 @ X18 ) @ X21 @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 @ sk_C @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('12',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 @ sk_C @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8','13'])).

thf('15',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X12 @ ( k1_relat_1 @ X11 ) )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('16',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C ) ),
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

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('18',plain,(
    ! [X37: $i,X38: $i] :
      ( ( zip_tseitin_1 @ X37 @ X38 )
      | ( X37 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('19',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('20',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('21',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ X24 @ X25 )
      | ~ ( r1_tarski @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_1 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_5,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_7,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_1 @ B @ A )
         => ( zip_tseitin_2 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('26',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( zip_tseitin_1 @ X42 @ X43 )
      | ( zip_tseitin_2 @ X44 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('27',plain,
    ( ( zip_tseitin_2 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_2 @ X41 @ X39 @ X40 )
      | ( X39
        = ( k1_relset_1 @ X39 @ X40 @ X41 ) )
      | ~ ( zip_tseitin_2 @ X41 @ X40 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('31',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('33',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('34',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['28','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('38',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X27 @ X28 @ X26 @ X29 ) @ ( k1_zfmisc_1 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('40',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf('43',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['17','42'])).

thf('44',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_A ),
    inference(demod,[status(thm)],['16','43'])).

thf('45',plain,(
    ! [X45: $i] :
      ( ~ ( r2_hidden @ X45 @ sk_A )
      | ~ ( r2_hidden @ X45 @ sk_C )
      | ( sk_E_2
       != ( k1_funct_1 @ sk_D_1 @ X45 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( sk_E_2
     != ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) ) )
    | ~ ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 @ sk_C @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8','13'])).

thf('48',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( X13
        = ( k1_funct_1 @ X11 @ X12 ) )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('49',plain,
    ( sk_E_2
    = ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 @ sk_C @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8','13'])).

thf('51',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( r2_hidden @ X12 @ X14 )
      | ~ ( zip_tseitin_0 @ X12 @ X13 @ X14 @ X11 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('52',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_C ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    sk_E_2 != sk_E_2 ),
    inference(demod,[status(thm)],['46','49','52'])).

thf('54',plain,(
    $false ),
    inference(simplify,[status(thm)],['53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FdbJXBNhyq
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:59:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.67/0.89  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.67/0.89  % Solved by: fo/fo7.sh
% 0.67/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.89  % done 231 iterations in 0.438s
% 0.67/0.89  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.67/0.89  % SZS output start Refutation
% 0.67/0.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.67/0.89  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.67/0.89  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.67/0.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.67/0.89  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.67/0.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.67/0.89  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.67/0.89  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.67/0.89  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.67/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.89  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.67/0.89  thf(sk_C_type, type, sk_C: $i).
% 0.67/0.89  thf(sk_B_type, type, sk_B: $i > $i).
% 0.67/0.89  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.67/0.89  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.67/0.89  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.67/0.89  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.67/0.89  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.67/0.89  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.67/0.89  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.67/0.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.67/0.89  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.67/0.89  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.67/0.89  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.67/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.67/0.89  thf(t115_funct_2, conjecture,
% 0.67/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.89     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.67/0.89         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.67/0.89       ( ![E:$i]:
% 0.67/0.89         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.67/0.89              ( ![F:$i]:
% 0.67/0.89                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.67/0.89                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.67/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.89    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.89        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.67/0.89            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.67/0.89          ( ![E:$i]:
% 0.67/0.89            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.67/0.89                 ( ![F:$i]:
% 0.67/0.89                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.67/0.89                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 0.67/0.89    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 0.67/0.89  thf('0', plain,
% 0.67/0.89      ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C))),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.89  thf('1', plain,
% 0.67/0.89      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.89  thf(redefinition_k7_relset_1, axiom,
% 0.67/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.89       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.67/0.89  thf('2', plain,
% 0.67/0.89      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.67/0.89         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.67/0.89          | ((k7_relset_1 @ X34 @ X35 @ X33 @ X36) = (k9_relat_1 @ X33 @ X36)))),
% 0.67/0.89      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.67/0.89  thf('3', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 0.67/0.89           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.67/0.89      inference('sup-', [status(thm)], ['1', '2'])).
% 0.67/0.89  thf('4', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.67/0.89      inference('demod', [status(thm)], ['0', '3'])).
% 0.67/0.89  thf(d12_funct_1, axiom,
% 0.67/0.89    (![A:$i]:
% 0.67/0.89     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.67/0.89       ( ![B:$i,C:$i]:
% 0.67/0.89         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.67/0.89           ( ![D:$i]:
% 0.67/0.89             ( ( r2_hidden @ D @ C ) <=>
% 0.67/0.89               ( ?[E:$i]:
% 0.67/0.89                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 0.67/0.89                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 0.67/0.89  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.67/0.89  thf(zf_stmt_2, axiom,
% 0.67/0.89    (![E:$i,D:$i,B:$i,A:$i]:
% 0.67/0.89     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.67/0.89       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 0.67/0.89         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 0.67/0.89  thf(zf_stmt_3, axiom,
% 0.67/0.89    (![A:$i]:
% 0.67/0.89     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.67/0.89       ( ![B:$i,C:$i]:
% 0.67/0.89         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.67/0.89           ( ![D:$i]:
% 0.67/0.89             ( ( r2_hidden @ D @ C ) <=>
% 0.67/0.89               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 0.67/0.89  thf('5', plain,
% 0.67/0.89      (![X17 : $i, X18 : $i, X20 : $i, X21 : $i]:
% 0.67/0.89         (((X20) != (k9_relat_1 @ X18 @ X17))
% 0.67/0.89          | (zip_tseitin_0 @ (sk_E_1 @ X21 @ X17 @ X18) @ X21 @ X17 @ X18)
% 0.67/0.89          | ~ (r2_hidden @ X21 @ X20)
% 0.67/0.89          | ~ (v1_funct_1 @ X18)
% 0.67/0.89          | ~ (v1_relat_1 @ X18))),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.67/0.89  thf('6', plain,
% 0.67/0.89      (![X17 : $i, X18 : $i, X21 : $i]:
% 0.67/0.89         (~ (v1_relat_1 @ X18)
% 0.67/0.89          | ~ (v1_funct_1 @ X18)
% 0.67/0.89          | ~ (r2_hidden @ X21 @ (k9_relat_1 @ X18 @ X17))
% 0.67/0.89          | (zip_tseitin_0 @ (sk_E_1 @ X21 @ X17 @ X18) @ X21 @ X17 @ X18))),
% 0.67/0.89      inference('simplify', [status(thm)], ['5'])).
% 0.67/0.89  thf('7', plain,
% 0.67/0.89      (((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.67/0.89         sk_D_1)
% 0.67/0.89        | ~ (v1_funct_1 @ sk_D_1)
% 0.67/0.89        | ~ (v1_relat_1 @ sk_D_1))),
% 0.67/0.89      inference('sup-', [status(thm)], ['4', '6'])).
% 0.67/0.89  thf('8', plain, ((v1_funct_1 @ sk_D_1)),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.89  thf('9', plain,
% 0.67/0.89      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.89  thf(cc2_relat_1, axiom,
% 0.67/0.89    (![A:$i]:
% 0.67/0.89     ( ( v1_relat_1 @ A ) =>
% 0.67/0.89       ( ![B:$i]:
% 0.67/0.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.67/0.89  thf('10', plain,
% 0.67/0.89      (![X7 : $i, X8 : $i]:
% 0.67/0.89         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.67/0.89          | (v1_relat_1 @ X7)
% 0.67/0.89          | ~ (v1_relat_1 @ X8))),
% 0.67/0.89      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.67/0.89  thf('11', plain,
% 0.67/0.89      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D_1))),
% 0.67/0.89      inference('sup-', [status(thm)], ['9', '10'])).
% 0.67/0.89  thf(fc6_relat_1, axiom,
% 0.67/0.89    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.67/0.89  thf('12', plain,
% 0.67/0.89      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.67/0.89      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.67/0.89  thf('13', plain, ((v1_relat_1 @ sk_D_1)),
% 0.67/0.89      inference('demod', [status(thm)], ['11', '12'])).
% 0.67/0.89  thf('14', plain,
% 0.67/0.89      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.67/0.89        sk_D_1)),
% 0.67/0.89      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.67/0.89  thf('15', plain,
% 0.67/0.89      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.67/0.89         ((r2_hidden @ X12 @ (k1_relat_1 @ X11))
% 0.67/0.89          | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X11))),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.67/0.89  thf('16', plain,
% 0.67/0.89      ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ (k1_relat_1 @ sk_D_1))),
% 0.67/0.89      inference('sup-', [status(thm)], ['14', '15'])).
% 0.67/0.89  thf('17', plain,
% 0.67/0.89      ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C))),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.89  thf(d1_funct_2, axiom,
% 0.67/0.89    (![A:$i,B:$i,C:$i]:
% 0.67/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.89       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.67/0.89           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.67/0.89             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.67/0.89         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.67/0.89           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.67/0.89             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.67/0.89  thf(zf_stmt_4, axiom,
% 0.67/0.89    (![B:$i,A:$i]:
% 0.67/0.89     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.67/0.89       ( zip_tseitin_1 @ B @ A ) ))).
% 0.67/0.89  thf('18', plain,
% 0.67/0.89      (![X37 : $i, X38 : $i]:
% 0.67/0.89         ((zip_tseitin_1 @ X37 @ X38) | ((X37) = (k1_xboole_0)))),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.67/0.89  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.67/0.89  thf('19', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.67/0.89      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.67/0.89  thf(d1_xboole_0, axiom,
% 0.67/0.89    (![A:$i]:
% 0.67/0.89     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.67/0.89  thf('20', plain,
% 0.67/0.89      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.67/0.89      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.67/0.89  thf(t7_ordinal1, axiom,
% 0.67/0.89    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.67/0.89  thf('21', plain,
% 0.67/0.89      (![X24 : $i, X25 : $i]:
% 0.67/0.89         (~ (r2_hidden @ X24 @ X25) | ~ (r1_tarski @ X25 @ X24))),
% 0.67/0.89      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.67/0.89  thf('22', plain,
% 0.67/0.89      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.67/0.89      inference('sup-', [status(thm)], ['20', '21'])).
% 0.67/0.89  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.67/0.89      inference('sup-', [status(thm)], ['19', '22'])).
% 0.67/0.89  thf('24', plain,
% 0.67/0.89      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_1 @ X0 @ X1))),
% 0.67/0.89      inference('sup+', [status(thm)], ['18', '23'])).
% 0.67/0.89  thf('25', plain,
% 0.67/0.89      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.89  thf(zf_stmt_5, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.67/0.89  thf(zf_stmt_6, axiom,
% 0.67/0.89    (![C:$i,B:$i,A:$i]:
% 0.67/0.89     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.67/0.89       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.67/0.89  thf(zf_stmt_7, type, zip_tseitin_1 : $i > $i > $o).
% 0.67/0.89  thf(zf_stmt_8, axiom,
% 0.67/0.89    (![A:$i,B:$i,C:$i]:
% 0.67/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.89       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.67/0.89         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.67/0.89           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.67/0.89             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.67/0.89  thf('26', plain,
% 0.67/0.89      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.67/0.89         (~ (zip_tseitin_1 @ X42 @ X43)
% 0.67/0.89          | (zip_tseitin_2 @ X44 @ X42 @ X43)
% 0.67/0.89          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42))))),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.67/0.89  thf('27', plain,
% 0.67/0.89      (((zip_tseitin_2 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.67/0.89        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A))),
% 0.67/0.89      inference('sup-', [status(thm)], ['25', '26'])).
% 0.67/0.89  thf('28', plain,
% 0.67/0.89      (((v1_xboole_0 @ sk_B_1) | (zip_tseitin_2 @ sk_D_1 @ sk_B_1 @ sk_A))),
% 0.67/0.89      inference('sup-', [status(thm)], ['24', '27'])).
% 0.67/0.89  thf('29', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B_1)),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.89  thf('30', plain,
% 0.67/0.89      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.67/0.89         (~ (v1_funct_2 @ X41 @ X39 @ X40)
% 0.67/0.89          | ((X39) = (k1_relset_1 @ X39 @ X40 @ X41))
% 0.67/0.89          | ~ (zip_tseitin_2 @ X41 @ X40 @ X39))),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.67/0.89  thf('31', plain,
% 0.67/0.89      ((~ (zip_tseitin_2 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.67/0.89        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1)))),
% 0.67/0.89      inference('sup-', [status(thm)], ['29', '30'])).
% 0.67/0.89  thf('32', plain,
% 0.67/0.89      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.89  thf(redefinition_k1_relset_1, axiom,
% 0.67/0.89    (![A:$i,B:$i,C:$i]:
% 0.67/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.89       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.67/0.89  thf('33', plain,
% 0.67/0.89      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.67/0.89         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 0.67/0.89          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.67/0.89      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.67/0.89  thf('34', plain,
% 0.67/0.89      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.67/0.89      inference('sup-', [status(thm)], ['32', '33'])).
% 0.67/0.89  thf('35', plain,
% 0.67/0.89      ((~ (zip_tseitin_2 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.67/0.89        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.67/0.89      inference('demod', [status(thm)], ['31', '34'])).
% 0.67/0.89  thf('36', plain,
% 0.67/0.89      (((v1_xboole_0 @ sk_B_1) | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.67/0.89      inference('sup-', [status(thm)], ['28', '35'])).
% 0.67/0.89  thf('37', plain,
% 0.67/0.89      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.89  thf(dt_k7_relset_1, axiom,
% 0.67/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.67/0.89       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.67/0.89  thf('38', plain,
% 0.67/0.89      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.67/0.89         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.67/0.89          | (m1_subset_1 @ (k7_relset_1 @ X27 @ X28 @ X26 @ X29) @ 
% 0.67/0.89             (k1_zfmisc_1 @ X28)))),
% 0.67/0.89      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.67/0.89  thf('39', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0) @ 
% 0.67/0.89          (k1_zfmisc_1 @ sk_B_1))),
% 0.67/0.89      inference('sup-', [status(thm)], ['37', '38'])).
% 0.67/0.89  thf(t5_subset, axiom,
% 0.67/0.89    (![A:$i,B:$i,C:$i]:
% 0.67/0.89     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.67/0.89          ( v1_xboole_0 @ C ) ) ))).
% 0.67/0.89  thf('40', plain,
% 0.67/0.89      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.67/0.89         (~ (r2_hidden @ X4 @ X5)
% 0.67/0.89          | ~ (v1_xboole_0 @ X6)
% 0.67/0.89          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.67/0.89      inference('cnf', [status(esa)], [t5_subset])).
% 0.67/0.89  thf('41', plain,
% 0.67/0.89      (![X0 : $i, X1 : $i]:
% 0.67/0.89         (~ (v1_xboole_0 @ sk_B_1)
% 0.67/0.89          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)))),
% 0.67/0.89      inference('sup-', [status(thm)], ['39', '40'])).
% 0.67/0.89  thf('42', plain,
% 0.67/0.89      (![X0 : $i, X1 : $i]:
% 0.67/0.89         (((sk_A) = (k1_relat_1 @ sk_D_1))
% 0.67/0.89          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)))),
% 0.67/0.89      inference('sup-', [status(thm)], ['36', '41'])).
% 0.67/0.89  thf('43', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.67/0.89      inference('sup-', [status(thm)], ['17', '42'])).
% 0.67/0.89  thf('44', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_A)),
% 0.67/0.89      inference('demod', [status(thm)], ['16', '43'])).
% 0.67/0.89  thf('45', plain,
% 0.67/0.89      (![X45 : $i]:
% 0.67/0.89         (~ (r2_hidden @ X45 @ sk_A)
% 0.67/0.89          | ~ (r2_hidden @ X45 @ sk_C)
% 0.67/0.89          | ((sk_E_2) != (k1_funct_1 @ sk_D_1 @ X45)))),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.89  thf('46', plain,
% 0.67/0.89      ((((sk_E_2) != (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1)))
% 0.67/0.89        | ~ (r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_C))),
% 0.67/0.89      inference('sup-', [status(thm)], ['44', '45'])).
% 0.67/0.89  thf('47', plain,
% 0.67/0.89      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.67/0.89        sk_D_1)),
% 0.67/0.89      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.67/0.89  thf('48', plain,
% 0.67/0.89      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.67/0.89         (((X13) = (k1_funct_1 @ X11 @ X12))
% 0.67/0.89          | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X11))),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.67/0.89  thf('49', plain,
% 0.67/0.89      (((sk_E_2) = (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1)))),
% 0.67/0.89      inference('sup-', [status(thm)], ['47', '48'])).
% 0.67/0.89  thf('50', plain,
% 0.67/0.89      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.67/0.89        sk_D_1)),
% 0.67/0.89      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.67/0.89  thf('51', plain,
% 0.67/0.89      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.67/0.89         ((r2_hidden @ X12 @ X14) | ~ (zip_tseitin_0 @ X12 @ X13 @ X14 @ X11))),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.67/0.89  thf('52', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_C)),
% 0.67/0.89      inference('sup-', [status(thm)], ['50', '51'])).
% 0.67/0.89  thf('53', plain, (((sk_E_2) != (sk_E_2))),
% 0.67/0.89      inference('demod', [status(thm)], ['46', '49', '52'])).
% 0.67/0.89  thf('54', plain, ($false), inference('simplify', [status(thm)], ['53'])).
% 0.67/0.89  
% 0.67/0.89  % SZS output end Refutation
% 0.67/0.89  
% 0.71/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
