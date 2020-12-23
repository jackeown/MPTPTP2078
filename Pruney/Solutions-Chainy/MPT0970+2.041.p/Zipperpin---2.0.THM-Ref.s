%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ei5ZTqt5YQ

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:22 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 237 expanded)
%              Number of leaves         :   48 (  91 expanded)
%              Depth                    :   21
%              Number of atoms          :  891 (3075 expanded)
%              Number of equality atoms :   53 ( 202 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_3_type,type,(
    sk_E_3: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(t16_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( ( r2_hidden @ E @ A )
                    & ( D
                      = ( k1_funct_1 @ C @ E ) ) ) )
       => ( ( k2_relset_1 @ A @ B @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ! [D: $i] :
              ~ ( ( r2_hidden @ D @ B )
                & ! [E: $i] :
                    ~ ( ( r2_hidden @ E @ A )
                      & ( D
                        = ( k1_funct_1 @ C @ E ) ) ) )
         => ( ( k2_relset_1 @ A @ B @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k2_relset_1 @ X34 @ X35 @ X33 )
        = ( k2_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('2',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) )
      <=> ( ( k2_relset_1 @ A @ B @ C )
          = B ) ) ) )).

thf('5',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ X38 @ X36 ) @ X36 )
      | ( ( k2_relset_1 @ X37 @ X36 @ X38 )
        = X36 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_relset_1])).

thf('6',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
      = sk_B )
    | ( r2_hidden @ ( sk_D_2 @ sk_C @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('8',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = sk_B )
    | ( r2_hidden @ ( sk_D_2 @ sk_C @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('11',plain,(
    ( k2_relat_1 @ sk_C )
 != sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ ( sk_D_2 @ sk_C @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X49: $i] :
      ( ~ ( r2_hidden @ X49 @ sk_B )
      | ( r2_hidden @ ( sk_E_3 @ X49 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r2_hidden @ ( sk_E_3 @ ( sk_D_2 @ sk_C @ sk_B ) ) @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r2_hidden @ ( sk_E_3 @ ( sk_D_2 @ sk_C @ sk_B ) ) @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('16',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
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

thf('17',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( v1_funct_2 @ X45 @ X43 @ X44 )
      | ( X43
        = ( k1_relset_1 @ X43 @ X44 @ X45 ) )
      | ~ ( zip_tseitin_2 @ X45 @ X44 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('18',plain,
    ( ~ ( zip_tseitin_2 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( v5_relat_1 @ X27 @ X29 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('21',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['19','20'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('22',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v5_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k2_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('25',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_relat_1 @ X4 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('27',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('28',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['23','28'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('30',plain,(
    ! [X41: $i,X42: $i] :
      ( ( zip_tseitin_1 @ X41 @ X42 )
      | ( X41 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('31',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['30','31'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('33',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X1 @ X2 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_C )
        = sk_B )
      | ( zip_tseitin_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('37',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ~ ( zip_tseitin_1 @ X46 @ X47 )
      | ( zip_tseitin_2 @ X48 @ X46 @ X47 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('38',plain,
    ( ( zip_tseitin_2 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = sk_B )
    | ( zip_tseitin_2 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['35','38'])).

thf('40',plain,(
    ( k2_relat_1 @ sk_C )
 != sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('41',plain,(
    zip_tseitin_2 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['39','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('43',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( ( k1_relset_1 @ X31 @ X32 @ X30 )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('44',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['18','41','44'])).

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

thf(zf_stmt_6,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( D
          = ( k1_funct_1 @ A @ E ) )
        & ( r2_hidden @ E @ B )
        & ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ) )).

thf('46',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 @ X17 @ X18 )
      | ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X18 ) )
      | ~ ( r2_hidden @ X15 @ X17 )
      | ( X16
       != ( k1_funct_1 @ X18 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('47',plain,(
    ! [X15: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X15 @ X17 )
      | ~ ( r2_hidden @ X15 @ ( k1_relat_1 @ X18 ) )
      | ( zip_tseitin_0 @ X15 @ ( k1_funct_1 @ X18 @ X15 ) @ X17 @ X18 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( zip_tseitin_0 @ X0 @ ( k1_funct_1 @ sk_C @ X0 ) @ X1 @ sk_C )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_E_3 @ ( sk_D_2 @ sk_C @ sk_B ) ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_E_3 @ ( sk_D_2 @ sk_C @ sk_B ) ) @ ( k1_funct_1 @ sk_C @ ( sk_E_3 @ ( sk_D_2 @ sk_C @ sk_B ) ) ) @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','48'])).

thf('50',plain,(
    r2_hidden @ ( sk_D_2 @ sk_C @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['8','11'])).

thf('51',plain,(
    ! [X49: $i] :
      ( ~ ( r2_hidden @ X49 @ sk_B )
      | ( X49
        = ( k1_funct_1 @ sk_C @ ( sk_E_3 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( sk_D_2 @ sk_C @ sk_B )
    = ( k1_funct_1 @ sk_C @ ( sk_E_3 @ ( sk_D_2 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_E_3 @ ( sk_D_2 @ sk_C @ sk_B ) ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_E_3 @ ( sk_D_2 @ sk_C @ sk_B ) ) @ ( sk_D_2 @ sk_C @ sk_B ) @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['49','52'])).

thf('54',plain,(
    zip_tseitin_0 @ ( sk_E_3 @ ( sk_D_2 @ sk_C @ sk_B ) ) @ ( sk_D_2 @ sk_C @ sk_B ) @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['14','53'])).

thf(zf_stmt_7,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

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

thf('55',plain,(
    ! [X20: $i,X21: $i,X23: $i,X25: $i,X26: $i] :
      ( ( X23
       != ( k9_relat_1 @ X21 @ X20 ) )
      | ( r2_hidden @ X25 @ X23 )
      | ~ ( zip_tseitin_0 @ X26 @ X25 @ X20 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('56',plain,(
    ! [X20: $i,X21: $i,X25: $i,X26: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( zip_tseitin_0 @ X26 @ X25 @ X20 @ X21 )
      | ( r2_hidden @ X25 @ ( k9_relat_1 @ X21 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_C @ sk_B ) @ ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['54','56'])).

thf('58',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['26','27'])).

thf('60',plain,(
    r2_hidden @ ( sk_D_2 @ sk_C @ sk_B ) @ ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['57','58','59'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('61',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ ( k9_relat_1 @ X13 @ X11 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X13 @ X11 @ X12 ) @ X12 ) @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('62',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_C @ sk_A @ ( sk_D_2 @ sk_C @ sk_B ) ) @ ( sk_D_2 @ sk_C @ sk_B ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['26','27'])).

thf('64',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_C @ sk_A @ ( sk_D_2 @ sk_C @ sk_B ) ) @ ( sk_D_2 @ sk_C @ sk_B ) ) @ sk_C ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X36: $i,X37: $i,X38: $i,X40: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X40 @ ( sk_D_2 @ X38 @ X36 ) ) @ X38 )
      | ( ( k2_relset_1 @ X37 @ X36 @ X38 )
        = X36 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_relset_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X0 @ sk_B @ sk_C )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference('sup-',[status(thm)],['3','66'])).

thf('68',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['2','67'])).

thf('69',plain,(
    ( k2_relat_1 @ sk_C )
 != sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('70',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['68','69'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ei5ZTqt5YQ
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:51:50 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.42/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.62  % Solved by: fo/fo7.sh
% 0.42/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.62  % done 138 iterations in 0.166s
% 0.42/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.62  % SZS output start Refutation
% 0.42/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.42/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.62  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.42/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.62  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.42/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.42/0.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.42/0.62  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.42/0.62  thf(sk_E_3_type, type, sk_E_3: $i > $i).
% 0.42/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.42/0.62  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.42/0.62  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.42/0.62  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.42/0.62  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.42/0.62  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.42/0.62  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.42/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.62  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.42/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.42/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.62  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.42/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.62  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.42/0.62  thf(t16_funct_2, conjecture,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.42/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.62       ( ( ![D:$i]:
% 0.42/0.62           ( ~( ( r2_hidden @ D @ B ) & 
% 0.42/0.62                ( ![E:$i]:
% 0.42/0.62                  ( ~( ( r2_hidden @ E @ A ) & 
% 0.42/0.62                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.42/0.62         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.42/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.62    (~( ![A:$i,B:$i,C:$i]:
% 0.42/0.62        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.42/0.62            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.62          ( ( ![D:$i]:
% 0.42/0.62              ( ~( ( r2_hidden @ D @ B ) & 
% 0.42/0.62                   ( ![E:$i]:
% 0.42/0.62                     ( ~( ( r2_hidden @ E @ A ) & 
% 0.42/0.62                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.42/0.62            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.42/0.62    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 0.42/0.62  thf('0', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(redefinition_k2_relset_1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.62       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.42/0.62  thf('1', plain,
% 0.42/0.62      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.42/0.62         (((k2_relset_1 @ X34 @ X35 @ X33) = (k2_relat_1 @ X33))
% 0.42/0.62          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.42/0.62      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.42/0.62  thf('2', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.42/0.62      inference('sup-', [status(thm)], ['0', '1'])).
% 0.42/0.62  thf('3', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('4', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(t23_relset_1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.62       ( ( ![D:$i]:
% 0.42/0.62           ( ~( ( r2_hidden @ D @ B ) & 
% 0.42/0.62                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) ) ) ) ) ) <=>
% 0.42/0.62         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.42/0.62  thf('5', plain,
% 0.42/0.62      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.42/0.62         ((r2_hidden @ (sk_D_2 @ X38 @ X36) @ X36)
% 0.42/0.62          | ((k2_relset_1 @ X37 @ X36 @ X38) = (X36))
% 0.42/0.62          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 0.42/0.62      inference('cnf', [status(esa)], [t23_relset_1])).
% 0.42/0.62  thf('6', plain,
% 0.42/0.62      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))
% 0.42/0.62        | (r2_hidden @ (sk_D_2 @ sk_C @ sk_B) @ sk_B))),
% 0.42/0.62      inference('sup-', [status(thm)], ['4', '5'])).
% 0.42/0.62  thf('7', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.42/0.62      inference('sup-', [status(thm)], ['0', '1'])).
% 0.42/0.62  thf('8', plain,
% 0.42/0.62      ((((k2_relat_1 @ sk_C) = (sk_B))
% 0.42/0.62        | (r2_hidden @ (sk_D_2 @ sk_C @ sk_B) @ sk_B))),
% 0.42/0.62      inference('demod', [status(thm)], ['6', '7'])).
% 0.42/0.62  thf('9', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('10', plain,
% 0.42/0.62      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.42/0.62      inference('sup-', [status(thm)], ['0', '1'])).
% 0.42/0.62  thf('11', plain, (((k2_relat_1 @ sk_C) != (sk_B))),
% 0.42/0.62      inference('demod', [status(thm)], ['9', '10'])).
% 0.42/0.62  thf('12', plain, ((r2_hidden @ (sk_D_2 @ sk_C @ sk_B) @ sk_B)),
% 0.42/0.62      inference('simplify_reflect-', [status(thm)], ['8', '11'])).
% 0.42/0.62  thf('13', plain,
% 0.42/0.62      (![X49 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X49 @ sk_B) | (r2_hidden @ (sk_E_3 @ X49) @ sk_A))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('14', plain, ((r2_hidden @ (sk_E_3 @ (sk_D_2 @ sk_C @ sk_B)) @ sk_A)),
% 0.42/0.62      inference('sup-', [status(thm)], ['12', '13'])).
% 0.42/0.62  thf('15', plain, ((r2_hidden @ (sk_E_3 @ (sk_D_2 @ sk_C @ sk_B)) @ sk_A)),
% 0.42/0.62      inference('sup-', [status(thm)], ['12', '13'])).
% 0.42/0.62  thf('16', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(d1_funct_2, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.62       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.62           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.42/0.62             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.42/0.62         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.62           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.42/0.62             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.42/0.62  thf(zf_stmt_1, axiom,
% 0.42/0.62    (![C:$i,B:$i,A:$i]:
% 0.42/0.62     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.42/0.62       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.42/0.62  thf('17', plain,
% 0.42/0.62      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.42/0.62         (~ (v1_funct_2 @ X45 @ X43 @ X44)
% 0.42/0.62          | ((X43) = (k1_relset_1 @ X43 @ X44 @ X45))
% 0.42/0.62          | ~ (zip_tseitin_2 @ X45 @ X44 @ X43))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.42/0.62  thf('18', plain,
% 0.42/0.62      ((~ (zip_tseitin_2 @ sk_C @ sk_B @ sk_A)
% 0.42/0.62        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['16', '17'])).
% 0.42/0.62  thf('19', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(cc2_relset_1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.62       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.42/0.62  thf('20', plain,
% 0.42/0.62      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.42/0.62         ((v5_relat_1 @ X27 @ X29)
% 0.42/0.62          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.42/0.62      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.42/0.62  thf('21', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.42/0.62      inference('sup-', [status(thm)], ['19', '20'])).
% 0.42/0.62  thf(d19_relat_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( v1_relat_1 @ B ) =>
% 0.42/0.62       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.42/0.62  thf('22', plain,
% 0.42/0.62      (![X6 : $i, X7 : $i]:
% 0.42/0.62         (~ (v5_relat_1 @ X6 @ X7)
% 0.42/0.62          | (r1_tarski @ (k2_relat_1 @ X6) @ X7)
% 0.42/0.62          | ~ (v1_relat_1 @ X6))),
% 0.42/0.62      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.42/0.62  thf('23', plain,
% 0.42/0.62      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.42/0.62      inference('sup-', [status(thm)], ['21', '22'])).
% 0.42/0.62  thf('24', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(cc2_relat_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( v1_relat_1 @ A ) =>
% 0.42/0.62       ( ![B:$i]:
% 0.42/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.42/0.62  thf('25', plain,
% 0.42/0.62      (![X4 : $i, X5 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.42/0.62          | (v1_relat_1 @ X4)
% 0.42/0.62          | ~ (v1_relat_1 @ X5))),
% 0.42/0.62      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.42/0.62  thf('26', plain,
% 0.42/0.62      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.42/0.62      inference('sup-', [status(thm)], ['24', '25'])).
% 0.42/0.62  thf(fc6_relat_1, axiom,
% 0.42/0.62    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.42/0.62  thf('27', plain,
% 0.42/0.62      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.42/0.62      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.42/0.62  thf('28', plain, ((v1_relat_1 @ sk_C)),
% 0.42/0.62      inference('demod', [status(thm)], ['26', '27'])).
% 0.42/0.62  thf('29', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.42/0.62      inference('demod', [status(thm)], ['23', '28'])).
% 0.42/0.62  thf(zf_stmt_2, axiom,
% 0.42/0.62    (![B:$i,A:$i]:
% 0.42/0.62     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.42/0.62       ( zip_tseitin_1 @ B @ A ) ))).
% 0.42/0.62  thf('30', plain,
% 0.42/0.62      (![X41 : $i, X42 : $i]:
% 0.42/0.62         ((zip_tseitin_1 @ X41 @ X42) | ((X41) = (k1_xboole_0)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.42/0.62  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.42/0.62  thf('31', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.42/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.42/0.62  thf('32', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         ((r1_tarski @ X0 @ X1) | (zip_tseitin_1 @ X0 @ X2))),
% 0.42/0.62      inference('sup+', [status(thm)], ['30', '31'])).
% 0.42/0.62  thf(d10_xboole_0, axiom,
% 0.42/0.62    (![A:$i,B:$i]:
% 0.42/0.62     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.42/0.62  thf('33', plain,
% 0.42/0.62      (![X0 : $i, X2 : $i]:
% 0.42/0.62         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.42/0.62      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.42/0.62  thf('34', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.62         ((zip_tseitin_1 @ X1 @ X2) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['32', '33'])).
% 0.42/0.62  thf('35', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (((k2_relat_1 @ sk_C) = (sk_B)) | (zip_tseitin_1 @ sk_B @ X0))),
% 0.42/0.62      inference('sup-', [status(thm)], ['29', '34'])).
% 0.42/0.62  thf('36', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.42/0.62  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $o).
% 0.42/0.62  thf(zf_stmt_5, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.62       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.42/0.62         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.42/0.62           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.42/0.62             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.42/0.62  thf('37', plain,
% 0.42/0.62      (![X46 : $i, X47 : $i, X48 : $i]:
% 0.42/0.62         (~ (zip_tseitin_1 @ X46 @ X47)
% 0.42/0.62          | (zip_tseitin_2 @ X48 @ X46 @ X47)
% 0.42/0.62          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46))))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.42/0.62  thf('38', plain,
% 0.42/0.62      (((zip_tseitin_2 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_1 @ sk_B @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['36', '37'])).
% 0.42/0.62  thf('39', plain,
% 0.42/0.62      ((((k2_relat_1 @ sk_C) = (sk_B)) | (zip_tseitin_2 @ sk_C @ sk_B @ sk_A))),
% 0.42/0.62      inference('sup-', [status(thm)], ['35', '38'])).
% 0.42/0.62  thf('40', plain, (((k2_relat_1 @ sk_C) != (sk_B))),
% 0.42/0.62      inference('demod', [status(thm)], ['9', '10'])).
% 0.42/0.62  thf('41', plain, ((zip_tseitin_2 @ sk_C @ sk_B @ sk_A)),
% 0.42/0.62      inference('simplify_reflect-', [status(thm)], ['39', '40'])).
% 0.42/0.62  thf('42', plain,
% 0.42/0.62      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf(redefinition_k1_relset_1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.62       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.42/0.62  thf('43', plain,
% 0.42/0.62      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.42/0.62         (((k1_relset_1 @ X31 @ X32 @ X30) = (k1_relat_1 @ X30))
% 0.42/0.62          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.42/0.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.42/0.62  thf('44', plain,
% 0.42/0.62      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.42/0.62      inference('sup-', [status(thm)], ['42', '43'])).
% 0.42/0.62  thf('45', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.42/0.62      inference('demod', [status(thm)], ['18', '41', '44'])).
% 0.42/0.62  thf(d12_funct_1, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.42/0.62       ( ![B:$i,C:$i]:
% 0.42/0.62         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.42/0.62           ( ![D:$i]:
% 0.42/0.62             ( ( r2_hidden @ D @ C ) <=>
% 0.42/0.62               ( ?[E:$i]:
% 0.42/0.62                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 0.42/0.62                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 0.42/0.62  thf(zf_stmt_6, axiom,
% 0.42/0.62    (![E:$i,D:$i,B:$i,A:$i]:
% 0.42/0.62     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.42/0.62       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 0.42/0.62         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 0.42/0.62  thf('46', plain,
% 0.42/0.62      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.42/0.62         ((zip_tseitin_0 @ X15 @ X16 @ X17 @ X18)
% 0.42/0.62          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ X18))
% 0.42/0.62          | ~ (r2_hidden @ X15 @ X17)
% 0.42/0.62          | ((X16) != (k1_funct_1 @ X18 @ X15)))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.42/0.62  thf('47', plain,
% 0.42/0.62      (![X15 : $i, X17 : $i, X18 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X15 @ X17)
% 0.42/0.62          | ~ (r2_hidden @ X15 @ (k1_relat_1 @ X18))
% 0.42/0.62          | (zip_tseitin_0 @ X15 @ (k1_funct_1 @ X18 @ X15) @ X17 @ X18))),
% 0.42/0.62      inference('simplify', [status(thm)], ['46'])).
% 0.42/0.62  thf('48', plain,
% 0.42/0.62      (![X0 : $i, X1 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X0 @ sk_A)
% 0.42/0.62          | (zip_tseitin_0 @ X0 @ (k1_funct_1 @ sk_C @ X0) @ X1 @ sk_C)
% 0.42/0.62          | ~ (r2_hidden @ X0 @ X1))),
% 0.42/0.62      inference('sup-', [status(thm)], ['45', '47'])).
% 0.42/0.62  thf('49', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (r2_hidden @ (sk_E_3 @ (sk_D_2 @ sk_C @ sk_B)) @ X0)
% 0.42/0.62          | (zip_tseitin_0 @ (sk_E_3 @ (sk_D_2 @ sk_C @ sk_B)) @ 
% 0.42/0.62             (k1_funct_1 @ sk_C @ (sk_E_3 @ (sk_D_2 @ sk_C @ sk_B))) @ X0 @ 
% 0.42/0.62             sk_C))),
% 0.42/0.62      inference('sup-', [status(thm)], ['15', '48'])).
% 0.42/0.62  thf('50', plain, ((r2_hidden @ (sk_D_2 @ sk_C @ sk_B) @ sk_B)),
% 0.42/0.62      inference('simplify_reflect-', [status(thm)], ['8', '11'])).
% 0.42/0.62  thf('51', plain,
% 0.42/0.62      (![X49 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X49 @ sk_B)
% 0.42/0.62          | ((X49) = (k1_funct_1 @ sk_C @ (sk_E_3 @ X49))))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('52', plain,
% 0.42/0.62      (((sk_D_2 @ sk_C @ sk_B)
% 0.42/0.62         = (k1_funct_1 @ sk_C @ (sk_E_3 @ (sk_D_2 @ sk_C @ sk_B))))),
% 0.42/0.62      inference('sup-', [status(thm)], ['50', '51'])).
% 0.42/0.62  thf('53', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (r2_hidden @ (sk_E_3 @ (sk_D_2 @ sk_C @ sk_B)) @ X0)
% 0.42/0.62          | (zip_tseitin_0 @ (sk_E_3 @ (sk_D_2 @ sk_C @ sk_B)) @ 
% 0.42/0.62             (sk_D_2 @ sk_C @ sk_B) @ X0 @ sk_C))),
% 0.42/0.62      inference('demod', [status(thm)], ['49', '52'])).
% 0.42/0.62  thf('54', plain,
% 0.42/0.62      ((zip_tseitin_0 @ (sk_E_3 @ (sk_D_2 @ sk_C @ sk_B)) @ 
% 0.42/0.62        (sk_D_2 @ sk_C @ sk_B) @ sk_A @ sk_C)),
% 0.42/0.62      inference('sup-', [status(thm)], ['14', '53'])).
% 0.42/0.62  thf(zf_stmt_7, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.42/0.62  thf(zf_stmt_8, axiom,
% 0.42/0.62    (![A:$i]:
% 0.42/0.62     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.42/0.62       ( ![B:$i,C:$i]:
% 0.42/0.62         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.42/0.62           ( ![D:$i]:
% 0.42/0.62             ( ( r2_hidden @ D @ C ) <=>
% 0.42/0.62               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 0.42/0.62  thf('55', plain,
% 0.42/0.62      (![X20 : $i, X21 : $i, X23 : $i, X25 : $i, X26 : $i]:
% 0.42/0.62         (((X23) != (k9_relat_1 @ X21 @ X20))
% 0.42/0.62          | (r2_hidden @ X25 @ X23)
% 0.42/0.62          | ~ (zip_tseitin_0 @ X26 @ X25 @ X20 @ X21)
% 0.42/0.62          | ~ (v1_funct_1 @ X21)
% 0.42/0.62          | ~ (v1_relat_1 @ X21))),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.42/0.62  thf('56', plain,
% 0.42/0.62      (![X20 : $i, X21 : $i, X25 : $i, X26 : $i]:
% 0.42/0.62         (~ (v1_relat_1 @ X21)
% 0.42/0.62          | ~ (v1_funct_1 @ X21)
% 0.42/0.62          | ~ (zip_tseitin_0 @ X26 @ X25 @ X20 @ X21)
% 0.42/0.62          | (r2_hidden @ X25 @ (k9_relat_1 @ X21 @ X20)))),
% 0.42/0.62      inference('simplify', [status(thm)], ['55'])).
% 0.42/0.62  thf('57', plain,
% 0.42/0.62      (((r2_hidden @ (sk_D_2 @ sk_C @ sk_B) @ (k9_relat_1 @ sk_C @ sk_A))
% 0.42/0.62        | ~ (v1_funct_1 @ sk_C)
% 0.42/0.62        | ~ (v1_relat_1 @ sk_C))),
% 0.42/0.62      inference('sup-', [status(thm)], ['54', '56'])).
% 0.42/0.62  thf('58', plain, ((v1_funct_1 @ sk_C)),
% 0.42/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.62  thf('59', plain, ((v1_relat_1 @ sk_C)),
% 0.42/0.62      inference('demod', [status(thm)], ['26', '27'])).
% 0.42/0.62  thf('60', plain,
% 0.42/0.62      ((r2_hidden @ (sk_D_2 @ sk_C @ sk_B) @ (k9_relat_1 @ sk_C @ sk_A))),
% 0.42/0.62      inference('demod', [status(thm)], ['57', '58', '59'])).
% 0.42/0.62  thf(t143_relat_1, axiom,
% 0.42/0.62    (![A:$i,B:$i,C:$i]:
% 0.42/0.62     ( ( v1_relat_1 @ C ) =>
% 0.42/0.62       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.42/0.62         ( ?[D:$i]:
% 0.42/0.62           ( ( r2_hidden @ D @ B ) & 
% 0.42/0.62             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.42/0.62             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.42/0.62  thf('61', plain,
% 0.42/0.62      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.42/0.62         (~ (r2_hidden @ X12 @ (k9_relat_1 @ X13 @ X11))
% 0.42/0.62          | (r2_hidden @ (k4_tarski @ (sk_D @ X13 @ X11 @ X12) @ X12) @ X13)
% 0.42/0.62          | ~ (v1_relat_1 @ X13))),
% 0.42/0.62      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.42/0.62  thf('62', plain,
% 0.42/0.62      ((~ (v1_relat_1 @ sk_C)
% 0.42/0.62        | (r2_hidden @ 
% 0.42/0.62           (k4_tarski @ (sk_D @ sk_C @ sk_A @ (sk_D_2 @ sk_C @ sk_B)) @ 
% 0.42/0.62            (sk_D_2 @ sk_C @ sk_B)) @ 
% 0.42/0.62           sk_C))),
% 0.42/0.62      inference('sup-', [status(thm)], ['60', '61'])).
% 0.42/0.62  thf('63', plain, ((v1_relat_1 @ sk_C)),
% 0.42/0.62      inference('demod', [status(thm)], ['26', '27'])).
% 0.42/0.62  thf('64', plain,
% 0.42/0.62      ((r2_hidden @ 
% 0.42/0.62        (k4_tarski @ (sk_D @ sk_C @ sk_A @ (sk_D_2 @ sk_C @ sk_B)) @ 
% 0.42/0.62         (sk_D_2 @ sk_C @ sk_B)) @ 
% 0.42/0.62        sk_C)),
% 0.42/0.62      inference('demod', [status(thm)], ['62', '63'])).
% 0.42/0.62  thf('65', plain,
% 0.42/0.62      (![X36 : $i, X37 : $i, X38 : $i, X40 : $i]:
% 0.42/0.62         (~ (r2_hidden @ (k4_tarski @ X40 @ (sk_D_2 @ X38 @ X36)) @ X38)
% 0.42/0.62          | ((k2_relset_1 @ X37 @ X36 @ X38) = (X36))
% 0.42/0.62          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 0.42/0.62      inference('cnf', [status(esa)], [t23_relset_1])).
% 0.42/0.62  thf('66', plain,
% 0.42/0.62      (![X0 : $i]:
% 0.42/0.62         (~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.42/0.62          | ((k2_relset_1 @ X0 @ sk_B @ sk_C) = (sk_B)))),
% 0.42/0.62      inference('sup-', [status(thm)], ['64', '65'])).
% 0.42/0.62  thf('67', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.42/0.62      inference('sup-', [status(thm)], ['3', '66'])).
% 0.42/0.62  thf('68', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.42/0.62      inference('sup+', [status(thm)], ['2', '67'])).
% 0.42/0.62  thf('69', plain, (((k2_relat_1 @ sk_C) != (sk_B))),
% 0.42/0.62      inference('demod', [status(thm)], ['9', '10'])).
% 0.42/0.62  thf('70', plain, ($false),
% 0.42/0.62      inference('simplify_reflect-', [status(thm)], ['68', '69'])).
% 0.42/0.62  
% 0.42/0.62  % SZS output end Refutation
% 0.42/0.62  
% 0.42/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
