%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QcA3uUDi4M

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:26 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 183 expanded)
%              Number of leaves         :   39 (  71 expanded)
%              Depth                    :   17
%              Number of atoms          :  689 (2396 expanded)
%              Number of equality atoms :   47 ( 168 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(sk_D_4_type,type,(
    sk_D_4: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X33 @ X31 )
        = ( k2_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('2',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 )
    = ( k2_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( r2_hidden @ ( sk_D_4 @ X36 @ X34 ) @ X34 )
      | ( ( k2_relset_1 @ X35 @ X34 @ X36 )
        = X34 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_relset_1])).

thf('6',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 )
      = sk_B )
    | ( r2_hidden @ ( sk_D_4 @ sk_C_3 @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 )
    = ( k2_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('8',plain,
    ( ( ( k2_relat_1 @ sk_C_3 )
      = sk_B )
    | ( r2_hidden @ ( sk_D_4 @ sk_C_3 @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 )
    = ( k2_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('11',plain,(
    ( k2_relat_1 @ sk_C_3 )
 != sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ ( sk_D_4 @ sk_C_3 @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X47: $i] :
      ( ~ ( r2_hidden @ X47 @ sk_B )
      | ( r2_hidden @ ( sk_E_1 @ X47 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r2_hidden @ ( sk_E_1 @ ( sk_D_4 @ sk_C_3 @ sk_B ) ) @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    v1_funct_2 @ sk_C_3 @ sk_A @ sk_B ),
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

thf('16',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ( X41
        = ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ~ ( zip_tseitin_1 @ X43 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('17',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_3 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('18',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_0 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('19',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('22',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( zip_tseitin_0 @ X44 @ X45 )
      | ( zip_tseitin_1 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('23',plain,
    ( ( zip_tseitin_1 @ sk_C_3 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_1 @ sk_C_3 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    r2_hidden @ ( sk_D_4 @ sk_C_3 @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['8','11'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('26',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ~ ( r1_tarski @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('27',plain,(
    ~ ( r1_tarski @ sk_B @ ( sk_D_4 @ sk_C_3 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    zip_tseitin_1 @ sk_C_3 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['24','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('30',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('31',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C_3 )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['17','28','31'])).

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

thf('33',plain,(
    ! [X20: $i,X22: $i,X24: $i,X25: $i] :
      ( ( X22
       != ( k2_relat_1 @ X20 ) )
      | ( r2_hidden @ X24 @ X22 )
      | ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X20 ) )
      | ( X24
       != ( k1_funct_1 @ X20 @ X25 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('34',plain,(
    ! [X20: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( r2_hidden @ X25 @ ( k1_relat_1 @ X20 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X20 @ X25 ) @ ( k2_relat_1 @ X20 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_3 @ X0 ) @ ( k2_relat_1 @ sk_C_3 ) )
      | ~ ( v1_funct_1 @ sk_C_3 )
      | ~ ( v1_relat_1 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_C_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('38',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('40',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('41',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( r2_hidden @ ( k1_funct_1 @ sk_C_3 @ X0 ) @ ( k2_relat_1 @ sk_C_3 ) ) ) ),
    inference(demod,[status(thm)],['35','36','41'])).

thf('43',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_C_3 @ ( sk_E_1 @ ( sk_D_4 @ sk_C_3 @ sk_B ) ) ) @ ( k2_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['14','42'])).

thf('44',plain,(
    r2_hidden @ ( sk_D_4 @ sk_C_3 @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['8','11'])).

thf('45',plain,(
    ! [X47: $i] :
      ( ~ ( r2_hidden @ X47 @ sk_B )
      | ( X47
        = ( k1_funct_1 @ sk_C_3 @ ( sk_E_1 @ X47 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,
    ( ( sk_D_4 @ sk_C_3 @ sk_B )
    = ( k1_funct_1 @ sk_C_3 @ ( sk_E_1 @ ( sk_D_4 @ sk_C_3 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    r2_hidden @ ( sk_D_4 @ sk_C_3 @ sk_B ) @ ( k2_relat_1 @ sk_C_3 ) ),
    inference(demod,[status(thm)],['43','46'])).

thf(d5_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k2_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) )).

thf('48',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X14 @ X13 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X14 @ X12 ) @ X14 ) @ X12 )
      | ( X13
       != ( k2_relat_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[d5_relat_1])).

thf('49',plain,(
    ! [X12: $i,X14: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D_1 @ X14 @ X12 ) @ X14 ) @ X12 )
      | ~ ( r2_hidden @ X14 @ ( k2_relat_1 @ X12 ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_1 @ ( sk_D_4 @ sk_C_3 @ sk_B ) @ sk_C_3 ) @ ( sk_D_4 @ sk_C_3 @ sk_B ) ) @ sk_C_3 ),
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    ! [X34: $i,X35: $i,X36: $i,X38: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X38 @ ( sk_D_4 @ X36 @ X34 ) ) @ X36 )
      | ( ( k2_relset_1 @ X35 @ X34 @ X36 )
        = X34 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_relset_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X0 @ sk_B @ sk_C_3 )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C_3 )
    = sk_B ),
    inference('sup-',[status(thm)],['3','52'])).

thf('54',plain,
    ( ( k2_relat_1 @ sk_C_3 )
    = sk_B ),
    inference('sup+',[status(thm)],['2','53'])).

thf('55',plain,(
    ( k2_relat_1 @ sk_C_3 )
 != sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('56',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['54','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.QcA3uUDi4M
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:26:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.75/1.00  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.75/1.00  % Solved by: fo/fo7.sh
% 0.75/1.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/1.00  % done 498 iterations in 0.509s
% 0.75/1.00  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.75/1.00  % SZS output start Refutation
% 0.75/1.00  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.75/1.00  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.75/1.00  thf(sk_B_type, type, sk_B: $i).
% 0.75/1.00  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.75/1.00  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/1.00  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.75/1.00  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/1.00  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.75/1.00  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.75/1.00  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.75/1.00  thf(sk_D_4_type, type, sk_D_4: $i > $i > $i).
% 0.75/1.00  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.75/1.00  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.75/1.00  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.75/1.00  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/1.00  thf(sk_E_1_type, type, sk_E_1: $i > $i).
% 0.75/1.00  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.75/1.00  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.75/1.00  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.75/1.00  thf(sk_A_type, type, sk_A: $i).
% 0.75/1.00  thf(sk_D_1_type, type, sk_D_1: $i > $i > $i).
% 0.75/1.00  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.75/1.00  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.75/1.00  thf(t16_funct_2, conjecture,
% 0.75/1.00    (![A:$i,B:$i,C:$i]:
% 0.75/1.00     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.75/1.00         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/1.00       ( ( ![D:$i]:
% 0.75/1.00           ( ~( ( r2_hidden @ D @ B ) & 
% 0.75/1.00                ( ![E:$i]:
% 0.75/1.00                  ( ~( ( r2_hidden @ E @ A ) & 
% 0.75/1.00                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.75/1.00         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.75/1.00  thf(zf_stmt_0, negated_conjecture,
% 0.75/1.00    (~( ![A:$i,B:$i,C:$i]:
% 0.75/1.00        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.75/1.00            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/1.00          ( ( ![D:$i]:
% 0.75/1.00              ( ~( ( r2_hidden @ D @ B ) & 
% 0.75/1.00                   ( ![E:$i]:
% 0.75/1.00                     ( ~( ( r2_hidden @ E @ A ) & 
% 0.75/1.00                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.75/1.00            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.75/1.00    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 0.75/1.00  thf('0', plain,
% 0.75/1.00      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.00  thf(redefinition_k2_relset_1, axiom,
% 0.75/1.00    (![A:$i,B:$i,C:$i]:
% 0.75/1.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/1.00       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.75/1.00  thf('1', plain,
% 0.75/1.00      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.75/1.00         (((k2_relset_1 @ X32 @ X33 @ X31) = (k2_relat_1 @ X31))
% 0.75/1.00          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.75/1.00      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.75/1.00  thf('2', plain,
% 0.75/1.00      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_3) = (k2_relat_1 @ sk_C_3))),
% 0.75/1.00      inference('sup-', [status(thm)], ['0', '1'])).
% 0.75/1.00  thf('3', plain,
% 0.75/1.00      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.00  thf('4', plain,
% 0.75/1.00      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.00  thf(t23_relset_1, axiom,
% 0.75/1.00    (![A:$i,B:$i,C:$i]:
% 0.75/1.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/1.00       ( ( ![D:$i]:
% 0.75/1.00           ( ~( ( r2_hidden @ D @ B ) & 
% 0.75/1.00                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) ) ) ) ) ) <=>
% 0.75/1.00         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.75/1.00  thf('5', plain,
% 0.75/1.00      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.75/1.00         ((r2_hidden @ (sk_D_4 @ X36 @ X34) @ X34)
% 0.75/1.00          | ((k2_relset_1 @ X35 @ X34 @ X36) = (X34))
% 0.75/1.00          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 0.75/1.00      inference('cnf', [status(esa)], [t23_relset_1])).
% 0.75/1.00  thf('6', plain,
% 0.75/1.00      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C_3) = (sk_B))
% 0.75/1.00        | (r2_hidden @ (sk_D_4 @ sk_C_3 @ sk_B) @ sk_B))),
% 0.75/1.00      inference('sup-', [status(thm)], ['4', '5'])).
% 0.75/1.00  thf('7', plain,
% 0.75/1.00      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_3) = (k2_relat_1 @ sk_C_3))),
% 0.75/1.00      inference('sup-', [status(thm)], ['0', '1'])).
% 0.75/1.00  thf('8', plain,
% 0.75/1.00      ((((k2_relat_1 @ sk_C_3) = (sk_B))
% 0.75/1.00        | (r2_hidden @ (sk_D_4 @ sk_C_3 @ sk_B) @ sk_B))),
% 0.75/1.00      inference('demod', [status(thm)], ['6', '7'])).
% 0.75/1.00  thf('9', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_3) != (sk_B))),
% 0.75/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.00  thf('10', plain,
% 0.75/1.00      (((k2_relset_1 @ sk_A @ sk_B @ sk_C_3) = (k2_relat_1 @ sk_C_3))),
% 0.75/1.00      inference('sup-', [status(thm)], ['0', '1'])).
% 0.75/1.00  thf('11', plain, (((k2_relat_1 @ sk_C_3) != (sk_B))),
% 0.75/1.00      inference('demod', [status(thm)], ['9', '10'])).
% 0.75/1.00  thf('12', plain, ((r2_hidden @ (sk_D_4 @ sk_C_3 @ sk_B) @ sk_B)),
% 0.75/1.00      inference('simplify_reflect-', [status(thm)], ['8', '11'])).
% 0.75/1.00  thf('13', plain,
% 0.75/1.00      (![X47 : $i]:
% 0.75/1.00         (~ (r2_hidden @ X47 @ sk_B) | (r2_hidden @ (sk_E_1 @ X47) @ sk_A))),
% 0.75/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.00  thf('14', plain, ((r2_hidden @ (sk_E_1 @ (sk_D_4 @ sk_C_3 @ sk_B)) @ sk_A)),
% 0.75/1.00      inference('sup-', [status(thm)], ['12', '13'])).
% 0.75/1.00  thf('15', plain, ((v1_funct_2 @ sk_C_3 @ sk_A @ sk_B)),
% 0.75/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.00  thf(d1_funct_2, axiom,
% 0.75/1.00    (![A:$i,B:$i,C:$i]:
% 0.75/1.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/1.00       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.75/1.00           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.75/1.00             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.75/1.00         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.75/1.00           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.75/1.00             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.75/1.00  thf(zf_stmt_1, axiom,
% 0.75/1.00    (![C:$i,B:$i,A:$i]:
% 0.75/1.00     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.75/1.00       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.75/1.00  thf('16', plain,
% 0.75/1.00      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.75/1.00         (~ (v1_funct_2 @ X43 @ X41 @ X42)
% 0.75/1.00          | ((X41) = (k1_relset_1 @ X41 @ X42 @ X43))
% 0.75/1.00          | ~ (zip_tseitin_1 @ X43 @ X42 @ X41))),
% 0.75/1.00      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/1.00  thf('17', plain,
% 0.75/1.00      ((~ (zip_tseitin_1 @ sk_C_3 @ sk_B @ sk_A)
% 0.75/1.00        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C_3)))),
% 0.75/1.00      inference('sup-', [status(thm)], ['15', '16'])).
% 0.75/1.00  thf(zf_stmt_2, axiom,
% 0.75/1.00    (![B:$i,A:$i]:
% 0.75/1.00     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.75/1.00       ( zip_tseitin_0 @ B @ A ) ))).
% 0.75/1.00  thf('18', plain,
% 0.75/1.00      (![X39 : $i, X40 : $i]:
% 0.75/1.00         ((zip_tseitin_0 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 0.75/1.00      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.75/1.00  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.75/1.00  thf('19', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.75/1.00      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.75/1.00  thf('20', plain,
% 0.75/1.00      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/1.00         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.75/1.00      inference('sup+', [status(thm)], ['18', '19'])).
% 0.75/1.00  thf('21', plain,
% 0.75/1.00      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.00  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.75/1.00  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.75/1.00  thf(zf_stmt_5, axiom,
% 0.75/1.00    (![A:$i,B:$i,C:$i]:
% 0.75/1.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/1.00       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.75/1.00         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.75/1.00           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.75/1.00             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.75/1.00  thf('22', plain,
% 0.75/1.00      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.75/1.00         (~ (zip_tseitin_0 @ X44 @ X45)
% 0.75/1.00          | (zip_tseitin_1 @ X46 @ X44 @ X45)
% 0.75/1.00          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 0.75/1.00      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.75/1.00  thf('23', plain,
% 0.75/1.00      (((zip_tseitin_1 @ sk_C_3 @ sk_B @ sk_A)
% 0.75/1.00        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.75/1.00      inference('sup-', [status(thm)], ['21', '22'])).
% 0.75/1.00  thf('24', plain,
% 0.75/1.00      (![X0 : $i]:
% 0.75/1.00         ((r1_tarski @ sk_B @ X0) | (zip_tseitin_1 @ sk_C_3 @ sk_B @ sk_A))),
% 0.75/1.00      inference('sup-', [status(thm)], ['20', '23'])).
% 0.75/1.00  thf('25', plain, ((r2_hidden @ (sk_D_4 @ sk_C_3 @ sk_B) @ sk_B)),
% 0.75/1.00      inference('simplify_reflect-', [status(thm)], ['8', '11'])).
% 0.75/1.00  thf(t7_ordinal1, axiom,
% 0.75/1.00    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.75/1.00  thf('26', plain,
% 0.75/1.00      (![X26 : $i, X27 : $i]:
% 0.75/1.00         (~ (r2_hidden @ X26 @ X27) | ~ (r1_tarski @ X27 @ X26))),
% 0.75/1.00      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.75/1.00  thf('27', plain, (~ (r1_tarski @ sk_B @ (sk_D_4 @ sk_C_3 @ sk_B))),
% 0.75/1.00      inference('sup-', [status(thm)], ['25', '26'])).
% 0.75/1.00  thf('28', plain, ((zip_tseitin_1 @ sk_C_3 @ sk_B @ sk_A)),
% 0.75/1.00      inference('sup-', [status(thm)], ['24', '27'])).
% 0.75/1.00  thf('29', plain,
% 0.75/1.00      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.00  thf(redefinition_k1_relset_1, axiom,
% 0.75/1.00    (![A:$i,B:$i,C:$i]:
% 0.75/1.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/1.00       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.75/1.00  thf('30', plain,
% 0.75/1.00      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.75/1.00         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 0.75/1.00          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.75/1.00      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.75/1.00  thf('31', plain,
% 0.75/1.00      (((k1_relset_1 @ sk_A @ sk_B @ sk_C_3) = (k1_relat_1 @ sk_C_3))),
% 0.75/1.00      inference('sup-', [status(thm)], ['29', '30'])).
% 0.75/1.00  thf('32', plain, (((sk_A) = (k1_relat_1 @ sk_C_3))),
% 0.75/1.00      inference('demod', [status(thm)], ['17', '28', '31'])).
% 0.75/1.00  thf(d5_funct_1, axiom,
% 0.75/1.00    (![A:$i]:
% 0.75/1.00     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.75/1.00       ( ![B:$i]:
% 0.75/1.00         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.75/1.00           ( ![C:$i]:
% 0.75/1.00             ( ( r2_hidden @ C @ B ) <=>
% 0.75/1.00               ( ?[D:$i]:
% 0.75/1.00                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.75/1.00                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.75/1.00  thf('33', plain,
% 0.75/1.00      (![X20 : $i, X22 : $i, X24 : $i, X25 : $i]:
% 0.75/1.00         (((X22) != (k2_relat_1 @ X20))
% 0.75/1.00          | (r2_hidden @ X24 @ X22)
% 0.75/1.00          | ~ (r2_hidden @ X25 @ (k1_relat_1 @ X20))
% 0.75/1.00          | ((X24) != (k1_funct_1 @ X20 @ X25))
% 0.75/1.00          | ~ (v1_funct_1 @ X20)
% 0.75/1.00          | ~ (v1_relat_1 @ X20))),
% 0.75/1.00      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.75/1.00  thf('34', plain,
% 0.75/1.00      (![X20 : $i, X25 : $i]:
% 0.75/1.00         (~ (v1_relat_1 @ X20)
% 0.75/1.00          | ~ (v1_funct_1 @ X20)
% 0.75/1.00          | ~ (r2_hidden @ X25 @ (k1_relat_1 @ X20))
% 0.75/1.00          | (r2_hidden @ (k1_funct_1 @ X20 @ X25) @ (k2_relat_1 @ X20)))),
% 0.75/1.00      inference('simplify', [status(thm)], ['33'])).
% 0.75/1.00  thf('35', plain,
% 0.75/1.00      (![X0 : $i]:
% 0.75/1.00         (~ (r2_hidden @ X0 @ sk_A)
% 0.75/1.00          | (r2_hidden @ (k1_funct_1 @ sk_C_3 @ X0) @ (k2_relat_1 @ sk_C_3))
% 0.75/1.00          | ~ (v1_funct_1 @ sk_C_3)
% 0.75/1.00          | ~ (v1_relat_1 @ sk_C_3))),
% 0.75/1.00      inference('sup-', [status(thm)], ['32', '34'])).
% 0.75/1.00  thf('36', plain, ((v1_funct_1 @ sk_C_3)),
% 0.75/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.00  thf('37', plain,
% 0.75/1.00      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.00  thf(cc2_relat_1, axiom,
% 0.75/1.00    (![A:$i]:
% 0.75/1.00     ( ( v1_relat_1 @ A ) =>
% 0.75/1.00       ( ![B:$i]:
% 0.75/1.00         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.75/1.00  thf('38', plain,
% 0.75/1.00      (![X8 : $i, X9 : $i]:
% 0.75/1.00         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 0.75/1.00          | (v1_relat_1 @ X8)
% 0.75/1.00          | ~ (v1_relat_1 @ X9))),
% 0.75/1.00      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.75/1.00  thf('39', plain,
% 0.75/1.00      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C_3))),
% 0.75/1.00      inference('sup-', [status(thm)], ['37', '38'])).
% 0.75/1.00  thf(fc6_relat_1, axiom,
% 0.75/1.00    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.75/1.00  thf('40', plain,
% 0.75/1.00      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 0.75/1.00      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.75/1.00  thf('41', plain, ((v1_relat_1 @ sk_C_3)),
% 0.75/1.00      inference('demod', [status(thm)], ['39', '40'])).
% 0.75/1.00  thf('42', plain,
% 0.75/1.00      (![X0 : $i]:
% 0.75/1.00         (~ (r2_hidden @ X0 @ sk_A)
% 0.75/1.00          | (r2_hidden @ (k1_funct_1 @ sk_C_3 @ X0) @ (k2_relat_1 @ sk_C_3)))),
% 0.75/1.00      inference('demod', [status(thm)], ['35', '36', '41'])).
% 0.75/1.00  thf('43', plain,
% 0.75/1.00      ((r2_hidden @ 
% 0.75/1.00        (k1_funct_1 @ sk_C_3 @ (sk_E_1 @ (sk_D_4 @ sk_C_3 @ sk_B))) @ 
% 0.75/1.00        (k2_relat_1 @ sk_C_3))),
% 0.75/1.00      inference('sup-', [status(thm)], ['14', '42'])).
% 0.75/1.00  thf('44', plain, ((r2_hidden @ (sk_D_4 @ sk_C_3 @ sk_B) @ sk_B)),
% 0.75/1.00      inference('simplify_reflect-', [status(thm)], ['8', '11'])).
% 0.75/1.00  thf('45', plain,
% 0.75/1.00      (![X47 : $i]:
% 0.75/1.00         (~ (r2_hidden @ X47 @ sk_B)
% 0.75/1.00          | ((X47) = (k1_funct_1 @ sk_C_3 @ (sk_E_1 @ X47))))),
% 0.75/1.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/1.00  thf('46', plain,
% 0.75/1.00      (((sk_D_4 @ sk_C_3 @ sk_B)
% 0.75/1.00         = (k1_funct_1 @ sk_C_3 @ (sk_E_1 @ (sk_D_4 @ sk_C_3 @ sk_B))))),
% 0.75/1.00      inference('sup-', [status(thm)], ['44', '45'])).
% 0.75/1.00  thf('47', plain,
% 0.75/1.00      ((r2_hidden @ (sk_D_4 @ sk_C_3 @ sk_B) @ (k2_relat_1 @ sk_C_3))),
% 0.75/1.00      inference('demod', [status(thm)], ['43', '46'])).
% 0.75/1.00  thf(d5_relat_1, axiom,
% 0.75/1.00    (![A:$i,B:$i]:
% 0.75/1.00     ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.75/1.00       ( ![C:$i]:
% 0.75/1.00         ( ( r2_hidden @ C @ B ) <=>
% 0.75/1.00           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ D @ C ) @ A ) ) ) ) ))).
% 0.75/1.00  thf('48', plain,
% 0.75/1.00      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.75/1.00         (~ (r2_hidden @ X14 @ X13)
% 0.75/1.00          | (r2_hidden @ (k4_tarski @ (sk_D_1 @ X14 @ X12) @ X14) @ X12)
% 0.75/1.00          | ((X13) != (k2_relat_1 @ X12)))),
% 0.75/1.00      inference('cnf', [status(esa)], [d5_relat_1])).
% 0.75/1.00  thf('49', plain,
% 0.75/1.00      (![X12 : $i, X14 : $i]:
% 0.75/1.00         ((r2_hidden @ (k4_tarski @ (sk_D_1 @ X14 @ X12) @ X14) @ X12)
% 0.75/1.00          | ~ (r2_hidden @ X14 @ (k2_relat_1 @ X12)))),
% 0.75/1.00      inference('simplify', [status(thm)], ['48'])).
% 0.75/1.00  thf('50', plain,
% 0.75/1.00      ((r2_hidden @ 
% 0.75/1.00        (k4_tarski @ (sk_D_1 @ (sk_D_4 @ sk_C_3 @ sk_B) @ sk_C_3) @ 
% 0.75/1.00         (sk_D_4 @ sk_C_3 @ sk_B)) @ 
% 0.75/1.00        sk_C_3)),
% 0.75/1.00      inference('sup-', [status(thm)], ['47', '49'])).
% 0.75/1.00  thf('51', plain,
% 0.75/1.00      (![X34 : $i, X35 : $i, X36 : $i, X38 : $i]:
% 0.75/1.00         (~ (r2_hidden @ (k4_tarski @ X38 @ (sk_D_4 @ X36 @ X34)) @ X36)
% 0.75/1.00          | ((k2_relset_1 @ X35 @ X34 @ X36) = (X34))
% 0.75/1.00          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34))))),
% 0.75/1.00      inference('cnf', [status(esa)], [t23_relset_1])).
% 0.75/1.00  thf('52', plain,
% 0.75/1.00      (![X0 : $i]:
% 0.75/1.00         (~ (m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.75/1.00          | ((k2_relset_1 @ X0 @ sk_B @ sk_C_3) = (sk_B)))),
% 0.75/1.00      inference('sup-', [status(thm)], ['50', '51'])).
% 0.75/1.00  thf('53', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C_3) = (sk_B))),
% 0.75/1.00      inference('sup-', [status(thm)], ['3', '52'])).
% 0.75/1.00  thf('54', plain, (((k2_relat_1 @ sk_C_3) = (sk_B))),
% 0.75/1.00      inference('sup+', [status(thm)], ['2', '53'])).
% 0.75/1.00  thf('55', plain, (((k2_relat_1 @ sk_C_3) != (sk_B))),
% 0.75/1.00      inference('demod', [status(thm)], ['9', '10'])).
% 0.75/1.00  thf('56', plain, ($false),
% 0.75/1.00      inference('simplify_reflect-', [status(thm)], ['54', '55'])).
% 0.75/1.00  
% 0.75/1.00  % SZS output end Refutation
% 0.75/1.00  
% 0.75/1.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
