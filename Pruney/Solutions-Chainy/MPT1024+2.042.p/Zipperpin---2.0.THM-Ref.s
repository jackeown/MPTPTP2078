%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3X4VYVNUht

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:39 EST 2020

% Result     : Theorem 0.61s
% Output     : Refutation 0.61s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 170 expanded)
%              Number of leaves         :   43 (  70 expanded)
%              Depth                    :   14
%              Number of atoms          :  693 (2073 expanded)
%              Number of equality atoms :   34 (  80 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

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
    r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1 ) ),
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
    ! [X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X47 ) ) )
      | ( ( k7_relset_1 @ X46 @ X47 @ X45 @ X48 )
        = ( k9_relat_1 @ X45 @ X48 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ sk_C_1 ) ),
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
    ! [X29: $i,X30: $i,X32: $i,X33: $i] :
      ( ( X32
       != ( k9_relat_1 @ X30 @ X29 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X33 @ X29 @ X30 ) @ X33 @ X29 @ X30 )
      | ~ ( r2_hidden @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X29: $i,X30: $i,X33: $i] :
      ( ~ ( v1_relat_1 @ X30 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( r2_hidden @ X33 @ ( k9_relat_1 @ X30 @ X29 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X33 @ X29 @ X30 ) @ X33 @ X29 @ X30 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1 ) @ sk_E_2 @ sk_C_1 @ sk_D_1 )
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
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('12',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1 ) @ sk_E_2 @ sk_C_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8','13'])).

thf('15',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ X24 @ ( k1_relat_1 @ X23 ) )
      | ~ ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('16',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1 ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B_1 ),
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
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('18',plain,(
    ! [X51: $i,X52: $i,X53: $i] :
      ( ~ ( v1_funct_2 @ X53 @ X51 @ X52 )
      | ( X51
        = ( k1_relset_1 @ X51 @ X52 @ X53 ) )
      | ~ ( zip_tseitin_2 @ X53 @ X52 @ X51 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('19',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_5,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_6,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_7,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_1 @ B @ A )
         => ( zip_tseitin_2 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('21',plain,(
    ! [X54: $i,X55: $i,X56: $i] :
      ( ~ ( zip_tseitin_1 @ X54 @ X55 )
      | ( zip_tseitin_2 @ X56 @ X54 @ X55 )
      | ~ ( m1_subset_1 @ X56 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X54 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('22',plain,
    ( ( zip_tseitin_2 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X49: $i,X50: $i] :
      ( ( zip_tseitin_1 @ X49 @ X50 )
      | ( X49 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('24',plain,(
    ! [X10: $i] :
      ( r1_tarski @ k1_xboole_0 @ X10 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['23','24'])).

thf('26',plain,(
    r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('28',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X39 @ X40 @ X38 @ X41 ) @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('30',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('32',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( r2_hidden @ X3 @ X5 )
      | ~ ( r1_tarski @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ sk_B_1 )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ sk_E_2 @ sk_B_1 ),
    inference('sup-',[status(thm)],['26','33'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('35',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( r2_hidden @ X36 @ X37 )
      | ~ ( r1_tarski @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('36',plain,(
    ~ ( r1_tarski @ sk_B_1 @ sk_E_2 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ sk_B_1 @ X0 ) ),
    inference('sup-',[status(thm)],['25','36'])).

thf('38',plain,(
    zip_tseitin_2 @ sk_D_1 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['22','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('40',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( ( k1_relset_1 @ X43 @ X44 @ X42 )
        = ( k1_relat_1 @ X42 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('41',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['19','38','41'])).

thf('43',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1 ) @ sk_A ),
    inference(demod,[status(thm)],['16','42'])).

thf('44',plain,(
    ! [X57: $i] :
      ( ~ ( r2_hidden @ X57 @ sk_A )
      | ~ ( r2_hidden @ X57 @ sk_C_1 )
      | ( sk_E_2
       != ( k1_funct_1 @ sk_D_1 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( sk_E_2
     != ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1 ) ) )
    | ~ ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1 ) @ sk_E_2 @ sk_C_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8','13'])).

thf('47',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X25
        = ( k1_funct_1 @ X23 @ X24 ) )
      | ~ ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('48',plain,
    ( sk_E_2
    = ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1 ) @ sk_E_2 @ sk_C_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8','13'])).

thf('50',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( r2_hidden @ X24 @ X26 )
      | ~ ( zip_tseitin_0 @ X24 @ X25 @ X26 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('51',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1 ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    sk_E_2 != sk_E_2 ),
    inference(demod,[status(thm)],['45','48','51'])).

thf('53',plain,(
    $false ),
    inference(simplify,[status(thm)],['52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3X4VYVNUht
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:05:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.61/0.79  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.61/0.79  % Solved by: fo/fo7.sh
% 0.61/0.79  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.61/0.79  % done 350 iterations in 0.339s
% 0.61/0.79  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.61/0.79  % SZS output start Refutation
% 0.61/0.79  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.61/0.79  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.61/0.79  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.61/0.79  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.61/0.79  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.61/0.79  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.61/0.79  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.61/0.79  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.61/0.79  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.61/0.79  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.61/0.79  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.61/0.79  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.61/0.79  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.61/0.79  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.61/0.79  thf(sk_A_type, type, sk_A: $i).
% 0.61/0.79  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.61/0.79  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.61/0.79  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.61/0.79  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.61/0.79  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.61/0.79  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.61/0.79  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.61/0.79  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.61/0.79  thf(t115_funct_2, conjecture,
% 0.61/0.79    (![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.79     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.61/0.79         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.61/0.79       ( ![E:$i]:
% 0.61/0.79         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.61/0.79              ( ![F:$i]:
% 0.61/0.79                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.61/0.79                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.61/0.79  thf(zf_stmt_0, negated_conjecture,
% 0.61/0.79    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.79        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.61/0.79            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.61/0.79          ( ![E:$i]:
% 0.61/0.79            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.61/0.79                 ( ![F:$i]:
% 0.61/0.79                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.61/0.79                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 0.61/0.79    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 0.61/0.79  thf('0', plain,
% 0.61/0.79      ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1))),
% 0.61/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.79  thf('1', plain,
% 0.61/0.79      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.61/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.79  thf(redefinition_k7_relset_1, axiom,
% 0.61/0.79    (![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.79       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.61/0.79  thf('2', plain,
% 0.61/0.79      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.61/0.79         (~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X47)))
% 0.61/0.79          | ((k7_relset_1 @ X46 @ X47 @ X45 @ X48) = (k9_relat_1 @ X45 @ X48)))),
% 0.61/0.79      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.61/0.79  thf('3', plain,
% 0.61/0.79      (![X0 : $i]:
% 0.61/0.79         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 0.61/0.79           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.61/0.79      inference('sup-', [status(thm)], ['1', '2'])).
% 0.61/0.79  thf('4', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_1 @ sk_C_1))),
% 0.61/0.79      inference('demod', [status(thm)], ['0', '3'])).
% 0.61/0.79  thf(d12_funct_1, axiom,
% 0.61/0.79    (![A:$i]:
% 0.61/0.79     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.61/0.79       ( ![B:$i,C:$i]:
% 0.61/0.79         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.61/0.79           ( ![D:$i]:
% 0.61/0.79             ( ( r2_hidden @ D @ C ) <=>
% 0.61/0.79               ( ?[E:$i]:
% 0.61/0.79                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 0.61/0.79                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 0.61/0.79  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.61/0.79  thf(zf_stmt_2, axiom,
% 0.61/0.79    (![E:$i,D:$i,B:$i,A:$i]:
% 0.61/0.79     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.61/0.79       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 0.61/0.79         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 0.61/0.79  thf(zf_stmt_3, axiom,
% 0.61/0.79    (![A:$i]:
% 0.61/0.79     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.61/0.79       ( ![B:$i,C:$i]:
% 0.61/0.79         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.61/0.79           ( ![D:$i]:
% 0.61/0.79             ( ( r2_hidden @ D @ C ) <=>
% 0.61/0.79               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 0.61/0.79  thf('5', plain,
% 0.61/0.79      (![X29 : $i, X30 : $i, X32 : $i, X33 : $i]:
% 0.61/0.79         (((X32) != (k9_relat_1 @ X30 @ X29))
% 0.61/0.79          | (zip_tseitin_0 @ (sk_E_1 @ X33 @ X29 @ X30) @ X33 @ X29 @ X30)
% 0.61/0.79          | ~ (r2_hidden @ X33 @ X32)
% 0.61/0.79          | ~ (v1_funct_1 @ X30)
% 0.61/0.79          | ~ (v1_relat_1 @ X30))),
% 0.61/0.79      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.61/0.79  thf('6', plain,
% 0.61/0.79      (![X29 : $i, X30 : $i, X33 : $i]:
% 0.61/0.79         (~ (v1_relat_1 @ X30)
% 0.61/0.79          | ~ (v1_funct_1 @ X30)
% 0.61/0.79          | ~ (r2_hidden @ X33 @ (k9_relat_1 @ X30 @ X29))
% 0.61/0.79          | (zip_tseitin_0 @ (sk_E_1 @ X33 @ X29 @ X30) @ X33 @ X29 @ X30))),
% 0.61/0.79      inference('simplify', [status(thm)], ['5'])).
% 0.61/0.79  thf('7', plain,
% 0.61/0.79      (((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1) @ sk_E_2 @ 
% 0.61/0.79         sk_C_1 @ sk_D_1)
% 0.61/0.79        | ~ (v1_funct_1 @ sk_D_1)
% 0.61/0.79        | ~ (v1_relat_1 @ sk_D_1))),
% 0.61/0.79      inference('sup-', [status(thm)], ['4', '6'])).
% 0.61/0.79  thf('8', plain, ((v1_funct_1 @ sk_D_1)),
% 0.61/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.79  thf('9', plain,
% 0.61/0.79      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.61/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.79  thf(cc2_relat_1, axiom,
% 0.61/0.79    (![A:$i]:
% 0.61/0.79     ( ( v1_relat_1 @ A ) =>
% 0.61/0.79       ( ![B:$i]:
% 0.61/0.79         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.61/0.79  thf('10', plain,
% 0.61/0.79      (![X19 : $i, X20 : $i]:
% 0.61/0.79         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.61/0.79          | (v1_relat_1 @ X19)
% 0.61/0.79          | ~ (v1_relat_1 @ X20))),
% 0.61/0.79      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.61/0.79  thf('11', plain,
% 0.61/0.79      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_D_1))),
% 0.61/0.79      inference('sup-', [status(thm)], ['9', '10'])).
% 0.61/0.79  thf(fc6_relat_1, axiom,
% 0.61/0.79    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.61/0.79  thf('12', plain,
% 0.61/0.79      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 0.61/0.79      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.61/0.79  thf('13', plain, ((v1_relat_1 @ sk_D_1)),
% 0.61/0.79      inference('demod', [status(thm)], ['11', '12'])).
% 0.61/0.79  thf('14', plain,
% 0.61/0.79      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1) @ sk_E_2 @ 
% 0.61/0.79        sk_C_1 @ sk_D_1)),
% 0.61/0.79      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.61/0.79  thf('15', plain,
% 0.61/0.79      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.61/0.79         ((r2_hidden @ X24 @ (k1_relat_1 @ X23))
% 0.61/0.79          | ~ (zip_tseitin_0 @ X24 @ X25 @ X26 @ X23))),
% 0.61/0.79      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.61/0.79  thf('16', plain,
% 0.61/0.79      ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1) @ (k1_relat_1 @ sk_D_1))),
% 0.61/0.79      inference('sup-', [status(thm)], ['14', '15'])).
% 0.61/0.79  thf('17', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B_1)),
% 0.61/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.79  thf(d1_funct_2, axiom,
% 0.61/0.79    (![A:$i,B:$i,C:$i]:
% 0.61/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.79       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.61/0.79           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.61/0.79             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.61/0.79         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.61/0.79           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.61/0.79             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.61/0.79  thf(zf_stmt_4, axiom,
% 0.61/0.79    (![C:$i,B:$i,A:$i]:
% 0.61/0.79     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.61/0.79       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.61/0.79  thf('18', plain,
% 0.61/0.79      (![X51 : $i, X52 : $i, X53 : $i]:
% 0.61/0.79         (~ (v1_funct_2 @ X53 @ X51 @ X52)
% 0.61/0.79          | ((X51) = (k1_relset_1 @ X51 @ X52 @ X53))
% 0.61/0.79          | ~ (zip_tseitin_2 @ X53 @ X52 @ X51))),
% 0.61/0.79      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.61/0.79  thf('19', plain,
% 0.61/0.79      ((~ (zip_tseitin_2 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.61/0.79        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1)))),
% 0.61/0.79      inference('sup-', [status(thm)], ['17', '18'])).
% 0.61/0.79  thf('20', plain,
% 0.61/0.79      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.61/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.79  thf(zf_stmt_5, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.61/0.79  thf(zf_stmt_6, type, zip_tseitin_1 : $i > $i > $o).
% 0.61/0.79  thf(zf_stmt_7, axiom,
% 0.61/0.79    (![B:$i,A:$i]:
% 0.61/0.79     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.61/0.79       ( zip_tseitin_1 @ B @ A ) ))).
% 0.61/0.79  thf(zf_stmt_8, axiom,
% 0.61/0.79    (![A:$i,B:$i,C:$i]:
% 0.61/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.79       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.61/0.79         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.61/0.79           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.61/0.79             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.61/0.79  thf('21', plain,
% 0.61/0.79      (![X54 : $i, X55 : $i, X56 : $i]:
% 0.61/0.79         (~ (zip_tseitin_1 @ X54 @ X55)
% 0.61/0.79          | (zip_tseitin_2 @ X56 @ X54 @ X55)
% 0.61/0.79          | ~ (m1_subset_1 @ X56 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X54))))),
% 0.61/0.79      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.61/0.79  thf('22', plain,
% 0.61/0.79      (((zip_tseitin_2 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.61/0.79        | ~ (zip_tseitin_1 @ sk_B_1 @ sk_A))),
% 0.61/0.79      inference('sup-', [status(thm)], ['20', '21'])).
% 0.61/0.79  thf('23', plain,
% 0.61/0.79      (![X49 : $i, X50 : $i]:
% 0.61/0.79         ((zip_tseitin_1 @ X49 @ X50) | ((X49) = (k1_xboole_0)))),
% 0.61/0.79      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.61/0.79  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.61/0.79  thf('24', plain, (![X10 : $i]: (r1_tarski @ k1_xboole_0 @ X10)),
% 0.61/0.79      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.61/0.79  thf('25', plain,
% 0.61/0.79      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.61/0.79         ((r1_tarski @ X0 @ X1) | (zip_tseitin_1 @ X0 @ X2))),
% 0.61/0.79      inference('sup+', [status(thm)], ['23', '24'])).
% 0.61/0.79  thf('26', plain,
% 0.61/0.79      ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C_1))),
% 0.61/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.79  thf('27', plain,
% 0.61/0.79      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.61/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.79  thf(dt_k7_relset_1, axiom,
% 0.61/0.79    (![A:$i,B:$i,C:$i,D:$i]:
% 0.61/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.79       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.61/0.79  thf('28', plain,
% 0.61/0.79      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.61/0.79         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.61/0.79          | (m1_subset_1 @ (k7_relset_1 @ X39 @ X40 @ X38 @ X41) @ 
% 0.61/0.79             (k1_zfmisc_1 @ X40)))),
% 0.61/0.79      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.61/0.79  thf('29', plain,
% 0.61/0.79      (![X0 : $i]:
% 0.61/0.79         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0) @ 
% 0.61/0.79          (k1_zfmisc_1 @ sk_B_1))),
% 0.61/0.79      inference('sup-', [status(thm)], ['27', '28'])).
% 0.61/0.79  thf(t3_subset, axiom,
% 0.61/0.79    (![A:$i,B:$i]:
% 0.61/0.79     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.61/0.79  thf('30', plain,
% 0.61/0.79      (![X13 : $i, X14 : $i]:
% 0.61/0.79         ((r1_tarski @ X13 @ X14) | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14)))),
% 0.61/0.79      inference('cnf', [status(esa)], [t3_subset])).
% 0.61/0.79  thf('31', plain,
% 0.61/0.79      (![X0 : $i]:
% 0.61/0.79         (r1_tarski @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0) @ sk_B_1)),
% 0.61/0.79      inference('sup-', [status(thm)], ['29', '30'])).
% 0.61/0.79  thf(d3_tarski, axiom,
% 0.61/0.79    (![A:$i,B:$i]:
% 0.61/0.79     ( ( r1_tarski @ A @ B ) <=>
% 0.61/0.79       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.61/0.79  thf('32', plain,
% 0.61/0.79      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.61/0.79         (~ (r2_hidden @ X3 @ X4)
% 0.61/0.79          | (r2_hidden @ X3 @ X5)
% 0.61/0.79          | ~ (r1_tarski @ X4 @ X5))),
% 0.61/0.79      inference('cnf', [status(esa)], [d3_tarski])).
% 0.61/0.79  thf('33', plain,
% 0.61/0.79      (![X0 : $i, X1 : $i]:
% 0.61/0.79         ((r2_hidden @ X1 @ sk_B_1)
% 0.61/0.79          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)))),
% 0.61/0.79      inference('sup-', [status(thm)], ['31', '32'])).
% 0.61/0.79  thf('34', plain, ((r2_hidden @ sk_E_2 @ sk_B_1)),
% 0.61/0.79      inference('sup-', [status(thm)], ['26', '33'])).
% 0.61/0.79  thf(t7_ordinal1, axiom,
% 0.61/0.79    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.61/0.79  thf('35', plain,
% 0.61/0.79      (![X36 : $i, X37 : $i]:
% 0.61/0.79         (~ (r2_hidden @ X36 @ X37) | ~ (r1_tarski @ X37 @ X36))),
% 0.61/0.79      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.61/0.79  thf('36', plain, (~ (r1_tarski @ sk_B_1 @ sk_E_2)),
% 0.61/0.79      inference('sup-', [status(thm)], ['34', '35'])).
% 0.61/0.79  thf('37', plain, (![X0 : $i]: (zip_tseitin_1 @ sk_B_1 @ X0)),
% 0.61/0.79      inference('sup-', [status(thm)], ['25', '36'])).
% 0.61/0.79  thf('38', plain, ((zip_tseitin_2 @ sk_D_1 @ sk_B_1 @ sk_A)),
% 0.61/0.79      inference('demod', [status(thm)], ['22', '37'])).
% 0.61/0.79  thf('39', plain,
% 0.61/0.79      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.61/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.79  thf(redefinition_k1_relset_1, axiom,
% 0.61/0.79    (![A:$i,B:$i,C:$i]:
% 0.61/0.79     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.61/0.79       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.61/0.79  thf('40', plain,
% 0.61/0.79      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.61/0.79         (((k1_relset_1 @ X43 @ X44 @ X42) = (k1_relat_1 @ X42))
% 0.61/0.79          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44))))),
% 0.61/0.79      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.61/0.79  thf('41', plain,
% 0.61/0.79      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.61/0.79      inference('sup-', [status(thm)], ['39', '40'])).
% 0.61/0.79  thf('42', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.61/0.79      inference('demod', [status(thm)], ['19', '38', '41'])).
% 0.61/0.79  thf('43', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1) @ sk_A)),
% 0.61/0.79      inference('demod', [status(thm)], ['16', '42'])).
% 0.61/0.79  thf('44', plain,
% 0.61/0.79      (![X57 : $i]:
% 0.61/0.79         (~ (r2_hidden @ X57 @ sk_A)
% 0.61/0.79          | ~ (r2_hidden @ X57 @ sk_C_1)
% 0.61/0.79          | ((sk_E_2) != (k1_funct_1 @ sk_D_1 @ X57)))),
% 0.61/0.79      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.61/0.79  thf('45', plain,
% 0.61/0.79      ((((sk_E_2)
% 0.61/0.79          != (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1)))
% 0.61/0.79        | ~ (r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1) @ sk_C_1))),
% 0.61/0.79      inference('sup-', [status(thm)], ['43', '44'])).
% 0.61/0.79  thf('46', plain,
% 0.61/0.79      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1) @ sk_E_2 @ 
% 0.61/0.79        sk_C_1 @ sk_D_1)),
% 0.61/0.79      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.61/0.79  thf('47', plain,
% 0.61/0.79      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.61/0.79         (((X25) = (k1_funct_1 @ X23 @ X24))
% 0.61/0.79          | ~ (zip_tseitin_0 @ X24 @ X25 @ X26 @ X23))),
% 0.61/0.79      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.61/0.79  thf('48', plain,
% 0.61/0.79      (((sk_E_2) = (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1)))),
% 0.61/0.79      inference('sup-', [status(thm)], ['46', '47'])).
% 0.61/0.79  thf('49', plain,
% 0.61/0.79      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1) @ sk_E_2 @ 
% 0.61/0.79        sk_C_1 @ sk_D_1)),
% 0.61/0.79      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.61/0.79  thf('50', plain,
% 0.61/0.79      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.61/0.79         ((r2_hidden @ X24 @ X26) | ~ (zip_tseitin_0 @ X24 @ X25 @ X26 @ X23))),
% 0.61/0.79      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.61/0.79  thf('51', plain,
% 0.61/0.79      ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C_1 @ sk_D_1) @ sk_C_1)),
% 0.61/0.79      inference('sup-', [status(thm)], ['49', '50'])).
% 0.61/0.79  thf('52', plain, (((sk_E_2) != (sk_E_2))),
% 0.61/0.79      inference('demod', [status(thm)], ['45', '48', '51'])).
% 0.61/0.79  thf('53', plain, ($false), inference('simplify', [status(thm)], ['52'])).
% 0.61/0.79  
% 0.61/0.79  % SZS output end Refutation
% 0.61/0.79  
% 0.61/0.80  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
