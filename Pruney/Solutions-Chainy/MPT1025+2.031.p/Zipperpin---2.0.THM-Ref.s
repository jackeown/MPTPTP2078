%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mFR3sxE2Mn

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:47 EST 2020

% Result     : Theorem 0.76s
% Output     : Refutation 0.76s
% Verified   : 
% Statistics : Number of formulae       :  162 (1753 expanded)
%              Number of leaves         :   45 ( 534 expanded)
%              Depth                    :   19
%              Number of atoms          : 1064 (22288 expanded)
%              Number of equality atoms :   77 ( 889 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t116_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
            & ! [F: $i] :
                ( ( m1_subset_1 @ F @ A )
               => ~ ( ( r2_hidden @ F @ C )
                    & ( E
                      = ( k1_funct_1 @ D @ F ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [E: $i] :
            ~ ( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) )
              & ! [F: $i] :
                  ( ( m1_subset_1 @ F @ A )
                 => ~ ( ( r2_hidden @ F @ C )
                      & ( E
                        = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t116_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_E_1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_3 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k7_relset_1 @ X33 @ X34 @ X32 @ X35 )
        = ( k9_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_3 @ X0 )
      = ( k9_relat_1 @ sk_D_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_3 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('5',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k9_relat_1 @ X22 @ X20 ) )
      | ( r2_hidden @ ( sk_D_2 @ X22 @ X20 @ X21 ) @ ( k1_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_C_2 @ sk_E_1 ) @ ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('8',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('9',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_C_2 @ sk_E_1 ) @ ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('11',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('12',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('15',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('16',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('17',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('20',plain,(
    v1_funct_2 @ sk_D_3 @ sk_A @ sk_B ),
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

thf('21',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ( X42
        = ( k1_relset_1 @ X42 @ X43 @ X44 ) )
      | ~ ( zip_tseitin_1 @ X44 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('22',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('24',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('25',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_3 )
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('27',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_0 @ X40 @ X41 )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('28',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('29',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( zip_tseitin_0 @ X45 @ X46 )
      | ( zip_tseitin_1 @ X47 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('30',plain,
    ( ( zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['27','30'])).

thf('32',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('33',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_C_2 @ sk_E_1 ) @ ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('35',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_C_2 @ sk_E_1 ) @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('36',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('37',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_D_2 @ sk_D_3 @ sk_C_2 @ sk_E_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_3 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('39',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k9_relat_1 @ X22 @ X20 ) )
      | ( r2_hidden @ ( sk_D_2 @ X22 @ X20 @ X21 ) @ X20 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ( r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_C_2 @ sk_E_1 ) @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('42',plain,(
    r2_hidden @ ( sk_D_2 @ sk_D_3 @ sk_C_2 @ sk_E_1 ) @ sk_C_2 ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X48: $i] :
      ( ( sk_E_1
       != ( k1_funct_1 @ sk_D_3 @ X48 ) )
      | ~ ( r2_hidden @ X48 @ sk_C_2 )
      | ~ ( m1_subset_1 @ X48 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ~ ( m1_subset_1 @ ( sk_D_2 @ sk_D_3 @ sk_C_2 @ sk_E_1 ) @ sk_A )
    | ( sk_E_1
     != ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ sk_C_2 @ sk_E_1 ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E_1
     != ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ sk_C_2 @ sk_E_1 ) ) ) ),
    inference('sup-',[status(thm)],['37','44'])).

thf('46',plain,(
    r2_hidden @ sk_E_1 @ ( k9_relat_1 @ sk_D_3 @ sk_C_2 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('47',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k9_relat_1 @ X22 @ X20 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ X22 @ X20 @ X21 ) @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_D_3 @ sk_C_2 @ sk_E_1 ) @ sk_E_1 ) @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('50',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D_2 @ sk_D_3 @ sk_C_2 @ sk_E_1 ) @ sk_E_1 ) @ sk_D_3 ),
    inference(demod,[status(thm)],['48','49'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('51',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X23 @ X25 ) @ X24 )
      | ( X25
        = ( k1_funct_1 @ X24 @ X23 ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('52',plain,
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ~ ( v1_funct_1 @ sk_D_3 )
    | ( sk_E_1
      = ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ sk_C_2 @ sk_E_1 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('54',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( sk_E_1
    = ( k1_funct_1 @ sk_D_3 @ ( sk_D_2 @ sk_D_3 @ sk_C_2 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E_1 != sk_E_1 ) ),
    inference(demod,[status(thm)],['45','55'])).

thf('57',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['26','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['56'])).

thf('61',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( X45 != k1_xboole_0 )
      | ( X46 = k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X47 @ X46 @ X45 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('63',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X47 @ X46 @ k1_xboole_0 )
      | ( X47 = k1_xboole_0 )
      | ( X46 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['62'])).

thf('64',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_3 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_D_3 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','63'])).

thf('65',plain,(
    v1_funct_2 @ sk_D_3 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['56'])).

thf('67',plain,(
    v1_funct_2 @ sk_D_3 @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_3 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X6: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X8 ) )
      | ~ ( r1_tarski @ X6 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('75',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( ( k1_relset_1 @ X1 @ X0 @ X2 )
        = ( k1_relat_1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( ( k1_relset_1 @ X1 @ X0 @ X2 )
        = ( k1_relat_1 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('77',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('78',plain,(
    ! [X14: $i,X17: $i] :
      ( ( X17
        = ( k1_relat_1 @ X14 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C_1 @ X17 @ X14 ) @ ( sk_D @ X17 @ X14 ) ) @ X14 )
      | ( r2_hidden @ ( sk_C_1 @ X17 @ X14 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_C_1 @ X1 @ X0 ) @ X1 )
      | ( X1
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X0
        = ( k1_relat_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k1_xboole_0
        = ( k1_relset_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['76','83'])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k1_relset_1 @ X2 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['84'])).

thf('86',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('87',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k1_relset_1 @ X2 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['75','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['10','18'])).

thf('91',plain,(
    ~ ( v1_xboole_0 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['68','91'])).

thf('93',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('94',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['92','93'])).

thf('95',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['92','93'])).

thf('96',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ k1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['58','94','95'])).

thf('97',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X0
        = ( k1_relat_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','82'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0 = X0 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['100'])).

thf('102',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_0 @ X40 @ X41 )
      | ( X41 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('103',plain,(
    ! [X40: $i] :
      ( zip_tseitin_0 @ X40 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['101','103'])).

thf('105',plain,
    ( ( zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('106',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['56'])).

thf('108',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( zip_tseitin_1 @ sk_D_3 @ k1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['92','93'])).

thf('110',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('111',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['92','93'])).

thf('112',plain,(
    zip_tseitin_1 @ sk_D_3 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['108','109','110','111'])).

thf('113',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['96','112'])).

thf('114',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('115',plain,(
    $false ),
    inference(demod,[status(thm)],['19','113','114'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mFR3sxE2Mn
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:42:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.19/0.34  % Python version: Python 3.6.8
% 0.19/0.34  % Running in FO mode
% 0.76/0.97  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.76/0.97  % Solved by: fo/fo7.sh
% 0.76/0.97  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.76/0.97  % done 362 iterations in 0.526s
% 0.76/0.97  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.76/0.97  % SZS output start Refutation
% 0.76/0.97  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.76/0.97  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.76/0.97  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.76/0.97  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.76/0.97  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.76/0.97  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.76/0.97  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.76/0.97  thf(sk_B_type, type, sk_B: $i).
% 0.76/0.97  thf(sk_D_type, type, sk_D: $i > $i > $i).
% 0.76/0.97  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i > $i).
% 0.76/0.97  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.76/0.97  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.76/0.97  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.76/0.97  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.76/0.97  thf(sk_A_type, type, sk_A: $i).
% 0.76/0.97  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.76/0.97  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.76/0.97  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.76/0.97  thf(sk_E_1_type, type, sk_E_1: $i).
% 0.76/0.97  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.76/0.97  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.76/0.97  thf(sk_C_1_type, type, sk_C_1: $i > $i > $i).
% 0.76/0.97  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.76/0.97  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.76/0.97  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.76/0.97  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.76/0.97  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.76/0.97  thf(t116_funct_2, conjecture,
% 0.76/0.97    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.97     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.76/0.97         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.97       ( ![E:$i]:
% 0.76/0.97         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.76/0.97              ( ![F:$i]:
% 0.76/0.97                ( ( m1_subset_1 @ F @ A ) =>
% 0.76/0.97                  ( ~( ( r2_hidden @ F @ C ) & 
% 0.76/0.97                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 0.76/0.97  thf(zf_stmt_0, negated_conjecture,
% 0.76/0.97    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.97        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.76/0.97            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.76/0.97          ( ![E:$i]:
% 0.76/0.97            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.76/0.97                 ( ![F:$i]:
% 0.76/0.97                   ( ( m1_subset_1 @ F @ A ) =>
% 0.76/0.97                     ( ~( ( r2_hidden @ F @ C ) & 
% 0.76/0.97                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.76/0.97    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 0.76/0.97  thf('0', plain,
% 0.76/0.97      ((r2_hidden @ sk_E_1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_3 @ sk_C_2))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('1', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(redefinition_k7_relset_1, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i,D:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.97       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.76/0.97  thf('2', plain,
% 0.76/0.97      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.76/0.97          | ((k7_relset_1 @ X33 @ X34 @ X32 @ X35) = (k9_relat_1 @ X32 @ X35)))),
% 0.76/0.97      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.76/0.97  thf('3', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_3 @ X0)
% 0.76/0.97           = (k9_relat_1 @ sk_D_3 @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['1', '2'])).
% 0.76/0.97  thf('4', plain, ((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_3 @ sk_C_2))),
% 0.76/0.97      inference('demod', [status(thm)], ['0', '3'])).
% 0.76/0.97  thf(t143_relat_1, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( v1_relat_1 @ C ) =>
% 0.76/0.97       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.76/0.97         ( ?[D:$i]:
% 0.76/0.97           ( ( r2_hidden @ D @ B ) & 
% 0.76/0.97             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.76/0.97             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.76/0.97  thf('5', plain,
% 0.76/0.97      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X21 @ (k9_relat_1 @ X22 @ X20))
% 0.76/0.97          | (r2_hidden @ (sk_D_2 @ X22 @ X20 @ X21) @ (k1_relat_1 @ X22))
% 0.76/0.97          | ~ (v1_relat_1 @ X22))),
% 0.76/0.97      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.76/0.97  thf('6', plain,
% 0.76/0.97      ((~ (v1_relat_1 @ sk_D_3)
% 0.76/0.97        | (r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_C_2 @ sk_E_1) @ 
% 0.76/0.97           (k1_relat_1 @ sk_D_3)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['4', '5'])).
% 0.76/0.97  thf('7', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(cc1_relset_1, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.97       ( v1_relat_1 @ C ) ))).
% 0.76/0.97  thf('8', plain,
% 0.76/0.97      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.76/0.97         ((v1_relat_1 @ X26)
% 0.76/0.97          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.76/0.97      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.76/0.97  thf('9', plain, ((v1_relat_1 @ sk_D_3)),
% 0.76/0.97      inference('sup-', [status(thm)], ['7', '8'])).
% 0.76/0.97  thf('10', plain,
% 0.76/0.97      ((r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_C_2 @ sk_E_1) @ (k1_relat_1 @ sk_D_3))),
% 0.76/0.97      inference('demod', [status(thm)], ['6', '9'])).
% 0.76/0.97  thf(d3_tarski, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( r1_tarski @ A @ B ) <=>
% 0.76/0.97       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.76/0.97  thf('11', plain,
% 0.76/0.97      (![X1 : $i, X3 : $i]:
% 0.76/0.97         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.76/0.97      inference('cnf', [status(esa)], [d3_tarski])).
% 0.76/0.97  thf('12', plain,
% 0.76/0.97      (![X1 : $i, X3 : $i]:
% 0.76/0.97         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.76/0.97      inference('cnf', [status(esa)], [d3_tarski])).
% 0.76/0.97  thf('13', plain,
% 0.76/0.97      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['11', '12'])).
% 0.76/0.97  thf('14', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.76/0.97      inference('simplify', [status(thm)], ['13'])).
% 0.76/0.97  thf(t3_subset, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.76/0.97  thf('15', plain,
% 0.76/0.97      (![X6 : $i, X8 : $i]:
% 0.76/0.97         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.76/0.97      inference('cnf', [status(esa)], [t3_subset])).
% 0.76/0.97  thf('16', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['14', '15'])).
% 0.76/0.97  thf(t5_subset, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.76/0.97          ( v1_xboole_0 @ C ) ) ))).
% 0.76/0.97  thf('17', plain,
% 0.76/0.97      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X9 @ X10)
% 0.76/0.97          | ~ (v1_xboole_0 @ X11)
% 0.76/0.97          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.76/0.97      inference('cnf', [status(esa)], [t5_subset])).
% 0.76/0.97  thf('18', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['16', '17'])).
% 0.76/0.97  thf('19', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_D_3))),
% 0.76/0.97      inference('sup-', [status(thm)], ['10', '18'])).
% 0.76/0.97  thf('20', plain, ((v1_funct_2 @ sk_D_3 @ sk_A @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(d1_funct_2, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.97       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.76/0.97           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.76/0.97             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.76/0.97         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.76/0.97           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.76/0.97             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.76/0.97  thf(zf_stmt_1, axiom,
% 0.76/0.97    (![C:$i,B:$i,A:$i]:
% 0.76/0.97     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.76/0.97       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.76/0.97  thf('21', plain,
% 0.76/0.97      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.76/0.97         (~ (v1_funct_2 @ X44 @ X42 @ X43)
% 0.76/0.97          | ((X42) = (k1_relset_1 @ X42 @ X43 @ X44))
% 0.76/0.97          | ~ (zip_tseitin_1 @ X44 @ X43 @ X42))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.76/0.97  thf('22', plain,
% 0.76/0.97      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A)
% 0.76/0.97        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_3)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['20', '21'])).
% 0.76/0.97  thf('23', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(redefinition_k1_relset_1, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.97       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.76/0.97  thf('24', plain,
% 0.76/0.97      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.76/0.97         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 0.76/0.97          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.76/0.97      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.76/0.97  thf('25', plain,
% 0.76/0.97      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_3) = (k1_relat_1 @ sk_D_3))),
% 0.76/0.97      inference('sup-', [status(thm)], ['23', '24'])).
% 0.76/0.97  thf('26', plain,
% 0.76/0.97      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A)
% 0.76/0.97        | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 0.76/0.97      inference('demod', [status(thm)], ['22', '25'])).
% 0.76/0.97  thf(zf_stmt_2, axiom,
% 0.76/0.97    (![B:$i,A:$i]:
% 0.76/0.97     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.76/0.97       ( zip_tseitin_0 @ B @ A ) ))).
% 0.76/0.97  thf('27', plain,
% 0.76/0.97      (![X40 : $i, X41 : $i]:
% 0.76/0.97         ((zip_tseitin_0 @ X40 @ X41) | ((X40) = (k1_xboole_0)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.76/0.97  thf('28', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.76/0.97  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.76/0.97  thf(zf_stmt_5, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.76/0.97       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.76/0.97         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.76/0.97           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.76/0.97             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.76/0.97  thf('29', plain,
% 0.76/0.97      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.76/0.97         (~ (zip_tseitin_0 @ X45 @ X46)
% 0.76/0.97          | (zip_tseitin_1 @ X47 @ X45 @ X46)
% 0.76/0.97          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45))))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.76/0.97  thf('30', plain,
% 0.76/0.97      (((zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A)
% 0.76/0.97        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['28', '29'])).
% 0.76/0.97  thf('31', plain,
% 0.76/0.97      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['27', '30'])).
% 0.76/0.97  thf('32', plain,
% 0.76/0.97      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A)
% 0.76/0.97        | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 0.76/0.97      inference('demod', [status(thm)], ['22', '25'])).
% 0.76/0.97  thf('33', plain,
% 0.76/0.97      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['31', '32'])).
% 0.76/0.97  thf('34', plain,
% 0.76/0.97      ((r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_C_2 @ sk_E_1) @ (k1_relat_1 @ sk_D_3))),
% 0.76/0.97      inference('demod', [status(thm)], ['6', '9'])).
% 0.76/0.97  thf('35', plain,
% 0.76/0.97      (((r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_C_2 @ sk_E_1) @ sk_A)
% 0.76/0.97        | ((sk_B) = (k1_xboole_0)))),
% 0.76/0.97      inference('sup+', [status(thm)], ['33', '34'])).
% 0.76/0.97  thf(t1_subset, axiom,
% 0.76/0.97    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.76/0.97  thf('36', plain,
% 0.76/0.97      (![X4 : $i, X5 : $i]: ((m1_subset_1 @ X4 @ X5) | ~ (r2_hidden @ X4 @ X5))),
% 0.76/0.97      inference('cnf', [status(esa)], [t1_subset])).
% 0.76/0.97  thf('37', plain,
% 0.76/0.97      ((((sk_B) = (k1_xboole_0))
% 0.76/0.97        | (m1_subset_1 @ (sk_D_2 @ sk_D_3 @ sk_C_2 @ sk_E_1) @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['35', '36'])).
% 0.76/0.97  thf('38', plain, ((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_3 @ sk_C_2))),
% 0.76/0.97      inference('demod', [status(thm)], ['0', '3'])).
% 0.76/0.97  thf('39', plain,
% 0.76/0.97      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X21 @ (k9_relat_1 @ X22 @ X20))
% 0.76/0.97          | (r2_hidden @ (sk_D_2 @ X22 @ X20 @ X21) @ X20)
% 0.76/0.97          | ~ (v1_relat_1 @ X22))),
% 0.76/0.97      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.76/0.97  thf('40', plain,
% 0.76/0.97      ((~ (v1_relat_1 @ sk_D_3)
% 0.76/0.97        | (r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_C_2 @ sk_E_1) @ sk_C_2))),
% 0.76/0.97      inference('sup-', [status(thm)], ['38', '39'])).
% 0.76/0.97  thf('41', plain, ((v1_relat_1 @ sk_D_3)),
% 0.76/0.97      inference('sup-', [status(thm)], ['7', '8'])).
% 0.76/0.97  thf('42', plain,
% 0.76/0.97      ((r2_hidden @ (sk_D_2 @ sk_D_3 @ sk_C_2 @ sk_E_1) @ sk_C_2)),
% 0.76/0.97      inference('demod', [status(thm)], ['40', '41'])).
% 0.76/0.97  thf('43', plain,
% 0.76/0.97      (![X48 : $i]:
% 0.76/0.97         (((sk_E_1) != (k1_funct_1 @ sk_D_3 @ X48))
% 0.76/0.97          | ~ (r2_hidden @ X48 @ sk_C_2)
% 0.76/0.97          | ~ (m1_subset_1 @ X48 @ sk_A))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('44', plain,
% 0.76/0.97      ((~ (m1_subset_1 @ (sk_D_2 @ sk_D_3 @ sk_C_2 @ sk_E_1) @ sk_A)
% 0.76/0.97        | ((sk_E_1)
% 0.76/0.97            != (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ sk_C_2 @ sk_E_1))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['42', '43'])).
% 0.76/0.97  thf('45', plain,
% 0.76/0.97      ((((sk_B) = (k1_xboole_0))
% 0.76/0.97        | ((sk_E_1)
% 0.76/0.97            != (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ sk_C_2 @ sk_E_1))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['37', '44'])).
% 0.76/0.97  thf('46', plain, ((r2_hidden @ sk_E_1 @ (k9_relat_1 @ sk_D_3 @ sk_C_2))),
% 0.76/0.97      inference('demod', [status(thm)], ['0', '3'])).
% 0.76/0.97  thf('47', plain,
% 0.76/0.97      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.76/0.97         (~ (r2_hidden @ X21 @ (k9_relat_1 @ X22 @ X20))
% 0.76/0.97          | (r2_hidden @ (k4_tarski @ (sk_D_2 @ X22 @ X20 @ X21) @ X21) @ X22)
% 0.76/0.97          | ~ (v1_relat_1 @ X22))),
% 0.76/0.97      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.76/0.97  thf('48', plain,
% 0.76/0.97      ((~ (v1_relat_1 @ sk_D_3)
% 0.76/0.97        | (r2_hidden @ 
% 0.76/0.97           (k4_tarski @ (sk_D_2 @ sk_D_3 @ sk_C_2 @ sk_E_1) @ sk_E_1) @ sk_D_3))),
% 0.76/0.97      inference('sup-', [status(thm)], ['46', '47'])).
% 0.76/0.97  thf('49', plain, ((v1_relat_1 @ sk_D_3)),
% 0.76/0.97      inference('sup-', [status(thm)], ['7', '8'])).
% 0.76/0.97  thf('50', plain,
% 0.76/0.97      ((r2_hidden @ 
% 0.76/0.97        (k4_tarski @ (sk_D_2 @ sk_D_3 @ sk_C_2 @ sk_E_1) @ sk_E_1) @ sk_D_3)),
% 0.76/0.97      inference('demod', [status(thm)], ['48', '49'])).
% 0.76/0.97  thf(t8_funct_1, axiom,
% 0.76/0.97    (![A:$i,B:$i,C:$i]:
% 0.76/0.97     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.76/0.97       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.76/0.97         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.76/0.97           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.76/0.97  thf('51', plain,
% 0.76/0.97      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.76/0.97         (~ (r2_hidden @ (k4_tarski @ X23 @ X25) @ X24)
% 0.76/0.97          | ((X25) = (k1_funct_1 @ X24 @ X23))
% 0.76/0.97          | ~ (v1_funct_1 @ X24)
% 0.76/0.97          | ~ (v1_relat_1 @ X24))),
% 0.76/0.97      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.76/0.97  thf('52', plain,
% 0.76/0.97      ((~ (v1_relat_1 @ sk_D_3)
% 0.76/0.97        | ~ (v1_funct_1 @ sk_D_3)
% 0.76/0.97        | ((sk_E_1)
% 0.76/0.97            = (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ sk_C_2 @ sk_E_1))))),
% 0.76/0.97      inference('sup-', [status(thm)], ['50', '51'])).
% 0.76/0.97  thf('53', plain, ((v1_relat_1 @ sk_D_3)),
% 0.76/0.97      inference('sup-', [status(thm)], ['7', '8'])).
% 0.76/0.97  thf('54', plain, ((v1_funct_1 @ sk_D_3)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('55', plain,
% 0.76/0.97      (((sk_E_1) = (k1_funct_1 @ sk_D_3 @ (sk_D_2 @ sk_D_3 @ sk_C_2 @ sk_E_1)))),
% 0.76/0.97      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.76/0.97  thf('56', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_E_1) != (sk_E_1)))),
% 0.76/0.97      inference('demod', [status(thm)], ['45', '55'])).
% 0.76/0.97  thf('57', plain, (((sk_B) = (k1_xboole_0))),
% 0.76/0.97      inference('simplify', [status(thm)], ['56'])).
% 0.76/0.97  thf('58', plain,
% 0.76/0.97      ((~ (zip_tseitin_1 @ sk_D_3 @ k1_xboole_0 @ sk_A)
% 0.76/0.97        | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 0.76/0.97      inference('demod', [status(thm)], ['26', '57'])).
% 0.76/0.97  thf('59', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('60', plain, (((sk_B) = (k1_xboole_0))),
% 0.76/0.97      inference('simplify', [status(thm)], ['56'])).
% 0.76/0.97  thf('61', plain,
% 0.76/0.97      ((m1_subset_1 @ sk_D_3 @ 
% 0.76/0.97        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.76/0.97      inference('demod', [status(thm)], ['59', '60'])).
% 0.76/0.97  thf('62', plain,
% 0.76/0.97      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.76/0.97         (((X45) != (k1_xboole_0))
% 0.76/0.97          | ((X46) = (k1_xboole_0))
% 0.76/0.97          | ((X47) = (k1_xboole_0))
% 0.76/0.97          | ~ (v1_funct_2 @ X47 @ X46 @ X45)
% 0.76/0.97          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45))))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.76/0.97  thf('63', plain,
% 0.76/0.97      (![X46 : $i, X47 : $i]:
% 0.76/0.97         (~ (m1_subset_1 @ X47 @ 
% 0.76/0.97             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ k1_xboole_0)))
% 0.76/0.97          | ~ (v1_funct_2 @ X47 @ X46 @ k1_xboole_0)
% 0.76/0.97          | ((X47) = (k1_xboole_0))
% 0.76/0.97          | ((X46) = (k1_xboole_0)))),
% 0.76/0.97      inference('simplify', [status(thm)], ['62'])).
% 0.76/0.97  thf('64', plain,
% 0.76/0.97      ((((sk_A) = (k1_xboole_0))
% 0.76/0.97        | ((sk_D_3) = (k1_xboole_0))
% 0.76/0.97        | ~ (v1_funct_2 @ sk_D_3 @ sk_A @ k1_xboole_0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['61', '63'])).
% 0.76/0.97  thf('65', plain, ((v1_funct_2 @ sk_D_3 @ sk_A @ sk_B)),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.76/0.97  thf('66', plain, (((sk_B) = (k1_xboole_0))),
% 0.76/0.97      inference('simplify', [status(thm)], ['56'])).
% 0.76/0.97  thf('67', plain, ((v1_funct_2 @ sk_D_3 @ sk_A @ k1_xboole_0)),
% 0.76/0.97      inference('demod', [status(thm)], ['65', '66'])).
% 0.76/0.97  thf('68', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_D_3) = (k1_xboole_0)))),
% 0.76/0.97      inference('demod', [status(thm)], ['64', '67'])).
% 0.76/0.97  thf('69', plain,
% 0.76/0.97      (![X1 : $i, X3 : $i]:
% 0.76/0.97         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.76/0.97      inference('cnf', [status(esa)], [d3_tarski])).
% 0.76/0.97  thf('70', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['16', '17'])).
% 0.76/0.97  thf('71', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['69', '70'])).
% 0.76/0.97  thf('72', plain,
% 0.76/0.97      (![X6 : $i, X8 : $i]:
% 0.76/0.97         ((m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X8)) | ~ (r1_tarski @ X6 @ X8))),
% 0.76/0.97      inference('cnf', [status(esa)], [t3_subset])).
% 0.76/0.97  thf('73', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['71', '72'])).
% 0.76/0.97  thf('74', plain,
% 0.76/0.97      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.76/0.97         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 0.76/0.97          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.76/0.97      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.76/0.97  thf('75', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         (~ (v1_xboole_0 @ X2)
% 0.76/0.97          | ((k1_relset_1 @ X1 @ X0 @ X2) = (k1_relat_1 @ X2)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['73', '74'])).
% 0.76/0.97  thf('76', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         (~ (v1_xboole_0 @ X2)
% 0.76/0.97          | ((k1_relset_1 @ X1 @ X0 @ X2) = (k1_relat_1 @ X2)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['73', '74'])).
% 0.76/0.97  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.76/0.97  thf('77', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/0.97      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/0.97  thf(d4_relat_1, axiom,
% 0.76/0.97    (![A:$i,B:$i]:
% 0.76/0.97     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.76/0.97       ( ![C:$i]:
% 0.76/0.97         ( ( r2_hidden @ C @ B ) <=>
% 0.76/0.97           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.76/0.97  thf('78', plain,
% 0.76/0.97      (![X14 : $i, X17 : $i]:
% 0.76/0.97         (((X17) = (k1_relat_1 @ X14))
% 0.76/0.97          | (r2_hidden @ 
% 0.76/0.97             (k4_tarski @ (sk_C_1 @ X17 @ X14) @ (sk_D @ X17 @ X14)) @ X14)
% 0.76/0.97          | (r2_hidden @ (sk_C_1 @ X17 @ X14) @ X17))),
% 0.76/0.97      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.76/0.97  thf('79', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['16', '17'])).
% 0.76/0.97  thf('80', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         ((r2_hidden @ (sk_C_1 @ X1 @ X0) @ X1)
% 0.76/0.97          | ((X1) = (k1_relat_1 @ X0))
% 0.76/0.97          | ~ (v1_xboole_0 @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['78', '79'])).
% 0.76/0.97  thf('81', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['16', '17'])).
% 0.76/0.97  thf('82', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (~ (v1_xboole_0 @ X1)
% 0.76/0.97          | ((X0) = (k1_relat_1 @ X1))
% 0.76/0.97          | ~ (v1_xboole_0 @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['80', '81'])).
% 0.76/0.97  thf('83', plain,
% 0.76/0.97      (![X0 : $i]: (((k1_xboole_0) = (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['77', '82'])).
% 0.76/0.97  thf('84', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         (((k1_xboole_0) = (k1_relset_1 @ X2 @ X1 @ X0))
% 0.76/0.97          | ~ (v1_xboole_0 @ X0)
% 0.76/0.97          | ~ (v1_xboole_0 @ X0))),
% 0.76/0.97      inference('sup+', [status(thm)], ['76', '83'])).
% 0.76/0.97  thf('85', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (k1_relset_1 @ X2 @ X1 @ X0)))),
% 0.76/0.97      inference('simplify', [status(thm)], ['84'])).
% 0.76/0.97  thf('86', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/0.97      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/0.97  thf('87', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.76/0.97         ((v1_xboole_0 @ (k1_relset_1 @ X2 @ X1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.76/0.97      inference('sup+', [status(thm)], ['85', '86'])).
% 0.76/0.97  thf('88', plain,
% 0.76/0.97      (![X0 : $i]:
% 0.76/0.97         ((v1_xboole_0 @ (k1_relat_1 @ X0))
% 0.76/0.97          | ~ (v1_xboole_0 @ X0)
% 0.76/0.97          | ~ (v1_xboole_0 @ X0))),
% 0.76/0.97      inference('sup+', [status(thm)], ['75', '87'])).
% 0.76/0.97  thf('89', plain,
% 0.76/0.97      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.76/0.97      inference('simplify', [status(thm)], ['88'])).
% 0.76/0.97  thf('90', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_D_3))),
% 0.76/0.97      inference('sup-', [status(thm)], ['10', '18'])).
% 0.76/0.97  thf('91', plain, (~ (v1_xboole_0 @ sk_D_3)),
% 0.76/0.97      inference('sup-', [status(thm)], ['89', '90'])).
% 0.76/0.97  thf('92', plain,
% 0.76/0.97      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0)))),
% 0.76/0.97      inference('sup-', [status(thm)], ['68', '91'])).
% 0.76/0.97  thf('93', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/0.97      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/0.97  thf('94', plain, (((sk_A) = (k1_xboole_0))),
% 0.76/0.97      inference('demod', [status(thm)], ['92', '93'])).
% 0.76/0.97  thf('95', plain, (((sk_A) = (k1_xboole_0))),
% 0.76/0.97      inference('demod', [status(thm)], ['92', '93'])).
% 0.76/0.97  thf('96', plain,
% 0.76/0.97      ((~ (zip_tseitin_1 @ sk_D_3 @ k1_xboole_0 @ k1_xboole_0)
% 0.76/0.97        | ((k1_xboole_0) = (k1_relat_1 @ sk_D_3)))),
% 0.76/0.97      inference('demod', [status(thm)], ['58', '94', '95'])).
% 0.76/0.97  thf('97', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (~ (v1_xboole_0 @ X1)
% 0.76/0.97          | ((X0) = (k1_relat_1 @ X1))
% 0.76/0.97          | ~ (v1_xboole_0 @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['80', '81'])).
% 0.76/0.97  thf('98', plain,
% 0.76/0.97      (![X0 : $i]: (((k1_xboole_0) = (k1_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 0.76/0.97      inference('sup-', [status(thm)], ['77', '82'])).
% 0.76/0.97  thf('99', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (((k1_xboole_0) = (X0))
% 0.76/0.97          | ~ (v1_xboole_0 @ X0)
% 0.76/0.97          | ~ (v1_xboole_0 @ X1)
% 0.76/0.97          | ~ (v1_xboole_0 @ X1))),
% 0.76/0.97      inference('sup+', [status(thm)], ['97', '98'])).
% 0.76/0.97  thf('100', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]:
% 0.76/0.97         (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (X0)))),
% 0.76/0.97      inference('simplify', [status(thm)], ['99'])).
% 0.76/0.97  thf('101', plain,
% 0.76/0.97      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.76/0.97      inference('condensation', [status(thm)], ['100'])).
% 0.76/0.97  thf('102', plain,
% 0.76/0.97      (![X40 : $i, X41 : $i]:
% 0.76/0.97         ((zip_tseitin_0 @ X40 @ X41) | ((X41) != (k1_xboole_0)))),
% 0.76/0.97      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.76/0.97  thf('103', plain, (![X40 : $i]: (zip_tseitin_0 @ X40 @ k1_xboole_0)),
% 0.76/0.97      inference('simplify', [status(thm)], ['102'])).
% 0.76/0.97  thf('104', plain,
% 0.76/0.97      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.76/0.97      inference('sup+', [status(thm)], ['101', '103'])).
% 0.76/0.97  thf('105', plain,
% 0.76/0.97      (((zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A)
% 0.76/0.97        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['28', '29'])).
% 0.76/0.97  thf('106', plain,
% 0.76/0.97      ((~ (v1_xboole_0 @ sk_A) | (zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A))),
% 0.76/0.97      inference('sup-', [status(thm)], ['104', '105'])).
% 0.76/0.97  thf('107', plain, (((sk_B) = (k1_xboole_0))),
% 0.76/0.97      inference('simplify', [status(thm)], ['56'])).
% 0.76/0.97  thf('108', plain,
% 0.76/0.97      ((~ (v1_xboole_0 @ sk_A) | (zip_tseitin_1 @ sk_D_3 @ k1_xboole_0 @ sk_A))),
% 0.76/0.97      inference('demod', [status(thm)], ['106', '107'])).
% 0.76/0.97  thf('109', plain, (((sk_A) = (k1_xboole_0))),
% 0.76/0.97      inference('demod', [status(thm)], ['92', '93'])).
% 0.76/0.97  thf('110', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/0.97      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/0.97  thf('111', plain, (((sk_A) = (k1_xboole_0))),
% 0.76/0.97      inference('demod', [status(thm)], ['92', '93'])).
% 0.76/0.97  thf('112', plain, ((zip_tseitin_1 @ sk_D_3 @ k1_xboole_0 @ k1_xboole_0)),
% 0.76/0.97      inference('demod', [status(thm)], ['108', '109', '110', '111'])).
% 0.76/0.97  thf('113', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_D_3))),
% 0.76/0.97      inference('demod', [status(thm)], ['96', '112'])).
% 0.76/0.97  thf('114', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.76/0.97      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.76/0.97  thf('115', plain, ($false),
% 0.76/0.97      inference('demod', [status(thm)], ['19', '113', '114'])).
% 0.76/0.97  
% 0.76/0.97  % SZS output end Refutation
% 0.76/0.97  
% 0.76/0.98  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
