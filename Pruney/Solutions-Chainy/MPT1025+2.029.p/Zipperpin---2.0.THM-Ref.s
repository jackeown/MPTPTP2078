%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tyGO49ATE8

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:47 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  136 (1395 expanded)
%              Number of leaves         :   38 ( 421 expanded)
%              Depth                    :   21
%              Number of atoms          :  899 (20068 expanded)
%              Number of equality atoms :   65 ( 857 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

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
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C ) ),
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
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( ( k7_relset_1 @ X20 @ X21 @ X19 @ X22 )
        = ( k9_relat_1 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k9_relat_1 @ X9 @ X7 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X7 @ X8 ) @ ( k1_relat_1 @ X9 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('8',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('9',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('12',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
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

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('14',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('15',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('17',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('18',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('20',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('21',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('23',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('26',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf('28',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_A )
    | ( sk_B_1 = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('29',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( m1_subset_1 @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('31',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(clc,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_A ) ),
    inference('sup-',[status(thm)],['28','31'])).

thf('33',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('34',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k9_relat_1 @ X9 @ X7 ) )
      | ( r2_hidden @ ( sk_D @ X9 @ X7 @ X8 ) @ X7 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('35',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('37',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X31: $i] :
      ( ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ X31 ) )
      | ~ ( r2_hidden @ X31 @ sk_C )
      | ~ ( m1_subset_1 @ X31 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_A )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['32','39'])).

thf('41',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('42',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k9_relat_1 @ X9 @ X7 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X9 @ X7 @ X8 ) @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('45',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['43','44'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('46',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X10 @ X12 ) @ X11 )
      | ( X12
        = ( k1_funct_1 @ X11 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('49',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_E != sk_E ) ),
    inference(demod,[status(thm)],['40','50'])).

thf('52',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['19','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['51'])).

thf('56',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( X28 != k1_xboole_0 )
      | ( X29 = k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X30 @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('58',plain,(
    ! [X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X29 @ k1_xboole_0 )
      | ( X30 = k1_xboole_0 )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_D_1 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['56','58'])).

thf('60',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['51'])).

thf('62',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['43','44'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('66',plain,(
    ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','66'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('68',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('69',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['67','68'])).

thf('71',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['53','69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('73',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['67','68'])).

thf('74',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('76',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('78',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X24 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('79',plain,(
    ! [X23: $i] :
      ( zip_tseitin_0 @ X23 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['77','79'])).

thf('81',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( v1_xboole_0 @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ( zip_tseitin_0 @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('88',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_A @ X0 ) ),
    inference(clc,[status(thm)],['86','89'])).

thf('91',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['67','68'])).

thf('92',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,(
    zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['76','92'])).

thf('94',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['71','93'])).

thf('95',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('96',plain,(
    $false ),
    inference(demod,[status(thm)],['12','94','95'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.tyGO49ATE8
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:44:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.49/0.71  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.49/0.71  % Solved by: fo/fo7.sh
% 0.49/0.71  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.71  % done 230 iterations in 0.257s
% 0.49/0.71  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.49/0.71  % SZS output start Refutation
% 0.49/0.71  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.49/0.71  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.49/0.71  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.49/0.71  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.49/0.71  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.49/0.71  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.71  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.49/0.71  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.49/0.71  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.49/0.71  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.49/0.71  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.71  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.49/0.71  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.49/0.71  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.49/0.71  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.49/0.71  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.49/0.71  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.49/0.71  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.71  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.49/0.71  thf(sk_C_type, type, sk_C: $i).
% 0.49/0.71  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.49/0.71  thf(sk_E_type, type, sk_E: $i).
% 0.49/0.71  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.49/0.71  thf(t116_funct_2, conjecture,
% 0.49/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.71     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.49/0.71         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.49/0.71       ( ![E:$i]:
% 0.49/0.71         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.49/0.71              ( ![F:$i]:
% 0.49/0.71                ( ( m1_subset_1 @ F @ A ) =>
% 0.49/0.71                  ( ~( ( r2_hidden @ F @ C ) & 
% 0.49/0.71                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 0.49/0.71  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.71    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.71        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.49/0.71            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.49/0.71          ( ![E:$i]:
% 0.49/0.71            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.49/0.71                 ( ![F:$i]:
% 0.49/0.71                   ( ( m1_subset_1 @ F @ A ) =>
% 0.49/0.71                     ( ~( ( r2_hidden @ F @ C ) & 
% 0.49/0.71                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.49/0.71    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 0.49/0.71  thf('0', plain,
% 0.49/0.71      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_C))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('1', plain,
% 0.49/0.71      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf(redefinition_k7_relset_1, axiom,
% 0.49/0.71    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.71       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.49/0.71  thf('2', plain,
% 0.49/0.71      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.49/0.71         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.49/0.71          | ((k7_relset_1 @ X20 @ X21 @ X19 @ X22) = (k9_relat_1 @ X19 @ X22)))),
% 0.49/0.71      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.49/0.71  thf('3', plain,
% 0.49/0.71      (![X0 : $i]:
% 0.49/0.71         ((k7_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ X0)
% 0.49/0.71           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.49/0.71      inference('sup-', [status(thm)], ['1', '2'])).
% 0.49/0.71  thf('4', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.49/0.71      inference('demod', [status(thm)], ['0', '3'])).
% 0.49/0.71  thf(t143_relat_1, axiom,
% 0.49/0.71    (![A:$i,B:$i,C:$i]:
% 0.49/0.71     ( ( v1_relat_1 @ C ) =>
% 0.49/0.71       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.49/0.71         ( ?[D:$i]:
% 0.49/0.71           ( ( r2_hidden @ D @ B ) & 
% 0.49/0.71             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.49/0.71             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.49/0.71  thf('5', plain,
% 0.49/0.71      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.49/0.71         (~ (r2_hidden @ X8 @ (k9_relat_1 @ X9 @ X7))
% 0.49/0.71          | (r2_hidden @ (sk_D @ X9 @ X7 @ X8) @ (k1_relat_1 @ X9))
% 0.49/0.71          | ~ (v1_relat_1 @ X9))),
% 0.49/0.71      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.49/0.71  thf('6', plain,
% 0.49/0.71      ((~ (v1_relat_1 @ sk_D_1)
% 0.49/0.71        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['4', '5'])).
% 0.49/0.71  thf('7', plain,
% 0.49/0.71      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf(cc1_relset_1, axiom,
% 0.49/0.71    (![A:$i,B:$i,C:$i]:
% 0.49/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.71       ( v1_relat_1 @ C ) ))).
% 0.49/0.71  thf('8', plain,
% 0.49/0.71      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.49/0.71         ((v1_relat_1 @ X13)
% 0.49/0.71          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.49/0.71      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.49/0.71  thf('9', plain, ((v1_relat_1 @ sk_D_1)),
% 0.49/0.71      inference('sup-', [status(thm)], ['7', '8'])).
% 0.49/0.71  thf('10', plain,
% 0.49/0.71      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.49/0.71      inference('demod', [status(thm)], ['6', '9'])).
% 0.49/0.71  thf(d1_xboole_0, axiom,
% 0.49/0.71    (![A:$i]:
% 0.49/0.71     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.49/0.71  thf('11', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.49/0.71      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.49/0.71  thf('12', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_D_1))),
% 0.49/0.71      inference('sup-', [status(thm)], ['10', '11'])).
% 0.49/0.71  thf('13', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B_1)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf(d1_funct_2, axiom,
% 0.49/0.71    (![A:$i,B:$i,C:$i]:
% 0.49/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.71       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.49/0.71           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.49/0.71             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.49/0.71         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.49/0.71           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.49/0.71             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.49/0.71  thf(zf_stmt_1, axiom,
% 0.49/0.71    (![C:$i,B:$i,A:$i]:
% 0.49/0.71     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.49/0.71       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.49/0.71  thf('14', plain,
% 0.49/0.71      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.49/0.71         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 0.49/0.71          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 0.49/0.71          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.49/0.71  thf('15', plain,
% 0.49/0.71      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.49/0.71        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['13', '14'])).
% 0.49/0.71  thf('16', plain,
% 0.49/0.71      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf(redefinition_k1_relset_1, axiom,
% 0.49/0.71    (![A:$i,B:$i,C:$i]:
% 0.49/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.71       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.49/0.71  thf('17', plain,
% 0.49/0.71      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.49/0.71         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.49/0.71          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.49/0.71      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.49/0.71  thf('18', plain,
% 0.49/0.71      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.49/0.71      inference('sup-', [status(thm)], ['16', '17'])).
% 0.49/0.71  thf('19', plain,
% 0.49/0.71      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.49/0.71        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.49/0.71      inference('demod', [status(thm)], ['15', '18'])).
% 0.49/0.71  thf(zf_stmt_2, axiom,
% 0.49/0.71    (![B:$i,A:$i]:
% 0.49/0.71     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.49/0.71       ( zip_tseitin_0 @ B @ A ) ))).
% 0.49/0.71  thf('20', plain,
% 0.49/0.71      (![X23 : $i, X24 : $i]:
% 0.49/0.71         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.49/0.71  thf('21', plain,
% 0.49/0.71      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.49/0.71  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.49/0.71  thf(zf_stmt_5, axiom,
% 0.49/0.71    (![A:$i,B:$i,C:$i]:
% 0.49/0.71     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.71       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.49/0.71         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.49/0.71           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.49/0.71             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.49/0.71  thf('22', plain,
% 0.49/0.71      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.49/0.71         (~ (zip_tseitin_0 @ X28 @ X29)
% 0.49/0.71          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 0.49/0.71          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.49/0.71  thf('23', plain,
% 0.49/0.71      (((zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.49/0.71        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.49/0.71      inference('sup-', [status(thm)], ['21', '22'])).
% 0.49/0.71  thf('24', plain,
% 0.49/0.71      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A))),
% 0.49/0.71      inference('sup-', [status(thm)], ['20', '23'])).
% 0.49/0.71  thf('25', plain,
% 0.49/0.71      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.49/0.71        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.49/0.71      inference('demod', [status(thm)], ['15', '18'])).
% 0.49/0.71  thf('26', plain,
% 0.49/0.71      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['24', '25'])).
% 0.49/0.71  thf('27', plain,
% 0.49/0.71      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.49/0.71      inference('demod', [status(thm)], ['6', '9'])).
% 0.49/0.71  thf('28', plain,
% 0.49/0.71      (((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_A)
% 0.49/0.71        | ((sk_B_1) = (k1_xboole_0)))),
% 0.49/0.71      inference('sup+', [status(thm)], ['26', '27'])).
% 0.49/0.71  thf(d2_subset_1, axiom,
% 0.49/0.71    (![A:$i,B:$i]:
% 0.49/0.71     ( ( ( v1_xboole_0 @ A ) =>
% 0.49/0.71         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.49/0.71       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.49/0.71         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.49/0.71  thf('29', plain,
% 0.49/0.71      (![X3 : $i, X4 : $i]:
% 0.49/0.71         (~ (r2_hidden @ X3 @ X4)
% 0.49/0.71          | (m1_subset_1 @ X3 @ X4)
% 0.49/0.71          | (v1_xboole_0 @ X4))),
% 0.49/0.71      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.49/0.71  thf('30', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.49/0.71      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.49/0.71  thf('31', plain,
% 0.49/0.71      (![X3 : $i, X4 : $i]: ((m1_subset_1 @ X3 @ X4) | ~ (r2_hidden @ X3 @ X4))),
% 0.49/0.71      inference('clc', [status(thm)], ['29', '30'])).
% 0.49/0.71  thf('32', plain,
% 0.49/0.71      ((((sk_B_1) = (k1_xboole_0))
% 0.49/0.71        | (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_A))),
% 0.49/0.71      inference('sup-', [status(thm)], ['28', '31'])).
% 0.49/0.71  thf('33', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.49/0.71      inference('demod', [status(thm)], ['0', '3'])).
% 0.49/0.71  thf('34', plain,
% 0.49/0.71      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.49/0.71         (~ (r2_hidden @ X8 @ (k9_relat_1 @ X9 @ X7))
% 0.49/0.71          | (r2_hidden @ (sk_D @ X9 @ X7 @ X8) @ X7)
% 0.49/0.71          | ~ (v1_relat_1 @ X9))),
% 0.49/0.71      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.49/0.71  thf('35', plain,
% 0.49/0.71      ((~ (v1_relat_1 @ sk_D_1)
% 0.49/0.71        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C))),
% 0.49/0.71      inference('sup-', [status(thm)], ['33', '34'])).
% 0.49/0.71  thf('36', plain, ((v1_relat_1 @ sk_D_1)),
% 0.49/0.71      inference('sup-', [status(thm)], ['7', '8'])).
% 0.49/0.71  thf('37', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C)),
% 0.49/0.71      inference('demod', [status(thm)], ['35', '36'])).
% 0.49/0.71  thf('38', plain,
% 0.49/0.71      (![X31 : $i]:
% 0.49/0.71         (((sk_E) != (k1_funct_1 @ sk_D_1 @ X31))
% 0.49/0.71          | ~ (r2_hidden @ X31 @ sk_C)
% 0.49/0.71          | ~ (m1_subset_1 @ X31 @ sk_A))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('39', plain,
% 0.49/0.71      ((~ (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_A)
% 0.49/0.71        | ((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E))))),
% 0.49/0.71      inference('sup-', [status(thm)], ['37', '38'])).
% 0.49/0.71  thf('40', plain,
% 0.49/0.71      ((((sk_B_1) = (k1_xboole_0))
% 0.49/0.71        | ((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E))))),
% 0.49/0.71      inference('sup-', [status(thm)], ['32', '39'])).
% 0.49/0.71  thf('41', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.49/0.71      inference('demod', [status(thm)], ['0', '3'])).
% 0.49/0.71  thf('42', plain,
% 0.49/0.71      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.49/0.71         (~ (r2_hidden @ X8 @ (k9_relat_1 @ X9 @ X7))
% 0.49/0.71          | (r2_hidden @ (k4_tarski @ (sk_D @ X9 @ X7 @ X8) @ X8) @ X9)
% 0.49/0.71          | ~ (v1_relat_1 @ X9))),
% 0.49/0.71      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.49/0.71  thf('43', plain,
% 0.49/0.71      ((~ (v1_relat_1 @ sk_D_1)
% 0.49/0.71        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ 
% 0.49/0.71           sk_D_1))),
% 0.49/0.71      inference('sup-', [status(thm)], ['41', '42'])).
% 0.49/0.71  thf('44', plain, ((v1_relat_1 @ sk_D_1)),
% 0.49/0.71      inference('sup-', [status(thm)], ['7', '8'])).
% 0.49/0.71  thf('45', plain,
% 0.49/0.71      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ sk_D_1)),
% 0.49/0.71      inference('demod', [status(thm)], ['43', '44'])).
% 0.49/0.71  thf(t8_funct_1, axiom,
% 0.49/0.71    (![A:$i,B:$i,C:$i]:
% 0.49/0.71     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.49/0.71       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.49/0.71         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.49/0.71           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.49/0.71  thf('46', plain,
% 0.49/0.71      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.49/0.71         (~ (r2_hidden @ (k4_tarski @ X10 @ X12) @ X11)
% 0.49/0.71          | ((X12) = (k1_funct_1 @ X11 @ X10))
% 0.49/0.71          | ~ (v1_funct_1 @ X11)
% 0.49/0.71          | ~ (v1_relat_1 @ X11))),
% 0.49/0.71      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.49/0.71  thf('47', plain,
% 0.49/0.71      ((~ (v1_relat_1 @ sk_D_1)
% 0.49/0.71        | ~ (v1_funct_1 @ sk_D_1)
% 0.49/0.71        | ((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E))))),
% 0.49/0.71      inference('sup-', [status(thm)], ['45', '46'])).
% 0.49/0.71  thf('48', plain, ((v1_relat_1 @ sk_D_1)),
% 0.49/0.71      inference('sup-', [status(thm)], ['7', '8'])).
% 0.49/0.71  thf('49', plain, ((v1_funct_1 @ sk_D_1)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('50', plain,
% 0.49/0.71      (((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E)))),
% 0.49/0.71      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.49/0.71  thf('51', plain, ((((sk_B_1) = (k1_xboole_0)) | ((sk_E) != (sk_E)))),
% 0.49/0.71      inference('demod', [status(thm)], ['40', '50'])).
% 0.49/0.71  thf('52', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.49/0.71      inference('simplify', [status(thm)], ['51'])).
% 0.49/0.71  thf('53', plain,
% 0.49/0.71      ((~ (zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ sk_A)
% 0.49/0.71        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.49/0.71      inference('demod', [status(thm)], ['19', '52'])).
% 0.49/0.71  thf('54', plain,
% 0.49/0.71      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('55', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.49/0.71      inference('simplify', [status(thm)], ['51'])).
% 0.49/0.71  thf('56', plain,
% 0.49/0.71      ((m1_subset_1 @ sk_D_1 @ 
% 0.49/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.49/0.71      inference('demod', [status(thm)], ['54', '55'])).
% 0.49/0.71  thf('57', plain,
% 0.49/0.71      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.49/0.71         (((X28) != (k1_xboole_0))
% 0.49/0.71          | ((X29) = (k1_xboole_0))
% 0.49/0.71          | ((X30) = (k1_xboole_0))
% 0.49/0.71          | ~ (v1_funct_2 @ X30 @ X29 @ X28)
% 0.49/0.71          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.49/0.71  thf('58', plain,
% 0.49/0.71      (![X29 : $i, X30 : $i]:
% 0.49/0.71         (~ (m1_subset_1 @ X30 @ 
% 0.49/0.71             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ k1_xboole_0)))
% 0.49/0.71          | ~ (v1_funct_2 @ X30 @ X29 @ k1_xboole_0)
% 0.49/0.71          | ((X30) = (k1_xboole_0))
% 0.49/0.71          | ((X29) = (k1_xboole_0)))),
% 0.49/0.71      inference('simplify', [status(thm)], ['57'])).
% 0.49/0.71  thf('59', plain,
% 0.49/0.71      ((((sk_A) = (k1_xboole_0))
% 0.49/0.71        | ((sk_D_1) = (k1_xboole_0))
% 0.49/0.71        | ~ (v1_funct_2 @ sk_D_1 @ sk_A @ k1_xboole_0))),
% 0.49/0.71      inference('sup-', [status(thm)], ['56', '58'])).
% 0.49/0.71  thf('60', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B_1)),
% 0.49/0.71      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.71  thf('61', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.49/0.71      inference('simplify', [status(thm)], ['51'])).
% 0.49/0.71  thf('62', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ k1_xboole_0)),
% 0.49/0.71      inference('demod', [status(thm)], ['60', '61'])).
% 0.49/0.71  thf('63', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_D_1) = (k1_xboole_0)))),
% 0.49/0.71      inference('demod', [status(thm)], ['59', '62'])).
% 0.49/0.71  thf('64', plain,
% 0.49/0.71      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ sk_D_1)),
% 0.49/0.71      inference('demod', [status(thm)], ['43', '44'])).
% 0.49/0.71  thf('65', plain,
% 0.49/0.71      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.49/0.71      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.49/0.71  thf('66', plain, (~ (v1_xboole_0 @ sk_D_1)),
% 0.49/0.71      inference('sup-', [status(thm)], ['64', '65'])).
% 0.49/0.71  thf('67', plain,
% 0.49/0.71      ((~ (v1_xboole_0 @ k1_xboole_0) | ((sk_A) = (k1_xboole_0)))),
% 0.49/0.71      inference('sup-', [status(thm)], ['63', '66'])).
% 0.49/0.71  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.49/0.71  thf('68', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.49/0.71      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.49/0.71  thf('69', plain, (((sk_A) = (k1_xboole_0))),
% 0.49/0.71      inference('demod', [status(thm)], ['67', '68'])).
% 0.49/0.71  thf('70', plain, (((sk_A) = (k1_xboole_0))),
% 0.49/0.71      inference('demod', [status(thm)], ['67', '68'])).
% 0.49/0.71  thf('71', plain,
% 0.49/0.71      ((~ (zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.49/0.71        | ((k1_xboole_0) = (k1_relat_1 @ sk_D_1)))),
% 0.49/0.71      inference('demod', [status(thm)], ['53', '69', '70'])).
% 0.49/0.71  thf('72', plain,
% 0.49/0.71      ((m1_subset_1 @ sk_D_1 @ 
% 0.49/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.49/0.71      inference('demod', [status(thm)], ['54', '55'])).
% 0.49/0.71  thf('73', plain, (((sk_A) = (k1_xboole_0))),
% 0.49/0.71      inference('demod', [status(thm)], ['67', '68'])).
% 0.49/0.71  thf('74', plain,
% 0.49/0.71      ((m1_subset_1 @ sk_D_1 @ 
% 0.49/0.71        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.49/0.71      inference('demod', [status(thm)], ['72', '73'])).
% 0.49/0.71  thf('75', plain,
% 0.49/0.71      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.49/0.71         (~ (zip_tseitin_0 @ X28 @ X29)
% 0.49/0.71          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 0.49/0.72          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.49/0.72  thf('76', plain,
% 0.49/0.72      (((zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.49/0.72        | ~ (zip_tseitin_0 @ k1_xboole_0 @ k1_xboole_0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['74', '75'])).
% 0.49/0.72  thf('77', plain,
% 0.49/0.72      (![X23 : $i, X24 : $i]:
% 0.49/0.72         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.49/0.72  thf('78', plain,
% 0.49/0.72      (![X23 : $i, X24 : $i]:
% 0.49/0.72         ((zip_tseitin_0 @ X23 @ X24) | ((X24) != (k1_xboole_0)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.49/0.72  thf('79', plain, (![X23 : $i]: (zip_tseitin_0 @ X23 @ k1_xboole_0)),
% 0.49/0.72      inference('simplify', [status(thm)], ['78'])).
% 0.49/0.72  thf('80', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.72         ((zip_tseitin_0 @ X1 @ X0) | (zip_tseitin_0 @ X0 @ X2))),
% 0.49/0.72      inference('sup+', [status(thm)], ['77', '79'])).
% 0.49/0.72  thf('81', plain,
% 0.49/0.72      (((zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.49/0.72        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.49/0.72      inference('sup-', [status(thm)], ['21', '22'])).
% 0.49/0.72  thf('82', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         ((zip_tseitin_0 @ sk_A @ X0)
% 0.49/0.72          | (zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A))),
% 0.49/0.72      inference('sup-', [status(thm)], ['80', '81'])).
% 0.49/0.72  thf('83', plain,
% 0.49/0.72      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B_1 @ sk_A)
% 0.49/0.72        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.49/0.72      inference('demod', [status(thm)], ['15', '18'])).
% 0.49/0.72  thf('84', plain,
% 0.49/0.72      (![X0 : $i]:
% 0.49/0.72         ((zip_tseitin_0 @ sk_A @ X0) | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.49/0.72      inference('sup-', [status(thm)], ['82', '83'])).
% 0.49/0.72  thf('85', plain, (~ (v1_xboole_0 @ (k1_relat_1 @ sk_D_1))),
% 0.49/0.72      inference('sup-', [status(thm)], ['10', '11'])).
% 0.49/0.72  thf('86', plain,
% 0.49/0.72      (![X0 : $i]: (~ (v1_xboole_0 @ sk_A) | (zip_tseitin_0 @ sk_A @ X0))),
% 0.49/0.72      inference('sup-', [status(thm)], ['84', '85'])).
% 0.49/0.72  thf('87', plain,
% 0.49/0.72      (![X23 : $i, X24 : $i]:
% 0.49/0.72         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 0.49/0.72      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.49/0.72  thf('88', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.49/0.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.49/0.72  thf('89', plain,
% 0.49/0.72      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.49/0.72      inference('sup+', [status(thm)], ['87', '88'])).
% 0.49/0.72  thf('90', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_A @ X0)),
% 0.49/0.72      inference('clc', [status(thm)], ['86', '89'])).
% 0.49/0.72  thf('91', plain, (((sk_A) = (k1_xboole_0))),
% 0.49/0.72      inference('demod', [status(thm)], ['67', '68'])).
% 0.49/0.72  thf('92', plain, (![X0 : $i]: (zip_tseitin_0 @ k1_xboole_0 @ X0)),
% 0.49/0.72      inference('demod', [status(thm)], ['90', '91'])).
% 0.49/0.72  thf('93', plain, ((zip_tseitin_1 @ sk_D_1 @ k1_xboole_0 @ k1_xboole_0)),
% 0.49/0.72      inference('demod', [status(thm)], ['76', '92'])).
% 0.49/0.72  thf('94', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_D_1))),
% 0.49/0.72      inference('demod', [status(thm)], ['71', '93'])).
% 0.49/0.72  thf('95', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.49/0.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.49/0.72  thf('96', plain, ($false),
% 0.49/0.72      inference('demod', [status(thm)], ['12', '94', '95'])).
% 0.49/0.72  
% 0.49/0.72  % SZS output end Refutation
% 0.49/0.72  
% 0.49/0.72  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
