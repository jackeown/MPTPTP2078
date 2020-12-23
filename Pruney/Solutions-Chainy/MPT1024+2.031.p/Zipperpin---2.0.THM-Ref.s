%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.G4MC4aqW1A

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:38 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 390 expanded)
%              Number of leaves         :   42 ( 132 expanded)
%              Depth                    :   14
%              Number of atoms          :  785 (5499 expanded)
%              Number of equality atoms :   43 ( 228 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( ( k7_relset_1 @ X29 @ X30 @ X28 @ X31 )
        = ( k9_relat_1 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X22 @ X23 @ X21 @ X24 ) @ ( k1_zfmisc_1 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('7',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( r2_hidden @ X1 @ ( k9_relat_1 @ sk_D_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

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

thf('12',plain,(
    ! [X32: $i,X33: $i] :
      ( ( zip_tseitin_0 @ X32 @ X33 )
      | ( X32 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('14',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( zip_tseitin_0 @ X37 @ X38 )
      | ( zip_tseitin_1 @ X39 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('15',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_2 @ X36 @ X34 @ X35 )
      | ( X34
        = ( k1_relset_1 @ X34 @ X35 @ X36 ) )
      | ~ ( zip_tseitin_1 @ X36 @ X35 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( ( k1_relset_1 @ X26 @ X27 @ X25 )
        = ( k1_relat_1 @ X25 ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['16','23'])).

thf('25',plain,(
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

thf('26',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k9_relat_1 @ X12 @ X10 ) )
      | ( r2_hidden @ ( sk_D @ X12 @ X10 @ X11 ) @ ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('29',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('30',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','31'])).

thf('33',plain,(
    ! [X40: $i] :
      ( ~ ( r2_hidden @ X40 @ sk_A )
      | ~ ( r2_hidden @ X40 @ sk_C )
      | ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('36',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k9_relat_1 @ X12 @ X10 ) )
      | ( r2_hidden @ ( sk_D @ X12 @ X10 @ X11 ) @ X10 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['28','29'])).

thf('39',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['34','39'])).

thf('41',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('42',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k9_relat_1 @ X12 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X12 @ X10 @ X11 ) @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['28','29'])).

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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X13 @ X15 ) @ X14 )
      | ( X15
        = ( k1_funct_1 @ X14 @ X13 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['28','29'])).

thf('49',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E != sk_E ) ),
    inference(demod,[status(thm)],['40','50'])).

thf('52',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k9_relat_1 @ sk_D_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','52'])).

thf('54',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('56',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ sk_B )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_E @ sk_B ),
    inference('sup-',[status(thm)],['54','57'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('59',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('60',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('61',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X16 @ X17 )
      | ~ ( r1_tarski @ X17 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('62',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( r1_tarski @ sk_B @ sk_E ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['51'])).

thf('64',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['51'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('65',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('66',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['62','63','64','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['53','66'])).

thf('68',plain,(
    $false ),
    inference('sup-',[status(thm)],['4','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.G4MC4aqW1A
% 0.13/0.37  % Computer   : n009.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 16:01:41 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.46/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.68  % Solved by: fo/fo7.sh
% 0.46/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.68  % done 183 iterations in 0.188s
% 0.46/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.68  % SZS output start Refutation
% 0.46/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.68  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.46/0.68  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.68  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.46/0.68  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.46/0.68  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.46/0.68  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.68  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.46/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.68  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.46/0.68  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.46/0.68  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.46/0.68  thf(sk_E_type, type, sk_E: $i).
% 0.46/0.68  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.46/0.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.68  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.68  thf(t115_funct_2, conjecture,
% 0.46/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.68     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.46/0.68         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.68       ( ![E:$i]:
% 0.46/0.68         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.46/0.68              ( ![F:$i]:
% 0.46/0.68                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.46/0.68                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.46/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.68    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.68        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.46/0.68            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.68          ( ![E:$i]:
% 0.46/0.68            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.46/0.68                 ( ![F:$i]:
% 0.46/0.68                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.46/0.68                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 0.46/0.68    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 0.46/0.68  thf('0', plain,
% 0.46/0.68      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('1', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(redefinition_k7_relset_1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.68       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.46/0.68  thf('2', plain,
% 0.46/0.68      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.46/0.68          | ((k7_relset_1 @ X29 @ X30 @ X28 @ X31) = (k9_relat_1 @ X28 @ X31)))),
% 0.46/0.68      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.46/0.68  thf('3', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.46/0.68           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.68  thf('4', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.46/0.68      inference('demod', [status(thm)], ['0', '3'])).
% 0.46/0.68  thf('5', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(dt_k7_relset_1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.68       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.46/0.68  thf('6', plain,
% 0.46/0.68      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.46/0.68          | (m1_subset_1 @ (k7_relset_1 @ X22 @ X23 @ X21 @ X24) @ 
% 0.46/0.68             (k1_zfmisc_1 @ X23)))),
% 0.46/0.68      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.46/0.68  thf('7', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0) @ 
% 0.46/0.68          (k1_zfmisc_1 @ sk_B))),
% 0.46/0.68      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.68  thf(t5_subset, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.46/0.68          ( v1_xboole_0 @ C ) ) ))).
% 0.46/0.68  thf('8', plain,
% 0.46/0.68      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X6 @ X7)
% 0.46/0.68          | ~ (v1_xboole_0 @ X8)
% 0.46/0.68          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t5_subset])).
% 0.46/0.68  thf('9', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (~ (v1_xboole_0 @ sk_B)
% 0.46/0.68          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['7', '8'])).
% 0.46/0.68  thf('10', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.46/0.68           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.68  thf('11', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (~ (v1_xboole_0 @ sk_B)
% 0.46/0.68          | ~ (r2_hidden @ X1 @ (k9_relat_1 @ sk_D_1 @ X0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['9', '10'])).
% 0.46/0.68  thf(d1_funct_2, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.68       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.68           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.46/0.68             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.46/0.68         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.68           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.46/0.68             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.46/0.68  thf(zf_stmt_1, axiom,
% 0.46/0.68    (![B:$i,A:$i]:
% 0.46/0.68     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.68       ( zip_tseitin_0 @ B @ A ) ))).
% 0.46/0.68  thf('12', plain,
% 0.46/0.68      (![X32 : $i, X33 : $i]:
% 0.46/0.68         ((zip_tseitin_0 @ X32 @ X33) | ((X32) = (k1_xboole_0)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.68  thf('13', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.46/0.68  thf(zf_stmt_3, axiom,
% 0.46/0.68    (![C:$i,B:$i,A:$i]:
% 0.46/0.68     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.46/0.68       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.46/0.68  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.46/0.68  thf(zf_stmt_5, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.68       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.46/0.68         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.68           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.46/0.68             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.46/0.68  thf('14', plain,
% 0.46/0.68      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.46/0.68         (~ (zip_tseitin_0 @ X37 @ X38)
% 0.46/0.68          | (zip_tseitin_1 @ X39 @ X37 @ X38)
% 0.46/0.68          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37))))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.68  thf('15', plain,
% 0.46/0.68      (((zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.46/0.68        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.46/0.68      inference('sup-', [status(thm)], ['13', '14'])).
% 0.46/0.68  thf('16', plain,
% 0.46/0.68      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A))),
% 0.46/0.68      inference('sup-', [status(thm)], ['12', '15'])).
% 0.46/0.68  thf('17', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('18', plain,
% 0.46/0.68      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.46/0.68         (~ (v1_funct_2 @ X36 @ X34 @ X35)
% 0.46/0.68          | ((X34) = (k1_relset_1 @ X34 @ X35 @ X36))
% 0.46/0.68          | ~ (zip_tseitin_1 @ X36 @ X35 @ X34))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.46/0.68  thf('19', plain,
% 0.46/0.68      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.46/0.68        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_1)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['17', '18'])).
% 0.46/0.68  thf('20', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(redefinition_k1_relset_1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.68       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.46/0.68  thf('21', plain,
% 0.46/0.68      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.46/0.68         (((k1_relset_1 @ X26 @ X27 @ X25) = (k1_relat_1 @ X25))
% 0.46/0.68          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.46/0.68      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.68  thf('22', plain,
% 0.46/0.68      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.46/0.68      inference('sup-', [status(thm)], ['20', '21'])).
% 0.46/0.68  thf('23', plain,
% 0.46/0.68      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.46/0.68        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.46/0.68      inference('demod', [status(thm)], ['19', '22'])).
% 0.46/0.68  thf('24', plain,
% 0.46/0.68      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['16', '23'])).
% 0.46/0.68  thf('25', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.46/0.68      inference('demod', [status(thm)], ['0', '3'])).
% 0.46/0.68  thf(t143_relat_1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( v1_relat_1 @ C ) =>
% 0.46/0.68       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.46/0.68         ( ?[D:$i]:
% 0.46/0.68           ( ( r2_hidden @ D @ B ) & 
% 0.46/0.68             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.46/0.68             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.46/0.68  thf('26', plain,
% 0.46/0.68      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X11 @ (k9_relat_1 @ X12 @ X10))
% 0.46/0.68          | (r2_hidden @ (sk_D @ X12 @ X10 @ X11) @ (k1_relat_1 @ X12))
% 0.46/0.68          | ~ (v1_relat_1 @ X12))),
% 0.46/0.68      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.46/0.68  thf('27', plain,
% 0.46/0.68      ((~ (v1_relat_1 @ sk_D_1)
% 0.46/0.68        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['25', '26'])).
% 0.46/0.68  thf('28', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(cc1_relset_1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.68       ( v1_relat_1 @ C ) ))).
% 0.46/0.68  thf('29', plain,
% 0.46/0.68      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.46/0.68         ((v1_relat_1 @ X18)
% 0.46/0.68          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.46/0.68      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.68  thf('30', plain, ((v1_relat_1 @ sk_D_1)),
% 0.46/0.68      inference('sup-', [status(thm)], ['28', '29'])).
% 0.46/0.68  thf('31', plain,
% 0.46/0.68      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.46/0.68      inference('demod', [status(thm)], ['27', '30'])).
% 0.46/0.68  thf('32', plain,
% 0.46/0.68      (((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_A)
% 0.46/0.68        | ((sk_B) = (k1_xboole_0)))),
% 0.46/0.68      inference('sup+', [status(thm)], ['24', '31'])).
% 0.46/0.68  thf('33', plain,
% 0.46/0.68      (![X40 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X40 @ sk_A)
% 0.46/0.68          | ~ (r2_hidden @ X40 @ sk_C)
% 0.46/0.68          | ((sk_E) != (k1_funct_1 @ sk_D_1 @ X40)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('34', plain,
% 0.46/0.68      ((((sk_B) = (k1_xboole_0))
% 0.46/0.68        | ((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E)))
% 0.46/0.68        | ~ (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C))),
% 0.46/0.68      inference('sup-', [status(thm)], ['32', '33'])).
% 0.46/0.68  thf('35', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.46/0.68      inference('demod', [status(thm)], ['0', '3'])).
% 0.46/0.68  thf('36', plain,
% 0.46/0.68      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X11 @ (k9_relat_1 @ X12 @ X10))
% 0.46/0.68          | (r2_hidden @ (sk_D @ X12 @ X10 @ X11) @ X10)
% 0.46/0.68          | ~ (v1_relat_1 @ X12))),
% 0.46/0.68      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.46/0.68  thf('37', plain,
% 0.46/0.68      ((~ (v1_relat_1 @ sk_D_1)
% 0.46/0.68        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C))),
% 0.46/0.68      inference('sup-', [status(thm)], ['35', '36'])).
% 0.46/0.68  thf('38', plain, ((v1_relat_1 @ sk_D_1)),
% 0.46/0.68      inference('sup-', [status(thm)], ['28', '29'])).
% 0.46/0.68  thf('39', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C)),
% 0.46/0.68      inference('demod', [status(thm)], ['37', '38'])).
% 0.46/0.68  thf('40', plain,
% 0.46/0.68      ((((sk_B) = (k1_xboole_0))
% 0.46/0.68        | ((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E))))),
% 0.46/0.68      inference('demod', [status(thm)], ['34', '39'])).
% 0.46/0.68  thf('41', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.46/0.68      inference('demod', [status(thm)], ['0', '3'])).
% 0.46/0.68  thf('42', plain,
% 0.46/0.68      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X11 @ (k9_relat_1 @ X12 @ X10))
% 0.46/0.68          | (r2_hidden @ (k4_tarski @ (sk_D @ X12 @ X10 @ X11) @ X11) @ X12)
% 0.46/0.68          | ~ (v1_relat_1 @ X12))),
% 0.46/0.68      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.46/0.68  thf('43', plain,
% 0.46/0.68      ((~ (v1_relat_1 @ sk_D_1)
% 0.46/0.68        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ 
% 0.46/0.68           sk_D_1))),
% 0.46/0.68      inference('sup-', [status(thm)], ['41', '42'])).
% 0.46/0.68  thf('44', plain, ((v1_relat_1 @ sk_D_1)),
% 0.46/0.68      inference('sup-', [status(thm)], ['28', '29'])).
% 0.46/0.68  thf('45', plain,
% 0.46/0.68      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ sk_D_1)),
% 0.46/0.68      inference('demod', [status(thm)], ['43', '44'])).
% 0.46/0.68  thf(t8_funct_1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.46/0.68       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.46/0.68         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.46/0.68           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.46/0.68  thf('46', plain,
% 0.46/0.68      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.68         (~ (r2_hidden @ (k4_tarski @ X13 @ X15) @ X14)
% 0.46/0.68          | ((X15) = (k1_funct_1 @ X14 @ X13))
% 0.46/0.68          | ~ (v1_funct_1 @ X14)
% 0.46/0.68          | ~ (v1_relat_1 @ X14))),
% 0.46/0.68      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.46/0.68  thf('47', plain,
% 0.46/0.68      ((~ (v1_relat_1 @ sk_D_1)
% 0.46/0.68        | ~ (v1_funct_1 @ sk_D_1)
% 0.46/0.68        | ((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E))))),
% 0.46/0.68      inference('sup-', [status(thm)], ['45', '46'])).
% 0.46/0.68  thf('48', plain, ((v1_relat_1 @ sk_D_1)),
% 0.46/0.68      inference('sup-', [status(thm)], ['28', '29'])).
% 0.46/0.68  thf('49', plain, ((v1_funct_1 @ sk_D_1)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('50', plain,
% 0.46/0.68      (((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E)))),
% 0.46/0.68      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.46/0.68  thf('51', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_E) != (sk_E)))),
% 0.46/0.68      inference('demod', [status(thm)], ['40', '50'])).
% 0.46/0.68  thf('52', plain, (((sk_B) = (k1_xboole_0))),
% 0.46/0.68      inference('simplify', [status(thm)], ['51'])).
% 0.46/0.68  thf('53', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.68          | ~ (r2_hidden @ X1 @ (k9_relat_1 @ sk_D_1 @ X0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['11', '52'])).
% 0.46/0.68  thf('54', plain,
% 0.46/0.68      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('55', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0) @ 
% 0.46/0.68          (k1_zfmisc_1 @ sk_B))),
% 0.46/0.68      inference('sup-', [status(thm)], ['5', '6'])).
% 0.46/0.68  thf(t4_subset, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.46/0.68       ( m1_subset_1 @ A @ C ) ))).
% 0.46/0.68  thf('56', plain,
% 0.46/0.68      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X3 @ X4)
% 0.46/0.68          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.46/0.68          | (m1_subset_1 @ X3 @ X5))),
% 0.46/0.68      inference('cnf', [status(esa)], [t4_subset])).
% 0.46/0.68  thf('57', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         ((m1_subset_1 @ X1 @ sk_B)
% 0.46/0.68          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['55', '56'])).
% 0.46/0.68  thf('58', plain, ((m1_subset_1 @ sk_E @ sk_B)),
% 0.46/0.68      inference('sup-', [status(thm)], ['54', '57'])).
% 0.46/0.68  thf(t2_subset, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( m1_subset_1 @ A @ B ) =>
% 0.46/0.68       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.46/0.68  thf('59', plain,
% 0.46/0.68      (![X1 : $i, X2 : $i]:
% 0.46/0.68         ((r2_hidden @ X1 @ X2)
% 0.46/0.68          | (v1_xboole_0 @ X2)
% 0.46/0.68          | ~ (m1_subset_1 @ X1 @ X2))),
% 0.46/0.68      inference('cnf', [status(esa)], [t2_subset])).
% 0.46/0.68  thf('60', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_E @ sk_B))),
% 0.46/0.68      inference('sup-', [status(thm)], ['58', '59'])).
% 0.46/0.68  thf(t7_ordinal1, axiom,
% 0.46/0.68    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.68  thf('61', plain,
% 0.46/0.68      (![X16 : $i, X17 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X16 @ X17) | ~ (r1_tarski @ X17 @ X16))),
% 0.46/0.68      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.46/0.68  thf('62', plain, (((v1_xboole_0 @ sk_B) | ~ (r1_tarski @ sk_B @ sk_E))),
% 0.46/0.68      inference('sup-', [status(thm)], ['60', '61'])).
% 0.46/0.68  thf('63', plain, (((sk_B) = (k1_xboole_0))),
% 0.46/0.68      inference('simplify', [status(thm)], ['51'])).
% 0.46/0.68  thf('64', plain, (((sk_B) = (k1_xboole_0))),
% 0.46/0.68      inference('simplify', [status(thm)], ['51'])).
% 0.46/0.68  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.46/0.68  thf('65', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.46/0.68      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.46/0.68  thf('66', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.68      inference('demod', [status(thm)], ['62', '63', '64', '65'])).
% 0.46/0.68  thf('67', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k9_relat_1 @ sk_D_1 @ X0))),
% 0.46/0.68      inference('demod', [status(thm)], ['53', '66'])).
% 0.46/0.68  thf('68', plain, ($false), inference('sup-', [status(thm)], ['4', '67'])).
% 0.46/0.68  
% 0.46/0.68  % SZS output end Refutation
% 0.46/0.68  
% 0.46/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
