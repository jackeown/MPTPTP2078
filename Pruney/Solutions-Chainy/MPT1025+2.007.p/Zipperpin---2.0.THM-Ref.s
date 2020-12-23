%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wEEn151Pli

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:43 EST 2020

% Result     : Theorem 0.91s
% Output     : Refutation 0.91s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 259 expanded)
%              Number of leaves         :   45 (  97 expanded)
%              Depth                    :   16
%              Number of atoms          :  836 (3097 expanded)
%              Number of equality atoms :   53 ( 123 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

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
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_3 @ sk_C_1 ) ),
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
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( ( k7_relset_1 @ X37 @ X38 @ X36 @ X39 )
        = ( k9_relat_1 @ X36 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_3 @ X0 )
      = ( k9_relat_1 @ sk_D_3 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ sk_C_1 ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k9_relat_1 @ X14 @ X12 ) )
      | ( r2_hidden @ ( sk_D @ X14 @ X12 @ X13 ) @ ( k1_relat_1 @ X14 ) )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('6',plain,
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ( r2_hidden @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) @ ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('8',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) @ ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['6','11'])).

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

thf('13',plain,(
    ! [X16: $i,X18: $i,X20: $i,X21: $i] :
      ( ( X18
       != ( k2_relat_1 @ X16 ) )
      | ( r2_hidden @ X20 @ X18 )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X16 ) )
      | ( X20
       != ( k1_funct_1 @ X16 @ X21 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('14',plain,(
    ! [X16: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( r2_hidden @ X21 @ ( k1_relat_1 @ X16 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X16 @ X21 ) @ ( k2_relat_1 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_D_3 @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) ) @ ( k2_relat_1 @ sk_D_3 ) )
    | ~ ( v1_funct_1 @ sk_D_3 )
    | ~ ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['12','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['9','10'])).

thf('18',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D_3 @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) ) @ ( k2_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('20',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k9_relat_1 @ X14 @ X12 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X14 @ X12 @ X13 ) @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_E ) @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['9','10'])).

thf('23',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_E ) @ sk_D_3 ),
    inference(demod,[status(thm)],['21','22'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('24',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X22 @ X24 ) @ X23 )
      | ( X24
        = ( k1_funct_1 @ X23 @ X22 ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ~ ( v1_funct_1 @ sk_D_3 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_3 @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['9','10'])).

thf('27',plain,(
    v1_funct_1 @ sk_D_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D_3 @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    r2_hidden @ sk_E @ ( k2_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['18','28'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('30',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r2_hidden @ X25 @ X26 )
      | ~ ( r1_tarski @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('31',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ sk_E ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('33',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_0 @ X40 @ X41 )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('34',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('35',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( zip_tseitin_0 @ X45 @ X46 )
      | ( zip_tseitin_1 @ X47 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('36',plain,
    ( ( zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    v1_funct_2 @ sk_D_3 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ( X42
        = ( k1_relset_1 @ X42 @ X43 @ X44 ) )
      | ~ ( zip_tseitin_1 @ X44 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('40',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('42',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( ( k1_relset_1 @ X34 @ X35 @ X33 )
        = ( k1_relat_1 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('43',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_3 )
    = ( k1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference(demod,[status(thm)],['40','43'])).

thf('45',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_3 ) ) ),
    inference('sup-',[status(thm)],['37','44'])).

thf('46',plain,(
    r2_hidden @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) @ ( k1_relat_1 @ sk_D_3 ) ),
    inference(demod,[status(thm)],['6','11'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('47',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('48',plain,(
    m1_subset_1 @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) @ ( k1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( m1_subset_1 @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','48'])).

thf('50',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('51',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ ( k9_relat_1 @ X14 @ X12 ) )
      | ( r2_hidden @ ( sk_D @ X14 @ X12 @ X13 ) @ X12 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('52',plain,
    ( ~ ( v1_relat_1 @ sk_D_3 )
    | ( r2_hidden @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['9','10'])).

thf('54',plain,(
    r2_hidden @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_C_1 ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X48: $i] :
      ( ( sk_E
       != ( k1_funct_1 @ sk_D_3 @ X48 ) )
      | ~ ( r2_hidden @ X48 @ sk_C_1 )
      | ~ ( m1_subset_1 @ X48 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_A )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_3 @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_3 @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['49','56'])).

thf('58',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D_3 @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('59',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E != sk_E ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['59'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('61',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('62',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','60','62'])).

thf('64',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('65',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['64'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('66',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v5_relat_1 @ X30 @ X32 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v5_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ sk_D_3 @ X0 ) ),
    inference('sup-',[status(thm)],['63','67'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('69',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( v5_relat_1 @ X7 @ X8 )
      | ( r1_tarski @ ( k2_relat_1 @ X7 ) @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_3 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['9','10'])).

thf('72',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ X0 ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    $false ),
    inference(demod,[status(thm)],['31','72'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.wEEn151Pli
% 0.13/0.35  % Computer   : n013.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:37:55 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.91/1.15  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.91/1.15  % Solved by: fo/fo7.sh
% 0.91/1.15  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.91/1.15  % done 519 iterations in 0.691s
% 0.91/1.15  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.91/1.15  % SZS output start Refutation
% 0.91/1.15  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.91/1.15  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.91/1.15  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.91/1.15  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.91/1.15  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.91/1.15  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.91/1.15  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.91/1.15  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.91/1.15  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.91/1.15  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.91/1.15  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.91/1.15  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.91/1.15  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.91/1.15  thf(sk_A_type, type, sk_A: $i).
% 0.91/1.15  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.91/1.15  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.91/1.15  thf(sk_E_type, type, sk_E: $i).
% 0.91/1.15  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.91/1.15  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.91/1.15  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.91/1.15  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.91/1.15  thf(sk_B_type, type, sk_B: $i).
% 0.91/1.15  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.91/1.15  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.91/1.15  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.91/1.15  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.91/1.15  thf(t116_funct_2, conjecture,
% 0.91/1.15    (![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.15     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.91/1.15         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.91/1.15       ( ![E:$i]:
% 0.91/1.15         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.91/1.15              ( ![F:$i]:
% 0.91/1.15                ( ( m1_subset_1 @ F @ A ) =>
% 0.91/1.15                  ( ~( ( r2_hidden @ F @ C ) & 
% 0.91/1.15                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 0.91/1.15  thf(zf_stmt_0, negated_conjecture,
% 0.91/1.15    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.15        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.91/1.15            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.91/1.15          ( ![E:$i]:
% 0.91/1.15            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.91/1.15                 ( ![F:$i]:
% 0.91/1.15                   ( ( m1_subset_1 @ F @ A ) =>
% 0.91/1.15                     ( ~( ( r2_hidden @ F @ C ) & 
% 0.91/1.15                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.91/1.15    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 0.91/1.15  thf('0', plain,
% 0.91/1.15      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_3 @ sk_C_1))),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.15  thf('1', plain,
% 0.91/1.15      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.15  thf(redefinition_k7_relset_1, axiom,
% 0.91/1.15    (![A:$i,B:$i,C:$i,D:$i]:
% 0.91/1.15     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.15       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.91/1.15  thf('2', plain,
% 0.91/1.15      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.91/1.15         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.91/1.15          | ((k7_relset_1 @ X37 @ X38 @ X36 @ X39) = (k9_relat_1 @ X36 @ X39)))),
% 0.91/1.15      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.91/1.15  thf('3', plain,
% 0.91/1.15      (![X0 : $i]:
% 0.91/1.15         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_3 @ X0)
% 0.91/1.15           = (k9_relat_1 @ sk_D_3 @ X0))),
% 0.91/1.15      inference('sup-', [status(thm)], ['1', '2'])).
% 0.91/1.15  thf('4', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ sk_C_1))),
% 0.91/1.15      inference('demod', [status(thm)], ['0', '3'])).
% 0.91/1.15  thf(t143_relat_1, axiom,
% 0.91/1.15    (![A:$i,B:$i,C:$i]:
% 0.91/1.15     ( ( v1_relat_1 @ C ) =>
% 0.91/1.15       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.91/1.15         ( ?[D:$i]:
% 0.91/1.15           ( ( r2_hidden @ D @ B ) & 
% 0.91/1.15             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.91/1.15             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.91/1.15  thf('5', plain,
% 0.91/1.15      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.91/1.15         (~ (r2_hidden @ X13 @ (k9_relat_1 @ X14 @ X12))
% 0.91/1.15          | (r2_hidden @ (sk_D @ X14 @ X12 @ X13) @ (k1_relat_1 @ X14))
% 0.91/1.15          | ~ (v1_relat_1 @ X14))),
% 0.91/1.15      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.91/1.15  thf('6', plain,
% 0.91/1.15      ((~ (v1_relat_1 @ sk_D_3)
% 0.91/1.15        | (r2_hidden @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E) @ (k1_relat_1 @ sk_D_3)))),
% 0.91/1.15      inference('sup-', [status(thm)], ['4', '5'])).
% 0.91/1.15  thf('7', plain,
% 0.91/1.15      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.15  thf(cc2_relat_1, axiom,
% 0.91/1.15    (![A:$i]:
% 0.91/1.15     ( ( v1_relat_1 @ A ) =>
% 0.91/1.15       ( ![B:$i]:
% 0.91/1.15         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.91/1.15  thf('8', plain,
% 0.91/1.15      (![X5 : $i, X6 : $i]:
% 0.91/1.15         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.91/1.15          | (v1_relat_1 @ X5)
% 0.91/1.15          | ~ (v1_relat_1 @ X6))),
% 0.91/1.15      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.91/1.15  thf('9', plain,
% 0.91/1.15      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_3))),
% 0.91/1.15      inference('sup-', [status(thm)], ['7', '8'])).
% 0.91/1.15  thf(fc6_relat_1, axiom,
% 0.91/1.15    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.91/1.15  thf('10', plain,
% 0.91/1.15      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.91/1.15      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.91/1.15  thf('11', plain, ((v1_relat_1 @ sk_D_3)),
% 0.91/1.15      inference('demod', [status(thm)], ['9', '10'])).
% 0.91/1.15  thf('12', plain,
% 0.91/1.15      ((r2_hidden @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E) @ (k1_relat_1 @ sk_D_3))),
% 0.91/1.15      inference('demod', [status(thm)], ['6', '11'])).
% 0.91/1.15  thf(d5_funct_1, axiom,
% 0.91/1.15    (![A:$i]:
% 0.91/1.15     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.91/1.15       ( ![B:$i]:
% 0.91/1.15         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.91/1.15           ( ![C:$i]:
% 0.91/1.15             ( ( r2_hidden @ C @ B ) <=>
% 0.91/1.15               ( ?[D:$i]:
% 0.91/1.15                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.91/1.15                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.91/1.15  thf('13', plain,
% 0.91/1.15      (![X16 : $i, X18 : $i, X20 : $i, X21 : $i]:
% 0.91/1.15         (((X18) != (k2_relat_1 @ X16))
% 0.91/1.15          | (r2_hidden @ X20 @ X18)
% 0.91/1.15          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X16))
% 0.91/1.15          | ((X20) != (k1_funct_1 @ X16 @ X21))
% 0.91/1.15          | ~ (v1_funct_1 @ X16)
% 0.91/1.15          | ~ (v1_relat_1 @ X16))),
% 0.91/1.15      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.91/1.15  thf('14', plain,
% 0.91/1.15      (![X16 : $i, X21 : $i]:
% 0.91/1.15         (~ (v1_relat_1 @ X16)
% 0.91/1.15          | ~ (v1_funct_1 @ X16)
% 0.91/1.15          | ~ (r2_hidden @ X21 @ (k1_relat_1 @ X16))
% 0.91/1.15          | (r2_hidden @ (k1_funct_1 @ X16 @ X21) @ (k2_relat_1 @ X16)))),
% 0.91/1.15      inference('simplify', [status(thm)], ['13'])).
% 0.91/1.15  thf('15', plain,
% 0.91/1.15      (((r2_hidden @ (k1_funct_1 @ sk_D_3 @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E)) @ 
% 0.91/1.15         (k2_relat_1 @ sk_D_3))
% 0.91/1.15        | ~ (v1_funct_1 @ sk_D_3)
% 0.91/1.15        | ~ (v1_relat_1 @ sk_D_3))),
% 0.91/1.15      inference('sup-', [status(thm)], ['12', '14'])).
% 0.91/1.15  thf('16', plain, ((v1_funct_1 @ sk_D_3)),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.15  thf('17', plain, ((v1_relat_1 @ sk_D_3)),
% 0.91/1.15      inference('demod', [status(thm)], ['9', '10'])).
% 0.91/1.15  thf('18', plain,
% 0.91/1.15      ((r2_hidden @ (k1_funct_1 @ sk_D_3 @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E)) @ 
% 0.91/1.15        (k2_relat_1 @ sk_D_3))),
% 0.91/1.15      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.91/1.15  thf('19', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ sk_C_1))),
% 0.91/1.15      inference('demod', [status(thm)], ['0', '3'])).
% 0.91/1.15  thf('20', plain,
% 0.91/1.15      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.91/1.15         (~ (r2_hidden @ X13 @ (k9_relat_1 @ X14 @ X12))
% 0.91/1.15          | (r2_hidden @ (k4_tarski @ (sk_D @ X14 @ X12 @ X13) @ X13) @ X14)
% 0.91/1.15          | ~ (v1_relat_1 @ X14))),
% 0.91/1.15      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.91/1.15  thf('21', plain,
% 0.91/1.15      ((~ (v1_relat_1 @ sk_D_3)
% 0.91/1.15        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_E) @ 
% 0.91/1.15           sk_D_3))),
% 0.91/1.15      inference('sup-', [status(thm)], ['19', '20'])).
% 0.91/1.15  thf('22', plain, ((v1_relat_1 @ sk_D_3)),
% 0.91/1.15      inference('demod', [status(thm)], ['9', '10'])).
% 0.91/1.15  thf('23', plain,
% 0.91/1.15      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_E) @ 
% 0.91/1.15        sk_D_3)),
% 0.91/1.15      inference('demod', [status(thm)], ['21', '22'])).
% 0.91/1.15  thf(t8_funct_1, axiom,
% 0.91/1.15    (![A:$i,B:$i,C:$i]:
% 0.91/1.15     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.91/1.15       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.91/1.15         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.91/1.15           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.91/1.15  thf('24', plain,
% 0.91/1.15      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.91/1.15         (~ (r2_hidden @ (k4_tarski @ X22 @ X24) @ X23)
% 0.91/1.15          | ((X24) = (k1_funct_1 @ X23 @ X22))
% 0.91/1.15          | ~ (v1_funct_1 @ X23)
% 0.91/1.15          | ~ (v1_relat_1 @ X23))),
% 0.91/1.15      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.91/1.15  thf('25', plain,
% 0.91/1.15      ((~ (v1_relat_1 @ sk_D_3)
% 0.91/1.15        | ~ (v1_funct_1 @ sk_D_3)
% 0.91/1.15        | ((sk_E) = (k1_funct_1 @ sk_D_3 @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E))))),
% 0.91/1.15      inference('sup-', [status(thm)], ['23', '24'])).
% 0.91/1.15  thf('26', plain, ((v1_relat_1 @ sk_D_3)),
% 0.91/1.15      inference('demod', [status(thm)], ['9', '10'])).
% 0.91/1.15  thf('27', plain, ((v1_funct_1 @ sk_D_3)),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.15  thf('28', plain,
% 0.91/1.15      (((sk_E) = (k1_funct_1 @ sk_D_3 @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E)))),
% 0.91/1.15      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.91/1.15  thf('29', plain, ((r2_hidden @ sk_E @ (k2_relat_1 @ sk_D_3))),
% 0.91/1.15      inference('demod', [status(thm)], ['18', '28'])).
% 0.91/1.15  thf(t7_ordinal1, axiom,
% 0.91/1.15    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.91/1.15  thf('30', plain,
% 0.91/1.15      (![X25 : $i, X26 : $i]:
% 0.91/1.15         (~ (r2_hidden @ X25 @ X26) | ~ (r1_tarski @ X26 @ X25))),
% 0.91/1.15      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.91/1.15  thf('31', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_D_3) @ sk_E)),
% 0.91/1.15      inference('sup-', [status(thm)], ['29', '30'])).
% 0.91/1.15  thf('32', plain,
% 0.91/1.15      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.15  thf(d1_funct_2, axiom,
% 0.91/1.15    (![A:$i,B:$i,C:$i]:
% 0.91/1.15     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.15       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.91/1.15           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.91/1.15             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.91/1.15         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.91/1.15           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.91/1.15             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.91/1.15  thf(zf_stmt_1, axiom,
% 0.91/1.15    (![B:$i,A:$i]:
% 0.91/1.15     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.91/1.15       ( zip_tseitin_0 @ B @ A ) ))).
% 0.91/1.15  thf('33', plain,
% 0.91/1.15      (![X40 : $i, X41 : $i]:
% 0.91/1.15         ((zip_tseitin_0 @ X40 @ X41) | ((X40) = (k1_xboole_0)))),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.91/1.15  thf('34', plain,
% 0.91/1.15      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.15  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.91/1.15  thf(zf_stmt_3, axiom,
% 0.91/1.15    (![C:$i,B:$i,A:$i]:
% 0.91/1.15     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.91/1.15       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.91/1.15  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.91/1.15  thf(zf_stmt_5, axiom,
% 0.91/1.15    (![A:$i,B:$i,C:$i]:
% 0.91/1.15     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.15       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.91/1.15         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.91/1.15           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.91/1.15             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.91/1.15  thf('35', plain,
% 0.91/1.15      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.91/1.15         (~ (zip_tseitin_0 @ X45 @ X46)
% 0.91/1.15          | (zip_tseitin_1 @ X47 @ X45 @ X46)
% 0.91/1.15          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45))))),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.91/1.15  thf('36', plain,
% 0.91/1.15      (((zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A)
% 0.91/1.15        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.91/1.15      inference('sup-', [status(thm)], ['34', '35'])).
% 0.91/1.15  thf('37', plain,
% 0.91/1.15      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A))),
% 0.91/1.15      inference('sup-', [status(thm)], ['33', '36'])).
% 0.91/1.15  thf('38', plain, ((v1_funct_2 @ sk_D_3 @ sk_A @ sk_B)),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.15  thf('39', plain,
% 0.91/1.15      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.91/1.15         (~ (v1_funct_2 @ X44 @ X42 @ X43)
% 0.91/1.15          | ((X42) = (k1_relset_1 @ X42 @ X43 @ X44))
% 0.91/1.15          | ~ (zip_tseitin_1 @ X44 @ X43 @ X42))),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.91/1.15  thf('40', plain,
% 0.91/1.15      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A)
% 0.91/1.15        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_3)))),
% 0.91/1.15      inference('sup-', [status(thm)], ['38', '39'])).
% 0.91/1.15  thf('41', plain,
% 0.91/1.15      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.15  thf(redefinition_k1_relset_1, axiom,
% 0.91/1.15    (![A:$i,B:$i,C:$i]:
% 0.91/1.15     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.15       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.91/1.15  thf('42', plain,
% 0.91/1.15      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.91/1.15         (((k1_relset_1 @ X34 @ X35 @ X33) = (k1_relat_1 @ X33))
% 0.91/1.15          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.91/1.15      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.91/1.15  thf('43', plain,
% 0.91/1.15      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_3) = (k1_relat_1 @ sk_D_3))),
% 0.91/1.15      inference('sup-', [status(thm)], ['41', '42'])).
% 0.91/1.15  thf('44', plain,
% 0.91/1.15      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A)
% 0.91/1.15        | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 0.91/1.15      inference('demod', [status(thm)], ['40', '43'])).
% 0.91/1.15  thf('45', plain,
% 0.91/1.15      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 0.91/1.15      inference('sup-', [status(thm)], ['37', '44'])).
% 0.91/1.15  thf('46', plain,
% 0.91/1.15      ((r2_hidden @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E) @ (k1_relat_1 @ sk_D_3))),
% 0.91/1.15      inference('demod', [status(thm)], ['6', '11'])).
% 0.91/1.15  thf(t1_subset, axiom,
% 0.91/1.15    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.91/1.15  thf('47', plain,
% 0.91/1.15      (![X3 : $i, X4 : $i]: ((m1_subset_1 @ X3 @ X4) | ~ (r2_hidden @ X3 @ X4))),
% 0.91/1.15      inference('cnf', [status(esa)], [t1_subset])).
% 0.91/1.15  thf('48', plain,
% 0.91/1.15      ((m1_subset_1 @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E) @ (k1_relat_1 @ sk_D_3))),
% 0.91/1.15      inference('sup-', [status(thm)], ['46', '47'])).
% 0.91/1.15  thf('49', plain,
% 0.91/1.15      (((m1_subset_1 @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_A)
% 0.91/1.15        | ((sk_B) = (k1_xboole_0)))),
% 0.91/1.15      inference('sup+', [status(thm)], ['45', '48'])).
% 0.91/1.15  thf('50', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ sk_C_1))),
% 0.91/1.15      inference('demod', [status(thm)], ['0', '3'])).
% 0.91/1.15  thf('51', plain,
% 0.91/1.15      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.91/1.15         (~ (r2_hidden @ X13 @ (k9_relat_1 @ X14 @ X12))
% 0.91/1.15          | (r2_hidden @ (sk_D @ X14 @ X12 @ X13) @ X12)
% 0.91/1.15          | ~ (v1_relat_1 @ X14))),
% 0.91/1.15      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.91/1.15  thf('52', plain,
% 0.91/1.15      ((~ (v1_relat_1 @ sk_D_3)
% 0.91/1.15        | (r2_hidden @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_C_1))),
% 0.91/1.15      inference('sup-', [status(thm)], ['50', '51'])).
% 0.91/1.15  thf('53', plain, ((v1_relat_1 @ sk_D_3)),
% 0.91/1.15      inference('demod', [status(thm)], ['9', '10'])).
% 0.91/1.15  thf('54', plain, ((r2_hidden @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_C_1)),
% 0.91/1.15      inference('demod', [status(thm)], ['52', '53'])).
% 0.91/1.15  thf('55', plain,
% 0.91/1.15      (![X48 : $i]:
% 0.91/1.15         (((sk_E) != (k1_funct_1 @ sk_D_3 @ X48))
% 0.91/1.15          | ~ (r2_hidden @ X48 @ sk_C_1)
% 0.91/1.15          | ~ (m1_subset_1 @ X48 @ sk_A))),
% 0.91/1.15      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.91/1.15  thf('56', plain,
% 0.91/1.15      ((~ (m1_subset_1 @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_A)
% 0.91/1.15        | ((sk_E) != (k1_funct_1 @ sk_D_3 @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E))))),
% 0.91/1.15      inference('sup-', [status(thm)], ['54', '55'])).
% 0.91/1.15  thf('57', plain,
% 0.91/1.15      ((((sk_B) = (k1_xboole_0))
% 0.91/1.15        | ((sk_E) != (k1_funct_1 @ sk_D_3 @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E))))),
% 0.91/1.15      inference('sup-', [status(thm)], ['49', '56'])).
% 0.91/1.15  thf('58', plain,
% 0.91/1.15      (((sk_E) = (k1_funct_1 @ sk_D_3 @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E)))),
% 0.91/1.15      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.91/1.15  thf('59', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_E) != (sk_E)))),
% 0.91/1.15      inference('demod', [status(thm)], ['57', '58'])).
% 0.91/1.15  thf('60', plain, (((sk_B) = (k1_xboole_0))),
% 0.91/1.15      inference('simplify', [status(thm)], ['59'])).
% 0.91/1.15  thf(t113_zfmisc_1, axiom,
% 0.91/1.15    (![A:$i,B:$i]:
% 0.91/1.15     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.91/1.15       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.91/1.15  thf('61', plain,
% 0.91/1.15      (![X1 : $i, X2 : $i]:
% 0.91/1.15         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.91/1.15      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.91/1.15  thf('62', plain,
% 0.91/1.15      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.91/1.15      inference('simplify', [status(thm)], ['61'])).
% 0.91/1.15  thf('63', plain, ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.91/1.15      inference('demod', [status(thm)], ['32', '60', '62'])).
% 0.91/1.15  thf('64', plain,
% 0.91/1.15      (![X1 : $i, X2 : $i]:
% 0.91/1.15         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.91/1.15      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.91/1.15  thf('65', plain,
% 0.91/1.15      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.91/1.15      inference('simplify', [status(thm)], ['64'])).
% 0.91/1.15  thf(cc2_relset_1, axiom,
% 0.91/1.15    (![A:$i,B:$i,C:$i]:
% 0.91/1.15     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.91/1.15       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.91/1.15  thf('66', plain,
% 0.91/1.15      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.91/1.15         ((v5_relat_1 @ X30 @ X32)
% 0.91/1.15          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.91/1.15      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.91/1.15  thf('67', plain,
% 0.91/1.15      (![X0 : $i, X1 : $i]:
% 0.91/1.15         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.91/1.15          | (v5_relat_1 @ X1 @ X0))),
% 0.91/1.15      inference('sup-', [status(thm)], ['65', '66'])).
% 0.91/1.15  thf('68', plain, (![X0 : $i]: (v5_relat_1 @ sk_D_3 @ X0)),
% 0.91/1.15      inference('sup-', [status(thm)], ['63', '67'])).
% 0.91/1.15  thf(d19_relat_1, axiom,
% 0.91/1.15    (![A:$i,B:$i]:
% 0.91/1.15     ( ( v1_relat_1 @ B ) =>
% 0.91/1.15       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.91/1.15  thf('69', plain,
% 0.91/1.15      (![X7 : $i, X8 : $i]:
% 0.91/1.15         (~ (v5_relat_1 @ X7 @ X8)
% 0.91/1.15          | (r1_tarski @ (k2_relat_1 @ X7) @ X8)
% 0.91/1.15          | ~ (v1_relat_1 @ X7))),
% 0.91/1.15      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.91/1.15  thf('70', plain,
% 0.91/1.15      (![X0 : $i]:
% 0.91/1.15         (~ (v1_relat_1 @ sk_D_3) | (r1_tarski @ (k2_relat_1 @ sk_D_3) @ X0))),
% 0.91/1.15      inference('sup-', [status(thm)], ['68', '69'])).
% 0.91/1.15  thf('71', plain, ((v1_relat_1 @ sk_D_3)),
% 0.91/1.15      inference('demod', [status(thm)], ['9', '10'])).
% 0.91/1.15  thf('72', plain, (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ sk_D_3) @ X0)),
% 0.91/1.15      inference('demod', [status(thm)], ['70', '71'])).
% 0.91/1.15  thf('73', plain, ($false), inference('demod', [status(thm)], ['31', '72'])).
% 0.91/1.15  
% 0.91/1.15  % SZS output end Refutation
% 0.91/1.15  
% 0.91/1.16  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
