%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.G0zrJb9uDp

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:34 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 256 expanded)
%              Number of leaves         :   44 (  96 expanded)
%              Depth                    :   16
%              Number of atoms          :  820 (3081 expanded)
%              Number of equality atoms :   54 ( 124 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_3_type,type,(
    sk_D_3: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

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
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( ( k7_relset_1 @ X35 @ X36 @ X34 @ X37 )
        = ( k9_relat_1 @ X34 @ X37 ) ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k9_relat_1 @ X12 @ X10 ) )
      | ( r2_hidden @ ( sk_D @ X12 @ X10 @ X11 ) @ ( k1_relat_1 @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
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
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_3 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('10',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
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
    ! [X14: $i,X16: $i,X18: $i,X19: $i] :
      ( ( X16
       != ( k2_relat_1 @ X14 ) )
      | ( r2_hidden @ X18 @ X16 )
      | ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X14 ) )
      | ( X18
       != ( k1_funct_1 @ X14 @ X19 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d5_funct_1])).

thf('14',plain,(
    ! [X14: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ X14 ) )
      | ( r2_hidden @ ( k1_funct_1 @ X14 @ X19 ) @ ( k2_relat_1 @ X14 ) ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k9_relat_1 @ X12 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X12 @ X10 @ X11 ) @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X20 @ X22 ) @ X21 )
      | ( X22
        = ( k1_funct_1 @ X21 @ X20 ) )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
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
    ! [X23: $i,X24: $i] :
      ( ~ ( r2_hidden @ X23 @ X24 )
      | ~ ( r1_tarski @ X24 @ X23 ) ) ),
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
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_0 @ X38 @ X39 )
      | ( X38 = k1_xboole_0 ) ) ),
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
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( zip_tseitin_0 @ X43 @ X44 )
      | ( zip_tseitin_1 @ X45 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ) ),
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
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ( X40
        = ( k1_relset_1 @ X40 @ X41 @ X42 ) )
      | ~ ( zip_tseitin_1 @ X42 @ X41 @ X40 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X33 @ X31 )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
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

thf('47',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X46: $i] :
      ( ~ ( r2_hidden @ X46 @ sk_A )
      | ~ ( r2_hidden @ X46 @ sk_C_1 )
      | ( sk_E
       != ( k1_funct_1 @ sk_D_3 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_3 @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) ) )
    | ~ ( r2_hidden @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_3 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('51',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k9_relat_1 @ X12 @ X10 ) )
      | ( r2_hidden @ ( sk_D @ X12 @ X10 @ X11 ) @ X10 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
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

thf('55',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_3 @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['49','54'])).

thf('56',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D_3 @ ( sk_D @ sk_D_3 @ sk_C_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('57',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E != sk_E ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['57'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('59',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('60',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    m1_subset_1 @ sk_D_3 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['32','58','60'])).

thf('62',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('63',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['62'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('64',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v5_relat_1 @ X28 @ X30 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v5_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ sk_D_3 @ X0 ) ),
    inference('sup-',[status(thm)],['61','65'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('67',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v5_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k2_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_3 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_D_3 ),
    inference(demod,[status(thm)],['9','10'])).

thf('70',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ sk_D_3 ) @ X0 ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['31','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.14/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.16  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.G0zrJb9uDp
% 0.16/0.37  % Computer   : n004.cluster.edu
% 0.16/0.37  % Model      : x86_64 x86_64
% 0.16/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.37  % Memory     : 8042.1875MB
% 0.16/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.37  % CPULimit   : 60
% 0.16/0.37  % DateTime   : Tue Dec  1 15:38:54 EST 2020
% 0.16/0.37  % CPUTime    : 
% 0.16/0.37  % Running portfolio for 600 s
% 0.16/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.37  % Number of cores: 8
% 0.16/0.37  % Python version: Python 3.6.8
% 0.16/0.37  % Running in FO mode
% 0.89/1.08  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.89/1.08  % Solved by: fo/fo7.sh
% 0.89/1.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.08  % done 495 iterations in 0.600s
% 0.89/1.08  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.89/1.08  % SZS output start Refutation
% 0.89/1.08  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.89/1.08  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.89/1.08  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.89/1.08  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.89/1.08  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.89/1.08  thf(sk_B_type, type, sk_B: $i).
% 0.89/1.08  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.89/1.08  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.89/1.08  thf(sk_E_type, type, sk_E: $i).
% 0.89/1.08  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.89/1.08  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.89/1.08  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.89/1.08  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.89/1.08  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.89/1.08  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.89/1.08  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.89/1.08  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.89/1.08  thf(sk_D_3_type, type, sk_D_3: $i).
% 0.89/1.08  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.89/1.08  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.89/1.08  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.89/1.08  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.89/1.08  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.08  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.89/1.08  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.89/1.08  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.89/1.08  thf(t115_funct_2, conjecture,
% 0.89/1.08    (![A:$i,B:$i,C:$i,D:$i]:
% 0.89/1.08     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.89/1.08         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.08       ( ![E:$i]:
% 0.89/1.08         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.89/1.08              ( ![F:$i]:
% 0.89/1.08                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.89/1.08                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.89/1.08  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.08    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.89/1.08        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.89/1.08            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.89/1.08          ( ![E:$i]:
% 0.89/1.08            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.89/1.08                 ( ![F:$i]:
% 0.89/1.08                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.89/1.08                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 0.89/1.08    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 0.89/1.08  thf('0', plain,
% 0.89/1.08      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_3 @ sk_C_1))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('1', plain,
% 0.89/1.08      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf(redefinition_k7_relset_1, axiom,
% 0.89/1.08    (![A:$i,B:$i,C:$i,D:$i]:
% 0.89/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.08       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.89/1.08  thf('2', plain,
% 0.89/1.08      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.89/1.08         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.89/1.08          | ((k7_relset_1 @ X35 @ X36 @ X34 @ X37) = (k9_relat_1 @ X34 @ X37)))),
% 0.89/1.08      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.89/1.08  thf('3', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_3 @ X0)
% 0.89/1.08           = (k9_relat_1 @ sk_D_3 @ X0))),
% 0.89/1.08      inference('sup-', [status(thm)], ['1', '2'])).
% 0.89/1.08  thf('4', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ sk_C_1))),
% 0.89/1.08      inference('demod', [status(thm)], ['0', '3'])).
% 0.89/1.08  thf(t143_relat_1, axiom,
% 0.89/1.08    (![A:$i,B:$i,C:$i]:
% 0.89/1.08     ( ( v1_relat_1 @ C ) =>
% 0.89/1.08       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.89/1.08         ( ?[D:$i]:
% 0.89/1.08           ( ( r2_hidden @ D @ B ) & 
% 0.89/1.08             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.89/1.08             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.89/1.08  thf('5', plain,
% 0.89/1.08      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.89/1.08         (~ (r2_hidden @ X11 @ (k9_relat_1 @ X12 @ X10))
% 0.89/1.08          | (r2_hidden @ (sk_D @ X12 @ X10 @ X11) @ (k1_relat_1 @ X12))
% 0.89/1.08          | ~ (v1_relat_1 @ X12))),
% 0.89/1.08      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.89/1.08  thf('6', plain,
% 0.89/1.08      ((~ (v1_relat_1 @ sk_D_3)
% 0.89/1.08        | (r2_hidden @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E) @ (k1_relat_1 @ sk_D_3)))),
% 0.89/1.08      inference('sup-', [status(thm)], ['4', '5'])).
% 0.89/1.08  thf('7', plain,
% 0.89/1.08      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf(cc2_relat_1, axiom,
% 0.89/1.08    (![A:$i]:
% 0.89/1.08     ( ( v1_relat_1 @ A ) =>
% 0.89/1.08       ( ![B:$i]:
% 0.89/1.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.89/1.08  thf('8', plain,
% 0.89/1.08      (![X3 : $i, X4 : $i]:
% 0.89/1.08         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.89/1.08          | (v1_relat_1 @ X3)
% 0.89/1.08          | ~ (v1_relat_1 @ X4))),
% 0.89/1.08      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.89/1.08  thf('9', plain,
% 0.89/1.08      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_3))),
% 0.89/1.08      inference('sup-', [status(thm)], ['7', '8'])).
% 0.89/1.08  thf(fc6_relat_1, axiom,
% 0.89/1.08    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.89/1.08  thf('10', plain,
% 0.89/1.08      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.89/1.08      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.89/1.08  thf('11', plain, ((v1_relat_1 @ sk_D_3)),
% 0.89/1.08      inference('demod', [status(thm)], ['9', '10'])).
% 0.89/1.08  thf('12', plain,
% 0.89/1.08      ((r2_hidden @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E) @ (k1_relat_1 @ sk_D_3))),
% 0.89/1.08      inference('demod', [status(thm)], ['6', '11'])).
% 0.89/1.08  thf(d5_funct_1, axiom,
% 0.89/1.08    (![A:$i]:
% 0.89/1.08     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.89/1.08       ( ![B:$i]:
% 0.89/1.08         ( ( ( B ) = ( k2_relat_1 @ A ) ) <=>
% 0.89/1.08           ( ![C:$i]:
% 0.89/1.08             ( ( r2_hidden @ C @ B ) <=>
% 0.89/1.08               ( ?[D:$i]:
% 0.89/1.08                 ( ( ( C ) = ( k1_funct_1 @ A @ D ) ) & 
% 0.89/1.08                   ( r2_hidden @ D @ ( k1_relat_1 @ A ) ) ) ) ) ) ) ) ))).
% 0.89/1.08  thf('13', plain,
% 0.89/1.08      (![X14 : $i, X16 : $i, X18 : $i, X19 : $i]:
% 0.89/1.08         (((X16) != (k2_relat_1 @ X14))
% 0.89/1.08          | (r2_hidden @ X18 @ X16)
% 0.89/1.08          | ~ (r2_hidden @ X19 @ (k1_relat_1 @ X14))
% 0.89/1.08          | ((X18) != (k1_funct_1 @ X14 @ X19))
% 0.89/1.08          | ~ (v1_funct_1 @ X14)
% 0.89/1.08          | ~ (v1_relat_1 @ X14))),
% 0.89/1.08      inference('cnf', [status(esa)], [d5_funct_1])).
% 0.89/1.08  thf('14', plain,
% 0.89/1.08      (![X14 : $i, X19 : $i]:
% 0.89/1.08         (~ (v1_relat_1 @ X14)
% 0.89/1.08          | ~ (v1_funct_1 @ X14)
% 0.89/1.08          | ~ (r2_hidden @ X19 @ (k1_relat_1 @ X14))
% 0.89/1.08          | (r2_hidden @ (k1_funct_1 @ X14 @ X19) @ (k2_relat_1 @ X14)))),
% 0.89/1.08      inference('simplify', [status(thm)], ['13'])).
% 0.89/1.08  thf('15', plain,
% 0.89/1.08      (((r2_hidden @ (k1_funct_1 @ sk_D_3 @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E)) @ 
% 0.89/1.08         (k2_relat_1 @ sk_D_3))
% 0.89/1.08        | ~ (v1_funct_1 @ sk_D_3)
% 0.89/1.08        | ~ (v1_relat_1 @ sk_D_3))),
% 0.89/1.08      inference('sup-', [status(thm)], ['12', '14'])).
% 0.89/1.08  thf('16', plain, ((v1_funct_1 @ sk_D_3)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('17', plain, ((v1_relat_1 @ sk_D_3)),
% 0.89/1.08      inference('demod', [status(thm)], ['9', '10'])).
% 0.89/1.08  thf('18', plain,
% 0.89/1.08      ((r2_hidden @ (k1_funct_1 @ sk_D_3 @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E)) @ 
% 0.89/1.08        (k2_relat_1 @ sk_D_3))),
% 0.89/1.08      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.89/1.08  thf('19', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ sk_C_1))),
% 0.89/1.08      inference('demod', [status(thm)], ['0', '3'])).
% 0.89/1.08  thf('20', plain,
% 0.89/1.08      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.89/1.08         (~ (r2_hidden @ X11 @ (k9_relat_1 @ X12 @ X10))
% 0.89/1.08          | (r2_hidden @ (k4_tarski @ (sk_D @ X12 @ X10 @ X11) @ X11) @ X12)
% 0.89/1.08          | ~ (v1_relat_1 @ X12))),
% 0.89/1.08      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.89/1.08  thf('21', plain,
% 0.89/1.08      ((~ (v1_relat_1 @ sk_D_3)
% 0.89/1.08        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_E) @ 
% 0.89/1.08           sk_D_3))),
% 0.89/1.08      inference('sup-', [status(thm)], ['19', '20'])).
% 0.89/1.08  thf('22', plain, ((v1_relat_1 @ sk_D_3)),
% 0.89/1.08      inference('demod', [status(thm)], ['9', '10'])).
% 0.89/1.08  thf('23', plain,
% 0.89/1.08      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_E) @ 
% 0.89/1.08        sk_D_3)),
% 0.89/1.08      inference('demod', [status(thm)], ['21', '22'])).
% 0.89/1.08  thf(t8_funct_1, axiom,
% 0.89/1.08    (![A:$i,B:$i,C:$i]:
% 0.89/1.08     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.89/1.08       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.89/1.08         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.89/1.08           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.89/1.08  thf('24', plain,
% 0.89/1.08      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.89/1.08         (~ (r2_hidden @ (k4_tarski @ X20 @ X22) @ X21)
% 0.89/1.08          | ((X22) = (k1_funct_1 @ X21 @ X20))
% 0.89/1.08          | ~ (v1_funct_1 @ X21)
% 0.89/1.08          | ~ (v1_relat_1 @ X21))),
% 0.89/1.08      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.89/1.08  thf('25', plain,
% 0.89/1.08      ((~ (v1_relat_1 @ sk_D_3)
% 0.89/1.08        | ~ (v1_funct_1 @ sk_D_3)
% 0.89/1.08        | ((sk_E) = (k1_funct_1 @ sk_D_3 @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E))))),
% 0.89/1.08      inference('sup-', [status(thm)], ['23', '24'])).
% 0.89/1.08  thf('26', plain, ((v1_relat_1 @ sk_D_3)),
% 0.89/1.08      inference('demod', [status(thm)], ['9', '10'])).
% 0.89/1.08  thf('27', plain, ((v1_funct_1 @ sk_D_3)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('28', plain,
% 0.89/1.08      (((sk_E) = (k1_funct_1 @ sk_D_3 @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E)))),
% 0.89/1.08      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.89/1.08  thf('29', plain, ((r2_hidden @ sk_E @ (k2_relat_1 @ sk_D_3))),
% 0.89/1.08      inference('demod', [status(thm)], ['18', '28'])).
% 0.89/1.08  thf(t7_ordinal1, axiom,
% 0.89/1.08    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.89/1.08  thf('30', plain,
% 0.89/1.08      (![X23 : $i, X24 : $i]:
% 0.89/1.08         (~ (r2_hidden @ X23 @ X24) | ~ (r1_tarski @ X24 @ X23))),
% 0.89/1.08      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.89/1.08  thf('31', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_D_3) @ sk_E)),
% 0.89/1.08      inference('sup-', [status(thm)], ['29', '30'])).
% 0.89/1.08  thf('32', plain,
% 0.89/1.08      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf(d1_funct_2, axiom,
% 0.89/1.08    (![A:$i,B:$i,C:$i]:
% 0.89/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.08       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.89/1.08           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.89/1.08             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.89/1.08         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.89/1.08           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.89/1.08             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.89/1.08  thf(zf_stmt_1, axiom,
% 0.89/1.08    (![B:$i,A:$i]:
% 0.89/1.08     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.89/1.08       ( zip_tseitin_0 @ B @ A ) ))).
% 0.89/1.08  thf('33', plain,
% 0.89/1.08      (![X38 : $i, X39 : $i]:
% 0.89/1.08         ((zip_tseitin_0 @ X38 @ X39) | ((X38) = (k1_xboole_0)))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.08  thf('34', plain,
% 0.89/1.08      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.89/1.08  thf(zf_stmt_3, axiom,
% 0.89/1.08    (![C:$i,B:$i,A:$i]:
% 0.89/1.08     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.89/1.08       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.89/1.08  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.89/1.08  thf(zf_stmt_5, axiom,
% 0.89/1.08    (![A:$i,B:$i,C:$i]:
% 0.89/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.08       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.89/1.08         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.89/1.08           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.89/1.08             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.89/1.08  thf('35', plain,
% 0.89/1.08      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.89/1.08         (~ (zip_tseitin_0 @ X43 @ X44)
% 0.89/1.08          | (zip_tseitin_1 @ X45 @ X43 @ X44)
% 0.89/1.08          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43))))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.89/1.08  thf('36', plain,
% 0.89/1.08      (((zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A)
% 0.89/1.08        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.89/1.08      inference('sup-', [status(thm)], ['34', '35'])).
% 0.89/1.08  thf('37', plain,
% 0.89/1.08      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A))),
% 0.89/1.08      inference('sup-', [status(thm)], ['33', '36'])).
% 0.89/1.08  thf('38', plain, ((v1_funct_2 @ sk_D_3 @ sk_A @ sk_B)),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('39', plain,
% 0.89/1.08      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.89/1.08         (~ (v1_funct_2 @ X42 @ X40 @ X41)
% 0.89/1.08          | ((X40) = (k1_relset_1 @ X40 @ X41 @ X42))
% 0.89/1.08          | ~ (zip_tseitin_1 @ X42 @ X41 @ X40))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.89/1.08  thf('40', plain,
% 0.89/1.08      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A)
% 0.89/1.08        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_3)))),
% 0.89/1.08      inference('sup-', [status(thm)], ['38', '39'])).
% 0.89/1.08  thf('41', plain,
% 0.89/1.08      ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf(redefinition_k1_relset_1, axiom,
% 0.89/1.08    (![A:$i,B:$i,C:$i]:
% 0.89/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.08       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.89/1.08  thf('42', plain,
% 0.89/1.08      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.89/1.08         (((k1_relset_1 @ X32 @ X33 @ X31) = (k1_relat_1 @ X31))
% 0.89/1.08          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.89/1.08      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.89/1.08  thf('43', plain,
% 0.89/1.08      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_3) = (k1_relat_1 @ sk_D_3))),
% 0.89/1.08      inference('sup-', [status(thm)], ['41', '42'])).
% 0.89/1.08  thf('44', plain,
% 0.89/1.08      ((~ (zip_tseitin_1 @ sk_D_3 @ sk_B @ sk_A)
% 0.89/1.08        | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 0.89/1.08      inference('demod', [status(thm)], ['40', '43'])).
% 0.89/1.08  thf('45', plain,
% 0.89/1.08      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_3)))),
% 0.89/1.08      inference('sup-', [status(thm)], ['37', '44'])).
% 0.89/1.08  thf('46', plain,
% 0.89/1.08      ((r2_hidden @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E) @ (k1_relat_1 @ sk_D_3))),
% 0.89/1.08      inference('demod', [status(thm)], ['6', '11'])).
% 0.89/1.08  thf('47', plain,
% 0.89/1.08      (((r2_hidden @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_A)
% 0.89/1.08        | ((sk_B) = (k1_xboole_0)))),
% 0.89/1.08      inference('sup+', [status(thm)], ['45', '46'])).
% 0.89/1.08  thf('48', plain,
% 0.89/1.08      (![X46 : $i]:
% 0.89/1.08         (~ (r2_hidden @ X46 @ sk_A)
% 0.89/1.08          | ~ (r2_hidden @ X46 @ sk_C_1)
% 0.89/1.08          | ((sk_E) != (k1_funct_1 @ sk_D_3 @ X46)))),
% 0.89/1.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.08  thf('49', plain,
% 0.89/1.08      ((((sk_B) = (k1_xboole_0))
% 0.89/1.08        | ((sk_E) != (k1_funct_1 @ sk_D_3 @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E)))
% 0.89/1.08        | ~ (r2_hidden @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_C_1))),
% 0.89/1.08      inference('sup-', [status(thm)], ['47', '48'])).
% 0.89/1.08  thf('50', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_3 @ sk_C_1))),
% 0.89/1.08      inference('demod', [status(thm)], ['0', '3'])).
% 0.89/1.08  thf('51', plain,
% 0.89/1.08      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.89/1.08         (~ (r2_hidden @ X11 @ (k9_relat_1 @ X12 @ X10))
% 0.89/1.08          | (r2_hidden @ (sk_D @ X12 @ X10 @ X11) @ X10)
% 0.89/1.08          | ~ (v1_relat_1 @ X12))),
% 0.89/1.08      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.89/1.08  thf('52', plain,
% 0.89/1.08      ((~ (v1_relat_1 @ sk_D_3)
% 0.89/1.08        | (r2_hidden @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_C_1))),
% 0.89/1.08      inference('sup-', [status(thm)], ['50', '51'])).
% 0.89/1.08  thf('53', plain, ((v1_relat_1 @ sk_D_3)),
% 0.89/1.08      inference('demod', [status(thm)], ['9', '10'])).
% 0.89/1.08  thf('54', plain, ((r2_hidden @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E) @ sk_C_1)),
% 0.89/1.08      inference('demod', [status(thm)], ['52', '53'])).
% 0.89/1.08  thf('55', plain,
% 0.89/1.08      ((((sk_B) = (k1_xboole_0))
% 0.89/1.08        | ((sk_E) != (k1_funct_1 @ sk_D_3 @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E))))),
% 0.89/1.08      inference('demod', [status(thm)], ['49', '54'])).
% 0.89/1.08  thf('56', plain,
% 0.89/1.08      (((sk_E) = (k1_funct_1 @ sk_D_3 @ (sk_D @ sk_D_3 @ sk_C_1 @ sk_E)))),
% 0.89/1.08      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.89/1.08  thf('57', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_E) != (sk_E)))),
% 0.89/1.08      inference('demod', [status(thm)], ['55', '56'])).
% 0.89/1.08  thf('58', plain, (((sk_B) = (k1_xboole_0))),
% 0.89/1.08      inference('simplify', [status(thm)], ['57'])).
% 0.89/1.08  thf(t113_zfmisc_1, axiom,
% 0.89/1.08    (![A:$i,B:$i]:
% 0.89/1.08     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.89/1.08       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.89/1.08  thf('59', plain,
% 0.89/1.08      (![X1 : $i, X2 : $i]:
% 0.89/1.08         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.89/1.08      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.89/1.08  thf('60', plain,
% 0.89/1.08      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.89/1.08      inference('simplify', [status(thm)], ['59'])).
% 0.89/1.08  thf('61', plain, ((m1_subset_1 @ sk_D_3 @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.89/1.08      inference('demod', [status(thm)], ['32', '58', '60'])).
% 0.89/1.08  thf('62', plain,
% 0.89/1.08      (![X1 : $i, X2 : $i]:
% 0.89/1.08         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 0.89/1.08      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.89/1.08  thf('63', plain,
% 0.89/1.08      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 0.89/1.08      inference('simplify', [status(thm)], ['62'])).
% 0.89/1.08  thf(cc2_relset_1, axiom,
% 0.89/1.08    (![A:$i,B:$i,C:$i]:
% 0.89/1.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.08       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.89/1.08  thf('64', plain,
% 0.89/1.08      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.89/1.08         ((v5_relat_1 @ X28 @ X30)
% 0.89/1.08          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.89/1.08      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.89/1.08  thf('65', plain,
% 0.89/1.08      (![X0 : $i, X1 : $i]:
% 0.89/1.08         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.89/1.08          | (v5_relat_1 @ X1 @ X0))),
% 0.89/1.08      inference('sup-', [status(thm)], ['63', '64'])).
% 0.89/1.08  thf('66', plain, (![X0 : $i]: (v5_relat_1 @ sk_D_3 @ X0)),
% 0.89/1.08      inference('sup-', [status(thm)], ['61', '65'])).
% 0.89/1.08  thf(d19_relat_1, axiom,
% 0.89/1.08    (![A:$i,B:$i]:
% 0.89/1.08     ( ( v1_relat_1 @ B ) =>
% 0.89/1.08       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.89/1.08  thf('67', plain,
% 0.89/1.08      (![X5 : $i, X6 : $i]:
% 0.89/1.08         (~ (v5_relat_1 @ X5 @ X6)
% 0.89/1.08          | (r1_tarski @ (k2_relat_1 @ X5) @ X6)
% 0.89/1.08          | ~ (v1_relat_1 @ X5))),
% 0.89/1.08      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.89/1.08  thf('68', plain,
% 0.89/1.08      (![X0 : $i]:
% 0.89/1.08         (~ (v1_relat_1 @ sk_D_3) | (r1_tarski @ (k2_relat_1 @ sk_D_3) @ X0))),
% 0.89/1.08      inference('sup-', [status(thm)], ['66', '67'])).
% 0.89/1.08  thf('69', plain, ((v1_relat_1 @ sk_D_3)),
% 0.89/1.08      inference('demod', [status(thm)], ['9', '10'])).
% 0.89/1.08  thf('70', plain, (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ sk_D_3) @ X0)),
% 0.89/1.08      inference('demod', [status(thm)], ['68', '69'])).
% 0.89/1.08  thf('71', plain, ($false), inference('demod', [status(thm)], ['31', '70'])).
% 0.89/1.08  
% 0.89/1.08  % SZS output end Refutation
% 0.89/1.08  
% 0.89/1.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
