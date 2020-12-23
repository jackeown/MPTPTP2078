%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HWWtUznk34

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:37 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  139 (1410 expanded)
%              Number of leaves         :   42 ( 425 expanded)
%              Depth                    :   21
%              Number of atoms          :  964 (21238 expanded)
%              Number of equality atoms :   66 ( 929 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

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
    r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ sk_C ) ),
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
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_2 ) @ ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('8',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('9',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    r2_hidden @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_2 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['6','9'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('11',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ~ ( r1_tarski @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('12',plain,(
    ~ ( r1_tarski @ ( k1_relat_1 @ sk_D_2 ) @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ sk_B ),
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

thf('14',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ( X40
        = ( k1_relset_1 @ X40 @ X41 @ X42 ) )
      | ~ ( zip_tseitin_2 @ X42 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('15',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('17',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X33 @ X31 )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('18',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('20',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_1 @ X38 @ X39 )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('21',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('22',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( zip_tseitin_1 @ X43 @ X44 )
      | ( zip_tseitin_2 @ X45 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('23',plain,
    ( ( zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('26',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ sk_C ) ),
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

thf('28',plain,(
    ! [X19: $i,X20: $i,X22: $i,X23: $i] :
      ( ( X22
       != ( k9_relat_1 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X23 @ X19 @ X20 ) @ X23 @ X19 @ X20 )
      | ~ ( r2_hidden @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('29',plain,(
    ! [X19: $i,X20: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( r2_hidden @ X23 @ ( k9_relat_1 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X23 @ X19 @ X20 ) @ X23 @ X19 @ X20 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,
    ( ( zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_E_2 @ sk_C @ sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('33',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_E_2 @ sk_C @ sk_D_2 ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X14 @ ( k1_relat_1 @ X13 ) )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('35',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['26','35'])).

thf('37',plain,(
    ! [X46: $i] :
      ( ~ ( r2_hidden @ X46 @ sk_A )
      | ~ ( r2_hidden @ X46 @ sk_C )
      | ( sk_E_2
       != ( k1_funct_1 @ sk_D_2 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E_2
     != ( k1_funct_1 @ sk_D_2 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) ) )
    | ~ ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_E_2 @ sk_C @ sk_D_2 ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('40',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X15
        = ( k1_funct_1 @ X13 @ X14 ) )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('41',plain,
    ( sk_E_2
    = ( k1_funct_1 @ sk_D_2 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_E_2 @ sk_C @ sk_D_2 ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('43',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X14 @ X16 )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('44',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_C ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E_2 != sk_E_2 ) ),
    inference(demod,[status(thm)],['38','41','44'])).

thf('46',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['19','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['45'])).

thf('50',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( X43 != k1_xboole_0 )
      | ( X44 = k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ~ ( v1_funct_2 @ X45 @ X44 @ X43 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('52',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ k1_xboole_0 ) ) )
      | ~ ( v1_funct_2 @ X45 @ X44 @ k1_xboole_0 )
      | ( X45 = k1_xboole_0 )
      | ( X44 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_2 = k1_xboole_0 )
    | ~ ( v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['45'])).

thf('56',plain,(
    v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0 ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_D_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['53','56'])).

thf('58',plain,(
    r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_2 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('59',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k9_relat_1 @ X12 @ X10 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X12 @ X10 @ X11 ) @ X11 ) @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('60',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_2 ) @ sk_E_2 ) @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['7','8'])).

thf('62',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_2 ) @ sk_E_2 ) @ sk_D_2 ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ~ ( r1_tarski @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('64',plain,(
    ~ ( r1_tarski @ sk_D_2 @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_2 ) @ sk_E_2 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_2 ) @ sk_E_2 ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['57','64'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('66',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('67',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['65','66'])).

thf('69',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ k1_xboole_0 )
    | ( k1_xboole_0
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['47','67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('71',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['65','66'])).

thf('72',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( zip_tseitin_1 @ X43 @ X44 )
      | ( zip_tseitin_2 @ X45 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('74',plain,
    ( ( zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ k1_xboole_0 )
    | ~ ( zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_1 @ X38 @ X39 )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('76',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_1 @ X38 @ X39 )
      | ( X39 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('77',plain,(
    ! [X38: $i] :
      ( zip_tseitin_1 @ X38 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['75','77'])).

thf('79',plain,
    ( ( zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_A @ X0 )
      | ( zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['15','18'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_1 @ sk_A @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_1 @ X38 @ X39 )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('84',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('85',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,(
    ~ ( r1_tarski @ ( k1_relat_1 @ sk_D_2 ) @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('87',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ ( k1_relat_1 @ sk_D_2 ) @ X0 ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ sk_A @ X0 )
      | ( zip_tseitin_1 @ sk_A @ X1 ) ) ),
    inference('sup+',[status(thm)],['82','87'])).

thf('89',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ sk_A @ X0 ) ),
    inference(condensation,[status(thm)],['88'])).

thf('90',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['65','66'])).

thf('91',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ k1_xboole_0 @ X0 ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,(
    zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['74','91'])).

thf('93',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['69','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('95',plain,(
    $false ),
    inference(demod,[status(thm)],['12','93','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.HWWtUznk34
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:53:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.60/0.81  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.60/0.81  % Solved by: fo/fo7.sh
% 0.60/0.81  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.81  % done 305 iterations in 0.357s
% 0.60/0.81  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.60/0.81  % SZS output start Refutation
% 0.60/0.81  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.81  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.60/0.81  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.60/0.81  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.60/0.81  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.81  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.60/0.81  thf(sk_C_type, type, sk_C: $i).
% 0.60/0.81  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.60/0.81  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.60/0.81  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.60/0.81  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.81  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.60/0.81  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.60/0.81  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.60/0.81  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.81  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.60/0.81  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.81  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.81  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.60/0.81  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.60/0.81  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.60/0.81  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.60/0.81  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.60/0.81  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.81  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.60/0.81  thf(t115_funct_2, conjecture,
% 0.60/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.81     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.60/0.81         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.60/0.81       ( ![E:$i]:
% 0.60/0.81         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.60/0.81              ( ![F:$i]:
% 0.60/0.81                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.60/0.81                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.60/0.81  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.81    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.81        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.60/0.81            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.60/0.81          ( ![E:$i]:
% 0.60/0.81            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.60/0.81                 ( ![F:$i]:
% 0.60/0.81                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.60/0.81                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 0.60/0.81    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 0.60/0.81  thf('0', plain,
% 0.60/0.81      ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C))),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.81  thf('1', plain,
% 0.60/0.81      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.81  thf(redefinition_k7_relset_1, axiom,
% 0.60/0.81    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.81       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.60/0.81  thf('2', plain,
% 0.60/0.81      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.60/0.81         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.60/0.81          | ((k7_relset_1 @ X35 @ X36 @ X34 @ X37) = (k9_relat_1 @ X34 @ X37)))),
% 0.60/0.81      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.60/0.81  thf('3', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0)
% 0.60/0.81           = (k9_relat_1 @ sk_D_2 @ X0))),
% 0.60/0.81      inference('sup-', [status(thm)], ['1', '2'])).
% 0.60/0.81  thf('4', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.60/0.81      inference('demod', [status(thm)], ['0', '3'])).
% 0.60/0.81  thf(t143_relat_1, axiom,
% 0.60/0.81    (![A:$i,B:$i,C:$i]:
% 0.60/0.81     ( ( v1_relat_1 @ C ) =>
% 0.60/0.81       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.60/0.81         ( ?[D:$i]:
% 0.60/0.81           ( ( r2_hidden @ D @ B ) & 
% 0.60/0.81             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.60/0.81             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.60/0.81  thf('5', plain,
% 0.60/0.81      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.60/0.81         (~ (r2_hidden @ X11 @ (k9_relat_1 @ X12 @ X10))
% 0.60/0.81          | (r2_hidden @ (sk_D @ X12 @ X10 @ X11) @ (k1_relat_1 @ X12))
% 0.60/0.81          | ~ (v1_relat_1 @ X12))),
% 0.60/0.81      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.60/0.81  thf('6', plain,
% 0.60/0.81      ((~ (v1_relat_1 @ sk_D_2)
% 0.60/0.81        | (r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_2) @ (k1_relat_1 @ sk_D_2)))),
% 0.60/0.81      inference('sup-', [status(thm)], ['4', '5'])).
% 0.60/0.81  thf('7', plain,
% 0.60/0.81      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.81  thf(cc1_relset_1, axiom,
% 0.60/0.81    (![A:$i,B:$i,C:$i]:
% 0.60/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.81       ( v1_relat_1 @ C ) ))).
% 0.60/0.81  thf('8', plain,
% 0.60/0.81      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.60/0.81         ((v1_relat_1 @ X28)
% 0.60/0.81          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.60/0.81      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.60/0.81  thf('9', plain, ((v1_relat_1 @ sk_D_2)),
% 0.60/0.81      inference('sup-', [status(thm)], ['7', '8'])).
% 0.60/0.81  thf('10', plain,
% 0.60/0.81      ((r2_hidden @ (sk_D @ sk_D_2 @ sk_C @ sk_E_2) @ (k1_relat_1 @ sk_D_2))),
% 0.60/0.81      inference('demod', [status(thm)], ['6', '9'])).
% 0.60/0.81  thf(t7_ordinal1, axiom,
% 0.60/0.81    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.60/0.81  thf('11', plain,
% 0.60/0.81      (![X26 : $i, X27 : $i]:
% 0.60/0.81         (~ (r2_hidden @ X26 @ X27) | ~ (r1_tarski @ X27 @ X26))),
% 0.60/0.81      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.60/0.81  thf('12', plain,
% 0.60/0.81      (~ (r1_tarski @ (k1_relat_1 @ sk_D_2) @ (sk_D @ sk_D_2 @ sk_C @ sk_E_2))),
% 0.60/0.81      inference('sup-', [status(thm)], ['10', '11'])).
% 0.60/0.81  thf('13', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B)),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.81  thf(d1_funct_2, axiom,
% 0.60/0.81    (![A:$i,B:$i,C:$i]:
% 0.60/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.81       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.60/0.81           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.60/0.81             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.60/0.81         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.60/0.81           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.60/0.81             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.60/0.81  thf(zf_stmt_1, axiom,
% 0.60/0.81    (![C:$i,B:$i,A:$i]:
% 0.60/0.81     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.60/0.81       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.60/0.81  thf('14', plain,
% 0.60/0.81      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.60/0.81         (~ (v1_funct_2 @ X42 @ X40 @ X41)
% 0.60/0.81          | ((X40) = (k1_relset_1 @ X40 @ X41 @ X42))
% 0.60/0.81          | ~ (zip_tseitin_2 @ X42 @ X41 @ X40))),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.60/0.81  thf('15', plain,
% 0.60/0.81      ((~ (zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A)
% 0.60/0.81        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_2)))),
% 0.60/0.81      inference('sup-', [status(thm)], ['13', '14'])).
% 0.60/0.81  thf('16', plain,
% 0.60/0.81      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.81  thf(redefinition_k1_relset_1, axiom,
% 0.60/0.81    (![A:$i,B:$i,C:$i]:
% 0.60/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.81       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.60/0.81  thf('17', plain,
% 0.60/0.81      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.60/0.81         (((k1_relset_1 @ X32 @ X33 @ X31) = (k1_relat_1 @ X31))
% 0.60/0.81          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.60/0.81      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.60/0.81  thf('18', plain,
% 0.60/0.81      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 0.60/0.81      inference('sup-', [status(thm)], ['16', '17'])).
% 0.60/0.81  thf('19', plain,
% 0.60/0.81      ((~ (zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A)
% 0.60/0.81        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.60/0.81      inference('demod', [status(thm)], ['15', '18'])).
% 0.60/0.81  thf(zf_stmt_2, axiom,
% 0.60/0.81    (![B:$i,A:$i]:
% 0.60/0.81     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.60/0.81       ( zip_tseitin_1 @ B @ A ) ))).
% 0.60/0.81  thf('20', plain,
% 0.60/0.81      (![X38 : $i, X39 : $i]:
% 0.60/0.81         ((zip_tseitin_1 @ X38 @ X39) | ((X38) = (k1_xboole_0)))),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.60/0.81  thf('21', plain,
% 0.60/0.81      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.81  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.60/0.81  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $o).
% 0.60/0.81  thf(zf_stmt_5, axiom,
% 0.60/0.81    (![A:$i,B:$i,C:$i]:
% 0.60/0.81     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.81       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.60/0.81         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.60/0.81           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.60/0.81             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.60/0.81  thf('22', plain,
% 0.60/0.81      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.60/0.81         (~ (zip_tseitin_1 @ X43 @ X44)
% 0.60/0.81          | (zip_tseitin_2 @ X45 @ X43 @ X44)
% 0.60/0.81          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43))))),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.60/0.81  thf('23', plain,
% 0.60/0.81      (((zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A)
% 0.60/0.81        | ~ (zip_tseitin_1 @ sk_B @ sk_A))),
% 0.60/0.81      inference('sup-', [status(thm)], ['21', '22'])).
% 0.60/0.81  thf('24', plain,
% 0.60/0.81      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A))),
% 0.60/0.81      inference('sup-', [status(thm)], ['20', '23'])).
% 0.60/0.81  thf('25', plain,
% 0.60/0.81      ((~ (zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A)
% 0.60/0.81        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.60/0.81      inference('demod', [status(thm)], ['15', '18'])).
% 0.60/0.81  thf('26', plain,
% 0.60/0.81      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.60/0.81      inference('sup-', [status(thm)], ['24', '25'])).
% 0.60/0.81  thf('27', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.60/0.81      inference('demod', [status(thm)], ['0', '3'])).
% 0.60/0.81  thf(d12_funct_1, axiom,
% 0.60/0.81    (![A:$i]:
% 0.60/0.81     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.60/0.81       ( ![B:$i,C:$i]:
% 0.60/0.81         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.60/0.81           ( ![D:$i]:
% 0.60/0.81             ( ( r2_hidden @ D @ C ) <=>
% 0.60/0.81               ( ?[E:$i]:
% 0.60/0.81                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 0.60/0.81                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 0.60/0.81  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.60/0.81  thf(zf_stmt_7, axiom,
% 0.60/0.81    (![E:$i,D:$i,B:$i,A:$i]:
% 0.60/0.81     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.60/0.81       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 0.60/0.81         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 0.60/0.81  thf(zf_stmt_8, axiom,
% 0.60/0.81    (![A:$i]:
% 0.60/0.81     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.60/0.81       ( ![B:$i,C:$i]:
% 0.60/0.81         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.60/0.81           ( ![D:$i]:
% 0.60/0.81             ( ( r2_hidden @ D @ C ) <=>
% 0.60/0.81               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 0.60/0.81  thf('28', plain,
% 0.60/0.81      (![X19 : $i, X20 : $i, X22 : $i, X23 : $i]:
% 0.60/0.81         (((X22) != (k9_relat_1 @ X20 @ X19))
% 0.60/0.81          | (zip_tseitin_0 @ (sk_E_1 @ X23 @ X19 @ X20) @ X23 @ X19 @ X20)
% 0.60/0.81          | ~ (r2_hidden @ X23 @ X22)
% 0.60/0.81          | ~ (v1_funct_1 @ X20)
% 0.60/0.81          | ~ (v1_relat_1 @ X20))),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.60/0.81  thf('29', plain,
% 0.60/0.81      (![X19 : $i, X20 : $i, X23 : $i]:
% 0.60/0.81         (~ (v1_relat_1 @ X20)
% 0.60/0.81          | ~ (v1_funct_1 @ X20)
% 0.60/0.81          | ~ (r2_hidden @ X23 @ (k9_relat_1 @ X20 @ X19))
% 0.60/0.81          | (zip_tseitin_0 @ (sk_E_1 @ X23 @ X19 @ X20) @ X23 @ X19 @ X20))),
% 0.60/0.81      inference('simplify', [status(thm)], ['28'])).
% 0.60/0.81  thf('30', plain,
% 0.60/0.81      (((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_E_2 @ sk_C @ 
% 0.60/0.81         sk_D_2)
% 0.60/0.81        | ~ (v1_funct_1 @ sk_D_2)
% 0.60/0.81        | ~ (v1_relat_1 @ sk_D_2))),
% 0.60/0.81      inference('sup-', [status(thm)], ['27', '29'])).
% 0.60/0.81  thf('31', plain, ((v1_funct_1 @ sk_D_2)),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.81  thf('32', plain, ((v1_relat_1 @ sk_D_2)),
% 0.60/0.81      inference('sup-', [status(thm)], ['7', '8'])).
% 0.60/0.81  thf('33', plain,
% 0.60/0.81      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_E_2 @ sk_C @ 
% 0.60/0.81        sk_D_2)),
% 0.60/0.81      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.60/0.81  thf('34', plain,
% 0.60/0.81      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.60/0.81         ((r2_hidden @ X14 @ (k1_relat_1 @ X13))
% 0.60/0.81          | ~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X13))),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.60/0.81  thf('35', plain,
% 0.60/0.81      ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ (k1_relat_1 @ sk_D_2))),
% 0.60/0.81      inference('sup-', [status(thm)], ['33', '34'])).
% 0.60/0.81  thf('36', plain,
% 0.60/0.81      (((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_A)
% 0.60/0.81        | ((sk_B) = (k1_xboole_0)))),
% 0.60/0.81      inference('sup+', [status(thm)], ['26', '35'])).
% 0.60/0.81  thf('37', plain,
% 0.60/0.81      (![X46 : $i]:
% 0.60/0.81         (~ (r2_hidden @ X46 @ sk_A)
% 0.60/0.81          | ~ (r2_hidden @ X46 @ sk_C)
% 0.60/0.81          | ((sk_E_2) != (k1_funct_1 @ sk_D_2 @ X46)))),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.81  thf('38', plain,
% 0.60/0.81      ((((sk_B) = (k1_xboole_0))
% 0.60/0.81        | ((sk_E_2)
% 0.60/0.81            != (k1_funct_1 @ sk_D_2 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2)))
% 0.60/0.81        | ~ (r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_C))),
% 0.60/0.81      inference('sup-', [status(thm)], ['36', '37'])).
% 0.60/0.81  thf('39', plain,
% 0.60/0.81      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_E_2 @ sk_C @ 
% 0.60/0.81        sk_D_2)),
% 0.60/0.81      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.60/0.81  thf('40', plain,
% 0.60/0.81      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.60/0.81         (((X15) = (k1_funct_1 @ X13 @ X14))
% 0.60/0.81          | ~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X13))),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.60/0.81  thf('41', plain,
% 0.60/0.81      (((sk_E_2) = (k1_funct_1 @ sk_D_2 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2)))),
% 0.60/0.81      inference('sup-', [status(thm)], ['39', '40'])).
% 0.60/0.81  thf('42', plain,
% 0.60/0.81      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_E_2 @ sk_C @ 
% 0.60/0.81        sk_D_2)),
% 0.60/0.81      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.60/0.81  thf('43', plain,
% 0.60/0.81      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.60/0.81         ((r2_hidden @ X14 @ X16) | ~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X13))),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.60/0.81  thf('44', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_C)),
% 0.60/0.81      inference('sup-', [status(thm)], ['42', '43'])).
% 0.60/0.81  thf('45', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_E_2) != (sk_E_2)))),
% 0.60/0.81      inference('demod', [status(thm)], ['38', '41', '44'])).
% 0.60/0.81  thf('46', plain, (((sk_B) = (k1_xboole_0))),
% 0.60/0.81      inference('simplify', [status(thm)], ['45'])).
% 0.60/0.81  thf('47', plain,
% 0.60/0.81      ((~ (zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ sk_A)
% 0.60/0.81        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.60/0.81      inference('demod', [status(thm)], ['19', '46'])).
% 0.60/0.81  thf('48', plain,
% 0.60/0.81      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.81  thf('49', plain, (((sk_B) = (k1_xboole_0))),
% 0.60/0.81      inference('simplify', [status(thm)], ['45'])).
% 0.60/0.81  thf('50', plain,
% 0.60/0.81      ((m1_subset_1 @ sk_D_2 @ 
% 0.60/0.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.60/0.81      inference('demod', [status(thm)], ['48', '49'])).
% 0.60/0.81  thf('51', plain,
% 0.60/0.81      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.60/0.81         (((X43) != (k1_xboole_0))
% 0.60/0.81          | ((X44) = (k1_xboole_0))
% 0.60/0.81          | ((X45) = (k1_xboole_0))
% 0.60/0.81          | ~ (v1_funct_2 @ X45 @ X44 @ X43)
% 0.60/0.81          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43))))),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.60/0.81  thf('52', plain,
% 0.60/0.81      (![X44 : $i, X45 : $i]:
% 0.60/0.81         (~ (m1_subset_1 @ X45 @ 
% 0.60/0.81             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ k1_xboole_0)))
% 0.60/0.81          | ~ (v1_funct_2 @ X45 @ X44 @ k1_xboole_0)
% 0.60/0.81          | ((X45) = (k1_xboole_0))
% 0.60/0.81          | ((X44) = (k1_xboole_0)))),
% 0.60/0.81      inference('simplify', [status(thm)], ['51'])).
% 0.60/0.81  thf('53', plain,
% 0.60/0.81      ((((sk_A) = (k1_xboole_0))
% 0.60/0.81        | ((sk_D_2) = (k1_xboole_0))
% 0.60/0.81        | ~ (v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0))),
% 0.60/0.81      inference('sup-', [status(thm)], ['50', '52'])).
% 0.60/0.81  thf('54', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B)),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.81  thf('55', plain, (((sk_B) = (k1_xboole_0))),
% 0.60/0.81      inference('simplify', [status(thm)], ['45'])).
% 0.60/0.81  thf('56', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ k1_xboole_0)),
% 0.60/0.81      inference('demod', [status(thm)], ['54', '55'])).
% 0.60/0.81  thf('57', plain, ((((sk_A) = (k1_xboole_0)) | ((sk_D_2) = (k1_xboole_0)))),
% 0.60/0.81      inference('demod', [status(thm)], ['53', '56'])).
% 0.60/0.81  thf('58', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.60/0.81      inference('demod', [status(thm)], ['0', '3'])).
% 0.60/0.81  thf('59', plain,
% 0.60/0.81      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.60/0.81         (~ (r2_hidden @ X11 @ (k9_relat_1 @ X12 @ X10))
% 0.60/0.81          | (r2_hidden @ (k4_tarski @ (sk_D @ X12 @ X10 @ X11) @ X11) @ X12)
% 0.60/0.81          | ~ (v1_relat_1 @ X12))),
% 0.60/0.81      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.60/0.81  thf('60', plain,
% 0.60/0.81      ((~ (v1_relat_1 @ sk_D_2)
% 0.60/0.81        | (r2_hidden @ 
% 0.60/0.81           (k4_tarski @ (sk_D @ sk_D_2 @ sk_C @ sk_E_2) @ sk_E_2) @ sk_D_2))),
% 0.60/0.81      inference('sup-', [status(thm)], ['58', '59'])).
% 0.60/0.81  thf('61', plain, ((v1_relat_1 @ sk_D_2)),
% 0.60/0.81      inference('sup-', [status(thm)], ['7', '8'])).
% 0.60/0.81  thf('62', plain,
% 0.60/0.81      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_2 @ sk_C @ sk_E_2) @ sk_E_2) @ 
% 0.60/0.81        sk_D_2)),
% 0.60/0.81      inference('demod', [status(thm)], ['60', '61'])).
% 0.60/0.81  thf('63', plain,
% 0.60/0.81      (![X26 : $i, X27 : $i]:
% 0.60/0.81         (~ (r2_hidden @ X26 @ X27) | ~ (r1_tarski @ X27 @ X26))),
% 0.60/0.81      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.60/0.81  thf('64', plain,
% 0.60/0.81      (~ (r1_tarski @ sk_D_2 @ 
% 0.60/0.81          (k4_tarski @ (sk_D @ sk_D_2 @ sk_C @ sk_E_2) @ sk_E_2))),
% 0.60/0.81      inference('sup-', [status(thm)], ['62', '63'])).
% 0.60/0.81  thf('65', plain,
% 0.60/0.81      ((~ (r1_tarski @ k1_xboole_0 @ 
% 0.60/0.81           (k4_tarski @ (sk_D @ sk_D_2 @ sk_C @ sk_E_2) @ sk_E_2))
% 0.60/0.81        | ((sk_A) = (k1_xboole_0)))),
% 0.60/0.81      inference('sup-', [status(thm)], ['57', '64'])).
% 0.60/0.81  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.60/0.81  thf('66', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.60/0.81      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.60/0.81  thf('67', plain, (((sk_A) = (k1_xboole_0))),
% 0.60/0.81      inference('demod', [status(thm)], ['65', '66'])).
% 0.60/0.81  thf('68', plain, (((sk_A) = (k1_xboole_0))),
% 0.60/0.81      inference('demod', [status(thm)], ['65', '66'])).
% 0.60/0.81  thf('69', plain,
% 0.60/0.81      ((~ (zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ k1_xboole_0)
% 0.60/0.81        | ((k1_xboole_0) = (k1_relat_1 @ sk_D_2)))),
% 0.60/0.81      inference('demod', [status(thm)], ['47', '67', '68'])).
% 0.60/0.81  thf('70', plain,
% 0.60/0.81      ((m1_subset_1 @ sk_D_2 @ 
% 0.60/0.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.60/0.81      inference('demod', [status(thm)], ['48', '49'])).
% 0.60/0.81  thf('71', plain, (((sk_A) = (k1_xboole_0))),
% 0.60/0.81      inference('demod', [status(thm)], ['65', '66'])).
% 0.60/0.81  thf('72', plain,
% 0.60/0.81      ((m1_subset_1 @ sk_D_2 @ 
% 0.60/0.81        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))),
% 0.60/0.81      inference('demod', [status(thm)], ['70', '71'])).
% 0.60/0.81  thf('73', plain,
% 0.60/0.81      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.60/0.81         (~ (zip_tseitin_1 @ X43 @ X44)
% 0.60/0.81          | (zip_tseitin_2 @ X45 @ X43 @ X44)
% 0.60/0.81          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43))))),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.60/0.81  thf('74', plain,
% 0.60/0.81      (((zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ k1_xboole_0)
% 0.60/0.81        | ~ (zip_tseitin_1 @ k1_xboole_0 @ k1_xboole_0))),
% 0.60/0.81      inference('sup-', [status(thm)], ['72', '73'])).
% 0.60/0.81  thf('75', plain,
% 0.60/0.81      (![X38 : $i, X39 : $i]:
% 0.60/0.81         ((zip_tseitin_1 @ X38 @ X39) | ((X38) = (k1_xboole_0)))),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.60/0.81  thf('76', plain,
% 0.60/0.81      (![X38 : $i, X39 : $i]:
% 0.60/0.81         ((zip_tseitin_1 @ X38 @ X39) | ((X39) != (k1_xboole_0)))),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.60/0.81  thf('77', plain, (![X38 : $i]: (zip_tseitin_1 @ X38 @ k1_xboole_0)),
% 0.60/0.81      inference('simplify', [status(thm)], ['76'])).
% 0.60/0.81  thf('78', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.81         ((zip_tseitin_1 @ X1 @ X0) | (zip_tseitin_1 @ X0 @ X2))),
% 0.60/0.81      inference('sup+', [status(thm)], ['75', '77'])).
% 0.60/0.81  thf('79', plain,
% 0.60/0.81      (((zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A)
% 0.60/0.81        | ~ (zip_tseitin_1 @ sk_B @ sk_A))),
% 0.60/0.81      inference('sup-', [status(thm)], ['21', '22'])).
% 0.60/0.81  thf('80', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         ((zip_tseitin_1 @ sk_A @ X0) | (zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A))),
% 0.60/0.81      inference('sup-', [status(thm)], ['78', '79'])).
% 0.60/0.81  thf('81', plain,
% 0.60/0.81      ((~ (zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A)
% 0.60/0.81        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.60/0.81      inference('demod', [status(thm)], ['15', '18'])).
% 0.60/0.81  thf('82', plain,
% 0.60/0.81      (![X0 : $i]:
% 0.60/0.81         ((zip_tseitin_1 @ sk_A @ X0) | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.60/0.81      inference('sup-', [status(thm)], ['80', '81'])).
% 0.60/0.81  thf('83', plain,
% 0.60/0.81      (![X38 : $i, X39 : $i]:
% 0.60/0.81         ((zip_tseitin_1 @ X38 @ X39) | ((X38) = (k1_xboole_0)))),
% 0.60/0.81      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.60/0.81  thf('84', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.60/0.81      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.60/0.81  thf('85', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.81         ((r1_tarski @ X0 @ X1) | (zip_tseitin_1 @ X0 @ X2))),
% 0.60/0.81      inference('sup+', [status(thm)], ['83', '84'])).
% 0.60/0.81  thf('86', plain,
% 0.60/0.81      (~ (r1_tarski @ (k1_relat_1 @ sk_D_2) @ (sk_D @ sk_D_2 @ sk_C @ sk_E_2))),
% 0.60/0.81      inference('sup-', [status(thm)], ['10', '11'])).
% 0.60/0.81  thf('87', plain, (![X0 : $i]: (zip_tseitin_1 @ (k1_relat_1 @ sk_D_2) @ X0)),
% 0.60/0.81      inference('sup-', [status(thm)], ['85', '86'])).
% 0.60/0.81  thf('88', plain,
% 0.60/0.81      (![X0 : $i, X1 : $i]:
% 0.60/0.81         ((zip_tseitin_1 @ sk_A @ X0) | (zip_tseitin_1 @ sk_A @ X1))),
% 0.60/0.81      inference('sup+', [status(thm)], ['82', '87'])).
% 0.60/0.81  thf('89', plain, (![X0 : $i]: (zip_tseitin_1 @ sk_A @ X0)),
% 0.60/0.81      inference('condensation', [status(thm)], ['88'])).
% 0.60/0.81  thf('90', plain, (((sk_A) = (k1_xboole_0))),
% 0.60/0.81      inference('demod', [status(thm)], ['65', '66'])).
% 0.60/0.81  thf('91', plain, (![X0 : $i]: (zip_tseitin_1 @ k1_xboole_0 @ X0)),
% 0.60/0.81      inference('demod', [status(thm)], ['89', '90'])).
% 0.60/0.81  thf('92', plain, ((zip_tseitin_2 @ sk_D_2 @ k1_xboole_0 @ k1_xboole_0)),
% 0.60/0.81      inference('demod', [status(thm)], ['74', '91'])).
% 0.60/0.81  thf('93', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_D_2))),
% 0.60/0.81      inference('demod', [status(thm)], ['69', '92'])).
% 0.60/0.81  thf('94', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.60/0.81      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.60/0.81  thf('95', plain, ($false),
% 0.60/0.81      inference('demod', [status(thm)], ['12', '93', '94'])).
% 0.60/0.81  
% 0.60/0.81  % SZS output end Refutation
% 0.60/0.81  
% 0.60/0.82  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
