%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hNS0kP1VVY

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:37 EST 2020

% Result     : Theorem 0.58s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 413 expanded)
%              Number of leaves         :   44 ( 140 expanded)
%              Depth                    :   14
%              Number of atoms          :  776 (5976 expanded)
%              Number of equality atoms :   44 ( 251 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

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
    r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ),
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
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( ( k7_relset_1 @ X35 @ X36 @ X34 @ X37 )
        = ( k9_relat_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_E_2 @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X28 @ X29 @ X27 @ X30 ) @ ( k1_zfmisc_1 @ X29 ) ) ) ),
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
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('12',plain,(
    ! [X38: $i,X39: $i] :
      ( ( zip_tseitin_1 @ X38 @ X39 )
      | ( X38 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('13',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

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

thf('14',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ~ ( zip_tseitin_1 @ X43 @ X44 )
      | ( zip_tseitin_2 @ X45 @ X43 @ X44 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('15',plain,
    ( ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_2 @ X42 @ X40 @ X41 )
      | ( X40
        = ( k1_relset_1 @ X40 @ X41 @ X42 ) )
      | ~ ( zip_tseitin_2 @ X42 @ X41 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('19',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A )
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X33 @ X31 )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['16','23'])).

thf('25',plain,(
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

thf('26',plain,(
    ! [X15: $i,X16: $i,X18: $i,X19: $i] :
      ( ( X18
       != ( k9_relat_1 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X19 @ X15 @ X16 ) @ X19 @ X15 @ X16 )
      | ~ ( r2_hidden @ X19 @ X18 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('27',plain,(
    ! [X15: $i,X16: $i,X19: $i] :
      ( ~ ( v1_relat_1 @ X16 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( r2_hidden @ X19 @ ( k9_relat_1 @ X16 @ X15 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X19 @ X15 @ X16 ) @ X19 @ X15 @ X16 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,
    ( ( zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 @ sk_C @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('31',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('32',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 @ sk_C @ sk_D_1 ),
    inference(demod,[status(thm)],['28','29','32'])).

thf('34',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X10 @ ( k1_relat_1 @ X9 ) )
      | ~ ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('35',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','35'])).

thf('37',plain,(
    ! [X46: $i] :
      ( ~ ( r2_hidden @ X46 @ sk_A )
      | ~ ( r2_hidden @ X46 @ sk_C )
      | ( sk_E_2
       != ( k1_funct_1 @ sk_D_1 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E_2
     != ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) ) )
    | ~ ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 @ sk_C @ sk_D_1 ),
    inference(demod,[status(thm)],['28','29','32'])).

thf('40',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( X11
        = ( k1_funct_1 @ X9 @ X10 ) )
      | ~ ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('41',plain,
    ( sk_E_2
    = ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 @ sk_C @ sk_D_1 ),
    inference(demod,[status(thm)],['28','29','32'])).

thf('43',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X10 @ X12 )
      | ~ ( zip_tseitin_0 @ X10 @ X11 @ X12 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('44',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_C ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E_2 != sk_E_2 ) ),
    inference(demod,[status(thm)],['38','41','44'])).

thf('46',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k9_relat_1 @ sk_D_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','46'])).

thf('48',plain,(
    r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('50',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ sk_B )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_E_2 @ sk_B ),
    inference('sup-',[status(thm)],['48','51'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('53',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('54',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_E_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('55',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( r1_tarski @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('56',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( r1_tarski @ sk_B @ sk_E_2 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['45'])).

thf('58',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['45'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('59',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('60',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['56','57','58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['47','60'])).

thf('62',plain,(
    $false ),
    inference('sup-',[status(thm)],['4','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.hNS0kP1VVY
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:44:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.58/0.82  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.58/0.82  % Solved by: fo/fo7.sh
% 0.58/0.82  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.58/0.82  % done 286 iterations in 0.351s
% 0.58/0.82  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.58/0.82  % SZS output start Refutation
% 0.58/0.82  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.58/0.82  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.58/0.82  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.58/0.82  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.58/0.82  thf(sk_A_type, type, sk_A: $i).
% 0.58/0.82  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.58/0.82  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.58/0.82  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.58/0.82  thf(sk_C_type, type, sk_C: $i).
% 0.58/0.82  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.58/0.82  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.58/0.82  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.58/0.82  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.58/0.82  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.58/0.82  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.58/0.82  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.58/0.82  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.58/0.82  thf(sk_B_type, type, sk_B: $i).
% 0.58/0.82  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.58/0.82  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.58/0.82  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.58/0.82  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.58/0.82  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.58/0.82  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.58/0.82  thf(t115_funct_2, conjecture,
% 0.58/0.82    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.82     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.58/0.82         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.82       ( ![E:$i]:
% 0.58/0.82         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.58/0.82              ( ![F:$i]:
% 0.58/0.82                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.58/0.82                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.58/0.82  thf(zf_stmt_0, negated_conjecture,
% 0.58/0.82    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.82        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.58/0.82            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.58/0.82          ( ![E:$i]:
% 0.58/0.82            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.58/0.82                 ( ![F:$i]:
% 0.58/0.82                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.58/0.82                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 0.58/0.82    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 0.58/0.82  thf('0', plain,
% 0.58/0.82      ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('1', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf(redefinition_k7_relset_1, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.82       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.58/0.82  thf('2', plain,
% 0.58/0.82      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.58/0.82         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.58/0.82          | ((k7_relset_1 @ X35 @ X36 @ X34 @ X37) = (k9_relat_1 @ X34 @ X37)))),
% 0.58/0.82      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.58/0.82  thf('3', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.58/0.82           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['1', '2'])).
% 0.58/0.82  thf('4', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.58/0.82      inference('demod', [status(thm)], ['0', '3'])).
% 0.58/0.82  thf('5', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf(dt_k7_relset_1, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.82       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.58/0.82  thf('6', plain,
% 0.58/0.82      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.58/0.82         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.58/0.82          | (m1_subset_1 @ (k7_relset_1 @ X28 @ X29 @ X27 @ X30) @ 
% 0.58/0.82             (k1_zfmisc_1 @ X29)))),
% 0.58/0.82      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.58/0.82  thf('7', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0) @ 
% 0.58/0.82          (k1_zfmisc_1 @ sk_B))),
% 0.58/0.82      inference('sup-', [status(thm)], ['5', '6'])).
% 0.58/0.82  thf(t5_subset, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i]:
% 0.58/0.82     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.58/0.82          ( v1_xboole_0 @ C ) ) ))).
% 0.58/0.82  thf('8', plain,
% 0.58/0.82      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.58/0.82         (~ (r2_hidden @ X6 @ X7)
% 0.58/0.82          | ~ (v1_xboole_0 @ X8)
% 0.58/0.82          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.58/0.82      inference('cnf', [status(esa)], [t5_subset])).
% 0.58/0.82  thf('9', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         (~ (v1_xboole_0 @ sk_B)
% 0.58/0.82          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['7', '8'])).
% 0.58/0.82  thf('10', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.58/0.82           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.58/0.82      inference('sup-', [status(thm)], ['1', '2'])).
% 0.58/0.82  thf('11', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         (~ (v1_xboole_0 @ sk_B)
% 0.58/0.82          | ~ (r2_hidden @ X1 @ (k9_relat_1 @ sk_D_1 @ X0)))),
% 0.58/0.82      inference('demod', [status(thm)], ['9', '10'])).
% 0.58/0.82  thf(d1_funct_2, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i]:
% 0.58/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.82       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.58/0.82           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.58/0.82             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.58/0.82         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.58/0.82           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.58/0.82             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.58/0.82  thf(zf_stmt_1, axiom,
% 0.58/0.82    (![B:$i,A:$i]:
% 0.58/0.82     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.58/0.82       ( zip_tseitin_1 @ B @ A ) ))).
% 0.58/0.82  thf('12', plain,
% 0.58/0.82      (![X38 : $i, X39 : $i]:
% 0.58/0.82         ((zip_tseitin_1 @ X38 @ X39) | ((X38) = (k1_xboole_0)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.58/0.82  thf('13', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.58/0.82  thf(zf_stmt_3, axiom,
% 0.58/0.82    (![C:$i,B:$i,A:$i]:
% 0.58/0.82     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.58/0.82       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.58/0.82  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $o).
% 0.58/0.82  thf(zf_stmt_5, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i]:
% 0.58/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.82       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.58/0.82         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.58/0.82           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.58/0.82             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.58/0.82  thf('14', plain,
% 0.58/0.82      (![X43 : $i, X44 : $i, X45 : $i]:
% 0.58/0.82         (~ (zip_tseitin_1 @ X43 @ X44)
% 0.58/0.82          | (zip_tseitin_2 @ X45 @ X43 @ X44)
% 0.58/0.82          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43))))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.58/0.82  thf('15', plain,
% 0.58/0.82      (((zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)
% 0.58/0.82        | ~ (zip_tseitin_1 @ sk_B @ sk_A))),
% 0.58/0.82      inference('sup-', [status(thm)], ['13', '14'])).
% 0.58/0.82  thf('16', plain,
% 0.58/0.82      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A))),
% 0.58/0.82      inference('sup-', [status(thm)], ['12', '15'])).
% 0.58/0.82  thf('17', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('18', plain,
% 0.58/0.82      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.58/0.82         (~ (v1_funct_2 @ X42 @ X40 @ X41)
% 0.58/0.82          | ((X40) = (k1_relset_1 @ X40 @ X41 @ X42))
% 0.58/0.82          | ~ (zip_tseitin_2 @ X42 @ X41 @ X40))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.58/0.82  thf('19', plain,
% 0.58/0.82      ((~ (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)
% 0.58/0.82        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_1)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['17', '18'])).
% 0.58/0.82  thf('20', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf(redefinition_k1_relset_1, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i]:
% 0.58/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.82       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.58/0.82  thf('21', plain,
% 0.58/0.82      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.58/0.82         (((k1_relset_1 @ X32 @ X33 @ X31) = (k1_relat_1 @ X31))
% 0.58/0.82          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.58/0.82      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.58/0.82  thf('22', plain,
% 0.58/0.82      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.58/0.82      inference('sup-', [status(thm)], ['20', '21'])).
% 0.58/0.82  thf('23', plain,
% 0.58/0.82      ((~ (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)
% 0.58/0.82        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.58/0.82      inference('demod', [status(thm)], ['19', '22'])).
% 0.58/0.82  thf('24', plain,
% 0.58/0.82      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['16', '23'])).
% 0.58/0.82  thf('25', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.58/0.82      inference('demod', [status(thm)], ['0', '3'])).
% 0.58/0.82  thf(d12_funct_1, axiom,
% 0.58/0.82    (![A:$i]:
% 0.58/0.82     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.58/0.82       ( ![B:$i,C:$i]:
% 0.58/0.82         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.58/0.82           ( ![D:$i]:
% 0.58/0.82             ( ( r2_hidden @ D @ C ) <=>
% 0.58/0.82               ( ?[E:$i]:
% 0.58/0.82                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 0.58/0.82                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 0.58/0.82  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.58/0.82  thf(zf_stmt_7, axiom,
% 0.58/0.82    (![E:$i,D:$i,B:$i,A:$i]:
% 0.58/0.82     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.58/0.82       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 0.58/0.82         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 0.58/0.82  thf(zf_stmt_8, axiom,
% 0.58/0.82    (![A:$i]:
% 0.58/0.82     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.58/0.82       ( ![B:$i,C:$i]:
% 0.58/0.82         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.58/0.82           ( ![D:$i]:
% 0.58/0.82             ( ( r2_hidden @ D @ C ) <=>
% 0.58/0.82               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 0.58/0.82  thf('26', plain,
% 0.58/0.82      (![X15 : $i, X16 : $i, X18 : $i, X19 : $i]:
% 0.58/0.82         (((X18) != (k9_relat_1 @ X16 @ X15))
% 0.58/0.82          | (zip_tseitin_0 @ (sk_E_1 @ X19 @ X15 @ X16) @ X19 @ X15 @ X16)
% 0.58/0.82          | ~ (r2_hidden @ X19 @ X18)
% 0.58/0.82          | ~ (v1_funct_1 @ X16)
% 0.58/0.82          | ~ (v1_relat_1 @ X16))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.58/0.82  thf('27', plain,
% 0.58/0.82      (![X15 : $i, X16 : $i, X19 : $i]:
% 0.58/0.82         (~ (v1_relat_1 @ X16)
% 0.58/0.82          | ~ (v1_funct_1 @ X16)
% 0.58/0.82          | ~ (r2_hidden @ X19 @ (k9_relat_1 @ X16 @ X15))
% 0.58/0.82          | (zip_tseitin_0 @ (sk_E_1 @ X19 @ X15 @ X16) @ X19 @ X15 @ X16))),
% 0.58/0.82      inference('simplify', [status(thm)], ['26'])).
% 0.58/0.82  thf('28', plain,
% 0.58/0.82      (((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.58/0.82         sk_D_1)
% 0.58/0.82        | ~ (v1_funct_1 @ sk_D_1)
% 0.58/0.82        | ~ (v1_relat_1 @ sk_D_1))),
% 0.58/0.82      inference('sup-', [status(thm)], ['25', '27'])).
% 0.58/0.82  thf('29', plain, ((v1_funct_1 @ sk_D_1)),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('30', plain,
% 0.58/0.82      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf(cc1_relset_1, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i]:
% 0.58/0.82     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.82       ( v1_relat_1 @ C ) ))).
% 0.58/0.82  thf('31', plain,
% 0.58/0.82      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.58/0.82         ((v1_relat_1 @ X24)
% 0.58/0.82          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.58/0.82      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.58/0.82  thf('32', plain, ((v1_relat_1 @ sk_D_1)),
% 0.58/0.82      inference('sup-', [status(thm)], ['30', '31'])).
% 0.58/0.82  thf('33', plain,
% 0.58/0.82      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.58/0.82        sk_D_1)),
% 0.58/0.82      inference('demod', [status(thm)], ['28', '29', '32'])).
% 0.58/0.82  thf('34', plain,
% 0.58/0.82      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.58/0.82         ((r2_hidden @ X10 @ (k1_relat_1 @ X9))
% 0.58/0.82          | ~ (zip_tseitin_0 @ X10 @ X11 @ X12 @ X9))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.58/0.82  thf('35', plain,
% 0.58/0.82      ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ (k1_relat_1 @ sk_D_1))),
% 0.58/0.82      inference('sup-', [status(thm)], ['33', '34'])).
% 0.58/0.82  thf('36', plain,
% 0.58/0.82      (((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_A)
% 0.58/0.82        | ((sk_B) = (k1_xboole_0)))),
% 0.58/0.82      inference('sup+', [status(thm)], ['24', '35'])).
% 0.58/0.82  thf('37', plain,
% 0.58/0.82      (![X46 : $i]:
% 0.58/0.82         (~ (r2_hidden @ X46 @ sk_A)
% 0.58/0.82          | ~ (r2_hidden @ X46 @ sk_C)
% 0.58/0.82          | ((sk_E_2) != (k1_funct_1 @ sk_D_1 @ X46)))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('38', plain,
% 0.58/0.82      ((((sk_B) = (k1_xboole_0))
% 0.58/0.82        | ((sk_E_2)
% 0.58/0.82            != (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1)))
% 0.58/0.82        | ~ (r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_C))),
% 0.58/0.82      inference('sup-', [status(thm)], ['36', '37'])).
% 0.58/0.82  thf('39', plain,
% 0.58/0.82      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.58/0.82        sk_D_1)),
% 0.58/0.82      inference('demod', [status(thm)], ['28', '29', '32'])).
% 0.58/0.82  thf('40', plain,
% 0.58/0.82      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.58/0.82         (((X11) = (k1_funct_1 @ X9 @ X10))
% 0.58/0.82          | ~ (zip_tseitin_0 @ X10 @ X11 @ X12 @ X9))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.58/0.82  thf('41', plain,
% 0.58/0.82      (((sk_E_2) = (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['39', '40'])).
% 0.58/0.82  thf('42', plain,
% 0.58/0.82      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.58/0.82        sk_D_1)),
% 0.58/0.82      inference('demod', [status(thm)], ['28', '29', '32'])).
% 0.58/0.82  thf('43', plain,
% 0.58/0.82      (![X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.58/0.82         ((r2_hidden @ X10 @ X12) | ~ (zip_tseitin_0 @ X10 @ X11 @ X12 @ X9))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.58/0.82  thf('44', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_C)),
% 0.58/0.82      inference('sup-', [status(thm)], ['42', '43'])).
% 0.58/0.82  thf('45', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_E_2) != (sk_E_2)))),
% 0.58/0.82      inference('demod', [status(thm)], ['38', '41', '44'])).
% 0.58/0.82  thf('46', plain, (((sk_B) = (k1_xboole_0))),
% 0.58/0.82      inference('simplify', [status(thm)], ['45'])).
% 0.58/0.82  thf('47', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.58/0.82          | ~ (r2_hidden @ X1 @ (k9_relat_1 @ sk_D_1 @ X0)))),
% 0.58/0.82      inference('demod', [status(thm)], ['11', '46'])).
% 0.58/0.82  thf('48', plain,
% 0.58/0.82      ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))),
% 0.58/0.82      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.82  thf('49', plain,
% 0.58/0.82      (![X0 : $i]:
% 0.58/0.82         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0) @ 
% 0.58/0.82          (k1_zfmisc_1 @ sk_B))),
% 0.58/0.82      inference('sup-', [status(thm)], ['5', '6'])).
% 0.58/0.82  thf(t4_subset, axiom,
% 0.58/0.82    (![A:$i,B:$i,C:$i]:
% 0.58/0.82     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.58/0.82       ( m1_subset_1 @ A @ C ) ))).
% 0.58/0.82  thf('50', plain,
% 0.58/0.82      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.82         (~ (r2_hidden @ X3 @ X4)
% 0.58/0.82          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.58/0.82          | (m1_subset_1 @ X3 @ X5))),
% 0.58/0.82      inference('cnf', [status(esa)], [t4_subset])).
% 0.58/0.82  thf('51', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]:
% 0.58/0.82         ((m1_subset_1 @ X1 @ sk_B)
% 0.58/0.82          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)))),
% 0.58/0.82      inference('sup-', [status(thm)], ['49', '50'])).
% 0.58/0.82  thf('52', plain, ((m1_subset_1 @ sk_E_2 @ sk_B)),
% 0.58/0.82      inference('sup-', [status(thm)], ['48', '51'])).
% 0.58/0.82  thf(t2_subset, axiom,
% 0.58/0.82    (![A:$i,B:$i]:
% 0.58/0.82     ( ( m1_subset_1 @ A @ B ) =>
% 0.58/0.82       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.58/0.82  thf('53', plain,
% 0.58/0.82      (![X1 : $i, X2 : $i]:
% 0.58/0.82         ((r2_hidden @ X1 @ X2)
% 0.58/0.82          | (v1_xboole_0 @ X2)
% 0.58/0.82          | ~ (m1_subset_1 @ X1 @ X2))),
% 0.58/0.82      inference('cnf', [status(esa)], [t2_subset])).
% 0.58/0.82  thf('54', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_E_2 @ sk_B))),
% 0.58/0.82      inference('sup-', [status(thm)], ['52', '53'])).
% 0.58/0.82  thf(t7_ordinal1, axiom,
% 0.58/0.82    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.58/0.82  thf('55', plain,
% 0.58/0.82      (![X22 : $i, X23 : $i]:
% 0.58/0.82         (~ (r2_hidden @ X22 @ X23) | ~ (r1_tarski @ X23 @ X22))),
% 0.58/0.82      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.58/0.82  thf('56', plain, (((v1_xboole_0 @ sk_B) | ~ (r1_tarski @ sk_B @ sk_E_2))),
% 0.58/0.82      inference('sup-', [status(thm)], ['54', '55'])).
% 0.58/0.82  thf('57', plain, (((sk_B) = (k1_xboole_0))),
% 0.58/0.82      inference('simplify', [status(thm)], ['45'])).
% 0.58/0.82  thf('58', plain, (((sk_B) = (k1_xboole_0))),
% 0.58/0.82      inference('simplify', [status(thm)], ['45'])).
% 0.58/0.82  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.58/0.82  thf('59', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.58/0.82      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.58/0.82  thf('60', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.58/0.82      inference('demod', [status(thm)], ['56', '57', '58', '59'])).
% 0.58/0.82  thf('61', plain,
% 0.58/0.82      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k9_relat_1 @ sk_D_1 @ X0))),
% 0.58/0.82      inference('demod', [status(thm)], ['47', '60'])).
% 0.58/0.82  thf('62', plain, ($false), inference('sup-', [status(thm)], ['4', '61'])).
% 0.58/0.82  
% 0.58/0.82  % SZS output end Refutation
% 0.58/0.82  
% 0.69/0.83  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
