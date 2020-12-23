%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bAXGSwEca7

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:50 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.45s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 435 expanded)
%              Number of leaves         :   44 ( 147 expanded)
%              Depth                    :   14
%              Number of atoms          :  817 (5721 expanded)
%              Number of equality atoms :   43 ( 228 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

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
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ( ( k7_relset_1 @ X32 @ X33 @ X31 @ X34 )
        = ( k9_relat_1 @ X31 @ X34 ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X25 @ X26 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ X26 ) ) ) ),
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
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
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
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_0 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
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
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_0 @ X40 @ X41 )
      | ( zip_tseitin_1 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
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
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ( X37
        = ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ~ ( zip_tseitin_1 @ X39 @ X38 @ X37 ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k9_relat_1 @ X18 @ X16 ) )
      | ( r2_hidden @ ( sk_D @ X18 @ X16 @ X17 ) @ ( k1_relat_1 @ X18 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('27',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('29',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( v1_relat_1 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('31',plain,(
    ! [X13: $i,X14: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('32',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['27','32'])).

thf('34',plain,
    ( ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['24','33'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('35',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('36',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('38',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k9_relat_1 @ X18 @ X16 ) )
      | ( r2_hidden @ ( sk_D @ X18 @ X16 @ X17 ) @ X16 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['30','31'])).

thf('41',plain,(
    r2_hidden @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X43: $i] :
      ( ( sk_E
       != ( k1_funct_1 @ sk_D_1 @ X43 ) )
      | ~ ( r2_hidden @ X43 @ sk_C )
      | ~ ( m1_subset_1 @ X43 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ~ ( m1_subset_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_A )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E
     != ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['36','43'])).

thf('45',plain,(
    r2_hidden @ sk_E @ ( k9_relat_1 @ sk_D_1 @ sk_C ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('46',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r2_hidden @ X17 @ ( k9_relat_1 @ X18 @ X16 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X18 @ X16 @ X17 ) @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['30','31'])).

thf('49',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) @ sk_E ) @ sk_D_1 ),
    inference(demod,[status(thm)],['47','48'])).

thf(t8_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
      <=> ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( B
            = ( k1_funct_1 @ C @ A ) ) ) ) ) )).

thf('50',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X19 @ X21 ) @ X20 )
      | ( X21
        = ( k1_funct_1 @ X20 @ X19 ) )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t8_funct_1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ( sk_E
      = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['30','31'])).

thf('53',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( sk_E
    = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_E != sk_E ) ),
    inference(demod,[status(thm)],['44','54'])).

thf('56',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X1 @ ( k9_relat_1 @ sk_D_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['11','56'])).

thf('58',plain,(
    r2_hidden @ sk_E @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('60',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( m1_subset_1 @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ sk_B )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_E @ sk_B ),
    inference('sup-',[status(thm)],['58','61'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('63',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('64',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('65',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r2_hidden @ X22 @ X23 )
      | ~ ( r1_tarski @ X23 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('66',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( r1_tarski @ sk_B @ sk_E ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['55'])).

thf('68',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['55'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('69',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('70',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['66','67','68','69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ~ ( r2_hidden @ X1 @ ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['57','70'])).

thf('72',plain,(
    $false ),
    inference('sup-',[status(thm)],['4','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.bAXGSwEca7
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:01:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.41/0.62  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.41/0.62  % Solved by: fo/fo7.sh
% 0.41/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.62  % done 202 iterations in 0.171s
% 0.41/0.62  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.41/0.62  % SZS output start Refutation
% 0.41/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.62  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.41/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.62  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.41/0.62  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.41/0.62  thf(sk_C_type, type, sk_C: $i).
% 0.41/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.62  thf(sk_E_type, type, sk_E: $i).
% 0.41/0.62  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.41/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.41/0.62  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.41/0.62  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.41/0.62  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.41/0.62  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.41/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.41/0.62  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.41/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.62  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.41/0.62  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.41/0.62  thf(t116_funct_2, conjecture,
% 0.41/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.62     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.41/0.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.62       ( ![E:$i]:
% 0.41/0.62         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.41/0.62              ( ![F:$i]:
% 0.41/0.62                ( ( m1_subset_1 @ F @ A ) =>
% 0.41/0.62                  ( ~( ( r2_hidden @ F @ C ) & 
% 0.41/0.62                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 0.41/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.62    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.62        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.41/0.62            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.62          ( ![E:$i]:
% 0.41/0.62            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.41/0.62                 ( ![F:$i]:
% 0.41/0.62                   ( ( m1_subset_1 @ F @ A ) =>
% 0.41/0.62                     ( ~( ( r2_hidden @ F @ C ) & 
% 0.41/0.62                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.41/0.62    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 0.41/0.62  thf('0', plain,
% 0.41/0.62      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('1', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(redefinition_k7_relset_1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.62       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.41/0.62  thf('2', plain,
% 0.41/0.62      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.41/0.62         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.41/0.62          | ((k7_relset_1 @ X32 @ X33 @ X31 @ X34) = (k9_relat_1 @ X31 @ X34)))),
% 0.41/0.62      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.41/0.62  thf('3', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.41/0.62           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.62  thf('4', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.41/0.62      inference('demod', [status(thm)], ['0', '3'])).
% 0.41/0.62  thf('5', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(dt_k7_relset_1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.62       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.41/0.62  thf('6', plain,
% 0.41/0.62      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.41/0.62         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.41/0.62          | (m1_subset_1 @ (k7_relset_1 @ X25 @ X26 @ X24 @ X27) @ 
% 0.41/0.62             (k1_zfmisc_1 @ X26)))),
% 0.41/0.62      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.41/0.62  thf('7', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0) @ 
% 0.41/0.62          (k1_zfmisc_1 @ sk_B))),
% 0.41/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.41/0.62  thf(t5_subset, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.41/0.62          ( v1_xboole_0 @ C ) ) ))).
% 0.41/0.62  thf('8', plain,
% 0.41/0.62      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X8 @ X9)
% 0.41/0.62          | ~ (v1_xboole_0 @ X10)
% 0.41/0.62          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 0.41/0.62      inference('cnf', [status(esa)], [t5_subset])).
% 0.41/0.62  thf('9', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (~ (v1_xboole_0 @ sk_B)
% 0.41/0.62          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['7', '8'])).
% 0.41/0.62  thf('10', plain,
% 0.41/0.62      (![X0 : $i]:
% 0.41/0.62         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.41/0.62           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.41/0.62      inference('sup-', [status(thm)], ['1', '2'])).
% 0.41/0.62  thf('11', plain,
% 0.41/0.62      (![X0 : $i, X1 : $i]:
% 0.41/0.62         (~ (v1_xboole_0 @ sk_B)
% 0.41/0.62          | ~ (r2_hidden @ X1 @ (k9_relat_1 @ sk_D_1 @ X0)))),
% 0.41/0.62      inference('demod', [status(thm)], ['9', '10'])).
% 0.41/0.62  thf(d1_funct_2, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.62       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.41/0.62           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.41/0.62             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.41/0.62         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.41/0.62           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.41/0.62             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.41/0.62  thf(zf_stmt_1, axiom,
% 0.41/0.62    (![B:$i,A:$i]:
% 0.41/0.62     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.41/0.62       ( zip_tseitin_0 @ B @ A ) ))).
% 0.41/0.62  thf('12', plain,
% 0.41/0.62      (![X35 : $i, X36 : $i]:
% 0.41/0.62         ((zip_tseitin_0 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.41/0.62  thf('13', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.41/0.62  thf(zf_stmt_3, axiom,
% 0.41/0.62    (![C:$i,B:$i,A:$i]:
% 0.41/0.62     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.41/0.62       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.41/0.62  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.41/0.62  thf(zf_stmt_5, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.62       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.41/0.62         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.41/0.62           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.41/0.62             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.41/0.62  thf('14', plain,
% 0.41/0.62      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.41/0.62         (~ (zip_tseitin_0 @ X40 @ X41)
% 0.41/0.62          | (zip_tseitin_1 @ X42 @ X40 @ X41)
% 0.41/0.62          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.41/0.62  thf('15', plain,
% 0.41/0.62      (((zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.41/0.62        | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.41/0.62      inference('sup-', [status(thm)], ['13', '14'])).
% 0.41/0.62  thf('16', plain,
% 0.41/0.62      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A))),
% 0.41/0.62      inference('sup-', [status(thm)], ['12', '15'])).
% 0.41/0.62  thf('17', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('18', plain,
% 0.41/0.62      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.41/0.62         (~ (v1_funct_2 @ X39 @ X37 @ X38)
% 0.41/0.62          | ((X37) = (k1_relset_1 @ X37 @ X38 @ X39))
% 0.41/0.62          | ~ (zip_tseitin_1 @ X39 @ X38 @ X37))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.41/0.62  thf('19', plain,
% 0.41/0.62      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.41/0.62        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_1)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['17', '18'])).
% 0.41/0.62  thf('20', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(redefinition_k1_relset_1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.62       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.41/0.62  thf('21', plain,
% 0.41/0.62      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.41/0.62         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 0.41/0.62          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.41/0.62      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.41/0.62  thf('22', plain,
% 0.41/0.62      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['20', '21'])).
% 0.41/0.62  thf('23', plain,
% 0.41/0.62      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_B @ sk_A)
% 0.41/0.62        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.41/0.62      inference('demod', [status(thm)], ['19', '22'])).
% 0.41/0.62  thf('24', plain,
% 0.41/0.62      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['16', '23'])).
% 0.41/0.62  thf('25', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.41/0.62      inference('demod', [status(thm)], ['0', '3'])).
% 0.41/0.62  thf(t143_relat_1, axiom,
% 0.41/0.62    (![A:$i,B:$i,C:$i]:
% 0.41/0.62     ( ( v1_relat_1 @ C ) =>
% 0.41/0.62       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.41/0.62         ( ?[D:$i]:
% 0.41/0.62           ( ( r2_hidden @ D @ B ) & 
% 0.41/0.62             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.41/0.62             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.41/0.62  thf('26', plain,
% 0.41/0.62      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X17 @ (k9_relat_1 @ X18 @ X16))
% 0.41/0.62          | (r2_hidden @ (sk_D @ X18 @ X16 @ X17) @ (k1_relat_1 @ X18))
% 0.41/0.62          | ~ (v1_relat_1 @ X18))),
% 0.41/0.62      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.41/0.62  thf('27', plain,
% 0.41/0.62      ((~ (v1_relat_1 @ sk_D_1)
% 0.41/0.62        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1)))),
% 0.41/0.62      inference('sup-', [status(thm)], ['25', '26'])).
% 0.41/0.62  thf('28', plain,
% 0.41/0.62      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf(cc2_relat_1, axiom,
% 0.41/0.62    (![A:$i]:
% 0.41/0.62     ( ( v1_relat_1 @ A ) =>
% 0.41/0.62       ( ![B:$i]:
% 0.41/0.62         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.41/0.62  thf('29', plain,
% 0.41/0.62      (![X11 : $i, X12 : $i]:
% 0.41/0.62         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 0.41/0.62          | (v1_relat_1 @ X11)
% 0.41/0.62          | ~ (v1_relat_1 @ X12))),
% 0.41/0.62      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.41/0.62  thf('30', plain,
% 0.41/0.62      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_1))),
% 0.41/0.62      inference('sup-', [status(thm)], ['28', '29'])).
% 0.41/0.62  thf(fc6_relat_1, axiom,
% 0.41/0.62    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.41/0.62  thf('31', plain,
% 0.41/0.62      (![X13 : $i, X14 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X13 @ X14))),
% 0.41/0.62      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.41/0.62  thf('32', plain, ((v1_relat_1 @ sk_D_1)),
% 0.41/0.62      inference('demod', [status(thm)], ['30', '31'])).
% 0.41/0.62  thf('33', plain,
% 0.41/0.62      ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ (k1_relat_1 @ sk_D_1))),
% 0.41/0.62      inference('demod', [status(thm)], ['27', '32'])).
% 0.41/0.62  thf('34', plain,
% 0.41/0.62      (((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_A)
% 0.41/0.62        | ((sk_B) = (k1_xboole_0)))),
% 0.41/0.62      inference('sup+', [status(thm)], ['24', '33'])).
% 0.41/0.62  thf(t1_subset, axiom,
% 0.41/0.62    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.41/0.62  thf('35', plain,
% 0.41/0.62      (![X1 : $i, X2 : $i]: ((m1_subset_1 @ X1 @ X2) | ~ (r2_hidden @ X1 @ X2))),
% 0.41/0.62      inference('cnf', [status(esa)], [t1_subset])).
% 0.41/0.62  thf('36', plain,
% 0.41/0.62      ((((sk_B) = (k1_xboole_0))
% 0.41/0.62        | (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_A))),
% 0.41/0.62      inference('sup-', [status(thm)], ['34', '35'])).
% 0.41/0.62  thf('37', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.41/0.62      inference('demod', [status(thm)], ['0', '3'])).
% 0.41/0.62  thf('38', plain,
% 0.41/0.62      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X17 @ (k9_relat_1 @ X18 @ X16))
% 0.41/0.62          | (r2_hidden @ (sk_D @ X18 @ X16 @ X17) @ X16)
% 0.41/0.62          | ~ (v1_relat_1 @ X18))),
% 0.41/0.62      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.41/0.62  thf('39', plain,
% 0.41/0.62      ((~ (v1_relat_1 @ sk_D_1)
% 0.41/0.62        | (r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C))),
% 0.41/0.62      inference('sup-', [status(thm)], ['37', '38'])).
% 0.41/0.62  thf('40', plain, ((v1_relat_1 @ sk_D_1)),
% 0.41/0.62      inference('demod', [status(thm)], ['30', '31'])).
% 0.41/0.62  thf('41', plain, ((r2_hidden @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_C)),
% 0.41/0.62      inference('demod', [status(thm)], ['39', '40'])).
% 0.41/0.62  thf('42', plain,
% 0.41/0.62      (![X43 : $i]:
% 0.41/0.62         (((sk_E) != (k1_funct_1 @ sk_D_1 @ X43))
% 0.41/0.62          | ~ (r2_hidden @ X43 @ sk_C)
% 0.41/0.62          | ~ (m1_subset_1 @ X43 @ sk_A))),
% 0.41/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.62  thf('43', plain,
% 0.41/0.62      ((~ (m1_subset_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_A)
% 0.41/0.62        | ((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['41', '42'])).
% 0.41/0.62  thf('44', plain,
% 0.41/0.62      ((((sk_B) = (k1_xboole_0))
% 0.41/0.62        | ((sk_E) != (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E))))),
% 0.41/0.62      inference('sup-', [status(thm)], ['36', '43'])).
% 0.41/0.62  thf('45', plain, ((r2_hidden @ sk_E @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.41/0.62      inference('demod', [status(thm)], ['0', '3'])).
% 0.41/0.62  thf('46', plain,
% 0.41/0.62      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.41/0.62         (~ (r2_hidden @ X17 @ (k9_relat_1 @ X18 @ X16))
% 0.41/0.62          | (r2_hidden @ (k4_tarski @ (sk_D @ X18 @ X16 @ X17) @ X17) @ X18)
% 0.41/0.62          | ~ (v1_relat_1 @ X18))),
% 0.41/0.62      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.45/0.62  thf('47', plain,
% 0.45/0.62      ((~ (v1_relat_1 @ sk_D_1)
% 0.45/0.62        | (r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ 
% 0.45/0.62           sk_D_1))),
% 0.45/0.62      inference('sup-', [status(thm)], ['45', '46'])).
% 0.45/0.62  thf('48', plain, ((v1_relat_1 @ sk_D_1)),
% 0.45/0.62      inference('demod', [status(thm)], ['30', '31'])).
% 0.45/0.62  thf('49', plain,
% 0.45/0.62      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_1 @ sk_C @ sk_E) @ sk_E) @ sk_D_1)),
% 0.45/0.62      inference('demod', [status(thm)], ['47', '48'])).
% 0.45/0.62  thf(t8_funct_1, axiom,
% 0.45/0.62    (![A:$i,B:$i,C:$i]:
% 0.45/0.62     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.45/0.62       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) <=>
% 0.45/0.62         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.45/0.62           ( ( B ) = ( k1_funct_1 @ C @ A ) ) ) ) ))).
% 0.45/0.62  thf('50', plain,
% 0.45/0.62      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.45/0.62         (~ (r2_hidden @ (k4_tarski @ X19 @ X21) @ X20)
% 0.45/0.62          | ((X21) = (k1_funct_1 @ X20 @ X19))
% 0.45/0.62          | ~ (v1_funct_1 @ X20)
% 0.45/0.62          | ~ (v1_relat_1 @ X20))),
% 0.45/0.62      inference('cnf', [status(esa)], [t8_funct_1])).
% 0.45/0.62  thf('51', plain,
% 0.45/0.62      ((~ (v1_relat_1 @ sk_D_1)
% 0.45/0.62        | ~ (v1_funct_1 @ sk_D_1)
% 0.45/0.62        | ((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E))))),
% 0.45/0.62      inference('sup-', [status(thm)], ['49', '50'])).
% 0.45/0.62  thf('52', plain, ((v1_relat_1 @ sk_D_1)),
% 0.45/0.62      inference('demod', [status(thm)], ['30', '31'])).
% 0.45/0.62  thf('53', plain, ((v1_funct_1 @ sk_D_1)),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.62  thf('54', plain,
% 0.45/0.62      (((sk_E) = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ sk_C @ sk_E)))),
% 0.45/0.62      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.45/0.62  thf('55', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_E) != (sk_E)))),
% 0.45/0.62      inference('demod', [status(thm)], ['44', '54'])).
% 0.45/0.62  thf('56', plain, (((sk_B) = (k1_xboole_0))),
% 0.45/0.62      inference('simplify', [status(thm)], ['55'])).
% 0.45/0.62  thf('57', plain,
% 0.45/0.62      (![X0 : $i, X1 : $i]:
% 0.45/0.62         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.45/0.62          | ~ (r2_hidden @ X1 @ (k9_relat_1 @ sk_D_1 @ X0)))),
% 0.45/0.62      inference('demod', [status(thm)], ['11', '56'])).
% 0.45/0.62  thf('58', plain,
% 0.45/0.62      ((r2_hidden @ sk_E @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))),
% 0.45/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.45/0.62  thf('59', plain,
% 0.45/0.62      (![X0 : $i]:
% 0.45/0.62         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0) @ 
% 0.45/0.62          (k1_zfmisc_1 @ sk_B))),
% 0.45/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.45/0.62  thf(t4_subset, axiom,
% 0.45/0.62    (![A:$i,B:$i,C:$i]:
% 0.45/0.62     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.45/0.62       ( m1_subset_1 @ A @ C ) ))).
% 0.45/0.62  thf('60', plain,
% 0.45/0.62      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.45/0.62         (~ (r2_hidden @ X5 @ X6)
% 0.45/0.62          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.45/0.62          | (m1_subset_1 @ X5 @ X7))),
% 0.45/0.62      inference('cnf', [status(esa)], [t4_subset])).
% 0.45/0.62  thf('61', plain,
% 0.45/0.62      (![X0 : $i, X1 : $i]:
% 0.45/0.62         ((m1_subset_1 @ X1 @ sk_B)
% 0.45/0.62          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)))),
% 0.45/0.62      inference('sup-', [status(thm)], ['59', '60'])).
% 0.45/0.62  thf('62', plain, ((m1_subset_1 @ sk_E @ sk_B)),
% 0.45/0.62      inference('sup-', [status(thm)], ['58', '61'])).
% 0.45/0.62  thf(t2_subset, axiom,
% 0.45/0.62    (![A:$i,B:$i]:
% 0.45/0.62     ( ( m1_subset_1 @ A @ B ) =>
% 0.45/0.62       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.45/0.62  thf('63', plain,
% 0.45/0.62      (![X3 : $i, X4 : $i]:
% 0.45/0.62         ((r2_hidden @ X3 @ X4)
% 0.45/0.62          | (v1_xboole_0 @ X4)
% 0.45/0.62          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.45/0.62      inference('cnf', [status(esa)], [t2_subset])).
% 0.45/0.62  thf('64', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_E @ sk_B))),
% 0.45/0.62      inference('sup-', [status(thm)], ['62', '63'])).
% 0.45/0.62  thf(t7_ordinal1, axiom,
% 0.45/0.62    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.45/0.62  thf('65', plain,
% 0.45/0.62      (![X22 : $i, X23 : $i]:
% 0.45/0.62         (~ (r2_hidden @ X22 @ X23) | ~ (r1_tarski @ X23 @ X22))),
% 0.45/0.62      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.45/0.62  thf('66', plain, (((v1_xboole_0 @ sk_B) | ~ (r1_tarski @ sk_B @ sk_E))),
% 0.45/0.62      inference('sup-', [status(thm)], ['64', '65'])).
% 0.45/0.62  thf('67', plain, (((sk_B) = (k1_xboole_0))),
% 0.45/0.62      inference('simplify', [status(thm)], ['55'])).
% 0.45/0.62  thf('68', plain, (((sk_B) = (k1_xboole_0))),
% 0.45/0.62      inference('simplify', [status(thm)], ['55'])).
% 0.45/0.62  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.45/0.62  thf('69', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.45/0.62      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.45/0.62  thf('70', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.45/0.62      inference('demod', [status(thm)], ['66', '67', '68', '69'])).
% 0.45/0.62  thf('71', plain,
% 0.45/0.62      (![X0 : $i, X1 : $i]: ~ (r2_hidden @ X1 @ (k9_relat_1 @ sk_D_1 @ X0))),
% 0.45/0.62      inference('demod', [status(thm)], ['57', '70'])).
% 0.45/0.62  thf('72', plain, ($false), inference('sup-', [status(thm)], ['4', '71'])).
% 0.45/0.62  
% 0.45/0.62  % SZS output end Refutation
% 0.45/0.62  
% 0.45/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
