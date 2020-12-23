%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CuAOBwXCqJ

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:46 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.50s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 162 expanded)
%              Number of leaves         :   42 (  67 expanded)
%              Depth                    :   11
%              Number of atoms          :  693 (2045 expanded)
%              Number of equality atoms :   36 (  82 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

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
    ! [X12: $i,X13: $i,X15: $i,X16: $i] :
      ( ( X15
       != ( k9_relat_1 @ X13 @ X12 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X16 @ X12 @ X13 ) @ X16 @ X12 @ X13 )
      | ~ ( r2_hidden @ X16 @ X15 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X12: $i,X13: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X13 )
      | ~ ( v1_funct_1 @ X13 )
      | ~ ( r2_hidden @ X16 @ ( k9_relat_1 @ X13 @ X12 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X16 @ X12 @ X13 ) @ X16 @ X12 @ X13 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 @ sk_C @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('10',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( v1_relat_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 @ sk_C @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('13',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X7 @ X9 )
      | ~ ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('14',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X43: $i] :
      ( ( sk_E_2
       != ( k1_funct_1 @ sk_D_1 @ X43 ) )
      | ~ ( r2_hidden @ X43 @ sk_C )
      | ~ ( m1_subset_1 @ X43 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_A )
    | ( sk_E_2
     != ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 @ sk_C @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('18',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( r2_hidden @ X7 @ ( k1_relat_1 @ X6 ) )
      | ~ ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('19',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('20',plain,(
    ! [X35: $i,X36: $i] :
      ( ( zip_tseitin_1 @ X35 @ X36 )
      | ( X35 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('21',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_5,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zf_stmt_6,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_7,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_1 @ B @ A )
         => ( zip_tseitin_2 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('24',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ~ ( zip_tseitin_1 @ X40 @ X41 )
      | ( zip_tseitin_2 @ X42 @ X40 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('25',plain,
    ( ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','25'])).

thf('27',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_2 @ X39 @ X37 @ X38 )
      | ( X37
        = ( k1_relset_1 @ X37 @ X38 @ X39 ) )
      | ~ ( zip_tseitin_2 @ X39 @ X38 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('29',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('31',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('32',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['26','33'])).

thf('35',plain,(
    r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('37',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X25 @ X26 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('39',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ sk_B )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    r2_hidden @ sk_E_2 @ sk_B ),
    inference('sup-',[status(thm)],['35','40'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('42',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X19 @ X20 )
      | ~ ( r1_tarski @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('43',plain,(
    ~ ( r1_tarski @ sk_B @ sk_E_2 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['34','43'])).

thf('45',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_A ),
    inference(demod,[status(thm)],['19','44'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('46',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('47',plain,(
    m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 @ sk_C @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('49',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( X8
        = ( k1_funct_1 @ X6 @ X7 ) )
      | ~ ( zip_tseitin_0 @ X7 @ X8 @ X9 @ X6 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('50',plain,
    ( sk_E_2
    = ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    sk_E_2 != sk_E_2 ),
    inference(demod,[status(thm)],['16','47','50'])).

thf('52',plain,(
    $false ),
    inference(simplify,[status(thm)],['51'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CuAOBwXCqJ
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:04:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.50/0.70  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.50/0.70  % Solved by: fo/fo7.sh
% 0.50/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.70  % done 192 iterations in 0.268s
% 0.50/0.70  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.50/0.70  % SZS output start Refutation
% 0.50/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.70  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.50/0.70  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.50/0.70  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.50/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.50/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.50/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.70  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.50/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.50/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.50/0.70  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.50/0.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.50/0.70  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.50/0.70  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.50/0.70  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.50/0.70  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.50/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.50/0.70  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.50/0.70  thf(t116_funct_2, conjecture,
% 0.50/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.70     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.50/0.70         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.50/0.70       ( ![E:$i]:
% 0.50/0.70         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.50/0.70              ( ![F:$i]:
% 0.50/0.70                ( ( m1_subset_1 @ F @ A ) =>
% 0.50/0.70                  ( ~( ( r2_hidden @ F @ C ) & 
% 0.50/0.70                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 0.50/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.70    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.70        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.50/0.70            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.50/0.70          ( ![E:$i]:
% 0.50/0.70            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.50/0.70                 ( ![F:$i]:
% 0.50/0.70                   ( ( m1_subset_1 @ F @ A ) =>
% 0.50/0.70                     ( ~( ( r2_hidden @ F @ C ) & 
% 0.50/0.70                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.50/0.70    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 0.50/0.70  thf('0', plain,
% 0.50/0.70      ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('1', plain,
% 0.50/0.70      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf(redefinition_k7_relset_1, axiom,
% 0.50/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.70       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.50/0.70  thf('2', plain,
% 0.50/0.70      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.50/0.70         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.50/0.70          | ((k7_relset_1 @ X32 @ X33 @ X31 @ X34) = (k9_relat_1 @ X31 @ X34)))),
% 0.50/0.70      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.50/0.70  thf('3', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.50/0.70           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.50/0.70      inference('sup-', [status(thm)], ['1', '2'])).
% 0.50/0.70  thf('4', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.50/0.70      inference('demod', [status(thm)], ['0', '3'])).
% 0.50/0.70  thf(d12_funct_1, axiom,
% 0.50/0.70    (![A:$i]:
% 0.50/0.70     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.50/0.70       ( ![B:$i,C:$i]:
% 0.50/0.70         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.50/0.70           ( ![D:$i]:
% 0.50/0.70             ( ( r2_hidden @ D @ C ) <=>
% 0.50/0.70               ( ?[E:$i]:
% 0.50/0.70                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 0.50/0.70                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 0.50/0.70  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.50/0.70  thf(zf_stmt_2, axiom,
% 0.50/0.70    (![E:$i,D:$i,B:$i,A:$i]:
% 0.50/0.70     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.50/0.70       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 0.50/0.70         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 0.50/0.70  thf(zf_stmt_3, axiom,
% 0.50/0.70    (![A:$i]:
% 0.50/0.70     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.50/0.70       ( ![B:$i,C:$i]:
% 0.50/0.70         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.50/0.70           ( ![D:$i]:
% 0.50/0.70             ( ( r2_hidden @ D @ C ) <=>
% 0.50/0.70               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 0.50/0.70  thf('5', plain,
% 0.50/0.70      (![X12 : $i, X13 : $i, X15 : $i, X16 : $i]:
% 0.50/0.70         (((X15) != (k9_relat_1 @ X13 @ X12))
% 0.50/0.70          | (zip_tseitin_0 @ (sk_E_1 @ X16 @ X12 @ X13) @ X16 @ X12 @ X13)
% 0.50/0.70          | ~ (r2_hidden @ X16 @ X15)
% 0.50/0.70          | ~ (v1_funct_1 @ X13)
% 0.50/0.70          | ~ (v1_relat_1 @ X13))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.50/0.70  thf('6', plain,
% 0.50/0.70      (![X12 : $i, X13 : $i, X16 : $i]:
% 0.50/0.70         (~ (v1_relat_1 @ X13)
% 0.50/0.70          | ~ (v1_funct_1 @ X13)
% 0.50/0.70          | ~ (r2_hidden @ X16 @ (k9_relat_1 @ X13 @ X12))
% 0.50/0.70          | (zip_tseitin_0 @ (sk_E_1 @ X16 @ X12 @ X13) @ X16 @ X12 @ X13))),
% 0.50/0.70      inference('simplify', [status(thm)], ['5'])).
% 0.50/0.70  thf('7', plain,
% 0.50/0.70      (((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.50/0.70         sk_D_1)
% 0.50/0.70        | ~ (v1_funct_1 @ sk_D_1)
% 0.50/0.70        | ~ (v1_relat_1 @ sk_D_1))),
% 0.50/0.70      inference('sup-', [status(thm)], ['4', '6'])).
% 0.50/0.70  thf('8', plain, ((v1_funct_1 @ sk_D_1)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('9', plain,
% 0.50/0.70      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf(cc1_relset_1, axiom,
% 0.50/0.70    (![A:$i,B:$i,C:$i]:
% 0.50/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.70       ( v1_relat_1 @ C ) ))).
% 0.50/0.70  thf('10', plain,
% 0.50/0.70      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.50/0.70         ((v1_relat_1 @ X21)
% 0.50/0.70          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.50/0.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.50/0.70  thf('11', plain, ((v1_relat_1 @ sk_D_1)),
% 0.50/0.70      inference('sup-', [status(thm)], ['9', '10'])).
% 0.50/0.70  thf('12', plain,
% 0.50/0.70      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.50/0.70        sk_D_1)),
% 0.50/0.70      inference('demod', [status(thm)], ['7', '8', '11'])).
% 0.50/0.70  thf('13', plain,
% 0.50/0.70      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.50/0.70         ((r2_hidden @ X7 @ X9) | ~ (zip_tseitin_0 @ X7 @ X8 @ X9 @ X6))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.50/0.70  thf('14', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_C)),
% 0.50/0.70      inference('sup-', [status(thm)], ['12', '13'])).
% 0.50/0.70  thf('15', plain,
% 0.50/0.70      (![X43 : $i]:
% 0.50/0.70         (((sk_E_2) != (k1_funct_1 @ sk_D_1 @ X43))
% 0.50/0.70          | ~ (r2_hidden @ X43 @ sk_C)
% 0.50/0.70          | ~ (m1_subset_1 @ X43 @ sk_A))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('16', plain,
% 0.50/0.70      ((~ (m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_A)
% 0.50/0.70        | ((sk_E_2)
% 0.50/0.70            != (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1))))),
% 0.50/0.70      inference('sup-', [status(thm)], ['14', '15'])).
% 0.50/0.70  thf('17', plain,
% 0.50/0.70      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.50/0.70        sk_D_1)),
% 0.50/0.70      inference('demod', [status(thm)], ['7', '8', '11'])).
% 0.50/0.70  thf('18', plain,
% 0.50/0.70      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.50/0.70         ((r2_hidden @ X7 @ (k1_relat_1 @ X6))
% 0.50/0.70          | ~ (zip_tseitin_0 @ X7 @ X8 @ X9 @ X6))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.50/0.70  thf('19', plain,
% 0.50/0.70      ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ (k1_relat_1 @ sk_D_1))),
% 0.50/0.70      inference('sup-', [status(thm)], ['17', '18'])).
% 0.50/0.70  thf(d1_funct_2, axiom,
% 0.50/0.70    (![A:$i,B:$i,C:$i]:
% 0.50/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.70       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.50/0.70           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.50/0.70             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.50/0.70         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.50/0.70           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.50/0.70             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.50/0.70  thf(zf_stmt_4, axiom,
% 0.50/0.70    (![B:$i,A:$i]:
% 0.50/0.70     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.50/0.70       ( zip_tseitin_1 @ B @ A ) ))).
% 0.50/0.70  thf('20', plain,
% 0.50/0.70      (![X35 : $i, X36 : $i]:
% 0.50/0.70         ((zip_tseitin_1 @ X35 @ X36) | ((X35) = (k1_xboole_0)))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.50/0.70  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.50/0.70  thf('21', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.50/0.70      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.50/0.70  thf('22', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.50/0.70         ((r1_tarski @ X0 @ X1) | (zip_tseitin_1 @ X0 @ X2))),
% 0.50/0.70      inference('sup+', [status(thm)], ['20', '21'])).
% 0.50/0.70  thf('23', plain,
% 0.50/0.70      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf(zf_stmt_5, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.50/0.70  thf(zf_stmt_6, axiom,
% 0.50/0.70    (![C:$i,B:$i,A:$i]:
% 0.50/0.70     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.50/0.70       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.50/0.70  thf(zf_stmt_7, type, zip_tseitin_1 : $i > $i > $o).
% 0.50/0.70  thf(zf_stmt_8, axiom,
% 0.50/0.70    (![A:$i,B:$i,C:$i]:
% 0.50/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.70       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.50/0.70         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.50/0.70           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.50/0.70             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.50/0.70  thf('24', plain,
% 0.50/0.70      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.50/0.70         (~ (zip_tseitin_1 @ X40 @ X41)
% 0.50/0.70          | (zip_tseitin_2 @ X42 @ X40 @ X41)
% 0.50/0.70          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40))))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.50/0.70  thf('25', plain,
% 0.50/0.70      (((zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)
% 0.50/0.70        | ~ (zip_tseitin_1 @ sk_B @ sk_A))),
% 0.50/0.70      inference('sup-', [status(thm)], ['23', '24'])).
% 0.50/0.70  thf('26', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         ((r1_tarski @ sk_B @ X0) | (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A))),
% 0.50/0.70      inference('sup-', [status(thm)], ['22', '25'])).
% 0.50/0.70  thf('27', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('28', plain,
% 0.50/0.70      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.50/0.70         (~ (v1_funct_2 @ X39 @ X37 @ X38)
% 0.50/0.70          | ((X37) = (k1_relset_1 @ X37 @ X38 @ X39))
% 0.50/0.70          | ~ (zip_tseitin_2 @ X39 @ X38 @ X37))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.50/0.70  thf('29', plain,
% 0.50/0.70      ((~ (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)
% 0.50/0.70        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_1)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['27', '28'])).
% 0.50/0.70  thf('30', plain,
% 0.50/0.70      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf(redefinition_k1_relset_1, axiom,
% 0.50/0.70    (![A:$i,B:$i,C:$i]:
% 0.50/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.70       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.50/0.70  thf('31', plain,
% 0.50/0.70      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.50/0.70         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 0.50/0.70          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.50/0.70      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.50/0.70  thf('32', plain,
% 0.50/0.70      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.50/0.70      inference('sup-', [status(thm)], ['30', '31'])).
% 0.50/0.70  thf('33', plain,
% 0.50/0.70      ((~ (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)
% 0.50/0.70        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.50/0.70      inference('demod', [status(thm)], ['29', '32'])).
% 0.50/0.70  thf('34', plain,
% 0.50/0.70      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['26', '33'])).
% 0.50/0.70  thf('35', plain,
% 0.50/0.70      ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf('36', plain,
% 0.50/0.70      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.70  thf(dt_k7_relset_1, axiom,
% 0.50/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.70       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.50/0.70  thf('37', plain,
% 0.50/0.70      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.50/0.70         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.50/0.70          | (m1_subset_1 @ (k7_relset_1 @ X25 @ X26 @ X24 @ X27) @ 
% 0.50/0.70             (k1_zfmisc_1 @ X26)))),
% 0.50/0.70      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.50/0.70  thf('38', plain,
% 0.50/0.70      (![X0 : $i]:
% 0.50/0.70         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0) @ 
% 0.50/0.70          (k1_zfmisc_1 @ sk_B))),
% 0.50/0.70      inference('sup-', [status(thm)], ['36', '37'])).
% 0.50/0.70  thf(l3_subset_1, axiom,
% 0.50/0.70    (![A:$i,B:$i]:
% 0.50/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.50/0.70       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 0.50/0.70  thf('39', plain,
% 0.50/0.70      (![X1 : $i, X2 : $i, X3 : $i]:
% 0.50/0.70         (~ (r2_hidden @ X1 @ X2)
% 0.50/0.70          | (r2_hidden @ X1 @ X3)
% 0.50/0.70          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.50/0.70      inference('cnf', [status(esa)], [l3_subset_1])).
% 0.50/0.70  thf('40', plain,
% 0.50/0.70      (![X0 : $i, X1 : $i]:
% 0.50/0.70         ((r2_hidden @ X1 @ sk_B)
% 0.50/0.70          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['38', '39'])).
% 0.50/0.70  thf('41', plain, ((r2_hidden @ sk_E_2 @ sk_B)),
% 0.50/0.70      inference('sup-', [status(thm)], ['35', '40'])).
% 0.50/0.70  thf(t7_ordinal1, axiom,
% 0.50/0.70    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.50/0.70  thf('42', plain,
% 0.50/0.70      (![X19 : $i, X20 : $i]:
% 0.50/0.70         (~ (r2_hidden @ X19 @ X20) | ~ (r1_tarski @ X20 @ X19))),
% 0.50/0.70      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.50/0.70  thf('43', plain, (~ (r1_tarski @ sk_B @ sk_E_2)),
% 0.50/0.70      inference('sup-', [status(thm)], ['41', '42'])).
% 0.50/0.70  thf('44', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.50/0.70      inference('sup-', [status(thm)], ['34', '43'])).
% 0.50/0.70  thf('45', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_A)),
% 0.50/0.70      inference('demod', [status(thm)], ['19', '44'])).
% 0.50/0.70  thf(t1_subset, axiom,
% 0.50/0.70    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.50/0.70  thf('46', plain,
% 0.50/0.70      (![X4 : $i, X5 : $i]: ((m1_subset_1 @ X4 @ X5) | ~ (r2_hidden @ X4 @ X5))),
% 0.50/0.70      inference('cnf', [status(esa)], [t1_subset])).
% 0.50/0.70  thf('47', plain, ((m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_A)),
% 0.50/0.70      inference('sup-', [status(thm)], ['45', '46'])).
% 0.50/0.70  thf('48', plain,
% 0.50/0.70      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.50/0.70        sk_D_1)),
% 0.50/0.70      inference('demod', [status(thm)], ['7', '8', '11'])).
% 0.50/0.70  thf('49', plain,
% 0.50/0.70      (![X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.50/0.70         (((X8) = (k1_funct_1 @ X6 @ X7))
% 0.50/0.70          | ~ (zip_tseitin_0 @ X7 @ X8 @ X9 @ X6))),
% 0.50/0.70      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.50/0.70  thf('50', plain,
% 0.50/0.70      (((sk_E_2) = (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1)))),
% 0.50/0.70      inference('sup-', [status(thm)], ['48', '49'])).
% 0.50/0.70  thf('51', plain, (((sk_E_2) != (sk_E_2))),
% 0.50/0.70      inference('demod', [status(thm)], ['16', '47', '50'])).
% 0.50/0.70  thf('52', plain, ($false), inference('simplify', [status(thm)], ['51'])).
% 0.50/0.70  
% 0.50/0.70  % SZS output end Refutation
% 0.50/0.70  
% 0.50/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
