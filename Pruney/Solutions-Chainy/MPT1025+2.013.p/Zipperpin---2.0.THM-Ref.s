%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XfRQDcEJcm

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:44 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 214 expanded)
%              Number of leaves         :   52 (  86 expanded)
%              Depth                    :   16
%              Number of atoms          :  867 (2588 expanded)
%              Number of equality atoms :   45 ( 105 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

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
    ! [X53: $i,X54: $i,X55: $i,X56: $i] :
      ( ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) )
      | ( ( k7_relset_1 @ X54 @ X55 @ X53 @ X56 )
        = ( k9_relat_1 @ X53 @ X56 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0 )
      = ( k9_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
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
    ! [X35: $i,X36: $i,X38: $i,X39: $i] :
      ( ( X38
       != ( k9_relat_1 @ X36 @ X35 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X39 @ X35 @ X36 ) @ X39 @ X35 @ X36 )
      | ~ ( r2_hidden @ X39 @ X38 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X35: $i,X36: $i,X39: $i] :
      ( ~ ( v1_relat_1 @ X36 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( r2_hidden @ X39 @ ( k9_relat_1 @ X36 @ X35 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X39 @ X35 @ X36 ) @ X39 @ X35 @ X36 ) ) ),
    inference(simplify,[status(thm)],['5'])).

thf('7',plain,
    ( ( zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_E_2 @ sk_C @ sk_D_2 )
    | ~ ( v1_funct_1 @ sk_D_2 )
    | ~ ( v1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['4','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_D_2 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('10',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ( v1_relat_1 @ X44 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('11',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_E_2 @ sk_C @ sk_D_2 ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('13',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ X30 @ X32 )
      | ~ ( zip_tseitin_0 @ X30 @ X31 @ X32 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('14',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_C ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X65: $i] :
      ( ( sk_E_2
       != ( k1_funct_1 @ sk_D_2 @ X65 ) )
      | ~ ( r2_hidden @ X65 @ sk_C )
      | ~ ( m1_subset_1 @ X65 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_A )
    | ( sk_E_2
     != ( k1_funct_1 @ sk_D_2 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_E_2 @ sk_C @ sk_D_2 ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('18',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( r2_hidden @ X30 @ ( k1_relat_1 @ X29 ) )
      | ~ ( zip_tseitin_0 @ X30 @ X31 @ X32 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('19',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
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

thf(zf_stmt_4,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_2 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('21',plain,(
    ! [X59: $i,X60: $i,X61: $i] :
      ( ~ ( v1_funct_2 @ X61 @ X59 @ X60 )
      | ( X59
        = ( k1_relset_1 @ X59 @ X60 @ X61 ) )
      | ~ ( zip_tseitin_2 @ X61 @ X60 @ X59 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf('22',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('24',plain,(
    ! [X50: $i,X51: $i,X52: $i] :
      ( ( ( k1_relset_1 @ X51 @ X52 @ X50 )
        = ( k1_relat_1 @ X50 ) )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X51 @ X52 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('25',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_2 )
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_2 ) ) ),
    inference(demod,[status(thm)],['22','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('28',plain,(
    ! [X62: $i,X63: $i,X64: $i] :
      ( ~ ( zip_tseitin_1 @ X62 @ X63 )
      | ( zip_tseitin_2 @ X64 @ X62 @ X63 )
      | ~ ( m1_subset_1 @ X64 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X63 @ X62 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('29',plain,
    ( ( zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X57: $i,X58: $i] :
      ( ( zip_tseitin_1 @ X57 @ X58 )
      | ( X57 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('31',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('32',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['30','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( zip_tseitin_1 @ sk_B @ X0 ) ) ),
    inference('sup+',[status(thm)],['33','34'])).

thf(cc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) )
         => ( v5_relat_1 @ C @ A ) ) ) )).

thf('36',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v5_relat_1 @ X12 @ X14 )
      | ~ ( v5_relat_1 @ X13 @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc6_relat_1])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ sk_B @ X1 )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v5_relat_1 @ k1_xboole_0 @ X0 )
      | ( v5_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('39',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['38'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('40',plain,(
    ! [X17: $i,X18: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('41',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['39','40'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('42',plain,(
    ! [X6: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('43',plain,(
    ! [X47: $i,X48: $i,X49: $i] :
      ( ( v5_relat_1 @ X47 @ X49 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X48 @ X49 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('44',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ sk_B @ X1 )
      | ( v5_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference(demod,[status(thm)],['37','41','44'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('46',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v5_relat_1 @ X15 @ X16 )
      | ( r1_tarski @ ( k2_relat_1 @ X15 ) @ X16 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ sk_B @ X1 )
      | ~ ( v1_relat_1 @ sk_D_2 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_1 @ sk_B @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ X0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
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

thf('51',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( r2_hidden @ X21 @ ( k9_relat_1 @ X22 @ X20 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X22 @ X20 @ X21 ) @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('52',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_2 ) @ sk_E_2 ) @ sk_D_2 ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('54',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_2 @ sk_C @ sk_E_2 ) @ sk_E_2 ) @ sk_D_2 ),
    inference(demod,[status(thm)],['52','53'])).

thf(t20_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C )
       => ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ) )).

thf('55',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X26 @ X27 ) @ X28 )
      | ( r2_hidden @ X27 @ ( k2_relat_1 @ X28 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t20_relat_1])).

thf('56',plain,
    ( ~ ( v1_relat_1 @ sk_D_2 )
    | ( r2_hidden @ sk_E_2 @ ( k2_relat_1 @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['9','10'])).

thf('58',plain,(
    r2_hidden @ sk_E_2 @ ( k2_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('59',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( r2_hidden @ X42 @ X43 )
      | ~ ( r1_tarski @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('60',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_2 ) @ sk_E_2 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( zip_tseitin_1 @ sk_B @ X0 ) ),
    inference('sup-',[status(thm)],['49','60'])).

thf('62',plain,(
    zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['29','61'])).

thf('63',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_2 ) ),
    inference(demod,[status(thm)],['26','62'])).

thf('64',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_A ),
    inference(demod,[status(thm)],['19','63'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('65',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('66',plain,(
    m1_subset_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_A ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) @ sk_E_2 @ sk_C @ sk_D_2 ),
    inference(demod,[status(thm)],['7','8','11'])).

thf('68',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( X31
        = ( k1_funct_1 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_0 @ X30 @ X31 @ X32 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('69',plain,
    ( sk_E_2
    = ( k1_funct_1 @ sk_D_2 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2 ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    sk_E_2 != sk_E_2 ),
    inference(demod,[status(thm)],['16','66','69'])).

thf('71',plain,(
    $false ),
    inference(simplify,[status(thm)],['70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.XfRQDcEJcm
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:30:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.60/0.78  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.60/0.78  % Solved by: fo/fo7.sh
% 0.60/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.78  % done 400 iterations in 0.328s
% 0.60/0.78  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.60/0.78  % SZS output start Refutation
% 0.60/0.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.60/0.78  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.60/0.78  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.60/0.78  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.60/0.78  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.60/0.78  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.60/0.78  thf(sk_D_2_type, type, sk_D_2: $i).
% 0.60/0.78  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.60/0.78  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.60/0.78  thf(sk_C_type, type, sk_C: $i).
% 0.60/0.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.78  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.60/0.78  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.60/0.78  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.60/0.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.78  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.60/0.78  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.60/0.78  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.60/0.78  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.60/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.60/0.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.60/0.78  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.60/0.78  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.78  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.60/0.78  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.60/0.78  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.60/0.78  thf(t116_funct_2, conjecture,
% 0.60/0.78    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.78     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.60/0.78         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.60/0.78       ( ![E:$i]:
% 0.60/0.78         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.60/0.78              ( ![F:$i]:
% 0.60/0.78                ( ( m1_subset_1 @ F @ A ) =>
% 0.60/0.78                  ( ~( ( r2_hidden @ F @ C ) & 
% 0.60/0.78                       ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ))).
% 0.60/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.78    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.78        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.60/0.78            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.60/0.78          ( ![E:$i]:
% 0.60/0.78            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.60/0.78                 ( ![F:$i]:
% 0.60/0.78                   ( ( m1_subset_1 @ F @ A ) =>
% 0.60/0.78                     ( ~( ( r2_hidden @ F @ C ) & 
% 0.60/0.78                          ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) )),
% 0.60/0.78    inference('cnf.neg', [status(esa)], [t116_funct_2])).
% 0.60/0.78  thf('0', plain,
% 0.60/0.78      ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ sk_C))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('1', plain,
% 0.60/0.78      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf(redefinition_k7_relset_1, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.78       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.60/0.78  thf('2', plain,
% 0.60/0.78      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i]:
% 0.60/0.78         (~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55)))
% 0.60/0.78          | ((k7_relset_1 @ X54 @ X55 @ X53 @ X56) = (k9_relat_1 @ X53 @ X56)))),
% 0.60/0.78      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.60/0.78  thf('3', plain,
% 0.60/0.78      (![X0 : $i]:
% 0.60/0.78         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_2 @ X0)
% 0.60/0.78           = (k9_relat_1 @ sk_D_2 @ X0))),
% 0.60/0.78      inference('sup-', [status(thm)], ['1', '2'])).
% 0.60/0.78  thf('4', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.60/0.78      inference('demod', [status(thm)], ['0', '3'])).
% 0.60/0.78  thf(d12_funct_1, axiom,
% 0.60/0.78    (![A:$i]:
% 0.60/0.78     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.60/0.78       ( ![B:$i,C:$i]:
% 0.60/0.78         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.60/0.78           ( ![D:$i]:
% 0.60/0.78             ( ( r2_hidden @ D @ C ) <=>
% 0.60/0.78               ( ?[E:$i]:
% 0.60/0.78                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 0.60/0.78                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 0.60/0.78  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.60/0.78  thf(zf_stmt_2, axiom,
% 0.60/0.78    (![E:$i,D:$i,B:$i,A:$i]:
% 0.60/0.78     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.60/0.78       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 0.60/0.78         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 0.60/0.78  thf(zf_stmt_3, axiom,
% 0.60/0.78    (![A:$i]:
% 0.60/0.78     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.60/0.78       ( ![B:$i,C:$i]:
% 0.60/0.78         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.60/0.78           ( ![D:$i]:
% 0.60/0.78             ( ( r2_hidden @ D @ C ) <=>
% 0.60/0.78               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 0.60/0.78  thf('5', plain,
% 0.60/0.78      (![X35 : $i, X36 : $i, X38 : $i, X39 : $i]:
% 0.60/0.78         (((X38) != (k9_relat_1 @ X36 @ X35))
% 0.60/0.78          | (zip_tseitin_0 @ (sk_E_1 @ X39 @ X35 @ X36) @ X39 @ X35 @ X36)
% 0.60/0.78          | ~ (r2_hidden @ X39 @ X38)
% 0.60/0.78          | ~ (v1_funct_1 @ X36)
% 0.60/0.78          | ~ (v1_relat_1 @ X36))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.60/0.78  thf('6', plain,
% 0.60/0.78      (![X35 : $i, X36 : $i, X39 : $i]:
% 0.60/0.78         (~ (v1_relat_1 @ X36)
% 0.60/0.78          | ~ (v1_funct_1 @ X36)
% 0.60/0.78          | ~ (r2_hidden @ X39 @ (k9_relat_1 @ X36 @ X35))
% 0.60/0.78          | (zip_tseitin_0 @ (sk_E_1 @ X39 @ X35 @ X36) @ X39 @ X35 @ X36))),
% 0.60/0.78      inference('simplify', [status(thm)], ['5'])).
% 0.60/0.78  thf('7', plain,
% 0.60/0.78      (((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_E_2 @ sk_C @ 
% 0.60/0.78         sk_D_2)
% 0.60/0.78        | ~ (v1_funct_1 @ sk_D_2)
% 0.60/0.78        | ~ (v1_relat_1 @ sk_D_2))),
% 0.60/0.78      inference('sup-', [status(thm)], ['4', '6'])).
% 0.60/0.78  thf('8', plain, ((v1_funct_1 @ sk_D_2)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('9', plain,
% 0.60/0.78      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf(cc1_relset_1, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i]:
% 0.60/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.78       ( v1_relat_1 @ C ) ))).
% 0.60/0.78  thf('10', plain,
% 0.60/0.78      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.60/0.78         ((v1_relat_1 @ X44)
% 0.60/0.78          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46))))),
% 0.60/0.78      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.60/0.78  thf('11', plain, ((v1_relat_1 @ sk_D_2)),
% 0.60/0.78      inference('sup-', [status(thm)], ['9', '10'])).
% 0.60/0.78  thf('12', plain,
% 0.60/0.78      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_E_2 @ sk_C @ 
% 0.60/0.78        sk_D_2)),
% 0.60/0.78      inference('demod', [status(thm)], ['7', '8', '11'])).
% 0.60/0.78  thf('13', plain,
% 0.60/0.78      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.60/0.78         ((r2_hidden @ X30 @ X32) | ~ (zip_tseitin_0 @ X30 @ X31 @ X32 @ X29))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.60/0.78  thf('14', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_C)),
% 0.60/0.78      inference('sup-', [status(thm)], ['12', '13'])).
% 0.60/0.78  thf('15', plain,
% 0.60/0.78      (![X65 : $i]:
% 0.60/0.78         (((sk_E_2) != (k1_funct_1 @ sk_D_2 @ X65))
% 0.60/0.78          | ~ (r2_hidden @ X65 @ sk_C)
% 0.60/0.78          | ~ (m1_subset_1 @ X65 @ sk_A))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('16', plain,
% 0.60/0.78      ((~ (m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_A)
% 0.60/0.78        | ((sk_E_2)
% 0.60/0.78            != (k1_funct_1 @ sk_D_2 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2))))),
% 0.60/0.78      inference('sup-', [status(thm)], ['14', '15'])).
% 0.60/0.78  thf('17', plain,
% 0.60/0.78      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_E_2 @ sk_C @ 
% 0.60/0.78        sk_D_2)),
% 0.60/0.78      inference('demod', [status(thm)], ['7', '8', '11'])).
% 0.60/0.78  thf('18', plain,
% 0.60/0.78      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.60/0.78         ((r2_hidden @ X30 @ (k1_relat_1 @ X29))
% 0.60/0.78          | ~ (zip_tseitin_0 @ X30 @ X31 @ X32 @ X29))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.60/0.78  thf('19', plain,
% 0.60/0.78      ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ (k1_relat_1 @ sk_D_2))),
% 0.60/0.78      inference('sup-', [status(thm)], ['17', '18'])).
% 0.60/0.78  thf('20', plain, ((v1_funct_2 @ sk_D_2 @ sk_A @ sk_B)),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf(d1_funct_2, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i]:
% 0.60/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.78       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.60/0.78           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.60/0.78             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.60/0.78         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.60/0.78           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.60/0.78             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.60/0.78  thf(zf_stmt_4, axiom,
% 0.60/0.78    (![C:$i,B:$i,A:$i]:
% 0.60/0.78     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.60/0.78       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.60/0.78  thf('21', plain,
% 0.60/0.78      (![X59 : $i, X60 : $i, X61 : $i]:
% 0.60/0.78         (~ (v1_funct_2 @ X61 @ X59 @ X60)
% 0.60/0.78          | ((X59) = (k1_relset_1 @ X59 @ X60 @ X61))
% 0.60/0.78          | ~ (zip_tseitin_2 @ X61 @ X60 @ X59))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.60/0.78  thf('22', plain,
% 0.60/0.78      ((~ (zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A)
% 0.60/0.78        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_2)))),
% 0.60/0.78      inference('sup-', [status(thm)], ['20', '21'])).
% 0.60/0.78  thf('23', plain,
% 0.60/0.78      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf(redefinition_k1_relset_1, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i]:
% 0.60/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.78       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.60/0.78  thf('24', plain,
% 0.60/0.78      (![X50 : $i, X51 : $i, X52 : $i]:
% 0.60/0.78         (((k1_relset_1 @ X51 @ X52 @ X50) = (k1_relat_1 @ X50))
% 0.60/0.78          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X51 @ X52))))),
% 0.60/0.78      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.60/0.78  thf('25', plain,
% 0.60/0.78      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_2) = (k1_relat_1 @ sk_D_2))),
% 0.60/0.78      inference('sup-', [status(thm)], ['23', '24'])).
% 0.60/0.78  thf('26', plain,
% 0.60/0.78      ((~ (zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A)
% 0.60/0.78        | ((sk_A) = (k1_relat_1 @ sk_D_2)))),
% 0.60/0.78      inference('demod', [status(thm)], ['22', '25'])).
% 0.60/0.78  thf('27', plain,
% 0.60/0.78      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf(zf_stmt_5, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.60/0.78  thf(zf_stmt_6, type, zip_tseitin_1 : $i > $i > $o).
% 0.60/0.78  thf(zf_stmt_7, axiom,
% 0.60/0.78    (![B:$i,A:$i]:
% 0.60/0.78     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.60/0.78       ( zip_tseitin_1 @ B @ A ) ))).
% 0.60/0.78  thf(zf_stmt_8, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i]:
% 0.60/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.78       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.60/0.78         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.60/0.78           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.60/0.78             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.60/0.78  thf('28', plain,
% 0.60/0.78      (![X62 : $i, X63 : $i, X64 : $i]:
% 0.60/0.78         (~ (zip_tseitin_1 @ X62 @ X63)
% 0.60/0.78          | (zip_tseitin_2 @ X64 @ X62 @ X63)
% 0.60/0.78          | ~ (m1_subset_1 @ X64 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X63 @ X62))))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.60/0.78  thf('29', plain,
% 0.60/0.78      (((zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A)
% 0.60/0.78        | ~ (zip_tseitin_1 @ sk_B @ sk_A))),
% 0.60/0.78      inference('sup-', [status(thm)], ['27', '28'])).
% 0.60/0.78  thf('30', plain,
% 0.60/0.78      (![X57 : $i, X58 : $i]:
% 0.60/0.78         ((zip_tseitin_1 @ X57 @ X58) | ((X57) = (k1_xboole_0)))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.60/0.78  thf(t113_zfmisc_1, axiom,
% 0.60/0.78    (![A:$i,B:$i]:
% 0.60/0.78     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.60/0.78       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.60/0.78  thf('31', plain,
% 0.60/0.78      (![X4 : $i, X5 : $i]:
% 0.60/0.78         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 0.60/0.78      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.60/0.78  thf('32', plain,
% 0.60/0.78      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.60/0.78      inference('simplify', [status(thm)], ['31'])).
% 0.60/0.78  thf('33', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.78         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_1 @ X0 @ X2))),
% 0.60/0.78      inference('sup+', [status(thm)], ['30', '32'])).
% 0.60/0.78  thf('34', plain,
% 0.60/0.78      ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.78  thf('35', plain,
% 0.60/0.78      (![X0 : $i]:
% 0.60/0.78         ((m1_subset_1 @ sk_D_2 @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.60/0.78          | (zip_tseitin_1 @ sk_B @ X0))),
% 0.60/0.78      inference('sup+', [status(thm)], ['33', '34'])).
% 0.60/0.78  thf(cc6_relat_1, axiom,
% 0.60/0.78    (![A:$i,B:$i]:
% 0.60/0.78     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.60/0.78       ( ![C:$i]:
% 0.60/0.78         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ B ) ) => ( v5_relat_1 @ C @ A ) ) ) ))).
% 0.60/0.78  thf('36', plain,
% 0.60/0.78      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.60/0.78         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 0.60/0.78          | (v5_relat_1 @ X12 @ X14)
% 0.60/0.78          | ~ (v5_relat_1 @ X13 @ X14)
% 0.60/0.78          | ~ (v1_relat_1 @ X13))),
% 0.60/0.78      inference('cnf', [status(esa)], [cc6_relat_1])).
% 0.60/0.78  thf('37', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         ((zip_tseitin_1 @ sk_B @ X1)
% 0.60/0.78          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.60/0.78          | ~ (v5_relat_1 @ k1_xboole_0 @ X0)
% 0.60/0.78          | (v5_relat_1 @ sk_D_2 @ X0))),
% 0.60/0.78      inference('sup-', [status(thm)], ['35', '36'])).
% 0.60/0.78  thf('38', plain,
% 0.60/0.78      (![X4 : $i, X5 : $i]:
% 0.60/0.78         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 0.60/0.78      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.60/0.78  thf('39', plain,
% 0.60/0.78      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 0.60/0.78      inference('simplify', [status(thm)], ['38'])).
% 0.60/0.78  thf(fc6_relat_1, axiom,
% 0.60/0.78    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.60/0.78  thf('40', plain,
% 0.60/0.78      (![X17 : $i, X18 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X17 @ X18))),
% 0.60/0.78      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.60/0.78  thf('41', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.60/0.78      inference('sup+', [status(thm)], ['39', '40'])).
% 0.60/0.78  thf(t4_subset_1, axiom,
% 0.60/0.78    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.60/0.78  thf('42', plain,
% 0.60/0.78      (![X6 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X6))),
% 0.60/0.78      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.60/0.78  thf(cc2_relset_1, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i]:
% 0.60/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.78       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.60/0.78  thf('43', plain,
% 0.60/0.78      (![X47 : $i, X48 : $i, X49 : $i]:
% 0.60/0.78         ((v5_relat_1 @ X47 @ X49)
% 0.60/0.78          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X48 @ X49))))),
% 0.60/0.78      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.60/0.78  thf('44', plain, (![X0 : $i]: (v5_relat_1 @ k1_xboole_0 @ X0)),
% 0.60/0.78      inference('sup-', [status(thm)], ['42', '43'])).
% 0.60/0.78  thf('45', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         ((zip_tseitin_1 @ sk_B @ X1) | (v5_relat_1 @ sk_D_2 @ X0))),
% 0.60/0.78      inference('demod', [status(thm)], ['37', '41', '44'])).
% 0.60/0.78  thf(d19_relat_1, axiom,
% 0.60/0.78    (![A:$i,B:$i]:
% 0.60/0.78     ( ( v1_relat_1 @ B ) =>
% 0.60/0.78       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.60/0.78  thf('46', plain,
% 0.60/0.78      (![X15 : $i, X16 : $i]:
% 0.60/0.78         (~ (v5_relat_1 @ X15 @ X16)
% 0.60/0.78          | (r1_tarski @ (k2_relat_1 @ X15) @ X16)
% 0.60/0.78          | ~ (v1_relat_1 @ X15))),
% 0.60/0.78      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.60/0.78  thf('47', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         ((zip_tseitin_1 @ sk_B @ X1)
% 0.60/0.78          | ~ (v1_relat_1 @ sk_D_2)
% 0.60/0.78          | (r1_tarski @ (k2_relat_1 @ sk_D_2) @ X0))),
% 0.60/0.78      inference('sup-', [status(thm)], ['45', '46'])).
% 0.60/0.78  thf('48', plain, ((v1_relat_1 @ sk_D_2)),
% 0.60/0.78      inference('sup-', [status(thm)], ['9', '10'])).
% 0.60/0.78  thf('49', plain,
% 0.60/0.78      (![X0 : $i, X1 : $i]:
% 0.60/0.78         ((zip_tseitin_1 @ sk_B @ X1)
% 0.60/0.78          | (r1_tarski @ (k2_relat_1 @ sk_D_2) @ X0))),
% 0.60/0.78      inference('demod', [status(thm)], ['47', '48'])).
% 0.60/0.78  thf('50', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_2 @ sk_C))),
% 0.60/0.78      inference('demod', [status(thm)], ['0', '3'])).
% 0.60/0.78  thf(t143_relat_1, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i]:
% 0.60/0.78     ( ( v1_relat_1 @ C ) =>
% 0.60/0.78       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.60/0.78         ( ?[D:$i]:
% 0.60/0.78           ( ( r2_hidden @ D @ B ) & 
% 0.60/0.78             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.60/0.78             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.60/0.78  thf('51', plain,
% 0.60/0.78      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.60/0.78         (~ (r2_hidden @ X21 @ (k9_relat_1 @ X22 @ X20))
% 0.60/0.78          | (r2_hidden @ (k4_tarski @ (sk_D @ X22 @ X20 @ X21) @ X21) @ X22)
% 0.60/0.78          | ~ (v1_relat_1 @ X22))),
% 0.60/0.78      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.60/0.78  thf('52', plain,
% 0.60/0.78      ((~ (v1_relat_1 @ sk_D_2)
% 0.60/0.78        | (r2_hidden @ 
% 0.60/0.78           (k4_tarski @ (sk_D @ sk_D_2 @ sk_C @ sk_E_2) @ sk_E_2) @ sk_D_2))),
% 0.60/0.78      inference('sup-', [status(thm)], ['50', '51'])).
% 0.60/0.78  thf('53', plain, ((v1_relat_1 @ sk_D_2)),
% 0.60/0.78      inference('sup-', [status(thm)], ['9', '10'])).
% 0.60/0.78  thf('54', plain,
% 0.60/0.78      ((r2_hidden @ (k4_tarski @ (sk_D @ sk_D_2 @ sk_C @ sk_E_2) @ sk_E_2) @ 
% 0.60/0.78        sk_D_2)),
% 0.60/0.78      inference('demod', [status(thm)], ['52', '53'])).
% 0.60/0.78  thf(t20_relat_1, axiom,
% 0.60/0.78    (![A:$i,B:$i,C:$i]:
% 0.60/0.78     ( ( v1_relat_1 @ C ) =>
% 0.60/0.78       ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ C ) =>
% 0.60/0.78         ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.60/0.78           ( r2_hidden @ B @ ( k2_relat_1 @ C ) ) ) ) ))).
% 0.60/0.78  thf('55', plain,
% 0.60/0.78      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.60/0.78         (~ (r2_hidden @ (k4_tarski @ X26 @ X27) @ X28)
% 0.60/0.78          | (r2_hidden @ X27 @ (k2_relat_1 @ X28))
% 0.60/0.78          | ~ (v1_relat_1 @ X28))),
% 0.60/0.78      inference('cnf', [status(esa)], [t20_relat_1])).
% 0.60/0.78  thf('56', plain,
% 0.60/0.78      ((~ (v1_relat_1 @ sk_D_2) | (r2_hidden @ sk_E_2 @ (k2_relat_1 @ sk_D_2)))),
% 0.60/0.78      inference('sup-', [status(thm)], ['54', '55'])).
% 0.60/0.78  thf('57', plain, ((v1_relat_1 @ sk_D_2)),
% 0.60/0.78      inference('sup-', [status(thm)], ['9', '10'])).
% 0.60/0.78  thf('58', plain, ((r2_hidden @ sk_E_2 @ (k2_relat_1 @ sk_D_2))),
% 0.60/0.78      inference('demod', [status(thm)], ['56', '57'])).
% 0.60/0.78  thf(t7_ordinal1, axiom,
% 0.60/0.78    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.60/0.78  thf('59', plain,
% 0.60/0.78      (![X42 : $i, X43 : $i]:
% 0.60/0.78         (~ (r2_hidden @ X42 @ X43) | ~ (r1_tarski @ X43 @ X42))),
% 0.60/0.78      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.60/0.78  thf('60', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_D_2) @ sk_E_2)),
% 0.60/0.78      inference('sup-', [status(thm)], ['58', '59'])).
% 0.60/0.78  thf('61', plain, (![X0 : $i]: (zip_tseitin_1 @ sk_B @ X0)),
% 0.60/0.78      inference('sup-', [status(thm)], ['49', '60'])).
% 0.60/0.78  thf('62', plain, ((zip_tseitin_2 @ sk_D_2 @ sk_B @ sk_A)),
% 0.60/0.78      inference('demod', [status(thm)], ['29', '61'])).
% 0.60/0.78  thf('63', plain, (((sk_A) = (k1_relat_1 @ sk_D_2))),
% 0.60/0.78      inference('demod', [status(thm)], ['26', '62'])).
% 0.60/0.78  thf('64', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_A)),
% 0.60/0.78      inference('demod', [status(thm)], ['19', '63'])).
% 0.60/0.78  thf(t1_subset, axiom,
% 0.60/0.78    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.60/0.78  thf('65', plain,
% 0.60/0.78      (![X7 : $i, X8 : $i]: ((m1_subset_1 @ X7 @ X8) | ~ (r2_hidden @ X7 @ X8))),
% 0.60/0.78      inference('cnf', [status(esa)], [t1_subset])).
% 0.60/0.78  thf('66', plain, ((m1_subset_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_A)),
% 0.60/0.78      inference('sup-', [status(thm)], ['64', '65'])).
% 0.60/0.78  thf('67', plain,
% 0.60/0.78      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2) @ sk_E_2 @ sk_C @ 
% 0.60/0.78        sk_D_2)),
% 0.60/0.78      inference('demod', [status(thm)], ['7', '8', '11'])).
% 0.60/0.78  thf('68', plain,
% 0.60/0.78      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.60/0.78         (((X31) = (k1_funct_1 @ X29 @ X30))
% 0.60/0.78          | ~ (zip_tseitin_0 @ X30 @ X31 @ X32 @ X29))),
% 0.60/0.78      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.60/0.78  thf('69', plain,
% 0.60/0.78      (((sk_E_2) = (k1_funct_1 @ sk_D_2 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_2)))),
% 0.60/0.78      inference('sup-', [status(thm)], ['67', '68'])).
% 0.60/0.78  thf('70', plain, (((sk_E_2) != (sk_E_2))),
% 0.60/0.78      inference('demod', [status(thm)], ['16', '66', '69'])).
% 0.60/0.78  thf('71', plain, ($false), inference('simplify', [status(thm)], ['70'])).
% 0.60/0.78  
% 0.60/0.78  % SZS output end Refutation
% 0.60/0.78  
% 0.60/0.79  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
