%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rwWnisi7DS

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 228 expanded)
%              Number of leaves         :   47 (  88 expanded)
%              Depth                    :   21
%              Number of atoms          :  877 (3033 expanded)
%              Number of equality atoms :   53 ( 202 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_2_type,type,(
    sk_D_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_E_3_type,type,(
    sk_E_3: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t16_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( ( r2_hidden @ E @ A )
                    & ( D
                      = ( k1_funct_1 @ C @ E ) ) ) )
       => ( ( k2_relset_1 @ A @ B @ C )
          = B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ! [D: $i] :
              ~ ( ( r2_hidden @ D @ B )
                & ! [E: $i] :
                    ~ ( ( r2_hidden @ E @ A )
                      & ( D
                        = ( k1_funct_1 @ C @ E ) ) ) )
         => ( ( k2_relset_1 @ A @ B @ C )
            = B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t16_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('1',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k2_relset_1 @ X33 @ X34 @ X32 )
        = ( k2_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('2',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t23_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ! [D: $i] :
            ~ ( ( r2_hidden @ D @ B )
              & ! [E: $i] :
                  ~ ( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) )
      <=> ( ( k2_relset_1 @ A @ B @ C )
          = B ) ) ) )).

thf('5',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( r2_hidden @ ( sk_D_2 @ X37 @ X35 ) @ X35 )
      | ( ( k2_relset_1 @ X36 @ X35 @ X37 )
        = X35 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_relset_1])).

thf('6',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
      = sk_B )
    | ( r2_hidden @ ( sk_D_2 @ sk_C @ sk_B ) @ sk_B ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('8',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = sk_B )
    | ( r2_hidden @ ( sk_D_2 @ sk_C @ sk_B ) @ sk_B ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
 != sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('11',plain,(
    ( k2_relat_1 @ sk_C )
 != sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ ( sk_D_2 @ sk_C @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['8','11'])).

thf('13',plain,(
    ! [X48: $i] :
      ( ~ ( r2_hidden @ X48 @ sk_B )
      | ( r2_hidden @ ( sk_E_3 @ X48 ) @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    r2_hidden @ ( sk_E_3 @ ( sk_D_2 @ sk_C @ sk_B ) ) @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    r2_hidden @ ( sk_E_3 @ ( sk_D_2 @ sk_C @ sk_B ) ) @ sk_A ),
    inference('sup-',[status(thm)],['12','13'])).

thf('16',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
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

thf('17',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ( X42
        = ( k1_relset_1 @ X42 @ X43 @ X44 ) )
      | ~ ( zip_tseitin_2 @ X44 @ X43 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('18',plain,
    ( ~ ( zip_tseitin_2 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v5_relat_1 @ X26 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('21',plain,(
    v5_relat_1 @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['19','20'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('22',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v5_relat_1 @ X4 @ X5 )
      | ( r1_tarski @ ( k2_relat_1 @ X4 ) @ X5 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('25',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( v1_relat_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('26',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['23','26'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('28',plain,(
    ! [X40: $i,X41: $i] :
      ( ( zip_tseitin_1 @ X40 @ X41 )
      | ( X40 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('29',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('32',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_1 @ X1 @ X2 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ sk_C )
        = sk_B )
      | ( zip_tseitin_1 @ sk_B @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('35',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( zip_tseitin_1 @ X45 @ X46 )
      | ( zip_tseitin_2 @ X47 @ X45 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('36',plain,
    ( ( zip_tseitin_2 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k2_relat_1 @ sk_C )
      = sk_B )
    | ( zip_tseitin_2 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ( k2_relat_1 @ sk_C )
 != sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('39',plain,(
    zip_tseitin_2 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('41',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( ( k1_relset_1 @ X30 @ X31 @ X29 )
        = ( k1_relat_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('42',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['18','39','42'])).

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

thf(zf_stmt_6,axiom,(
    ! [E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ E @ D @ B @ A )
    <=> ( ( D
          = ( k1_funct_1 @ A @ E ) )
        & ( r2_hidden @ E @ B )
        & ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ) )).

thf('44',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( zip_tseitin_0 @ X11 @ X12 @ X13 @ X14 )
      | ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X14 ) )
      | ~ ( r2_hidden @ X11 @ X13 )
      | ( X12
       != ( k1_funct_1 @ X14 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('45',plain,(
    ! [X11: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X11 @ X13 )
      | ~ ( r2_hidden @ X11 @ ( k1_relat_1 @ X14 ) )
      | ( zip_tseitin_0 @ X11 @ ( k1_funct_1 @ X14 @ X11 ) @ X13 @ X14 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ( zip_tseitin_0 @ X0 @ ( k1_funct_1 @ sk_C @ X0 ) @ X1 @ sk_C )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_E_3 @ ( sk_D_2 @ sk_C @ sk_B ) ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_E_3 @ ( sk_D_2 @ sk_C @ sk_B ) ) @ ( k1_funct_1 @ sk_C @ ( sk_E_3 @ ( sk_D_2 @ sk_C @ sk_B ) ) ) @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','46'])).

thf('48',plain,(
    r2_hidden @ ( sk_D_2 @ sk_C @ sk_B ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['8','11'])).

thf('49',plain,(
    ! [X48: $i] :
      ( ~ ( r2_hidden @ X48 @ sk_B )
      | ( X48
        = ( k1_funct_1 @ sk_C @ ( sk_E_3 @ X48 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( sk_D_2 @ sk_C @ sk_B )
    = ( k1_funct_1 @ sk_C @ ( sk_E_3 @ ( sk_D_2 @ sk_C @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ ( sk_E_3 @ ( sk_D_2 @ sk_C @ sk_B ) ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_E_3 @ ( sk_D_2 @ sk_C @ sk_B ) ) @ ( sk_D_2 @ sk_C @ sk_B ) @ X0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['47','50'])).

thf('52',plain,(
    zip_tseitin_0 @ ( sk_E_3 @ ( sk_D_2 @ sk_C @ sk_B ) ) @ ( sk_D_2 @ sk_C @ sk_B ) @ sk_A @ sk_C ),
    inference('sup-',[status(thm)],['14','51'])).

thf(zf_stmt_7,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

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

thf('53',plain,(
    ! [X16: $i,X17: $i,X19: $i,X21: $i,X22: $i] :
      ( ( X19
       != ( k9_relat_1 @ X17 @ X16 ) )
      | ( r2_hidden @ X21 @ X19 )
      | ~ ( zip_tseitin_0 @ X22 @ X21 @ X16 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('54',plain,(
    ! [X16: $i,X17: $i,X21: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( zip_tseitin_0 @ X22 @ X21 @ X16 @ X17 )
      | ( r2_hidden @ X21 @ ( k9_relat_1 @ X17 @ X16 ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( r2_hidden @ ( sk_D_2 @ sk_C @ sk_B ) @ ( k9_relat_1 @ sk_C @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['52','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['24','25'])).

thf('58',plain,(
    r2_hidden @ ( sk_D_2 @ sk_C @ sk_B ) @ ( k9_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('59',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X8 @ ( k9_relat_1 @ X9 @ X7 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X9 @ X7 @ X8 ) @ X8 ) @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('60',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_C @ sk_A @ ( sk_D_2 @ sk_C @ sk_B ) ) @ ( sk_D_2 @ sk_C @ sk_B ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['24','25'])).

thf('62',plain,(
    r2_hidden @ ( k4_tarski @ ( sk_D @ sk_C @ sk_A @ ( sk_D_2 @ sk_C @ sk_B ) ) @ ( sk_D_2 @ sk_C @ sk_B ) ) @ sk_C ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X35: $i,X36: $i,X37: $i,X39: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X39 @ ( sk_D_2 @ X37 @ X35 ) ) @ X37 )
      | ( ( k2_relset_1 @ X36 @ X35 @ X37 )
        = X35 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[t23_relset_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ( ( k2_relset_1 @ X0 @ sk_B @ sk_C )
        = sk_B ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference('sup-',[status(thm)],['3','64'])).

thf('66',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['2','65'])).

thf('67',plain,(
    ( k2_relat_1 @ sk_C )
 != sk_B ),
    inference(demod,[status(thm)],['9','10'])).

thf('68',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['66','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rwWnisi7DS
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:09:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.58  % Solved by: fo/fo7.sh
% 0.21/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.58  % done 138 iterations in 0.126s
% 0.21/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.58  % SZS output start Refutation
% 0.21/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.58  thf(sk_D_2_type, type, sk_D_2: $i > $i > $i).
% 0.21/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.21/0.58  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.21/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.58  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.21/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.58  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.21/0.58  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.21/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.58  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.58  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.58  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.58  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.58  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.58  thf(sk_E_3_type, type, sk_E_3: $i > $i).
% 0.21/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.58  thf(t16_funct_2, conjecture,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.58       ( ( ![D:$i]:
% 0.21/0.58           ( ~( ( r2_hidden @ D @ B ) & 
% 0.21/0.58                ( ![E:$i]:
% 0.21/0.58                  ( ~( ( r2_hidden @ E @ A ) & 
% 0.21/0.58                       ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.21/0.58         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.21/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.58    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.58        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.58            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.58          ( ( ![D:$i]:
% 0.21/0.58              ( ~( ( r2_hidden @ D @ B ) & 
% 0.21/0.58                   ( ![E:$i]:
% 0.21/0.58                     ( ~( ( r2_hidden @ E @ A ) & 
% 0.21/0.58                          ( ( D ) = ( k1_funct_1 @ C @ E ) ) ) ) ) ) ) ) =>
% 0.21/0.58            ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) )),
% 0.21/0.58    inference('cnf.neg', [status(esa)], [t16_funct_2])).
% 0.21/0.58  thf('0', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.58       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.58  thf('1', plain,
% 0.21/0.58      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.21/0.58         (((k2_relset_1 @ X33 @ X34 @ X32) = (k2_relat_1 @ X32))
% 0.21/0.58          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.21/0.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.58  thf('2', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.21/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.58  thf('3', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('4', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(t23_relset_1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.58       ( ( ![D:$i]:
% 0.21/0.58           ( ~( ( r2_hidden @ D @ B ) & 
% 0.21/0.58                ( ![E:$i]: ( ~( r2_hidden @ ( k4_tarski @ E @ D ) @ C ) ) ) ) ) ) <=>
% 0.21/0.58         ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ))).
% 0.21/0.58  thf('5', plain,
% 0.21/0.58      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.21/0.58         ((r2_hidden @ (sk_D_2 @ X37 @ X35) @ X35)
% 0.21/0.58          | ((k2_relset_1 @ X36 @ X35 @ X37) = (X35))
% 0.21/0.58          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 0.21/0.58      inference('cnf', [status(esa)], [t23_relset_1])).
% 0.21/0.58  thf('6', plain,
% 0.21/0.58      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))
% 0.21/0.58        | (r2_hidden @ (sk_D_2 @ sk_C @ sk_B) @ sk_B))),
% 0.21/0.58      inference('sup-', [status(thm)], ['4', '5'])).
% 0.21/0.58  thf('7', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.21/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.58  thf('8', plain,
% 0.21/0.58      ((((k2_relat_1 @ sk_C) = (sk_B))
% 0.21/0.58        | (r2_hidden @ (sk_D_2 @ sk_C @ sk_B) @ sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['6', '7'])).
% 0.21/0.58  thf('9', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('10', plain,
% 0.21/0.58      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.21/0.58      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.58  thf('11', plain, (((k2_relat_1 @ sk_C) != (sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.58  thf('12', plain, ((r2_hidden @ (sk_D_2 @ sk_C @ sk_B) @ sk_B)),
% 0.21/0.58      inference('simplify_reflect-', [status(thm)], ['8', '11'])).
% 0.21/0.58  thf('13', plain,
% 0.21/0.58      (![X48 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X48 @ sk_B) | (r2_hidden @ (sk_E_3 @ X48) @ sk_A))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('14', plain, ((r2_hidden @ (sk_E_3 @ (sk_D_2 @ sk_C @ sk_B)) @ sk_A)),
% 0.21/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.58  thf('15', plain, ((r2_hidden @ (sk_E_3 @ (sk_D_2 @ sk_C @ sk_B)) @ sk_A)),
% 0.21/0.58      inference('sup-', [status(thm)], ['12', '13'])).
% 0.21/0.58  thf('16', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(d1_funct_2, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.58       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.58           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.21/0.58             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.58         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.58           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.21/0.58             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.58  thf(zf_stmt_1, axiom,
% 0.21/0.58    (![C:$i,B:$i,A:$i]:
% 0.21/0.58     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.21/0.58       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.58  thf('17', plain,
% 0.21/0.58      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.21/0.58         (~ (v1_funct_2 @ X44 @ X42 @ X43)
% 0.21/0.58          | ((X42) = (k1_relset_1 @ X42 @ X43 @ X44))
% 0.21/0.58          | ~ (zip_tseitin_2 @ X44 @ X43 @ X42))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.58  thf('18', plain,
% 0.21/0.58      ((~ (zip_tseitin_2 @ sk_C @ sk_B @ sk_A)
% 0.21/0.58        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.58  thf('19', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(cc2_relset_1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.58       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.58  thf('20', plain,
% 0.21/0.58      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.21/0.58         ((v5_relat_1 @ X26 @ X28)
% 0.21/0.58          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.21/0.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.58  thf('21', plain, ((v5_relat_1 @ sk_C @ sk_B)),
% 0.21/0.58      inference('sup-', [status(thm)], ['19', '20'])).
% 0.21/0.58  thf(d19_relat_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( v1_relat_1 @ B ) =>
% 0.21/0.58       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.58  thf('22', plain,
% 0.21/0.58      (![X4 : $i, X5 : $i]:
% 0.21/0.58         (~ (v5_relat_1 @ X4 @ X5)
% 0.21/0.58          | (r1_tarski @ (k2_relat_1 @ X4) @ X5)
% 0.21/0.58          | ~ (v1_relat_1 @ X4))),
% 0.21/0.58      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.58  thf('23', plain,
% 0.21/0.58      ((~ (v1_relat_1 @ sk_C) | (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B))),
% 0.21/0.58      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.58  thf('24', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(cc1_relset_1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.58       ( v1_relat_1 @ C ) ))).
% 0.21/0.58  thf('25', plain,
% 0.21/0.58      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.21/0.58         ((v1_relat_1 @ X23)
% 0.21/0.58          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.21/0.58      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.58  thf('26', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.58      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.58  thf('27', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.21/0.58      inference('demod', [status(thm)], ['23', '26'])).
% 0.21/0.58  thf(zf_stmt_2, axiom,
% 0.21/0.58    (![B:$i,A:$i]:
% 0.21/0.58     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.58       ( zip_tseitin_1 @ B @ A ) ))).
% 0.21/0.58  thf('28', plain,
% 0.21/0.58      (![X40 : $i, X41 : $i]:
% 0.21/0.58         ((zip_tseitin_1 @ X40 @ X41) | ((X40) = (k1_xboole_0)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.21/0.58  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.58  thf('29', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.21/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.58  thf('30', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.58         ((r1_tarski @ X0 @ X1) | (zip_tseitin_1 @ X0 @ X2))),
% 0.21/0.58      inference('sup+', [status(thm)], ['28', '29'])).
% 0.21/0.58  thf(d10_xboole_0, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.58  thf('31', plain,
% 0.21/0.58      (![X0 : $i, X2 : $i]:
% 0.21/0.58         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.21/0.58      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.58  thf('32', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.21/0.58         ((zip_tseitin_1 @ X1 @ X2) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.58  thf('33', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (((k2_relat_1 @ sk_C) = (sk_B)) | (zip_tseitin_1 @ sk_B @ X0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['27', '32'])).
% 0.21/0.58  thf('34', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(zf_stmt_3, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.21/0.58  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $o).
% 0.21/0.58  thf(zf_stmt_5, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.58       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.21/0.58         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.58           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.58             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.21/0.58  thf('35', plain,
% 0.21/0.58      (![X45 : $i, X46 : $i, X47 : $i]:
% 0.21/0.58         (~ (zip_tseitin_1 @ X45 @ X46)
% 0.21/0.58          | (zip_tseitin_2 @ X47 @ X45 @ X46)
% 0.21/0.58          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45))))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.58  thf('36', plain,
% 0.21/0.58      (((zip_tseitin_2 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_1 @ sk_B @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['34', '35'])).
% 0.21/0.58  thf('37', plain,
% 0.21/0.58      ((((k2_relat_1 @ sk_C) = (sk_B)) | (zip_tseitin_2 @ sk_C @ sk_B @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['33', '36'])).
% 0.21/0.58  thf('38', plain, (((k2_relat_1 @ sk_C) != (sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.58  thf('39', plain, ((zip_tseitin_2 @ sk_C @ sk_B @ sk_A)),
% 0.21/0.58      inference('simplify_reflect-', [status(thm)], ['37', '38'])).
% 0.21/0.58  thf('40', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.58       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.58  thf('41', plain,
% 0.21/0.58      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.21/0.58         (((k1_relset_1 @ X30 @ X31 @ X29) = (k1_relat_1 @ X29))
% 0.21/0.58          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.21/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.58  thf('42', plain,
% 0.21/0.58      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.21/0.58      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.58  thf('43', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.21/0.58      inference('demod', [status(thm)], ['18', '39', '42'])).
% 0.21/0.58  thf(d12_funct_1, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.21/0.58       ( ![B:$i,C:$i]:
% 0.21/0.58         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.21/0.58           ( ![D:$i]:
% 0.21/0.58             ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.58               ( ?[E:$i]:
% 0.21/0.58                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 0.21/0.58                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 0.21/0.58  thf(zf_stmt_6, axiom,
% 0.21/0.58    (![E:$i,D:$i,B:$i,A:$i]:
% 0.21/0.58     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.21/0.58       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 0.21/0.58         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 0.21/0.58  thf('44', plain,
% 0.21/0.58      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.21/0.58         ((zip_tseitin_0 @ X11 @ X12 @ X13 @ X14)
% 0.21/0.58          | ~ (r2_hidden @ X11 @ (k1_relat_1 @ X14))
% 0.21/0.58          | ~ (r2_hidden @ X11 @ X13)
% 0.21/0.58          | ((X12) != (k1_funct_1 @ X14 @ X11)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.21/0.58  thf('45', plain,
% 0.21/0.58      (![X11 : $i, X13 : $i, X14 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X11 @ X13)
% 0.21/0.58          | ~ (r2_hidden @ X11 @ (k1_relat_1 @ X14))
% 0.21/0.58          | (zip_tseitin_0 @ X11 @ (k1_funct_1 @ X14 @ X11) @ X13 @ X14))),
% 0.21/0.58      inference('simplify', [status(thm)], ['44'])).
% 0.21/0.58  thf('46', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X0 @ sk_A)
% 0.21/0.58          | (zip_tseitin_0 @ X0 @ (k1_funct_1 @ sk_C @ X0) @ X1 @ sk_C)
% 0.21/0.58          | ~ (r2_hidden @ X0 @ X1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['43', '45'])).
% 0.21/0.58  thf('47', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (r2_hidden @ (sk_E_3 @ (sk_D_2 @ sk_C @ sk_B)) @ X0)
% 0.21/0.58          | (zip_tseitin_0 @ (sk_E_3 @ (sk_D_2 @ sk_C @ sk_B)) @ 
% 0.21/0.58             (k1_funct_1 @ sk_C @ (sk_E_3 @ (sk_D_2 @ sk_C @ sk_B))) @ X0 @ 
% 0.21/0.58             sk_C))),
% 0.21/0.58      inference('sup-', [status(thm)], ['15', '46'])).
% 0.21/0.58  thf('48', plain, ((r2_hidden @ (sk_D_2 @ sk_C @ sk_B) @ sk_B)),
% 0.21/0.58      inference('simplify_reflect-', [status(thm)], ['8', '11'])).
% 0.21/0.58  thf('49', plain,
% 0.21/0.58      (![X48 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X48 @ sk_B)
% 0.21/0.58          | ((X48) = (k1_funct_1 @ sk_C @ (sk_E_3 @ X48))))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('50', plain,
% 0.21/0.58      (((sk_D_2 @ sk_C @ sk_B)
% 0.21/0.58         = (k1_funct_1 @ sk_C @ (sk_E_3 @ (sk_D_2 @ sk_C @ sk_B))))),
% 0.21/0.58      inference('sup-', [status(thm)], ['48', '49'])).
% 0.21/0.58  thf('51', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (r2_hidden @ (sk_E_3 @ (sk_D_2 @ sk_C @ sk_B)) @ X0)
% 0.21/0.58          | (zip_tseitin_0 @ (sk_E_3 @ (sk_D_2 @ sk_C @ sk_B)) @ 
% 0.21/0.58             (sk_D_2 @ sk_C @ sk_B) @ X0 @ sk_C))),
% 0.21/0.58      inference('demod', [status(thm)], ['47', '50'])).
% 0.21/0.58  thf('52', plain,
% 0.21/0.58      ((zip_tseitin_0 @ (sk_E_3 @ (sk_D_2 @ sk_C @ sk_B)) @ 
% 0.21/0.58        (sk_D_2 @ sk_C @ sk_B) @ sk_A @ sk_C)),
% 0.21/0.58      inference('sup-', [status(thm)], ['14', '51'])).
% 0.21/0.58  thf(zf_stmt_7, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.21/0.58  thf(zf_stmt_8, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.21/0.58       ( ![B:$i,C:$i]:
% 0.21/0.58         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.21/0.58           ( ![D:$i]:
% 0.21/0.58             ( ( r2_hidden @ D @ C ) <=>
% 0.21/0.58               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 0.21/0.58  thf('53', plain,
% 0.21/0.58      (![X16 : $i, X17 : $i, X19 : $i, X21 : $i, X22 : $i]:
% 0.21/0.58         (((X19) != (k9_relat_1 @ X17 @ X16))
% 0.21/0.58          | (r2_hidden @ X21 @ X19)
% 0.21/0.58          | ~ (zip_tseitin_0 @ X22 @ X21 @ X16 @ X17)
% 0.21/0.58          | ~ (v1_funct_1 @ X17)
% 0.21/0.58          | ~ (v1_relat_1 @ X17))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.21/0.58  thf('54', plain,
% 0.21/0.58      (![X16 : $i, X17 : $i, X21 : $i, X22 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X17)
% 0.21/0.58          | ~ (v1_funct_1 @ X17)
% 0.21/0.58          | ~ (zip_tseitin_0 @ X22 @ X21 @ X16 @ X17)
% 0.21/0.58          | (r2_hidden @ X21 @ (k9_relat_1 @ X17 @ X16)))),
% 0.21/0.58      inference('simplify', [status(thm)], ['53'])).
% 0.21/0.58  thf('55', plain,
% 0.21/0.58      (((r2_hidden @ (sk_D_2 @ sk_C @ sk_B) @ (k9_relat_1 @ sk_C @ sk_A))
% 0.21/0.58        | ~ (v1_funct_1 @ sk_C)
% 0.21/0.58        | ~ (v1_relat_1 @ sk_C))),
% 0.21/0.58      inference('sup-', [status(thm)], ['52', '54'])).
% 0.21/0.58  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('57', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.58      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.58  thf('58', plain,
% 0.21/0.58      ((r2_hidden @ (sk_D_2 @ sk_C @ sk_B) @ (k9_relat_1 @ sk_C @ sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.21/0.58  thf(t143_relat_1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( v1_relat_1 @ C ) =>
% 0.21/0.58       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.21/0.58         ( ?[D:$i]:
% 0.21/0.58           ( ( r2_hidden @ D @ B ) & 
% 0.21/0.58             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.21/0.58             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.21/0.58  thf('59', plain,
% 0.21/0.58      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.21/0.58         (~ (r2_hidden @ X8 @ (k9_relat_1 @ X9 @ X7))
% 0.21/0.58          | (r2_hidden @ (k4_tarski @ (sk_D @ X9 @ X7 @ X8) @ X8) @ X9)
% 0.21/0.58          | ~ (v1_relat_1 @ X9))),
% 0.21/0.58      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.21/0.58  thf('60', plain,
% 0.21/0.58      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.58        | (r2_hidden @ 
% 0.21/0.58           (k4_tarski @ (sk_D @ sk_C @ sk_A @ (sk_D_2 @ sk_C @ sk_B)) @ 
% 0.21/0.58            (sk_D_2 @ sk_C @ sk_B)) @ 
% 0.21/0.58           sk_C))),
% 0.21/0.58      inference('sup-', [status(thm)], ['58', '59'])).
% 0.21/0.58  thf('61', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.58      inference('sup-', [status(thm)], ['24', '25'])).
% 0.21/0.58  thf('62', plain,
% 0.21/0.58      ((r2_hidden @ 
% 0.21/0.58        (k4_tarski @ (sk_D @ sk_C @ sk_A @ (sk_D_2 @ sk_C @ sk_B)) @ 
% 0.21/0.58         (sk_D_2 @ sk_C @ sk_B)) @ 
% 0.21/0.58        sk_C)),
% 0.21/0.58      inference('demod', [status(thm)], ['60', '61'])).
% 0.21/0.58  thf('63', plain,
% 0.21/0.58      (![X35 : $i, X36 : $i, X37 : $i, X39 : $i]:
% 0.21/0.58         (~ (r2_hidden @ (k4_tarski @ X39 @ (sk_D_2 @ X37 @ X35)) @ X37)
% 0.21/0.58          | ((k2_relset_1 @ X36 @ X35 @ X37) = (X35))
% 0.21/0.58          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 0.21/0.58      inference('cnf', [status(esa)], [t23_relset_1])).
% 0.21/0.58  thf('64', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.21/0.58          | ((k2_relset_1 @ X0 @ sk_B @ sk_C) = (sk_B)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['62', '63'])).
% 0.21/0.58  thf('65', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.21/0.58      inference('sup-', [status(thm)], ['3', '64'])).
% 0.21/0.58  thf('66', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.21/0.58      inference('sup+', [status(thm)], ['2', '65'])).
% 0.21/0.58  thf('67', plain, (((k2_relat_1 @ sk_C) != (sk_B))),
% 0.21/0.58      inference('demod', [status(thm)], ['9', '10'])).
% 0.21/0.58  thf('68', plain, ($false),
% 0.21/0.58      inference('simplify_reflect-', [status(thm)], ['66', '67'])).
% 0.21/0.58  
% 0.21/0.58  % SZS output end Refutation
% 0.21/0.58  
% 0.21/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
