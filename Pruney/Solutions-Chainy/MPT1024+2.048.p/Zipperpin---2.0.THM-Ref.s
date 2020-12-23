%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VhrH4PnJ9p

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:40 EST 2020

% Result     : Theorem 0.50s
% Output     : Refutation 0.58s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 187 expanded)
%              Number of leaves         :   45 (  75 expanded)
%              Depth                    :   15
%              Number of atoms          :  779 (2313 expanded)
%              Number of equality atoms :   39 (  89 expanded)
%              Maximal formula depth    :   17 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_E_2_type,type,(
    sk_E_2: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

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
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( ( k7_relset_1 @ X36 @ X37 @ X35 @ X38 )
        = ( k9_relat_1 @ X35 @ X38 ) ) ) ),
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
    ! [X19: $i,X20: $i,X22: $i,X23: $i] :
      ( ( X22
       != ( k9_relat_1 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X23 @ X19 @ X20 ) @ X23 @ X19 @ X20 )
      | ~ ( r2_hidden @ X23 @ X22 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('6',plain,(
    ! [X19: $i,X20: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ~ ( v1_funct_1 @ X20 )
      | ~ ( r2_hidden @ X23 @ ( k9_relat_1 @ X20 @ X19 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X23 @ X19 @ X20 ) @ X23 @ X19 @ X20 ) ) ),
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

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('10',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('11',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('12',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 @ sk_C @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8','13'])).

thf('15',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X14 @ ( k1_relat_1 @ X13 ) )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('16',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ),
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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('18',plain,(
    ! [X39: $i,X40: $i] :
      ( ( zip_tseitin_1 @ X39 @ X40 )
      | ( X39 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('19',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_1 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf('21',plain,(
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

thf('22',plain,(
    ! [X44: $i,X45: $i,X46: $i] :
      ( ~ ( zip_tseitin_1 @ X44 @ X45 )
      | ( zip_tseitin_2 @ X46 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('23',plain,
    ( ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_funct_2 @ X43 @ X41 @ X42 )
      | ( X41
        = ( k1_relset_1 @ X41 @ X42 @ X43 ) )
      | ~ ( zip_tseitin_2 @ X43 @ X42 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('27',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( ( k1_relset_1 @ X33 @ X34 @ X32 )
        = ( k1_relat_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('30',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_B @ X0 )
      | ( sk_A
        = ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['24','31'])).

thf('33',plain,(
    r2_hidden @ sk_E_2 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('35',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X29 @ X30 @ X28 @ X31 ) @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('37',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ sk_B )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_E_2 @ sk_B ),
    inference('sup-',[status(thm)],['33','38'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('40',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X2 )
      | ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('41',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_E_2 @ sk_B ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('42',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( r2_hidden @ X26 @ X27 )
      | ~ ( r1_tarski @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('43',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( r1_tarski @ sk_B @ sk_E_2 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['32','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('46',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ sk_B )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( sk_A
        = ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['17','48'])).

thf('50',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_A ),
    inference(demod,[status(thm)],['16','49'])).

thf('51',plain,(
    ! [X47: $i] :
      ( ~ ( r2_hidden @ X47 @ sk_A )
      | ~ ( r2_hidden @ X47 @ sk_C )
      | ( sk_E_2
       != ( k1_funct_1 @ sk_D_1 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,
    ( ( sk_E_2
     != ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) ) )
    | ~ ( r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 @ sk_C @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8','13'])).

thf('54',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_hidden @ X14 @ X16 )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('55',plain,(
    r2_hidden @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_C ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    sk_E_2
 != ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['52','55'])).

thf('57',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) @ sk_E_2 @ sk_C @ sk_D_1 ),
    inference(demod,[status(thm)],['7','8','13'])).

thf('58',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( X15
        = ( k1_funct_1 @ X13 @ X14 ) )
      | ~ ( zip_tseitin_0 @ X14 @ X15 @ X16 @ X13 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('59',plain,
    ( sk_E_2
    = ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    sk_E_2 != sk_E_2 ),
    inference(demod,[status(thm)],['56','59'])).

thf('61',plain,(
    $false ),
    inference(simplify,[status(thm)],['60'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.VhrH4PnJ9p
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:58:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.50/0.73  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.50/0.73  % Solved by: fo/fo7.sh
% 0.50/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.50/0.73  % done 221 iterations in 0.283s
% 0.50/0.73  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.50/0.73  % SZS output start Refutation
% 0.50/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.50/0.73  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.50/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.50/0.73  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.50/0.73  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.50/0.73  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.50/0.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.50/0.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.50/0.73  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.50/0.73  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.50/0.73  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.50/0.73  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.50/0.73  thf(sk_E_2_type, type, sk_E_2: $i).
% 0.50/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.50/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.50/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.50/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.50/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.50/0.73  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.50/0.73  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.50/0.73  thf(sk_B_type, type, sk_B: $i).
% 0.50/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.50/0.73  thf(sk_C_type, type, sk_C: $i).
% 0.50/0.73  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.50/0.73  thf(t115_funct_2, conjecture,
% 0.50/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.73     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.50/0.73         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.50/0.73       ( ![E:$i]:
% 0.50/0.73         ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.50/0.73              ( ![F:$i]:
% 0.50/0.73                ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.50/0.73                     ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ))).
% 0.50/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.50/0.73    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.73        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.50/0.73            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.50/0.73          ( ![E:$i]:
% 0.50/0.73            ( ~( ( r2_hidden @ E @ ( k7_relset_1 @ A @ B @ D @ C ) ) & 
% 0.50/0.73                 ( ![F:$i]:
% 0.50/0.73                   ( ~( ( r2_hidden @ F @ A ) & ( r2_hidden @ F @ C ) & 
% 0.50/0.73                        ( ( E ) = ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )),
% 0.50/0.73    inference('cnf.neg', [status(esa)], [t115_funct_2])).
% 0.50/0.73  thf('0', plain,
% 0.50/0.73      ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('1', plain,
% 0.50/0.73      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf(redefinition_k7_relset_1, axiom,
% 0.50/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.50/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.50/0.73       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.50/0.73  thf('2', plain,
% 0.50/0.73      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.50/0.73         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.50/0.73          | ((k7_relset_1 @ X36 @ X37 @ X35 @ X38) = (k9_relat_1 @ X35 @ X38)))),
% 0.50/0.73      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.50/0.73  thf('3', plain,
% 0.50/0.73      (![X0 : $i]:
% 0.50/0.73         ((k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)
% 0.50/0.73           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.50/0.73      inference('sup-', [status(thm)], ['1', '2'])).
% 0.50/0.73  thf('4', plain, ((r2_hidden @ sk_E_2 @ (k9_relat_1 @ sk_D_1 @ sk_C))),
% 0.50/0.73      inference('demod', [status(thm)], ['0', '3'])).
% 0.50/0.73  thf(d12_funct_1, axiom,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.50/0.73       ( ![B:$i,C:$i]:
% 0.50/0.73         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.50/0.73           ( ![D:$i]:
% 0.50/0.73             ( ( r2_hidden @ D @ C ) <=>
% 0.50/0.73               ( ?[E:$i]:
% 0.50/0.73                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 0.50/0.73                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 0.50/0.73  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.50/0.73  thf(zf_stmt_2, axiom,
% 0.50/0.73    (![E:$i,D:$i,B:$i,A:$i]:
% 0.50/0.73     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.50/0.73       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 0.50/0.73         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 0.50/0.73  thf(zf_stmt_3, axiom,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.50/0.73       ( ![B:$i,C:$i]:
% 0.50/0.73         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.50/0.73           ( ![D:$i]:
% 0.50/0.73             ( ( r2_hidden @ D @ C ) <=>
% 0.50/0.73               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 0.50/0.73  thf('5', plain,
% 0.50/0.73      (![X19 : $i, X20 : $i, X22 : $i, X23 : $i]:
% 0.50/0.73         (((X22) != (k9_relat_1 @ X20 @ X19))
% 0.50/0.73          | (zip_tseitin_0 @ (sk_E_1 @ X23 @ X19 @ X20) @ X23 @ X19 @ X20)
% 0.50/0.73          | ~ (r2_hidden @ X23 @ X22)
% 0.50/0.73          | ~ (v1_funct_1 @ X20)
% 0.50/0.73          | ~ (v1_relat_1 @ X20))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.50/0.73  thf('6', plain,
% 0.50/0.73      (![X19 : $i, X20 : $i, X23 : $i]:
% 0.50/0.73         (~ (v1_relat_1 @ X20)
% 0.50/0.73          | ~ (v1_funct_1 @ X20)
% 0.50/0.73          | ~ (r2_hidden @ X23 @ (k9_relat_1 @ X20 @ X19))
% 0.50/0.73          | (zip_tseitin_0 @ (sk_E_1 @ X23 @ X19 @ X20) @ X23 @ X19 @ X20))),
% 0.50/0.73      inference('simplify', [status(thm)], ['5'])).
% 0.50/0.73  thf('7', plain,
% 0.50/0.73      (((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.50/0.73         sk_D_1)
% 0.50/0.73        | ~ (v1_funct_1 @ sk_D_1)
% 0.50/0.73        | ~ (v1_relat_1 @ sk_D_1))),
% 0.50/0.73      inference('sup-', [status(thm)], ['4', '6'])).
% 0.50/0.73  thf('8', plain, ((v1_funct_1 @ sk_D_1)),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf('9', plain,
% 0.50/0.73      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.50/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.50/0.73  thf(cc2_relat_1, axiom,
% 0.50/0.73    (![A:$i]:
% 0.50/0.73     ( ( v1_relat_1 @ A ) =>
% 0.50/0.73       ( ![B:$i]:
% 0.50/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.50/0.73  thf('10', plain,
% 0.50/0.73      (![X9 : $i, X10 : $i]:
% 0.50/0.73         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.50/0.73          | (v1_relat_1 @ X9)
% 0.50/0.73          | ~ (v1_relat_1 @ X10))),
% 0.50/0.73      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.50/0.73  thf('11', plain,
% 0.50/0.73      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_1))),
% 0.50/0.73      inference('sup-', [status(thm)], ['9', '10'])).
% 0.50/0.73  thf(fc6_relat_1, axiom,
% 0.58/0.73    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.58/0.73  thf('12', plain,
% 0.58/0.73      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.58/0.73      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.58/0.73  thf('13', plain, ((v1_relat_1 @ sk_D_1)),
% 0.58/0.73      inference('demod', [status(thm)], ['11', '12'])).
% 0.58/0.73  thf('14', plain,
% 0.58/0.73      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.58/0.73        sk_D_1)),
% 0.58/0.73      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.58/0.73  thf('15', plain,
% 0.58/0.73      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.58/0.73         ((r2_hidden @ X14 @ (k1_relat_1 @ X13))
% 0.58/0.73          | ~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X13))),
% 0.58/0.73      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.58/0.73  thf('16', plain,
% 0.58/0.73      ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ (k1_relat_1 @ sk_D_1))),
% 0.58/0.73      inference('sup-', [status(thm)], ['14', '15'])).
% 0.58/0.73  thf('17', plain,
% 0.58/0.73      ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))),
% 0.58/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.73  thf(d1_funct_2, axiom,
% 0.58/0.73    (![A:$i,B:$i,C:$i]:
% 0.58/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.73       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.58/0.73           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.58/0.73             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.58/0.73         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.58/0.73           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.58/0.73             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.58/0.73  thf(zf_stmt_4, axiom,
% 0.58/0.73    (![B:$i,A:$i]:
% 0.58/0.73     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.58/0.73       ( zip_tseitin_1 @ B @ A ) ))).
% 0.58/0.73  thf('18', plain,
% 0.58/0.73      (![X39 : $i, X40 : $i]:
% 0.58/0.73         ((zip_tseitin_1 @ X39 @ X40) | ((X39) = (k1_xboole_0)))),
% 0.58/0.73      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.58/0.73  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.58/0.73  thf('19', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.58/0.73      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.58/0.73  thf('20', plain,
% 0.58/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.58/0.73         ((r1_tarski @ X0 @ X1) | (zip_tseitin_1 @ X0 @ X2))),
% 0.58/0.73      inference('sup+', [status(thm)], ['18', '19'])).
% 0.58/0.73  thf('21', plain,
% 0.58/0.73      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.73  thf(zf_stmt_5, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.58/0.73  thf(zf_stmt_6, axiom,
% 0.58/0.73    (![C:$i,B:$i,A:$i]:
% 0.58/0.73     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.58/0.73       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.58/0.73  thf(zf_stmt_7, type, zip_tseitin_1 : $i > $i > $o).
% 0.58/0.73  thf(zf_stmt_8, axiom,
% 0.58/0.73    (![A:$i,B:$i,C:$i]:
% 0.58/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.73       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.58/0.73         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.58/0.73           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.58/0.73             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.58/0.73  thf('22', plain,
% 0.58/0.73      (![X44 : $i, X45 : $i, X46 : $i]:
% 0.58/0.73         (~ (zip_tseitin_1 @ X44 @ X45)
% 0.58/0.73          | (zip_tseitin_2 @ X46 @ X44 @ X45)
% 0.58/0.73          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44))))),
% 0.58/0.73      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.58/0.73  thf('23', plain,
% 0.58/0.73      (((zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)
% 0.58/0.73        | ~ (zip_tseitin_1 @ sk_B @ sk_A))),
% 0.58/0.73      inference('sup-', [status(thm)], ['21', '22'])).
% 0.58/0.73  thf('24', plain,
% 0.58/0.73      (![X0 : $i]:
% 0.58/0.73         ((r1_tarski @ sk_B @ X0) | (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A))),
% 0.58/0.73      inference('sup-', [status(thm)], ['20', '23'])).
% 0.58/0.73  thf('25', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.58/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.73  thf('26', plain,
% 0.58/0.73      (![X41 : $i, X42 : $i, X43 : $i]:
% 0.58/0.73         (~ (v1_funct_2 @ X43 @ X41 @ X42)
% 0.58/0.73          | ((X41) = (k1_relset_1 @ X41 @ X42 @ X43))
% 0.58/0.73          | ~ (zip_tseitin_2 @ X43 @ X42 @ X41))),
% 0.58/0.73      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.58/0.73  thf('27', plain,
% 0.58/0.73      ((~ (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)
% 0.58/0.73        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_1)))),
% 0.58/0.73      inference('sup-', [status(thm)], ['25', '26'])).
% 0.58/0.73  thf('28', plain,
% 0.58/0.73      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.73  thf(redefinition_k1_relset_1, axiom,
% 0.58/0.73    (![A:$i,B:$i,C:$i]:
% 0.58/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.73       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.58/0.73  thf('29', plain,
% 0.58/0.73      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.58/0.73         (((k1_relset_1 @ X33 @ X34 @ X32) = (k1_relat_1 @ X32))
% 0.58/0.73          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.58/0.73      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.58/0.73  thf('30', plain,
% 0.58/0.73      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.58/0.73      inference('sup-', [status(thm)], ['28', '29'])).
% 0.58/0.73  thf('31', plain,
% 0.58/0.73      ((~ (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)
% 0.58/0.73        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.58/0.73      inference('demod', [status(thm)], ['27', '30'])).
% 0.58/0.73  thf('32', plain,
% 0.58/0.73      (![X0 : $i]: ((r1_tarski @ sk_B @ X0) | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.58/0.73      inference('sup-', [status(thm)], ['24', '31'])).
% 0.58/0.73  thf('33', plain,
% 0.58/0.73      ((r2_hidden @ sk_E_2 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ sk_C))),
% 0.58/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.73  thf('34', plain,
% 0.58/0.73      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.58/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.73  thf(dt_k7_relset_1, axiom,
% 0.58/0.73    (![A:$i,B:$i,C:$i,D:$i]:
% 0.58/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.58/0.73       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.58/0.73  thf('35', plain,
% 0.58/0.73      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.58/0.73         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.58/0.73          | (m1_subset_1 @ (k7_relset_1 @ X29 @ X30 @ X28 @ X31) @ 
% 0.58/0.73             (k1_zfmisc_1 @ X30)))),
% 0.58/0.73      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 0.58/0.73  thf('36', plain,
% 0.58/0.73      (![X0 : $i]:
% 0.58/0.73         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0) @ 
% 0.58/0.73          (k1_zfmisc_1 @ sk_B))),
% 0.58/0.73      inference('sup-', [status(thm)], ['34', '35'])).
% 0.58/0.73  thf(t4_subset, axiom,
% 0.58/0.73    (![A:$i,B:$i,C:$i]:
% 0.58/0.73     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.58/0.73       ( m1_subset_1 @ A @ C ) ))).
% 0.58/0.73  thf('37', plain,
% 0.58/0.73      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.58/0.73         (~ (r2_hidden @ X3 @ X4)
% 0.58/0.73          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.58/0.73          | (m1_subset_1 @ X3 @ X5))),
% 0.58/0.73      inference('cnf', [status(esa)], [t4_subset])).
% 0.58/0.73  thf('38', plain,
% 0.58/0.73      (![X0 : $i, X1 : $i]:
% 0.58/0.73         ((m1_subset_1 @ X1 @ sk_B)
% 0.58/0.73          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)))),
% 0.58/0.73      inference('sup-', [status(thm)], ['36', '37'])).
% 0.58/0.73  thf('39', plain, ((m1_subset_1 @ sk_E_2 @ sk_B)),
% 0.58/0.73      inference('sup-', [status(thm)], ['33', '38'])).
% 0.58/0.73  thf(t2_subset, axiom,
% 0.58/0.73    (![A:$i,B:$i]:
% 0.58/0.73     ( ( m1_subset_1 @ A @ B ) =>
% 0.58/0.73       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.58/0.73  thf('40', plain,
% 0.58/0.73      (![X1 : $i, X2 : $i]:
% 0.58/0.73         ((r2_hidden @ X1 @ X2)
% 0.58/0.73          | (v1_xboole_0 @ X2)
% 0.58/0.73          | ~ (m1_subset_1 @ X1 @ X2))),
% 0.58/0.73      inference('cnf', [status(esa)], [t2_subset])).
% 0.58/0.73  thf('41', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_E_2 @ sk_B))),
% 0.58/0.73      inference('sup-', [status(thm)], ['39', '40'])).
% 0.58/0.73  thf(t7_ordinal1, axiom,
% 0.58/0.74    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.58/0.74  thf('42', plain,
% 0.58/0.74      (![X26 : $i, X27 : $i]:
% 0.58/0.74         (~ (r2_hidden @ X26 @ X27) | ~ (r1_tarski @ X27 @ X26))),
% 0.58/0.74      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.58/0.74  thf('43', plain, (((v1_xboole_0 @ sk_B) | ~ (r1_tarski @ sk_B @ sk_E_2))),
% 0.58/0.74      inference('sup-', [status(thm)], ['41', '42'])).
% 0.58/0.74  thf('44', plain, ((((sk_A) = (k1_relat_1 @ sk_D_1)) | (v1_xboole_0 @ sk_B))),
% 0.58/0.74      inference('sup-', [status(thm)], ['32', '43'])).
% 0.58/0.74  thf('45', plain,
% 0.58/0.74      (![X0 : $i]:
% 0.58/0.74         (m1_subset_1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0) @ 
% 0.58/0.74          (k1_zfmisc_1 @ sk_B))),
% 0.58/0.74      inference('sup-', [status(thm)], ['34', '35'])).
% 0.58/0.74  thf(t5_subset, axiom,
% 0.58/0.74    (![A:$i,B:$i,C:$i]:
% 0.58/0.74     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.58/0.74          ( v1_xboole_0 @ C ) ) ))).
% 0.58/0.74  thf('46', plain,
% 0.58/0.74      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.58/0.74         (~ (r2_hidden @ X6 @ X7)
% 0.58/0.74          | ~ (v1_xboole_0 @ X8)
% 0.58/0.74          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.58/0.74      inference('cnf', [status(esa)], [t5_subset])).
% 0.58/0.74  thf('47', plain,
% 0.58/0.74      (![X0 : $i, X1 : $i]:
% 0.58/0.74         (~ (v1_xboole_0 @ sk_B)
% 0.58/0.74          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)))),
% 0.58/0.74      inference('sup-', [status(thm)], ['45', '46'])).
% 0.58/0.74  thf('48', plain,
% 0.58/0.74      (![X0 : $i, X1 : $i]:
% 0.58/0.74         (((sk_A) = (k1_relat_1 @ sk_D_1))
% 0.58/0.74          | ~ (r2_hidden @ X1 @ (k7_relset_1 @ sk_A @ sk_B @ sk_D_1 @ X0)))),
% 0.58/0.74      inference('sup-', [status(thm)], ['44', '47'])).
% 0.58/0.74  thf('49', plain, (((sk_A) = (k1_relat_1 @ sk_D_1))),
% 0.58/0.74      inference('sup-', [status(thm)], ['17', '48'])).
% 0.58/0.74  thf('50', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_A)),
% 0.58/0.74      inference('demod', [status(thm)], ['16', '49'])).
% 0.58/0.74  thf('51', plain,
% 0.58/0.74      (![X47 : $i]:
% 0.58/0.74         (~ (r2_hidden @ X47 @ sk_A)
% 0.58/0.74          | ~ (r2_hidden @ X47 @ sk_C)
% 0.58/0.74          | ((sk_E_2) != (k1_funct_1 @ sk_D_1 @ X47)))),
% 0.58/0.74      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.58/0.74  thf('52', plain,
% 0.58/0.74      ((((sk_E_2) != (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1)))
% 0.58/0.74        | ~ (r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_C))),
% 0.58/0.74      inference('sup-', [status(thm)], ['50', '51'])).
% 0.58/0.74  thf('53', plain,
% 0.58/0.74      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.58/0.74        sk_D_1)),
% 0.58/0.74      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.58/0.74  thf('54', plain,
% 0.58/0.74      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.58/0.74         ((r2_hidden @ X14 @ X16) | ~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X13))),
% 0.58/0.74      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.58/0.74  thf('55', plain, ((r2_hidden @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_C)),
% 0.58/0.74      inference('sup-', [status(thm)], ['53', '54'])).
% 0.58/0.74  thf('56', plain,
% 0.58/0.74      (((sk_E_2) != (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1)))),
% 0.58/0.74      inference('demod', [status(thm)], ['52', '55'])).
% 0.58/0.74  thf('57', plain,
% 0.58/0.74      ((zip_tseitin_0 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1) @ sk_E_2 @ sk_C @ 
% 0.58/0.74        sk_D_1)),
% 0.58/0.74      inference('demod', [status(thm)], ['7', '8', '13'])).
% 0.58/0.74  thf('58', plain,
% 0.58/0.74      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.58/0.74         (((X15) = (k1_funct_1 @ X13 @ X14))
% 0.58/0.74          | ~ (zip_tseitin_0 @ X14 @ X15 @ X16 @ X13))),
% 0.58/0.74      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.58/0.74  thf('59', plain,
% 0.58/0.74      (((sk_E_2) = (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_E_2 @ sk_C @ sk_D_1)))),
% 0.58/0.74      inference('sup-', [status(thm)], ['57', '58'])).
% 0.58/0.74  thf('60', plain, (((sk_E_2) != (sk_E_2))),
% 0.58/0.74      inference('demod', [status(thm)], ['56', '59'])).
% 0.58/0.74  thf('61', plain, ($false), inference('simplify', [status(thm)], ['60'])).
% 0.58/0.74  
% 0.58/0.74  % SZS output end Refutation
% 0.58/0.74  
% 0.58/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
