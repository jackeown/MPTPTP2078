%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.C02KNoLH29

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:31 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 256 expanded)
%              Number of leaves         :   42 (  93 expanded)
%              Depth                    :   17
%              Number of atoms          :  709 (3141 expanded)
%              Number of equality atoms :   46 ( 153 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t17_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ~ ( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) )
          & ! [E: $i] :
              ~ ( ( r2_hidden @ E @ A )
                & ( ( k1_funct_1 @ D @ E )
                  = C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ A @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ~ ( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) )
            & ! [E: $i] :
                ~ ( ( r2_hidden @ E @ A )
                  & ( ( k1_funct_1 @ D @ E )
                    = C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t17_funct_2])).

thf('0',plain,(
    r2_hidden @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ( ( k2_relset_1 @ X28 @ X29 @ X27 )
        = ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    r2_hidden @ sk_C @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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
     => ( zip_tseitin_1 @ B @ A ) ) )).

thf('6',plain,(
    ! [X30: $i,X31: $i] :
      ( ( zip_tseitin_1 @ X30 @ X31 )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('7',plain,(
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

thf('8',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( zip_tseitin_1 @ X35 @ X36 )
      | ( zip_tseitin_2 @ X37 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('9',plain,
    ( ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_2 @ X34 @ X32 @ X33 )
      | ( X32
        = ( k1_relset_1 @ X32 @ X33 @ X34 ) )
      | ~ ( zip_tseitin_2 @ X34 @ X33 @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('13',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('15',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k1_relset_1 @ X25 @ X26 @ X24 )
        = ( k1_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('16',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf('18',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['10','17'])).

thf('19',plain,(
    r2_hidden @ sk_C @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('20',plain,(
    ! [X7: $i] :
      ( ( ( k9_relat_1 @ X7 @ ( k1_relat_1 @ X7 ) )
        = ( k2_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

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

thf('21',plain,(
    ! [X14: $i,X15: $i,X17: $i,X18: $i] :
      ( ( X17
       != ( k9_relat_1 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X18 @ X14 @ X15 ) @ X18 @ X14 @ X15 )
      | ~ ( r2_hidden @ X18 @ X17 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('22',plain,(
    ! [X14: $i,X15: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ~ ( r2_hidden @ X18 @ ( k9_relat_1 @ X15 @ X14 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X18 @ X14 @ X15 ) @ X18 @ X14 @ X15 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X1 @ ( k1_relat_1 @ X0 ) @ X0 ) @ X1 @ ( k1_relat_1 @ X0 ) @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X1 @ ( k1_relat_1 @ X0 ) @ X0 ) @ X1 @ ( k1_relat_1 @ X0 ) @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( zip_tseitin_0 @ ( sk_E_1 @ sk_C @ ( k1_relat_1 @ sk_D_1 ) @ sk_D_1 ) @ sk_C @ ( k1_relat_1 @ sk_D_1 ) @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('27',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('29',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('30',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_C @ ( k1_relat_1 @ sk_D_1 ) @ sk_D_1 ) @ sk_C @ ( k1_relat_1 @ sk_D_1 ) @ sk_D_1 ),
    inference(demod,[status(thm)],['25','30','31'])).

thf('33',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( r2_hidden @ X9 @ X11 )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('34',plain,(
    r2_hidden @ ( sk_E_1 @ sk_C @ ( k1_relat_1 @ sk_D_1 ) @ sk_D_1 ) @ ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( r2_hidden @ ( sk_E_1 @ sk_C @ ( k1_relat_1 @ sk_D_1 ) @ sk_D_1 ) @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['18','34'])).

thf('36',plain,(
    ! [X38: $i] :
      ( ~ ( r2_hidden @ X38 @ sk_A )
      | ( ( k1_funct_1 @ sk_D_1 @ X38 )
       != sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_C @ ( k1_relat_1 @ sk_D_1 ) @ sk_D_1 ) )
     != sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    zip_tseitin_0 @ ( sk_E_1 @ sk_C @ ( k1_relat_1 @ sk_D_1 ) @ sk_D_1 ) @ sk_C @ ( k1_relat_1 @ sk_D_1 ) @ sk_D_1 ),
    inference(demod,[status(thm)],['25','30','31'])).

thf('39',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ( X10
        = ( k1_funct_1 @ X8 @ X9 ) )
      | ~ ( zip_tseitin_0 @ X9 @ X10 @ X11 @ X8 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('40',plain,
    ( sk_C
    = ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_C @ ( k1_relat_1 @ sk_D_1 ) @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C != sk_C ) ),
    inference(demod,[status(thm)],['37','40'])).

thf('42',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['5','42'])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('44',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X21 @ X22 @ X23 ) @ ( k1_zfmisc_1 @ X22 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('45',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ k1_xboole_0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('47',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['41'])).

thf('48',plain,
    ( ( k2_relset_1 @ sk_A @ k1_xboole_0 @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['45','48'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('52',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('53',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    $false ),
    inference('sup-',[status(thm)],['4','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.C02KNoLH29
% 0.16/0.38  % Computer   : n002.cluster.edu
% 0.16/0.38  % Model      : x86_64 x86_64
% 0.16/0.38  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.38  % Memory     : 8042.1875MB
% 0.16/0.38  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.38  % CPULimit   : 60
% 0.16/0.38  % DateTime   : Tue Dec  1 17:48:37 EST 2020
% 0.16/0.38  % CPUTime    : 
% 0.16/0.38  % Running portfolio for 600 s
% 0.16/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.16/0.38  % Number of cores: 8
% 0.16/0.38  % Python version: Python 3.6.8
% 0.16/0.38  % Running in FO mode
% 0.47/0.72  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.72  % Solved by: fo/fo7.sh
% 0.47/0.72  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.72  % done 153 iterations in 0.236s
% 0.47/0.72  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.72  % SZS output start Refutation
% 0.47/0.72  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.47/0.72  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 0.47/0.72  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.72  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 0.47/0.72  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.72  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.72  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.72  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.72  thf(sk_B_type, type, sk_B: $i).
% 0.47/0.72  thf(sk_C_type, type, sk_C: $i).
% 0.47/0.72  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.72  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.72  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.47/0.72  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.47/0.72  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.47/0.72  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.47/0.72  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.72  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 0.47/0.72  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.47/0.72  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.72  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 0.47/0.72  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.47/0.72  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.72  thf(t17_funct_2, conjecture,
% 0.47/0.72    (![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.72     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.47/0.72         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.72       ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 0.47/0.72            ( ![E:$i]:
% 0.47/0.72              ( ~( ( r2_hidden @ E @ A ) & ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ))).
% 0.47/0.72  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.72    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.47/0.72        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.47/0.72            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.47/0.72          ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 0.47/0.72               ( ![E:$i]:
% 0.47/0.72                 ( ~( ( r2_hidden @ E @ A ) & 
% 0.47/0.72                      ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ) )),
% 0.47/0.72    inference('cnf.neg', [status(esa)], [t17_funct_2])).
% 0.47/0.72  thf('0', plain, ((r2_hidden @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D_1))),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.72  thf('1', plain,
% 0.47/0.72      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.72  thf(redefinition_k2_relset_1, axiom,
% 0.47/0.72    (![A:$i,B:$i,C:$i]:
% 0.47/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.72       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.47/0.72  thf('2', plain,
% 0.47/0.72      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.47/0.72         (((k2_relset_1 @ X28 @ X29 @ X27) = (k2_relat_1 @ X27))
% 0.47/0.72          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29))))),
% 0.47/0.72      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.47/0.72  thf('3', plain,
% 0.47/0.72      (((k2_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.47/0.72      inference('sup-', [status(thm)], ['1', '2'])).
% 0.47/0.72  thf('4', plain, ((r2_hidden @ sk_C @ (k2_relat_1 @ sk_D_1))),
% 0.47/0.72      inference('demod', [status(thm)], ['0', '3'])).
% 0.47/0.72  thf('5', plain,
% 0.47/0.72      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.72  thf(d1_funct_2, axiom,
% 0.47/0.72    (![A:$i,B:$i,C:$i]:
% 0.47/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.72       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.47/0.72           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.47/0.72             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.47/0.72         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.72           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.47/0.72             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.47/0.72  thf(zf_stmt_1, axiom,
% 0.47/0.72    (![B:$i,A:$i]:
% 0.47/0.72     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.47/0.72       ( zip_tseitin_1 @ B @ A ) ))).
% 0.47/0.72  thf('6', plain,
% 0.47/0.72      (![X30 : $i, X31 : $i]:
% 0.47/0.72         ((zip_tseitin_1 @ X30 @ X31) | ((X30) = (k1_xboole_0)))),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.47/0.72  thf('7', plain,
% 0.47/0.72      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.72  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 0.47/0.72  thf(zf_stmt_3, axiom,
% 0.47/0.72    (![C:$i,B:$i,A:$i]:
% 0.47/0.72     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 0.47/0.72       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.47/0.72  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $o).
% 0.47/0.72  thf(zf_stmt_5, axiom,
% 0.47/0.72    (![A:$i,B:$i,C:$i]:
% 0.47/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.72       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 0.47/0.72         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.47/0.72           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.47/0.72             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.47/0.72  thf('8', plain,
% 0.47/0.72      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.47/0.72         (~ (zip_tseitin_1 @ X35 @ X36)
% 0.47/0.72          | (zip_tseitin_2 @ X37 @ X35 @ X36)
% 0.47/0.72          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35))))),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.47/0.72  thf('9', plain,
% 0.47/0.72      (((zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)
% 0.47/0.72        | ~ (zip_tseitin_1 @ sk_B @ sk_A))),
% 0.47/0.72      inference('sup-', [status(thm)], ['7', '8'])).
% 0.47/0.72  thf('10', plain,
% 0.47/0.72      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A))),
% 0.47/0.72      inference('sup-', [status(thm)], ['6', '9'])).
% 0.47/0.72  thf('11', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B)),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.72  thf('12', plain,
% 0.47/0.72      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.47/0.72         (~ (v1_funct_2 @ X34 @ X32 @ X33)
% 0.47/0.72          | ((X32) = (k1_relset_1 @ X32 @ X33 @ X34))
% 0.47/0.72          | ~ (zip_tseitin_2 @ X34 @ X33 @ X32))),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.47/0.72  thf('13', plain,
% 0.47/0.72      ((~ (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)
% 0.47/0.72        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_1)))),
% 0.47/0.72      inference('sup-', [status(thm)], ['11', '12'])).
% 0.47/0.72  thf('14', plain,
% 0.47/0.72      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.72  thf(redefinition_k1_relset_1, axiom,
% 0.47/0.72    (![A:$i,B:$i,C:$i]:
% 0.47/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.72       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.47/0.72  thf('15', plain,
% 0.47/0.72      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.47/0.72         (((k1_relset_1 @ X25 @ X26 @ X24) = (k1_relat_1 @ X24))
% 0.47/0.72          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.47/0.72      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.47/0.72  thf('16', plain,
% 0.47/0.72      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.47/0.72      inference('sup-', [status(thm)], ['14', '15'])).
% 0.47/0.72  thf('17', plain,
% 0.47/0.72      ((~ (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)
% 0.47/0.72        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.47/0.72      inference('demod', [status(thm)], ['13', '16'])).
% 0.47/0.72  thf('18', plain,
% 0.47/0.72      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 0.47/0.72      inference('sup-', [status(thm)], ['10', '17'])).
% 0.47/0.72  thf('19', plain, ((r2_hidden @ sk_C @ (k2_relat_1 @ sk_D_1))),
% 0.47/0.72      inference('demod', [status(thm)], ['0', '3'])).
% 0.47/0.72  thf(t146_relat_1, axiom,
% 0.47/0.72    (![A:$i]:
% 0.47/0.72     ( ( v1_relat_1 @ A ) =>
% 0.47/0.72       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.47/0.72  thf('20', plain,
% 0.47/0.72      (![X7 : $i]:
% 0.47/0.72         (((k9_relat_1 @ X7 @ (k1_relat_1 @ X7)) = (k2_relat_1 @ X7))
% 0.47/0.72          | ~ (v1_relat_1 @ X7))),
% 0.47/0.72      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.47/0.72  thf(d12_funct_1, axiom,
% 0.47/0.72    (![A:$i]:
% 0.47/0.72     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 0.47/0.72       ( ![B:$i,C:$i]:
% 0.47/0.72         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.47/0.72           ( ![D:$i]:
% 0.47/0.72             ( ( r2_hidden @ D @ C ) <=>
% 0.47/0.72               ( ?[E:$i]:
% 0.47/0.72                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 0.47/0.72                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 0.47/0.72  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 0.47/0.72  thf(zf_stmt_7, axiom,
% 0.47/0.72    (![E:$i,D:$i,B:$i,A:$i]:
% 0.47/0.72     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 0.47/0.72       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 0.47/0.72         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 0.47/0.72  thf(zf_stmt_8, axiom,
% 0.47/0.72    (![A:$i]:
% 0.47/0.72     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.47/0.72       ( ![B:$i,C:$i]:
% 0.47/0.72         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 0.47/0.72           ( ![D:$i]:
% 0.47/0.72             ( ( r2_hidden @ D @ C ) <=>
% 0.47/0.72               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 0.47/0.72  thf('21', plain,
% 0.47/0.72      (![X14 : $i, X15 : $i, X17 : $i, X18 : $i]:
% 0.47/0.72         (((X17) != (k9_relat_1 @ X15 @ X14))
% 0.47/0.72          | (zip_tseitin_0 @ (sk_E_1 @ X18 @ X14 @ X15) @ X18 @ X14 @ X15)
% 0.47/0.72          | ~ (r2_hidden @ X18 @ X17)
% 0.47/0.72          | ~ (v1_funct_1 @ X15)
% 0.47/0.72          | ~ (v1_relat_1 @ X15))),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.47/0.72  thf('22', plain,
% 0.47/0.72      (![X14 : $i, X15 : $i, X18 : $i]:
% 0.47/0.72         (~ (v1_relat_1 @ X15)
% 0.47/0.72          | ~ (v1_funct_1 @ X15)
% 0.47/0.72          | ~ (r2_hidden @ X18 @ (k9_relat_1 @ X15 @ X14))
% 0.47/0.72          | (zip_tseitin_0 @ (sk_E_1 @ X18 @ X14 @ X15) @ X18 @ X14 @ X15))),
% 0.47/0.72      inference('simplify', [status(thm)], ['21'])).
% 0.47/0.72  thf('23', plain,
% 0.47/0.72      (![X0 : $i, X1 : $i]:
% 0.47/0.72         (~ (r2_hidden @ X1 @ (k2_relat_1 @ X0))
% 0.47/0.72          | ~ (v1_relat_1 @ X0)
% 0.47/0.72          | (zip_tseitin_0 @ (sk_E_1 @ X1 @ (k1_relat_1 @ X0) @ X0) @ X1 @ 
% 0.47/0.72             (k1_relat_1 @ X0) @ X0)
% 0.47/0.72          | ~ (v1_funct_1 @ X0)
% 0.47/0.72          | ~ (v1_relat_1 @ X0))),
% 0.47/0.72      inference('sup-', [status(thm)], ['20', '22'])).
% 0.47/0.72  thf('24', plain,
% 0.47/0.72      (![X0 : $i, X1 : $i]:
% 0.47/0.72         (~ (v1_funct_1 @ X0)
% 0.47/0.72          | (zip_tseitin_0 @ (sk_E_1 @ X1 @ (k1_relat_1 @ X0) @ X0) @ X1 @ 
% 0.47/0.72             (k1_relat_1 @ X0) @ X0)
% 0.47/0.72          | ~ (v1_relat_1 @ X0)
% 0.47/0.72          | ~ (r2_hidden @ X1 @ (k2_relat_1 @ X0)))),
% 0.47/0.72      inference('simplify', [status(thm)], ['23'])).
% 0.47/0.72  thf('25', plain,
% 0.47/0.72      ((~ (v1_relat_1 @ sk_D_1)
% 0.47/0.72        | (zip_tseitin_0 @ (sk_E_1 @ sk_C @ (k1_relat_1 @ sk_D_1) @ sk_D_1) @ 
% 0.47/0.72           sk_C @ (k1_relat_1 @ sk_D_1) @ sk_D_1)
% 0.47/0.72        | ~ (v1_funct_1 @ sk_D_1))),
% 0.47/0.72      inference('sup-', [status(thm)], ['19', '24'])).
% 0.47/0.72  thf('26', plain,
% 0.47/0.72      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.72  thf(cc2_relat_1, axiom,
% 0.47/0.72    (![A:$i]:
% 0.47/0.72     ( ( v1_relat_1 @ A ) =>
% 0.47/0.72       ( ![B:$i]:
% 0.47/0.72         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.47/0.72  thf('27', plain,
% 0.47/0.72      (![X3 : $i, X4 : $i]:
% 0.47/0.72         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.47/0.72          | (v1_relat_1 @ X3)
% 0.47/0.72          | ~ (v1_relat_1 @ X4))),
% 0.47/0.72      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.47/0.72  thf('28', plain,
% 0.47/0.72      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_1))),
% 0.47/0.72      inference('sup-', [status(thm)], ['26', '27'])).
% 0.47/0.72  thf(fc6_relat_1, axiom,
% 0.47/0.72    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.47/0.72  thf('29', plain,
% 0.47/0.72      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.47/0.72      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.47/0.72  thf('30', plain, ((v1_relat_1 @ sk_D_1)),
% 0.47/0.72      inference('demod', [status(thm)], ['28', '29'])).
% 0.47/0.72  thf('31', plain, ((v1_funct_1 @ sk_D_1)),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.72  thf('32', plain,
% 0.47/0.72      ((zip_tseitin_0 @ (sk_E_1 @ sk_C @ (k1_relat_1 @ sk_D_1) @ sk_D_1) @ 
% 0.47/0.72        sk_C @ (k1_relat_1 @ sk_D_1) @ sk_D_1)),
% 0.47/0.72      inference('demod', [status(thm)], ['25', '30', '31'])).
% 0.47/0.72  thf('33', plain,
% 0.47/0.72      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.47/0.72         ((r2_hidden @ X9 @ X11) | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X8))),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.47/0.72  thf('34', plain,
% 0.47/0.72      ((r2_hidden @ (sk_E_1 @ sk_C @ (k1_relat_1 @ sk_D_1) @ sk_D_1) @ 
% 0.47/0.72        (k1_relat_1 @ sk_D_1))),
% 0.47/0.72      inference('sup-', [status(thm)], ['32', '33'])).
% 0.47/0.72  thf('35', plain,
% 0.47/0.72      (((r2_hidden @ (sk_E_1 @ sk_C @ (k1_relat_1 @ sk_D_1) @ sk_D_1) @ sk_A)
% 0.47/0.72        | ((sk_B) = (k1_xboole_0)))),
% 0.47/0.72      inference('sup+', [status(thm)], ['18', '34'])).
% 0.47/0.72  thf('36', plain,
% 0.47/0.72      (![X38 : $i]:
% 0.47/0.72         (~ (r2_hidden @ X38 @ sk_A) | ((k1_funct_1 @ sk_D_1 @ X38) != (sk_C)))),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.72  thf('37', plain,
% 0.47/0.72      ((((sk_B) = (k1_xboole_0))
% 0.47/0.72        | ((k1_funct_1 @ sk_D_1 @ 
% 0.47/0.72            (sk_E_1 @ sk_C @ (k1_relat_1 @ sk_D_1) @ sk_D_1)) != (sk_C)))),
% 0.47/0.72      inference('sup-', [status(thm)], ['35', '36'])).
% 0.47/0.72  thf('38', plain,
% 0.47/0.72      ((zip_tseitin_0 @ (sk_E_1 @ sk_C @ (k1_relat_1 @ sk_D_1) @ sk_D_1) @ 
% 0.47/0.72        sk_C @ (k1_relat_1 @ sk_D_1) @ sk_D_1)),
% 0.47/0.72      inference('demod', [status(thm)], ['25', '30', '31'])).
% 0.47/0.72  thf('39', plain,
% 0.47/0.72      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.47/0.72         (((X10) = (k1_funct_1 @ X8 @ X9))
% 0.47/0.72          | ~ (zip_tseitin_0 @ X9 @ X10 @ X11 @ X8))),
% 0.47/0.72      inference('cnf', [status(esa)], [zf_stmt_7])).
% 0.47/0.72  thf('40', plain,
% 0.47/0.72      (((sk_C)
% 0.47/0.72         = (k1_funct_1 @ sk_D_1 @ 
% 0.47/0.72            (sk_E_1 @ sk_C @ (k1_relat_1 @ sk_D_1) @ sk_D_1)))),
% 0.47/0.72      inference('sup-', [status(thm)], ['38', '39'])).
% 0.47/0.72  thf('41', plain, ((((sk_B) = (k1_xboole_0)) | ((sk_C) != (sk_C)))),
% 0.47/0.72      inference('demod', [status(thm)], ['37', '40'])).
% 0.47/0.72  thf('42', plain, (((sk_B) = (k1_xboole_0))),
% 0.47/0.72      inference('simplify', [status(thm)], ['41'])).
% 0.47/0.72  thf('43', plain,
% 0.47/0.72      ((m1_subset_1 @ sk_D_1 @ 
% 0.47/0.72        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0)))),
% 0.47/0.72      inference('demod', [status(thm)], ['5', '42'])).
% 0.47/0.72  thf(dt_k2_relset_1, axiom,
% 0.47/0.72    (![A:$i,B:$i,C:$i]:
% 0.47/0.72     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.72       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.47/0.72  thf('44', plain,
% 0.47/0.72      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.47/0.72         ((m1_subset_1 @ (k2_relset_1 @ X21 @ X22 @ X23) @ (k1_zfmisc_1 @ X22))
% 0.47/0.72          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.47/0.72      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.47/0.72  thf('45', plain,
% 0.47/0.72      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ k1_xboole_0 @ sk_D_1) @ 
% 0.47/0.72        (k1_zfmisc_1 @ k1_xboole_0))),
% 0.47/0.72      inference('sup-', [status(thm)], ['43', '44'])).
% 0.47/0.72  thf('46', plain,
% 0.47/0.72      (((k2_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.47/0.72      inference('sup-', [status(thm)], ['1', '2'])).
% 0.47/0.72  thf('47', plain, (((sk_B) = (k1_xboole_0))),
% 0.47/0.72      inference('simplify', [status(thm)], ['41'])).
% 0.47/0.72  thf('48', plain,
% 0.47/0.72      (((k2_relset_1 @ sk_A @ k1_xboole_0 @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.47/0.72      inference('demod', [status(thm)], ['46', '47'])).
% 0.47/0.72  thf('49', plain,
% 0.47/0.72      ((m1_subset_1 @ (k2_relat_1 @ sk_D_1) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.47/0.72      inference('demod', [status(thm)], ['45', '48'])).
% 0.47/0.72  thf(t5_subset, axiom,
% 0.47/0.72    (![A:$i,B:$i,C:$i]:
% 0.47/0.72     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.47/0.72          ( v1_xboole_0 @ C ) ) ))).
% 0.47/0.72  thf('50', plain,
% 0.47/0.72      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.47/0.72         (~ (r2_hidden @ X0 @ X1)
% 0.47/0.72          | ~ (v1_xboole_0 @ X2)
% 0.47/0.72          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.47/0.72      inference('cnf', [status(esa)], [t5_subset])).
% 0.47/0.72  thf('51', plain,
% 0.47/0.72      (![X0 : $i]:
% 0.47/0.72         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.47/0.72          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_1)))),
% 0.47/0.72      inference('sup-', [status(thm)], ['49', '50'])).
% 0.47/0.72  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.47/0.72  thf('52', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.72      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.72  thf('53', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_1))),
% 0.47/0.72      inference('demod', [status(thm)], ['51', '52'])).
% 0.47/0.72  thf('54', plain, ($false), inference('sup-', [status(thm)], ['4', '53'])).
% 0.47/0.72  
% 0.47/0.72  % SZS output end Refutation
% 0.47/0.72  
% 0.57/0.73  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
