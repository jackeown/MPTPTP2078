%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Oowbq9IZ4q

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:31 EST 2020

% Result     : Theorem 20.32s
% Output     : Refutation 20.32s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 425 expanded)
%              Number of leaves         :   43 ( 145 expanded)
%              Depth                    :   21
%              Number of atoms          :  852 (5184 expanded)
%              Number of equality atoms :   57 ( 266 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X33 @ X31 )
        = ( k2_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
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

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X25 @ X26 @ X27 ) @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('7',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('9',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference(demod,[status(thm)],['7','8'])).

thf(l3_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ B )
         => ( r2_hidden @ C @ A ) ) ) )).

thf('10',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    r2_hidden @ sk_C @ sk_B ),
    inference('sup-',[status(thm)],['4','11'])).

thf('13',plain,(
    r2_hidden @ sk_C @ ( k2_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

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

thf('14',plain,(
    ! [X34: $i,X35: $i] :
      ( ( zip_tseitin_1 @ X34 @ X35 )
      | ( X34 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( zip_tseitin_1 @ X39 @ X40 )
      | ( zip_tseitin_2 @ X41 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('17',plain,
    ( ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    v1_funct_2 @ sk_D_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_2 @ X38 @ X36 @ X37 )
      | ( X36
        = ( k1_relset_1 @ X36 @ X37 @ X38 ) )
      | ~ ( zip_tseitin_2 @ X38 @ X37 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('21',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('23',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('24',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['18','25'])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('27',plain,(
    ! [X11: $i] :
      ( ( ( k9_relat_1 @ X11 @ ( k1_relat_1 @ X11 ) )
        = ( k2_relat_1 @ X11 ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('28',plain,
    ( ( ( k9_relat_1 @ sk_D_1 @ sk_A )
      = ( k2_relat_1 @ sk_D_1 ) )
    | ( sk_B = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup+',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('30',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('32',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('33',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( ( k9_relat_1 @ sk_D_1 @ sk_A )
      = ( k2_relat_1 @ sk_D_1 ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','33'])).

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

thf('35',plain,(
    ! [X18: $i,X19: $i,X21: $i,X22: $i] :
      ( ( X21
       != ( k9_relat_1 @ X19 @ X18 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X22 @ X18 @ X19 ) @ X22 @ X18 @ X19 )
      | ~ ( r2_hidden @ X22 @ X21 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('36',plain,(
    ! [X18: $i,X19: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( r2_hidden @ X22 @ ( k9_relat_1 @ X19 @ X18 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X22 @ X18 @ X19 ) @ X22 @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_1 ) )
      | ( sk_B = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X0 @ sk_A @ sk_D_1 ) @ X0 @ sk_A @ sk_D_1 )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['31','32'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_D_1 ) )
      | ( sk_B = k1_xboole_0 )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X0 @ sk_A @ sk_D_1 ) @ X0 @ sk_A @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( zip_tseitin_0 @ ( sk_E_1 @ sk_C @ sk_A @ sk_D_1 ) @ sk_C @ sk_A @ sk_D_1 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','40'])).

thf('42',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X13 @ X15 )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('43',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( r2_hidden @ ( sk_E_1 @ sk_C @ sk_A @ sk_D_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X42: $i] :
      ( ~ ( r2_hidden @ X42 @ sk_A )
      | ( ( k1_funct_1 @ sk_D_1 @ X42 )
       != sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_C @ sk_A @ sk_D_1 ) )
     != sk_C ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( zip_tseitin_0 @ ( sk_E_1 @ sk_C @ sk_A @ sk_D_1 ) @ sk_C @ sk_A @ sk_D_1 )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['13','40'])).

thf('47',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X14
        = ( k1_funct_1 @ X12 @ X13 ) )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('48',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( sk_C
      = ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_C @ sk_A @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['45','48'])).

thf('50',plain,(
    r2_hidden @ sk_C @ k1_xboole_0 ),
    inference(demod,[status(thm)],['12','49'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('52',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('53',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X1 @ X2 )
      | ( r2_hidden @ X1 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[l3_subset_1])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( r2_hidden @ sk_C @ X0 ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    ! [X18: $i,X19: $i,X22: $i] :
      ( ~ ( v1_relat_1 @ X19 )
      | ~ ( v1_funct_1 @ X19 )
      | ~ ( r2_hidden @ X22 @ ( k9_relat_1 @ X19 @ X18 ) )
      | ( zip_tseitin_0 @ ( sk_E_1 @ X22 @ X18 @ X19 ) @ X22 @ X18 @ X19 ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_E_1 @ sk_C @ X0 @ X1 ) @ sk_C @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X14
        = ( k1_funct_1 @ X12 @ X13 ) )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( sk_C
        = ( k1_funct_1 @ X0 @ ( sk_E_1 @ sk_C @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ ( sk_E_1 @ sk_C @ X0 @ X1 ) @ sk_C @ X0 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('62',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( r2_hidden @ X13 @ X15 )
      | ~ ( zip_tseitin_0 @ X13 @ X14 @ X15 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_7])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_hidden @ ( sk_E_1 @ sk_C @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X42: $i] :
      ( ~ ( r2_hidden @ X42 @ sk_A )
      | ( ( k1_funct_1 @ sk_D_1 @ X42 )
       != sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_funct_1 @ sk_D_1 @ ( sk_E_1 @ sk_C @ sk_A @ X0 ) )
       != sk_C ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( sk_C != sk_C )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ~ ( v1_funct_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['60','65'])).

thf('67',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['31','32'])).

thf('69',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['31','32'])).

thf('70',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    sk_C != sk_C ),
    inference(demod,[status(thm)],['66','67','68','69','70'])).

thf('72',plain,(
    $false ),
    inference(simplify,[status(thm)],['71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Oowbq9IZ4q
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:49:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 20.32/20.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 20.32/20.54  % Solved by: fo/fo7.sh
% 20.32/20.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 20.32/20.54  % done 6522 iterations in 20.083s
% 20.32/20.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 20.32/20.54  % SZS output start Refutation
% 20.32/20.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 20.32/20.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 20.32/20.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 20.32/20.54  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 20.32/20.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 20.32/20.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 20.32/20.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 20.32/20.54  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 20.32/20.54  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $o).
% 20.32/20.54  thf(sk_C_type, type, sk_C: $i).
% 20.32/20.54  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $o).
% 20.32/20.54  thf(sk_E_1_type, type, sk_E_1: $i > $i > $i > $i).
% 20.32/20.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 20.32/20.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 20.32/20.54  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $o).
% 20.32/20.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 20.32/20.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 20.32/20.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 20.32/20.54  thf(sk_D_1_type, type, sk_D_1: $i).
% 20.32/20.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 20.32/20.54  thf(sk_A_type, type, sk_A: $i).
% 20.32/20.54  thf(sk_B_type, type, sk_B: $i).
% 20.32/20.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 20.32/20.54  thf(t17_funct_2, conjecture,
% 20.32/20.54    (![A:$i,B:$i,C:$i,D:$i]:
% 20.32/20.54     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 20.32/20.54         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 20.32/20.54       ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 20.32/20.54            ( ![E:$i]:
% 20.32/20.54              ( ~( ( r2_hidden @ E @ A ) & ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ))).
% 20.32/20.54  thf(zf_stmt_0, negated_conjecture,
% 20.32/20.54    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 20.32/20.54        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 20.32/20.54            ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 20.32/20.54          ( ~( ( r2_hidden @ C @ ( k2_relset_1 @ A @ B @ D ) ) & 
% 20.32/20.54               ( ![E:$i]:
% 20.32/20.54                 ( ~( ( r2_hidden @ E @ A ) & 
% 20.32/20.54                      ( ( k1_funct_1 @ D @ E ) = ( C ) ) ) ) ) ) ) ) )),
% 20.32/20.54    inference('cnf.neg', [status(esa)], [t17_funct_2])).
% 20.32/20.54  thf('0', plain, ((r2_hidden @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D_1))),
% 20.32/20.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.32/20.54  thf('1', plain,
% 20.32/20.54      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 20.32/20.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.32/20.54  thf(redefinition_k2_relset_1, axiom,
% 20.32/20.54    (![A:$i,B:$i,C:$i]:
% 20.32/20.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 20.32/20.54       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 20.32/20.54  thf('2', plain,
% 20.32/20.54      (![X31 : $i, X32 : $i, X33 : $i]:
% 20.32/20.54         (((k2_relset_1 @ X32 @ X33 @ X31) = (k2_relat_1 @ X31))
% 20.32/20.54          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 20.32/20.54      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 20.32/20.54  thf('3', plain,
% 20.32/20.54      (((k2_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 20.32/20.54      inference('sup-', [status(thm)], ['1', '2'])).
% 20.32/20.54  thf('4', plain, ((r2_hidden @ sk_C @ (k2_relat_1 @ sk_D_1))),
% 20.32/20.54      inference('demod', [status(thm)], ['0', '3'])).
% 20.32/20.54  thf('5', plain,
% 20.32/20.54      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 20.32/20.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.32/20.54  thf(dt_k2_relset_1, axiom,
% 20.32/20.54    (![A:$i,B:$i,C:$i]:
% 20.32/20.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 20.32/20.54       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 20.32/20.54  thf('6', plain,
% 20.32/20.54      (![X25 : $i, X26 : $i, X27 : $i]:
% 20.32/20.54         ((m1_subset_1 @ (k2_relset_1 @ X25 @ X26 @ X27) @ (k1_zfmisc_1 @ X26))
% 20.32/20.54          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 20.32/20.54      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 20.32/20.54  thf('7', plain,
% 20.32/20.54      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_D_1) @ 
% 20.32/20.54        (k1_zfmisc_1 @ sk_B))),
% 20.32/20.54      inference('sup-', [status(thm)], ['5', '6'])).
% 20.32/20.54  thf('8', plain,
% 20.32/20.54      (((k2_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 20.32/20.54      inference('sup-', [status(thm)], ['1', '2'])).
% 20.32/20.54  thf('9', plain,
% 20.32/20.54      ((m1_subset_1 @ (k2_relat_1 @ sk_D_1) @ (k1_zfmisc_1 @ sk_B))),
% 20.32/20.54      inference('demod', [status(thm)], ['7', '8'])).
% 20.32/20.54  thf(l3_subset_1, axiom,
% 20.32/20.54    (![A:$i,B:$i]:
% 20.32/20.54     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 20.32/20.54       ( ![C:$i]: ( ( r2_hidden @ C @ B ) => ( r2_hidden @ C @ A ) ) ) ))).
% 20.32/20.54  thf('10', plain,
% 20.32/20.54      (![X1 : $i, X2 : $i, X3 : $i]:
% 20.32/20.54         (~ (r2_hidden @ X1 @ X2)
% 20.32/20.54          | (r2_hidden @ X1 @ X3)
% 20.32/20.54          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 20.32/20.54      inference('cnf', [status(esa)], [l3_subset_1])).
% 20.32/20.54  thf('11', plain,
% 20.32/20.54      (![X0 : $i]:
% 20.32/20.54         ((r2_hidden @ X0 @ sk_B) | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_1)))),
% 20.32/20.54      inference('sup-', [status(thm)], ['9', '10'])).
% 20.32/20.54  thf('12', plain, ((r2_hidden @ sk_C @ sk_B)),
% 20.32/20.54      inference('sup-', [status(thm)], ['4', '11'])).
% 20.32/20.54  thf('13', plain, ((r2_hidden @ sk_C @ (k2_relat_1 @ sk_D_1))),
% 20.32/20.54      inference('demod', [status(thm)], ['0', '3'])).
% 20.32/20.54  thf(d1_funct_2, axiom,
% 20.32/20.54    (![A:$i,B:$i,C:$i]:
% 20.32/20.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 20.32/20.54       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 20.32/20.54           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 20.32/20.54             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 20.32/20.54         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 20.32/20.54           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 20.32/20.54             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 20.32/20.54  thf(zf_stmt_1, axiom,
% 20.32/20.54    (![B:$i,A:$i]:
% 20.32/20.54     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 20.32/20.54       ( zip_tseitin_1 @ B @ A ) ))).
% 20.32/20.54  thf('14', plain,
% 20.32/20.54      (![X34 : $i, X35 : $i]:
% 20.32/20.54         ((zip_tseitin_1 @ X34 @ X35) | ((X34) = (k1_xboole_0)))),
% 20.32/20.54      inference('cnf', [status(esa)], [zf_stmt_1])).
% 20.32/20.54  thf('15', plain,
% 20.32/20.54      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 20.32/20.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.32/20.54  thf(zf_stmt_2, type, zip_tseitin_2 : $i > $i > $i > $o).
% 20.32/20.54  thf(zf_stmt_3, axiom,
% 20.32/20.54    (![C:$i,B:$i,A:$i]:
% 20.32/20.54     ( ( zip_tseitin_2 @ C @ B @ A ) =>
% 20.32/20.54       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 20.32/20.54  thf(zf_stmt_4, type, zip_tseitin_1 : $i > $i > $o).
% 20.32/20.54  thf(zf_stmt_5, axiom,
% 20.32/20.54    (![A:$i,B:$i,C:$i]:
% 20.32/20.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 20.32/20.54       ( ( ( zip_tseitin_1 @ B @ A ) => ( zip_tseitin_2 @ C @ B @ A ) ) & 
% 20.32/20.54         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 20.32/20.54           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 20.32/20.54             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 20.32/20.54  thf('16', plain,
% 20.32/20.54      (![X39 : $i, X40 : $i, X41 : $i]:
% 20.32/20.54         (~ (zip_tseitin_1 @ X39 @ X40)
% 20.32/20.54          | (zip_tseitin_2 @ X41 @ X39 @ X40)
% 20.32/20.54          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39))))),
% 20.32/20.54      inference('cnf', [status(esa)], [zf_stmt_5])).
% 20.32/20.54  thf('17', plain,
% 20.32/20.54      (((zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)
% 20.32/20.54        | ~ (zip_tseitin_1 @ sk_B @ sk_A))),
% 20.32/20.54      inference('sup-', [status(thm)], ['15', '16'])).
% 20.32/20.54  thf('18', plain,
% 20.32/20.54      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A))),
% 20.32/20.54      inference('sup-', [status(thm)], ['14', '17'])).
% 20.32/20.54  thf('19', plain, ((v1_funct_2 @ sk_D_1 @ sk_A @ sk_B)),
% 20.32/20.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.32/20.54  thf('20', plain,
% 20.32/20.54      (![X36 : $i, X37 : $i, X38 : $i]:
% 20.32/20.54         (~ (v1_funct_2 @ X38 @ X36 @ X37)
% 20.32/20.54          | ((X36) = (k1_relset_1 @ X36 @ X37 @ X38))
% 20.32/20.54          | ~ (zip_tseitin_2 @ X38 @ X37 @ X36))),
% 20.32/20.54      inference('cnf', [status(esa)], [zf_stmt_3])).
% 20.32/20.54  thf('21', plain,
% 20.32/20.54      ((~ (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)
% 20.32/20.54        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_D_1)))),
% 20.32/20.54      inference('sup-', [status(thm)], ['19', '20'])).
% 20.32/20.54  thf('22', plain,
% 20.32/20.54      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 20.32/20.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.32/20.54  thf(redefinition_k1_relset_1, axiom,
% 20.32/20.54    (![A:$i,B:$i,C:$i]:
% 20.32/20.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 20.32/20.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 20.32/20.54  thf('23', plain,
% 20.32/20.54      (![X28 : $i, X29 : $i, X30 : $i]:
% 20.32/20.54         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 20.32/20.54          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 20.32/20.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 20.32/20.54  thf('24', plain,
% 20.32/20.54      (((k1_relset_1 @ sk_A @ sk_B @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 20.32/20.54      inference('sup-', [status(thm)], ['22', '23'])).
% 20.32/20.54  thf('25', plain,
% 20.32/20.54      ((~ (zip_tseitin_2 @ sk_D_1 @ sk_B @ sk_A)
% 20.32/20.54        | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 20.32/20.54      inference('demod', [status(thm)], ['21', '24'])).
% 20.32/20.54  thf('26', plain,
% 20.32/20.54      ((((sk_B) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_D_1)))),
% 20.32/20.54      inference('sup-', [status(thm)], ['18', '25'])).
% 20.32/20.54  thf(t146_relat_1, axiom,
% 20.32/20.54    (![A:$i]:
% 20.32/20.54     ( ( v1_relat_1 @ A ) =>
% 20.32/20.54       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 20.32/20.54  thf('27', plain,
% 20.32/20.54      (![X11 : $i]:
% 20.32/20.54         (((k9_relat_1 @ X11 @ (k1_relat_1 @ X11)) = (k2_relat_1 @ X11))
% 20.32/20.54          | ~ (v1_relat_1 @ X11))),
% 20.32/20.54      inference('cnf', [status(esa)], [t146_relat_1])).
% 20.32/20.54  thf('28', plain,
% 20.32/20.54      ((((k9_relat_1 @ sk_D_1 @ sk_A) = (k2_relat_1 @ sk_D_1))
% 20.32/20.54        | ((sk_B) = (k1_xboole_0))
% 20.32/20.54        | ~ (v1_relat_1 @ sk_D_1))),
% 20.32/20.54      inference('sup+', [status(thm)], ['26', '27'])).
% 20.32/20.54  thf('29', plain,
% 20.32/20.54      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 20.32/20.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.32/20.54  thf(cc2_relat_1, axiom,
% 20.32/20.54    (![A:$i]:
% 20.32/20.54     ( ( v1_relat_1 @ A ) =>
% 20.32/20.54       ( ![B:$i]:
% 20.32/20.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 20.32/20.54  thf('30', plain,
% 20.32/20.54      (![X7 : $i, X8 : $i]:
% 20.32/20.54         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 20.32/20.54          | (v1_relat_1 @ X7)
% 20.32/20.54          | ~ (v1_relat_1 @ X8))),
% 20.32/20.54      inference('cnf', [status(esa)], [cc2_relat_1])).
% 20.32/20.54  thf('31', plain,
% 20.32/20.54      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_D_1))),
% 20.32/20.54      inference('sup-', [status(thm)], ['29', '30'])).
% 20.32/20.54  thf(fc6_relat_1, axiom,
% 20.32/20.54    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 20.32/20.54  thf('32', plain,
% 20.32/20.54      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 20.32/20.54      inference('cnf', [status(esa)], [fc6_relat_1])).
% 20.32/20.54  thf('33', plain, ((v1_relat_1 @ sk_D_1)),
% 20.32/20.54      inference('demod', [status(thm)], ['31', '32'])).
% 20.32/20.54  thf('34', plain,
% 20.32/20.54      ((((k9_relat_1 @ sk_D_1 @ sk_A) = (k2_relat_1 @ sk_D_1))
% 20.32/20.54        | ((sk_B) = (k1_xboole_0)))),
% 20.32/20.54      inference('demod', [status(thm)], ['28', '33'])).
% 20.32/20.54  thf(d12_funct_1, axiom,
% 20.32/20.54    (![A:$i]:
% 20.32/20.54     ( ( ( v1_funct_1 @ A ) & ( v1_relat_1 @ A ) ) =>
% 20.32/20.54       ( ![B:$i,C:$i]:
% 20.32/20.54         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 20.32/20.54           ( ![D:$i]:
% 20.32/20.54             ( ( r2_hidden @ D @ C ) <=>
% 20.32/20.54               ( ?[E:$i]:
% 20.32/20.54                 ( ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) & 
% 20.32/20.54                   ( r2_hidden @ E @ B ) & ( ( D ) = ( k1_funct_1 @ A @ E ) ) ) ) ) ) ) ) ))).
% 20.32/20.54  thf(zf_stmt_6, type, zip_tseitin_0 : $i > $i > $i > $i > $o).
% 20.32/20.54  thf(zf_stmt_7, axiom,
% 20.32/20.54    (![E:$i,D:$i,B:$i,A:$i]:
% 20.32/20.54     ( ( zip_tseitin_0 @ E @ D @ B @ A ) <=>
% 20.32/20.54       ( ( ( D ) = ( k1_funct_1 @ A @ E ) ) & ( r2_hidden @ E @ B ) & 
% 20.32/20.54         ( r2_hidden @ E @ ( k1_relat_1 @ A ) ) ) ))).
% 20.32/20.54  thf(zf_stmt_8, axiom,
% 20.32/20.54    (![A:$i]:
% 20.32/20.54     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 20.32/20.54       ( ![B:$i,C:$i]:
% 20.32/20.54         ( ( ( C ) = ( k9_relat_1 @ A @ B ) ) <=>
% 20.32/20.54           ( ![D:$i]:
% 20.32/20.54             ( ( r2_hidden @ D @ C ) <=>
% 20.32/20.54               ( ?[E:$i]: ( zip_tseitin_0 @ E @ D @ B @ A ) ) ) ) ) ) ))).
% 20.32/20.54  thf('35', plain,
% 20.32/20.54      (![X18 : $i, X19 : $i, X21 : $i, X22 : $i]:
% 20.32/20.54         (((X21) != (k9_relat_1 @ X19 @ X18))
% 20.32/20.54          | (zip_tseitin_0 @ (sk_E_1 @ X22 @ X18 @ X19) @ X22 @ X18 @ X19)
% 20.32/20.54          | ~ (r2_hidden @ X22 @ X21)
% 20.32/20.54          | ~ (v1_funct_1 @ X19)
% 20.32/20.54          | ~ (v1_relat_1 @ X19))),
% 20.32/20.54      inference('cnf', [status(esa)], [zf_stmt_8])).
% 20.32/20.54  thf('36', plain,
% 20.32/20.54      (![X18 : $i, X19 : $i, X22 : $i]:
% 20.32/20.54         (~ (v1_relat_1 @ X19)
% 20.32/20.54          | ~ (v1_funct_1 @ X19)
% 20.32/20.54          | ~ (r2_hidden @ X22 @ (k9_relat_1 @ X19 @ X18))
% 20.32/20.54          | (zip_tseitin_0 @ (sk_E_1 @ X22 @ X18 @ X19) @ X22 @ X18 @ X19))),
% 20.32/20.54      inference('simplify', [status(thm)], ['35'])).
% 20.32/20.54  thf('37', plain,
% 20.32/20.54      (![X0 : $i]:
% 20.32/20.54         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_1))
% 20.32/20.54          | ((sk_B) = (k1_xboole_0))
% 20.32/20.54          | (zip_tseitin_0 @ (sk_E_1 @ X0 @ sk_A @ sk_D_1) @ X0 @ sk_A @ sk_D_1)
% 20.32/20.54          | ~ (v1_funct_1 @ sk_D_1)
% 20.32/20.54          | ~ (v1_relat_1 @ sk_D_1))),
% 20.32/20.54      inference('sup-', [status(thm)], ['34', '36'])).
% 20.32/20.54  thf('38', plain, ((v1_funct_1 @ sk_D_1)),
% 20.32/20.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.32/20.54  thf('39', plain, ((v1_relat_1 @ sk_D_1)),
% 20.32/20.54      inference('demod', [status(thm)], ['31', '32'])).
% 20.32/20.54  thf('40', plain,
% 20.32/20.54      (![X0 : $i]:
% 20.32/20.54         (~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_D_1))
% 20.32/20.54          | ((sk_B) = (k1_xboole_0))
% 20.32/20.54          | (zip_tseitin_0 @ (sk_E_1 @ X0 @ sk_A @ sk_D_1) @ X0 @ sk_A @ sk_D_1))),
% 20.32/20.54      inference('demod', [status(thm)], ['37', '38', '39'])).
% 20.32/20.54  thf('41', plain,
% 20.32/20.54      (((zip_tseitin_0 @ (sk_E_1 @ sk_C @ sk_A @ sk_D_1) @ sk_C @ sk_A @ sk_D_1)
% 20.32/20.54        | ((sk_B) = (k1_xboole_0)))),
% 20.32/20.54      inference('sup-', [status(thm)], ['13', '40'])).
% 20.32/20.54  thf('42', plain,
% 20.32/20.54      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 20.32/20.54         ((r2_hidden @ X13 @ X15) | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X12))),
% 20.32/20.54      inference('cnf', [status(esa)], [zf_stmt_7])).
% 20.32/20.54  thf('43', plain,
% 20.32/20.54      ((((sk_B) = (k1_xboole_0))
% 20.32/20.54        | (r2_hidden @ (sk_E_1 @ sk_C @ sk_A @ sk_D_1) @ sk_A))),
% 20.32/20.54      inference('sup-', [status(thm)], ['41', '42'])).
% 20.32/20.54  thf('44', plain,
% 20.32/20.54      (![X42 : $i]:
% 20.32/20.54         (~ (r2_hidden @ X42 @ sk_A) | ((k1_funct_1 @ sk_D_1 @ X42) != (sk_C)))),
% 20.32/20.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.32/20.54  thf('45', plain,
% 20.32/20.54      ((((sk_B) = (k1_xboole_0))
% 20.32/20.54        | ((k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_C @ sk_A @ sk_D_1)) != (sk_C)))),
% 20.32/20.54      inference('sup-', [status(thm)], ['43', '44'])).
% 20.32/20.54  thf('46', plain,
% 20.32/20.54      (((zip_tseitin_0 @ (sk_E_1 @ sk_C @ sk_A @ sk_D_1) @ sk_C @ sk_A @ sk_D_1)
% 20.32/20.54        | ((sk_B) = (k1_xboole_0)))),
% 20.32/20.54      inference('sup-', [status(thm)], ['13', '40'])).
% 20.32/20.54  thf('47', plain,
% 20.32/20.54      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 20.32/20.54         (((X14) = (k1_funct_1 @ X12 @ X13))
% 20.32/20.54          | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X12))),
% 20.32/20.54      inference('cnf', [status(esa)], [zf_stmt_7])).
% 20.32/20.54  thf('48', plain,
% 20.32/20.54      ((((sk_B) = (k1_xboole_0))
% 20.32/20.54        | ((sk_C) = (k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_C @ sk_A @ sk_D_1))))),
% 20.32/20.54      inference('sup-', [status(thm)], ['46', '47'])).
% 20.32/20.54  thf('49', plain, (((sk_B) = (k1_xboole_0))),
% 20.32/20.54      inference('clc', [status(thm)], ['45', '48'])).
% 20.32/20.54  thf('50', plain, ((r2_hidden @ sk_C @ k1_xboole_0)),
% 20.32/20.54      inference('demod', [status(thm)], ['12', '49'])).
% 20.32/20.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 20.32/20.54  thf('51', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 20.32/20.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 20.32/20.54  thf(t3_subset, axiom,
% 20.32/20.54    (![A:$i,B:$i]:
% 20.32/20.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 20.32/20.54  thf('52', plain,
% 20.32/20.54      (![X4 : $i, X6 : $i]:
% 20.32/20.54         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 20.32/20.54      inference('cnf', [status(esa)], [t3_subset])).
% 20.32/20.54  thf('53', plain,
% 20.32/20.54      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 20.32/20.54      inference('sup-', [status(thm)], ['51', '52'])).
% 20.32/20.54  thf('54', plain,
% 20.32/20.54      (![X1 : $i, X2 : $i, X3 : $i]:
% 20.32/20.54         (~ (r2_hidden @ X1 @ X2)
% 20.32/20.54          | (r2_hidden @ X1 @ X3)
% 20.32/20.54          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 20.32/20.54      inference('cnf', [status(esa)], [l3_subset_1])).
% 20.32/20.54  thf('55', plain,
% 20.32/20.54      (![X0 : $i, X1 : $i]:
% 20.32/20.54         ((r2_hidden @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 20.32/20.54      inference('sup-', [status(thm)], ['53', '54'])).
% 20.32/20.54  thf('56', plain, (![X0 : $i]: (r2_hidden @ sk_C @ X0)),
% 20.32/20.54      inference('sup-', [status(thm)], ['50', '55'])).
% 20.32/20.54  thf('57', plain,
% 20.32/20.54      (![X18 : $i, X19 : $i, X22 : $i]:
% 20.32/20.54         (~ (v1_relat_1 @ X19)
% 20.32/20.54          | ~ (v1_funct_1 @ X19)
% 20.32/20.54          | ~ (r2_hidden @ X22 @ (k9_relat_1 @ X19 @ X18))
% 20.32/20.54          | (zip_tseitin_0 @ (sk_E_1 @ X22 @ X18 @ X19) @ X22 @ X18 @ X19))),
% 20.32/20.54      inference('simplify', [status(thm)], ['35'])).
% 20.32/20.54  thf('58', plain,
% 20.32/20.54      (![X0 : $i, X1 : $i]:
% 20.32/20.54         ((zip_tseitin_0 @ (sk_E_1 @ sk_C @ X0 @ X1) @ sk_C @ X0 @ X1)
% 20.32/20.54          | ~ (v1_funct_1 @ X1)
% 20.32/20.54          | ~ (v1_relat_1 @ X1))),
% 20.32/20.54      inference('sup-', [status(thm)], ['56', '57'])).
% 20.32/20.54  thf('59', plain,
% 20.32/20.54      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 20.32/20.54         (((X14) = (k1_funct_1 @ X12 @ X13))
% 20.32/20.54          | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X12))),
% 20.32/20.54      inference('cnf', [status(esa)], [zf_stmt_7])).
% 20.32/20.54  thf('60', plain,
% 20.32/20.54      (![X0 : $i, X1 : $i]:
% 20.32/20.54         (~ (v1_relat_1 @ X0)
% 20.32/20.54          | ~ (v1_funct_1 @ X0)
% 20.32/20.54          | ((sk_C) = (k1_funct_1 @ X0 @ (sk_E_1 @ sk_C @ X1 @ X0))))),
% 20.32/20.54      inference('sup-', [status(thm)], ['58', '59'])).
% 20.32/20.54  thf('61', plain,
% 20.32/20.54      (![X0 : $i, X1 : $i]:
% 20.32/20.54         ((zip_tseitin_0 @ (sk_E_1 @ sk_C @ X0 @ X1) @ sk_C @ X0 @ X1)
% 20.32/20.54          | ~ (v1_funct_1 @ X1)
% 20.32/20.54          | ~ (v1_relat_1 @ X1))),
% 20.32/20.54      inference('sup-', [status(thm)], ['56', '57'])).
% 20.32/20.54  thf('62', plain,
% 20.32/20.54      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 20.32/20.54         ((r2_hidden @ X13 @ X15) | ~ (zip_tseitin_0 @ X13 @ X14 @ X15 @ X12))),
% 20.32/20.54      inference('cnf', [status(esa)], [zf_stmt_7])).
% 20.32/20.54  thf('63', plain,
% 20.32/20.54      (![X0 : $i, X1 : $i]:
% 20.32/20.54         (~ (v1_relat_1 @ X0)
% 20.32/20.54          | ~ (v1_funct_1 @ X0)
% 20.32/20.54          | (r2_hidden @ (sk_E_1 @ sk_C @ X1 @ X0) @ X1))),
% 20.32/20.54      inference('sup-', [status(thm)], ['61', '62'])).
% 20.32/20.54  thf('64', plain,
% 20.32/20.54      (![X42 : $i]:
% 20.32/20.54         (~ (r2_hidden @ X42 @ sk_A) | ((k1_funct_1 @ sk_D_1 @ X42) != (sk_C)))),
% 20.32/20.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.32/20.54  thf('65', plain,
% 20.32/20.54      (![X0 : $i]:
% 20.32/20.54         (~ (v1_funct_1 @ X0)
% 20.32/20.54          | ~ (v1_relat_1 @ X0)
% 20.32/20.54          | ((k1_funct_1 @ sk_D_1 @ (sk_E_1 @ sk_C @ sk_A @ X0)) != (sk_C)))),
% 20.32/20.54      inference('sup-', [status(thm)], ['63', '64'])).
% 20.32/20.54  thf('66', plain,
% 20.32/20.54      ((((sk_C) != (sk_C))
% 20.32/20.54        | ~ (v1_funct_1 @ sk_D_1)
% 20.32/20.54        | ~ (v1_relat_1 @ sk_D_1)
% 20.32/20.54        | ~ (v1_relat_1 @ sk_D_1)
% 20.32/20.54        | ~ (v1_funct_1 @ sk_D_1))),
% 20.32/20.54      inference('sup-', [status(thm)], ['60', '65'])).
% 20.32/20.54  thf('67', plain, ((v1_funct_1 @ sk_D_1)),
% 20.32/20.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.32/20.54  thf('68', plain, ((v1_relat_1 @ sk_D_1)),
% 20.32/20.54      inference('demod', [status(thm)], ['31', '32'])).
% 20.32/20.54  thf('69', plain, ((v1_relat_1 @ sk_D_1)),
% 20.32/20.54      inference('demod', [status(thm)], ['31', '32'])).
% 20.32/20.54  thf('70', plain, ((v1_funct_1 @ sk_D_1)),
% 20.32/20.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 20.32/20.54  thf('71', plain, (((sk_C) != (sk_C))),
% 20.32/20.54      inference('demod', [status(thm)], ['66', '67', '68', '69', '70'])).
% 20.32/20.54  thf('72', plain, ($false), inference('simplify', [status(thm)], ['71'])).
% 20.32/20.54  
% 20.32/20.54  % SZS output end Refutation
% 20.32/20.54  
% 20.32/20.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
