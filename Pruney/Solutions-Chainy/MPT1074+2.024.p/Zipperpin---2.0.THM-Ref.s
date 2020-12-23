%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2lIQ7Xa4Zo

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:25 EST 2020

% Result     : Theorem 2.33s
% Output     : Refutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :  144 (2114 expanded)
%              Number of leaves         :   47 ( 631 expanded)
%              Depth                    :   25
%              Number of atoms          : 1162 (28308 expanded)
%              Number of equality atoms :   62 (1297 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t191_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ~ ( v1_xboole_0 @ C )
         => ! [D: $i] :
              ( ( ( v1_funct_1 @ D )
                & ( v1_funct_2 @ D @ B @ C )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
             => ( ! [E: $i] :
                    ( ( m1_subset_1 @ E @ B )
                   => ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) )
               => ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ~ ( v1_xboole_0 @ B )
       => ! [C: $i] :
            ( ~ ( v1_xboole_0 @ C )
           => ! [D: $i] :
                ( ( ( v1_funct_1 @ D )
                  & ( v1_funct_2 @ D @ B @ C )
                  & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
               => ( ! [E: $i] :
                      ( ( m1_subset_1 @ E @ B )
                     => ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) )
                 => ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t191_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ) ),
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
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('5',plain,(
    ! [X21: $i,X22: $i] :
      ( ( zip_tseitin_0 @ X21 @ X22 )
      | ( X21 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('6',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('7',plain,(
    ! [X1: $i] :
      ( ( k2_zfmisc_1 @ X1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['5','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    r1_tarski @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ sk_D_1 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_C @ X0 ) ) ),
    inference('sup+',[status(thm)],['8','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( zip_tseitin_0 @ X26 @ X27 )
      | ( zip_tseitin_1 @ X28 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('15',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( r1_tarski @ sk_D_1 @ k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['12','15'])).

thf('17',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_2 @ X25 @ X23 @ X24 )
      | ( X23
        = ( k1_relset_1 @ X23 @ X24 @ X25 ) )
      | ~ ( zip_tseitin_1 @ X25 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('19',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('21',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('22',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,
    ( ( r1_tarski @ sk_D_1 @ k1_xboole_0 )
    | ( sk_B
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['16','23'])).

thf('25',plain,(
    ! [X5: $i,X7: $i] :
      ( ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,
    ( ( sk_B
      = ( k1_relat_1 @ sk_D_1 ) )
    | ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X2 )
        = k1_xboole_0 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('28',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( ( k2_relset_1 @ k1_xboole_0 @ X0 @ X1 )
        = ( k2_relat_1 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k1_relat_1 @ sk_D_1 ) )
      | ( ( k2_relset_1 @ k1_xboole_0 @ X0 @ sk_D_1 )
        = ( k2_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['26','30'])).

thf('32',plain,
    ( ( sk_B
      = ( k1_relat_1 @ sk_D_1 ) )
    | ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('33',plain,(
    ! [X2: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['27'])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('34',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X12 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( m1_subset_1 @ ( k2_relset_1 @ k1_xboole_0 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k1_relat_1 @ sk_D_1 ) )
      | ( m1_subset_1 @ ( k2_relset_1 @ k1_xboole_0 @ X0 @ sk_D_1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ X0 ) )
      | ( sk_B
        = ( k1_relat_1 @ sk_D_1 ) )
      | ( sk_B
        = ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup+',[status(thm)],['31','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k1_relat_1 @ sk_D_1 ) )
      | ( m1_subset_1 @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( sk_B
        = ( k1_relat_1 @ sk_D_1 ) )
      | ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('42',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t5_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_relat_1 @ C ) )
     => ( ( ! [D: $i] :
              ( ( r2_hidden @ D @ A )
             => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
          & ( ( k1_relat_1 @ C )
            = A ) )
       => ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
          & ( v1_funct_2 @ C @ A @ B )
          & ( v1_funct_1 @ C ) ) ) ) )).

thf(zf_stmt_6,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r2_hidden @ D @ A )
       => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
     => ( zip_tseitin_2 @ D @ C @ B @ A ) ) )).

thf('43',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( zip_tseitin_2 @ X35 @ X36 @ X37 @ X38 )
      | ( r2_hidden @ X35 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf(zf_stmt_7,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(zf_stmt_8,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_3 @ C @ B @ A )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_9,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(zf_stmt_10,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( ( k1_relat_1 @ C )
            = A )
          & ! [D: $i] :
              ( zip_tseitin_2 @ D @ C @ B @ A ) )
       => ( zip_tseitin_3 @ C @ B @ A ) ) ) )).

thf('44',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( ( k1_relat_1 @ X43 )
       != X42 )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X43 @ X44 @ X42 ) @ X43 @ X44 @ X42 )
      | ( zip_tseitin_3 @ X43 @ X44 @ X42 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('45',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ~ ( v1_funct_1 @ X43 )
      | ( zip_tseitin_3 @ X43 @ X44 @ ( k1_relat_1 @ X43 ) )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X43 @ X44 @ ( k1_relat_1 @ X43 ) ) @ X43 @ X44 @ ( k1_relat_1 @ X43 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) )
      | ( zip_tseitin_3 @ X0 @ X1 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['43','45'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('47',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( zip_tseitin_3 @ X0 @ X1 @ ( k1_relat_1 @ X0 ) )
      | ( m1_subset_1 @ ( sk_D @ X0 @ X1 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['42','48'])).

thf('50',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('51',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('52',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('54',plain,(
    ! [X8: $i,X9: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) )
      | ( v1_relat_1 @ X8 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('55',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('56',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('57',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','50','51','52','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('60',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X31 )
      | ~ ( v1_funct_1 @ X29 )
      | ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X32 @ X30 )
      | ( ( k3_funct_2 @ X30 @ X31 @ X29 @ X32 )
        = ( k1_funct_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) )
        = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['58','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['49','50','51','52','57'])).

thf('69',plain,(
    ! [X45: $i] :
      ( ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X45 ) @ sk_A )
      | ~ ( m1_subset_1 @ X45 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) @ sk_A )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['67','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( zip_tseitin_2 @ X35 @ X36 @ X37 @ X38 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X36 @ X35 ) @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('74',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('76',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ~ ( v1_funct_1 @ X43 )
      | ( zip_tseitin_3 @ X43 @ X44 @ ( k1_relat_1 @ X43 ) )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X43 @ X44 @ ( k1_relat_1 @ X43 ) ) @ X43 @ X44 @ ( k1_relat_1 @ X43 ) ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('79',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('80',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['55','56'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['77','78','79','80','81'])).

thf('83',plain,
    ( ( zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B )
    | ( zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['74','82'])).

thf('84',plain,(
    zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) )
      | ~ ( zip_tseitin_3 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('86',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X12 @ X13 @ X14 ) @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('88',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['86','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('90',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k2_relset_1 @ X19 @ X20 @ X18 )
        = ( k2_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('91',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('94',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    $false ),
    inference(demod,[status(thm)],['4','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.2lIQ7Xa4Zo
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:09:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.33/2.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 2.33/2.51  % Solved by: fo/fo7.sh
% 2.33/2.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.33/2.51  % done 1504 iterations in 2.050s
% 2.33/2.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 2.33/2.51  % SZS output start Refutation
% 2.33/2.51  thf(sk_C_type, type, sk_C: $i).
% 2.33/2.51  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.33/2.51  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $o).
% 2.33/2.51  thf(sk_B_type, type, sk_B: $i).
% 2.33/2.51  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.33/2.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.33/2.51  thf(sk_A_type, type, sk_A: $i).
% 2.33/2.51  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 2.33/2.51  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 2.33/2.51  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 2.33/2.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.33/2.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.33/2.51  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 2.33/2.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.33/2.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.33/2.51  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 2.33/2.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.33/2.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.33/2.51  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 2.33/2.51  thf(sk_D_1_type, type, sk_D_1: $i).
% 2.33/2.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.33/2.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 2.33/2.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.33/2.51  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.33/2.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.33/2.51  thf(t191_funct_2, conjecture,
% 2.33/2.51    (![A:$i,B:$i]:
% 2.33/2.51     ( ( ~( v1_xboole_0 @ B ) ) =>
% 2.33/2.51       ( ![C:$i]:
% 2.33/2.51         ( ( ~( v1_xboole_0 @ C ) ) =>
% 2.33/2.51           ( ![D:$i]:
% 2.33/2.51             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 2.33/2.51                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.33/2.51               ( ( ![E:$i]:
% 2.33/2.51                   ( ( m1_subset_1 @ E @ B ) =>
% 2.33/2.51                     ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 2.33/2.51                 ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ))).
% 2.33/2.51  thf(zf_stmt_0, negated_conjecture,
% 2.33/2.51    (~( ![A:$i,B:$i]:
% 2.33/2.51        ( ( ~( v1_xboole_0 @ B ) ) =>
% 2.33/2.51          ( ![C:$i]:
% 2.33/2.51            ( ( ~( v1_xboole_0 @ C ) ) =>
% 2.33/2.51              ( ![D:$i]:
% 2.33/2.51                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 2.33/2.51                    ( m1_subset_1 @
% 2.33/2.51                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.33/2.51                  ( ( ![E:$i]:
% 2.33/2.51                      ( ( m1_subset_1 @ E @ B ) =>
% 2.33/2.51                        ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 2.33/2.51                    ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ) )),
% 2.33/2.51    inference('cnf.neg', [status(esa)], [t191_funct_2])).
% 2.33/2.51  thf('0', plain,
% 2.33/2.51      (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D_1) @ sk_A)),
% 2.33/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.51  thf('1', plain,
% 2.33/2.51      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.33/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.51  thf(redefinition_k2_relset_1, axiom,
% 2.33/2.51    (![A:$i,B:$i,C:$i]:
% 2.33/2.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.33/2.51       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.33/2.51  thf('2', plain,
% 2.33/2.51      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.33/2.51         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 2.33/2.51          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 2.33/2.51      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.33/2.51  thf('3', plain,
% 2.33/2.51      (((k2_relset_1 @ sk_B @ sk_C @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 2.33/2.51      inference('sup-', [status(thm)], ['1', '2'])).
% 2.33/2.51  thf('4', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 2.33/2.51      inference('demod', [status(thm)], ['0', '3'])).
% 2.33/2.51  thf(d1_funct_2, axiom,
% 2.33/2.51    (![A:$i,B:$i,C:$i]:
% 2.33/2.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.33/2.51       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.33/2.51           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 2.33/2.51             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 2.33/2.51         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.33/2.51           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 2.33/2.51             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 2.33/2.51  thf(zf_stmt_1, axiom,
% 2.33/2.51    (![B:$i,A:$i]:
% 2.33/2.51     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 2.33/2.51       ( zip_tseitin_0 @ B @ A ) ))).
% 2.33/2.51  thf('5', plain,
% 2.33/2.51      (![X21 : $i, X22 : $i]:
% 2.33/2.51         ((zip_tseitin_0 @ X21 @ X22) | ((X21) = (k1_xboole_0)))),
% 2.33/2.51      inference('cnf', [status(esa)], [zf_stmt_1])).
% 2.33/2.51  thf(t113_zfmisc_1, axiom,
% 2.33/2.51    (![A:$i,B:$i]:
% 2.33/2.51     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.33/2.51       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.33/2.51  thf('6', plain,
% 2.33/2.51      (![X1 : $i, X2 : $i]:
% 2.33/2.51         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 2.33/2.51      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.33/2.51  thf('7', plain,
% 2.33/2.51      (![X1 : $i]: ((k2_zfmisc_1 @ X1 @ k1_xboole_0) = (k1_xboole_0))),
% 2.33/2.51      inference('simplify', [status(thm)], ['6'])).
% 2.33/2.51  thf('8', plain,
% 2.33/2.51      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.33/2.51         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | (zip_tseitin_0 @ X0 @ X2))),
% 2.33/2.51      inference('sup+', [status(thm)], ['5', '7'])).
% 2.33/2.51  thf('9', plain,
% 2.33/2.51      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.33/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.51  thf(t3_subset, axiom,
% 2.33/2.51    (![A:$i,B:$i]:
% 2.33/2.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.33/2.51  thf('10', plain,
% 2.33/2.51      (![X5 : $i, X6 : $i]:
% 2.33/2.51         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 2.33/2.51      inference('cnf', [status(esa)], [t3_subset])).
% 2.33/2.51  thf('11', plain, ((r1_tarski @ sk_D_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 2.33/2.51      inference('sup-', [status(thm)], ['9', '10'])).
% 2.33/2.51  thf('12', plain,
% 2.33/2.51      (![X0 : $i]:
% 2.33/2.51         ((r1_tarski @ sk_D_1 @ k1_xboole_0) | (zip_tseitin_0 @ sk_C @ X0))),
% 2.33/2.51      inference('sup+', [status(thm)], ['8', '11'])).
% 2.33/2.51  thf('13', plain,
% 2.33/2.51      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.33/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.51  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 2.33/2.51  thf(zf_stmt_3, axiom,
% 2.33/2.51    (![C:$i,B:$i,A:$i]:
% 2.33/2.51     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 2.33/2.51       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 2.33/2.51  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 2.33/2.51  thf(zf_stmt_5, axiom,
% 2.33/2.51    (![A:$i,B:$i,C:$i]:
% 2.33/2.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.33/2.51       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 2.33/2.51         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 2.33/2.51           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 2.33/2.51             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 2.33/2.51  thf('14', plain,
% 2.33/2.51      (![X26 : $i, X27 : $i, X28 : $i]:
% 2.33/2.51         (~ (zip_tseitin_0 @ X26 @ X27)
% 2.33/2.51          | (zip_tseitin_1 @ X28 @ X26 @ X27)
% 2.33/2.51          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X26))))),
% 2.33/2.51      inference('cnf', [status(esa)], [zf_stmt_5])).
% 2.33/2.51  thf('15', plain,
% 2.33/2.51      (((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)
% 2.33/2.51        | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 2.33/2.51      inference('sup-', [status(thm)], ['13', '14'])).
% 2.33/2.51  thf('16', plain,
% 2.33/2.51      (((r1_tarski @ sk_D_1 @ k1_xboole_0)
% 2.33/2.51        | (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B))),
% 2.33/2.51      inference('sup-', [status(thm)], ['12', '15'])).
% 2.33/2.51  thf('17', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_C)),
% 2.33/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.51  thf('18', plain,
% 2.33/2.51      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.33/2.51         (~ (v1_funct_2 @ X25 @ X23 @ X24)
% 2.33/2.51          | ((X23) = (k1_relset_1 @ X23 @ X24 @ X25))
% 2.33/2.51          | ~ (zip_tseitin_1 @ X25 @ X24 @ X23))),
% 2.33/2.51      inference('cnf', [status(esa)], [zf_stmt_3])).
% 2.33/2.51  thf('19', plain,
% 2.33/2.51      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)
% 2.33/2.51        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_D_1)))),
% 2.33/2.51      inference('sup-', [status(thm)], ['17', '18'])).
% 2.33/2.51  thf('20', plain,
% 2.33/2.51      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.33/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.51  thf(redefinition_k1_relset_1, axiom,
% 2.33/2.51    (![A:$i,B:$i,C:$i]:
% 2.33/2.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.33/2.51       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 2.33/2.51  thf('21', plain,
% 2.33/2.51      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.33/2.51         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 2.33/2.51          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 2.33/2.51      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 2.33/2.51  thf('22', plain,
% 2.33/2.51      (((k1_relset_1 @ sk_B @ sk_C @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 2.33/2.51      inference('sup-', [status(thm)], ['20', '21'])).
% 2.33/2.51  thf('23', plain,
% 2.33/2.51      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)
% 2.33/2.51        | ((sk_B) = (k1_relat_1 @ sk_D_1)))),
% 2.33/2.51      inference('demod', [status(thm)], ['19', '22'])).
% 2.33/2.51  thf('24', plain,
% 2.33/2.51      (((r1_tarski @ sk_D_1 @ k1_xboole_0) | ((sk_B) = (k1_relat_1 @ sk_D_1)))),
% 2.33/2.51      inference('sup-', [status(thm)], ['16', '23'])).
% 2.33/2.51  thf('25', plain,
% 2.33/2.51      (![X5 : $i, X7 : $i]:
% 2.33/2.51         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 2.33/2.51      inference('cnf', [status(esa)], [t3_subset])).
% 2.33/2.51  thf('26', plain,
% 2.33/2.51      ((((sk_B) = (k1_relat_1 @ sk_D_1))
% 2.33/2.51        | (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 2.33/2.51      inference('sup-', [status(thm)], ['24', '25'])).
% 2.33/2.51  thf('27', plain,
% 2.33/2.51      (![X1 : $i, X2 : $i]:
% 2.33/2.51         (((k2_zfmisc_1 @ X1 @ X2) = (k1_xboole_0)) | ((X1) != (k1_xboole_0)))),
% 2.33/2.51      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.33/2.51  thf('28', plain,
% 2.33/2.51      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 2.33/2.51      inference('simplify', [status(thm)], ['27'])).
% 2.33/2.51  thf('29', plain,
% 2.33/2.51      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.33/2.51         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 2.33/2.51          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 2.33/2.51      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.33/2.51  thf('30', plain,
% 2.33/2.51      (![X0 : $i, X1 : $i]:
% 2.33/2.51         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.33/2.51          | ((k2_relset_1 @ k1_xboole_0 @ X0 @ X1) = (k2_relat_1 @ X1)))),
% 2.33/2.51      inference('sup-', [status(thm)], ['28', '29'])).
% 2.33/2.51  thf('31', plain,
% 2.33/2.51      (![X0 : $i]:
% 2.33/2.51         (((sk_B) = (k1_relat_1 @ sk_D_1))
% 2.33/2.51          | ((k2_relset_1 @ k1_xboole_0 @ X0 @ sk_D_1) = (k2_relat_1 @ sk_D_1)))),
% 2.33/2.51      inference('sup-', [status(thm)], ['26', '30'])).
% 2.33/2.51  thf('32', plain,
% 2.33/2.51      ((((sk_B) = (k1_relat_1 @ sk_D_1))
% 2.33/2.51        | (m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 2.33/2.51      inference('sup-', [status(thm)], ['24', '25'])).
% 2.33/2.51  thf('33', plain,
% 2.33/2.51      (![X2 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 2.33/2.51      inference('simplify', [status(thm)], ['27'])).
% 2.33/2.51  thf(dt_k2_relset_1, axiom,
% 2.33/2.51    (![A:$i,B:$i,C:$i]:
% 2.33/2.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.33/2.51       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 2.33/2.51  thf('34', plain,
% 2.33/2.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.33/2.51         ((m1_subset_1 @ (k2_relset_1 @ X12 @ X13 @ X14) @ (k1_zfmisc_1 @ X13))
% 2.33/2.51          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 2.33/2.51      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 2.33/2.51  thf('35', plain,
% 2.33/2.51      (![X0 : $i, X1 : $i]:
% 2.33/2.51         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.33/2.51          | (m1_subset_1 @ (k2_relset_1 @ k1_xboole_0 @ X0 @ X1) @ 
% 2.33/2.51             (k1_zfmisc_1 @ X0)))),
% 2.33/2.51      inference('sup-', [status(thm)], ['33', '34'])).
% 2.33/2.51  thf('36', plain,
% 2.33/2.51      (![X0 : $i]:
% 2.33/2.51         (((sk_B) = (k1_relat_1 @ sk_D_1))
% 2.33/2.51          | (m1_subset_1 @ (k2_relset_1 @ k1_xboole_0 @ X0 @ sk_D_1) @ 
% 2.33/2.51             (k1_zfmisc_1 @ X0)))),
% 2.33/2.51      inference('sup-', [status(thm)], ['32', '35'])).
% 2.33/2.51  thf('37', plain,
% 2.33/2.51      (![X0 : $i]:
% 2.33/2.51         ((m1_subset_1 @ (k2_relat_1 @ sk_D_1) @ (k1_zfmisc_1 @ X0))
% 2.33/2.51          | ((sk_B) = (k1_relat_1 @ sk_D_1))
% 2.33/2.51          | ((sk_B) = (k1_relat_1 @ sk_D_1)))),
% 2.33/2.51      inference('sup+', [status(thm)], ['31', '36'])).
% 2.33/2.51  thf('38', plain,
% 2.33/2.51      (![X0 : $i]:
% 2.33/2.51         (((sk_B) = (k1_relat_1 @ sk_D_1))
% 2.33/2.51          | (m1_subset_1 @ (k2_relat_1 @ sk_D_1) @ (k1_zfmisc_1 @ X0)))),
% 2.33/2.51      inference('simplify', [status(thm)], ['37'])).
% 2.33/2.51  thf('39', plain,
% 2.33/2.51      (![X5 : $i, X6 : $i]:
% 2.33/2.51         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 2.33/2.51      inference('cnf', [status(esa)], [t3_subset])).
% 2.33/2.51  thf('40', plain,
% 2.33/2.51      (![X0 : $i]:
% 2.33/2.51         (((sk_B) = (k1_relat_1 @ sk_D_1))
% 2.33/2.51          | (r1_tarski @ (k2_relat_1 @ sk_D_1) @ X0))),
% 2.33/2.51      inference('sup-', [status(thm)], ['38', '39'])).
% 2.33/2.51  thf('41', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 2.33/2.51      inference('demod', [status(thm)], ['0', '3'])).
% 2.33/2.51  thf('42', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 2.33/2.51      inference('sup-', [status(thm)], ['40', '41'])).
% 2.33/2.51  thf(t5_funct_2, axiom,
% 2.33/2.51    (![A:$i,B:$i,C:$i]:
% 2.33/2.51     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 2.33/2.51       ( ( ( ![D:$i]:
% 2.33/2.51             ( ( r2_hidden @ D @ A ) =>
% 2.33/2.51               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 2.33/2.51           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 2.33/2.51         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.33/2.51           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 2.33/2.51  thf(zf_stmt_6, axiom,
% 2.33/2.51    (![D:$i,C:$i,B:$i,A:$i]:
% 2.33/2.51     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 2.33/2.51       ( zip_tseitin_2 @ D @ C @ B @ A ) ))).
% 2.33/2.51  thf('43', plain,
% 2.33/2.51      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 2.33/2.51         ((zip_tseitin_2 @ X35 @ X36 @ X37 @ X38) | (r2_hidden @ X35 @ X38))),
% 2.33/2.51      inference('cnf', [status(esa)], [zf_stmt_6])).
% 2.33/2.51  thf(zf_stmt_7, type, zip_tseitin_3 : $i > $i > $i > $o).
% 2.33/2.51  thf(zf_stmt_8, axiom,
% 2.33/2.51    (![C:$i,B:$i,A:$i]:
% 2.33/2.51     ( ( zip_tseitin_3 @ C @ B @ A ) =>
% 2.33/2.51       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.33/2.51         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 2.33/2.51  thf(zf_stmt_9, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 2.33/2.51  thf(zf_stmt_10, axiom,
% 2.33/2.51    (![A:$i,B:$i,C:$i]:
% 2.33/2.51     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 2.33/2.51       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 2.33/2.51           ( ![D:$i]: ( zip_tseitin_2 @ D @ C @ B @ A ) ) ) =>
% 2.33/2.51         ( zip_tseitin_3 @ C @ B @ A ) ) ))).
% 2.33/2.51  thf('44', plain,
% 2.33/2.51      (![X42 : $i, X43 : $i, X44 : $i]:
% 2.33/2.51         (((k1_relat_1 @ X43) != (X42))
% 2.33/2.51          | ~ (zip_tseitin_2 @ (sk_D @ X43 @ X44 @ X42) @ X43 @ X44 @ X42)
% 2.33/2.51          | (zip_tseitin_3 @ X43 @ X44 @ X42)
% 2.33/2.51          | ~ (v1_funct_1 @ X43)
% 2.33/2.51          | ~ (v1_relat_1 @ X43))),
% 2.33/2.51      inference('cnf', [status(esa)], [zf_stmt_10])).
% 2.33/2.51  thf('45', plain,
% 2.33/2.51      (![X43 : $i, X44 : $i]:
% 2.33/2.51         (~ (v1_relat_1 @ X43)
% 2.33/2.51          | ~ (v1_funct_1 @ X43)
% 2.33/2.51          | (zip_tseitin_3 @ X43 @ X44 @ (k1_relat_1 @ X43))
% 2.33/2.51          | ~ (zip_tseitin_2 @ (sk_D @ X43 @ X44 @ (k1_relat_1 @ X43)) @ X43 @ 
% 2.33/2.51               X44 @ (k1_relat_1 @ X43)))),
% 2.33/2.51      inference('simplify', [status(thm)], ['44'])).
% 2.33/2.51  thf('46', plain,
% 2.33/2.51      (![X0 : $i, X1 : $i]:
% 2.33/2.51         ((r2_hidden @ (sk_D @ X0 @ X1 @ (k1_relat_1 @ X0)) @ (k1_relat_1 @ X0))
% 2.33/2.51          | (zip_tseitin_3 @ X0 @ X1 @ (k1_relat_1 @ X0))
% 2.33/2.51          | ~ (v1_funct_1 @ X0)
% 2.33/2.51          | ~ (v1_relat_1 @ X0))),
% 2.33/2.51      inference('sup-', [status(thm)], ['43', '45'])).
% 2.33/2.51  thf(t1_subset, axiom,
% 2.33/2.51    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 2.33/2.51  thf('47', plain,
% 2.33/2.51      (![X3 : $i, X4 : $i]: ((m1_subset_1 @ X3 @ X4) | ~ (r2_hidden @ X3 @ X4))),
% 2.33/2.51      inference('cnf', [status(esa)], [t1_subset])).
% 2.33/2.51  thf('48', plain,
% 2.33/2.51      (![X0 : $i, X1 : $i]:
% 2.33/2.51         (~ (v1_relat_1 @ X0)
% 2.33/2.51          | ~ (v1_funct_1 @ X0)
% 2.33/2.51          | (zip_tseitin_3 @ X0 @ X1 @ (k1_relat_1 @ X0))
% 2.33/2.51          | (m1_subset_1 @ (sk_D @ X0 @ X1 @ (k1_relat_1 @ X0)) @ 
% 2.33/2.51             (k1_relat_1 @ X0)))),
% 2.33/2.51      inference('sup-', [status(thm)], ['46', '47'])).
% 2.33/2.51  thf('49', plain,
% 2.33/2.51      (![X0 : $i]:
% 2.33/2.51         ((m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1)) @ sk_B)
% 2.33/2.51          | (zip_tseitin_3 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 2.33/2.51          | ~ (v1_funct_1 @ sk_D_1)
% 2.33/2.51          | ~ (v1_relat_1 @ sk_D_1))),
% 2.33/2.51      inference('sup+', [status(thm)], ['42', '48'])).
% 2.33/2.51  thf('50', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 2.33/2.51      inference('sup-', [status(thm)], ['40', '41'])).
% 2.33/2.51  thf('51', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 2.33/2.51      inference('sup-', [status(thm)], ['40', '41'])).
% 2.33/2.51  thf('52', plain, ((v1_funct_1 @ sk_D_1)),
% 2.33/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.51  thf('53', plain,
% 2.33/2.51      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.33/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.51  thf(cc2_relat_1, axiom,
% 2.33/2.51    (![A:$i]:
% 2.33/2.51     ( ( v1_relat_1 @ A ) =>
% 2.33/2.51       ( ![B:$i]:
% 2.33/2.51         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.33/2.51  thf('54', plain,
% 2.33/2.51      (![X8 : $i, X9 : $i]:
% 2.33/2.51         (~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9))
% 2.33/2.51          | (v1_relat_1 @ X8)
% 2.33/2.51          | ~ (v1_relat_1 @ X9))),
% 2.33/2.51      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.33/2.51  thf('55', plain,
% 2.33/2.51      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_D_1))),
% 2.33/2.51      inference('sup-', [status(thm)], ['53', '54'])).
% 2.33/2.51  thf(fc6_relat_1, axiom,
% 2.33/2.51    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.33/2.51  thf('56', plain,
% 2.33/2.51      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 2.33/2.51      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.33/2.51  thf('57', plain, ((v1_relat_1 @ sk_D_1)),
% 2.33/2.51      inference('demod', [status(thm)], ['55', '56'])).
% 2.33/2.51  thf('58', plain,
% 2.33/2.51      (![X0 : $i]:
% 2.33/2.51         ((m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B)
% 2.33/2.51          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 2.33/2.51      inference('demod', [status(thm)], ['49', '50', '51', '52', '57'])).
% 2.33/2.51  thf('59', plain,
% 2.33/2.51      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 2.33/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.51  thf(redefinition_k3_funct_2, axiom,
% 2.33/2.51    (![A:$i,B:$i,C:$i,D:$i]:
% 2.33/2.51     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 2.33/2.51         ( v1_funct_2 @ C @ A @ B ) & 
% 2.33/2.51         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.33/2.51         ( m1_subset_1 @ D @ A ) ) =>
% 2.33/2.51       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 2.33/2.51  thf('60', plain,
% 2.33/2.51      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 2.33/2.51         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 2.33/2.51          | ~ (v1_funct_2 @ X29 @ X30 @ X31)
% 2.33/2.51          | ~ (v1_funct_1 @ X29)
% 2.33/2.51          | (v1_xboole_0 @ X30)
% 2.33/2.51          | ~ (m1_subset_1 @ X32 @ X30)
% 2.33/2.51          | ((k3_funct_2 @ X30 @ X31 @ X29 @ X32) = (k1_funct_1 @ X29 @ X32)))),
% 2.33/2.51      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 2.33/2.51  thf('61', plain,
% 2.33/2.51      (![X0 : $i]:
% 2.33/2.51         (((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 2.33/2.51            = (k1_funct_1 @ sk_D_1 @ X0))
% 2.33/2.51          | ~ (m1_subset_1 @ X0 @ sk_B)
% 2.33/2.51          | (v1_xboole_0 @ sk_B)
% 2.33/2.51          | ~ (v1_funct_1 @ sk_D_1)
% 2.33/2.51          | ~ (v1_funct_2 @ sk_D_1 @ sk_B @ sk_C))),
% 2.33/2.51      inference('sup-', [status(thm)], ['59', '60'])).
% 2.33/2.51  thf('62', plain, ((v1_funct_1 @ sk_D_1)),
% 2.33/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.51  thf('63', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_C)),
% 2.33/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.51  thf('64', plain,
% 2.33/2.51      (![X0 : $i]:
% 2.33/2.51         (((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 2.33/2.51            = (k1_funct_1 @ sk_D_1 @ X0))
% 2.33/2.51          | ~ (m1_subset_1 @ X0 @ sk_B)
% 2.33/2.51          | (v1_xboole_0 @ sk_B))),
% 2.33/2.51      inference('demod', [status(thm)], ['61', '62', '63'])).
% 2.33/2.51  thf('65', plain, (~ (v1_xboole_0 @ sk_B)),
% 2.33/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.51  thf('66', plain,
% 2.33/2.51      (![X0 : $i]:
% 2.33/2.51         (~ (m1_subset_1 @ X0 @ sk_B)
% 2.33/2.51          | ((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 2.33/2.51              = (k1_funct_1 @ sk_D_1 @ X0)))),
% 2.33/2.51      inference('clc', [status(thm)], ['64', '65'])).
% 2.33/2.51  thf('67', plain,
% 2.33/2.51      (![X0 : $i]:
% 2.33/2.51         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 2.33/2.51          | ((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B))
% 2.33/2.51              = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B))))),
% 2.33/2.51      inference('sup-', [status(thm)], ['58', '66'])).
% 2.33/2.51  thf('68', plain,
% 2.33/2.51      (![X0 : $i]:
% 2.33/2.51         ((m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B)
% 2.33/2.51          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 2.33/2.51      inference('demod', [status(thm)], ['49', '50', '51', '52', '57'])).
% 2.33/2.51  thf('69', plain,
% 2.33/2.51      (![X45 : $i]:
% 2.33/2.51         ((r2_hidden @ (k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X45) @ sk_A)
% 2.33/2.51          | ~ (m1_subset_1 @ X45 @ sk_B))),
% 2.33/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.51  thf('70', plain,
% 2.33/2.51      (![X0 : $i]:
% 2.33/2.51         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 2.33/2.51          | (r2_hidden @ 
% 2.33/2.51             (k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 2.33/2.51             sk_A))),
% 2.33/2.51      inference('sup-', [status(thm)], ['68', '69'])).
% 2.33/2.51  thf('71', plain,
% 2.33/2.51      (![X0 : $i]:
% 2.33/2.51         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 2.33/2.51           sk_A)
% 2.33/2.51          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 2.33/2.51          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 2.33/2.51      inference('sup+', [status(thm)], ['67', '70'])).
% 2.33/2.51  thf('72', plain,
% 2.33/2.51      (![X0 : $i]:
% 2.33/2.51         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 2.33/2.51          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 2.33/2.51             sk_A))),
% 2.33/2.51      inference('simplify', [status(thm)], ['71'])).
% 2.33/2.51  thf('73', plain,
% 2.33/2.51      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 2.33/2.51         ((zip_tseitin_2 @ X35 @ X36 @ X37 @ X38)
% 2.33/2.51          | ~ (r2_hidden @ (k1_funct_1 @ X36 @ X35) @ X37))),
% 2.33/2.51      inference('cnf', [status(esa)], [zf_stmt_6])).
% 2.33/2.51  thf('74', plain,
% 2.33/2.51      (![X0 : $i, X1 : $i]:
% 2.33/2.51         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 2.33/2.51          | (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ sk_A @ X1))),
% 2.33/2.51      inference('sup-', [status(thm)], ['72', '73'])).
% 2.33/2.51  thf('75', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 2.33/2.51      inference('sup-', [status(thm)], ['40', '41'])).
% 2.33/2.51  thf('76', plain,
% 2.33/2.51      (![X43 : $i, X44 : $i]:
% 2.33/2.51         (~ (v1_relat_1 @ X43)
% 2.33/2.51          | ~ (v1_funct_1 @ X43)
% 2.33/2.51          | (zip_tseitin_3 @ X43 @ X44 @ (k1_relat_1 @ X43))
% 2.33/2.51          | ~ (zip_tseitin_2 @ (sk_D @ X43 @ X44 @ (k1_relat_1 @ X43)) @ X43 @ 
% 2.33/2.51               X44 @ (k1_relat_1 @ X43)))),
% 2.33/2.51      inference('simplify', [status(thm)], ['44'])).
% 2.33/2.51  thf('77', plain,
% 2.33/2.51      (![X0 : $i]:
% 2.33/2.51         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1)) @ 
% 2.33/2.51             sk_D_1 @ X0 @ sk_B)
% 2.33/2.51          | (zip_tseitin_3 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 2.33/2.51          | ~ (v1_funct_1 @ sk_D_1)
% 2.33/2.51          | ~ (v1_relat_1 @ sk_D_1))),
% 2.33/2.51      inference('sup-', [status(thm)], ['75', '76'])).
% 2.33/2.51  thf('78', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 2.33/2.51      inference('sup-', [status(thm)], ['40', '41'])).
% 2.33/2.51  thf('79', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 2.33/2.51      inference('sup-', [status(thm)], ['40', '41'])).
% 2.33/2.51  thf('80', plain, ((v1_funct_1 @ sk_D_1)),
% 2.33/2.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.33/2.51  thf('81', plain, ((v1_relat_1 @ sk_D_1)),
% 2.33/2.51      inference('demod', [status(thm)], ['55', '56'])).
% 2.33/2.51  thf('82', plain,
% 2.33/2.51      (![X0 : $i]:
% 2.33/2.51         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ sk_B)
% 2.33/2.51          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 2.33/2.51      inference('demod', [status(thm)], ['77', '78', '79', '80', '81'])).
% 2.33/2.51  thf('83', plain,
% 2.33/2.51      (((zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B)
% 2.33/2.51        | (zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B))),
% 2.33/2.51      inference('sup-', [status(thm)], ['74', '82'])).
% 2.33/2.51  thf('84', plain, ((zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B)),
% 2.33/2.51      inference('simplify', [status(thm)], ['83'])).
% 2.33/2.51  thf('85', plain,
% 2.33/2.51      (![X39 : $i, X40 : $i, X41 : $i]:
% 2.33/2.51         ((m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 2.33/2.51          | ~ (zip_tseitin_3 @ X39 @ X40 @ X41))),
% 2.33/2.51      inference('cnf', [status(esa)], [zf_stmt_8])).
% 2.33/2.51  thf('86', plain,
% 2.33/2.51      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.33/2.51      inference('sup-', [status(thm)], ['84', '85'])).
% 2.33/2.51  thf('87', plain,
% 2.33/2.51      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.33/2.51         ((m1_subset_1 @ (k2_relset_1 @ X12 @ X13 @ X14) @ (k1_zfmisc_1 @ X13))
% 2.33/2.51          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 2.33/2.51      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 2.33/2.51  thf('88', plain,
% 2.33/2.51      ((m1_subset_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_D_1) @ 
% 2.33/2.51        (k1_zfmisc_1 @ sk_A))),
% 2.33/2.51      inference('sup-', [status(thm)], ['86', '87'])).
% 2.33/2.51  thf('89', plain,
% 2.33/2.51      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.33/2.51      inference('sup-', [status(thm)], ['84', '85'])).
% 2.33/2.51  thf('90', plain,
% 2.33/2.51      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.33/2.51         (((k2_relset_1 @ X19 @ X20 @ X18) = (k2_relat_1 @ X18))
% 2.33/2.51          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 2.33/2.51      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.33/2.51  thf('91', plain,
% 2.33/2.51      (((k2_relset_1 @ sk_B @ sk_A @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 2.33/2.51      inference('sup-', [status(thm)], ['89', '90'])).
% 2.33/2.51  thf('92', plain,
% 2.33/2.51      ((m1_subset_1 @ (k2_relat_1 @ sk_D_1) @ (k1_zfmisc_1 @ sk_A))),
% 2.33/2.51      inference('demod', [status(thm)], ['88', '91'])).
% 2.33/2.51  thf('93', plain,
% 2.33/2.51      (![X5 : $i, X6 : $i]:
% 2.33/2.51         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 2.33/2.51      inference('cnf', [status(esa)], [t3_subset])).
% 2.33/2.51  thf('94', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 2.33/2.51      inference('sup-', [status(thm)], ['92', '93'])).
% 2.33/2.51  thf('95', plain, ($false), inference('demod', [status(thm)], ['4', '94'])).
% 2.33/2.51  
% 2.33/2.51  % SZS output end Refutation
% 2.33/2.51  
% 2.33/2.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
