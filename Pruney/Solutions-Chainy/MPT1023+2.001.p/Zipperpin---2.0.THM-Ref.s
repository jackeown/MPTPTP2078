%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MDo6erxzYK

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:28 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :  188 (1248 expanded)
%              Number of leaves         :   43 ( 399 expanded)
%              Depth                    :   27
%              Number of atoms          : 1295 (13085 expanded)
%              Number of equality atoms :   83 ( 670 expanded)
%              Maximal formula depth    :   14 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t113_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ! [E: $i] :
                ( ( m1_subset_1 @ E @ A )
               => ( ( k1_funct_1 @ C @ E )
                  = ( k1_funct_1 @ D @ E ) ) )
           => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ! [E: $i] :
                  ( ( m1_subset_1 @ E @ A )
                 => ( ( k1_funct_1 @ C @ E )
                    = ( k1_funct_1 @ D @ E ) ) )
             => ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t113_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
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
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('2',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('3',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('5',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('6',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('9',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    ! [X33: $i,X34: $i] :
      ( ( zip_tseitin_0 @ X33 @ X34 )
      | ( X33 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('12',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('15',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 )
      | ( X1 = X2 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('17',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X5 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('18',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['16','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['13','21'])).

thf('23',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('24',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X23 ) ) )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('25',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('27',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('31',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('32',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('33',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('34',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( r2_relset_1 @ X29 @ X30 @ X31 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['30','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r2_relset_1 @ X3 @ X2 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['29','37'])).

thf('39',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['11','12'])).

thf('42',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X23 ) ) )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('44',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_B_1 @ X0 )
      | ( v1_xboole_0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('47',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['3','6'])).

thf('49',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( sk_A
      = ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('55',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('56',plain,(
    ! [X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( v4_relat_1 @ X2 @ X1 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('57',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v4_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_relat_1 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('60',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('61',plain,(
    ! [X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ X1 ) @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(clc,[status(thm)],['58','61'])).

thf('63',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( m1_subset_1 @ ( k1_relat_1 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ sk_D ) ),
    inference('sup+',[status(thm)],['49','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('69',plain,(
    ! [X4: $i,X5: $i] :
      ( ( ( k2_zfmisc_1 @ X4 @ X5 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('70',plain,(
    ! [X5: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X5 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_zfmisc_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['68','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('74',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['71','76'])).

thf('78',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('79',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,
    ( ~ ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['67','79'])).

thf('81',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(clc,[status(thm)],['40','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference('sup-',[status(thm)],['28','81'])).

thf('83',plain,(
    zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['10','82'])).

thf('84',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','83'])).

thf('85',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_2 @ X37 @ X35 @ X36 )
      | ( X35
        = ( k1_relset_1 @ X35 @ X36 @ X37 ) )
      | ~ ( zip_tseitin_1 @ X37 @ X36 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('87',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k1_relset_1 @ X27 @ X28 @ X26 )
        = ( k1_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('90',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ~ ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['87','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( zip_tseitin_0 @ X38 @ X39 )
      | ( zip_tseitin_1 @ X40 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('94',plain,
    ( ( zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference('sup-',[status(thm)],['28','81'])).

thf('96',plain,(
    zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['91','96'])).

thf(t9_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( ( k1_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ! [C: $i] :
                  ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) )
                 => ( ( k1_funct_1 @ A @ C )
                    = ( k1_funct_1 @ B @ C ) ) ) )
           => ( A = B ) ) ) ) )).

thf('98',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( X16 = X15 )
      | ( r2_hidden @ ( sk_C @ X15 @ X16 ) @ ( k1_relat_1 @ X16 ) )
      | ( ( k1_relat_1 @ X16 )
       != ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_C_1 )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ ( k1_relat_1 @ sk_C_1 ) )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('102',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['91','96'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( sk_A
       != ( k1_relat_1 @ X0 ) )
      | ( r2_hidden @ ( sk_C @ X0 @ sk_C_1 ) @ sk_A )
      | ( sk_C_1 = X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['99','102','103','104'])).

thf('106',plain,
    ( ( sk_A != sk_A )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['84','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('109',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,
    ( ( sk_A != sk_A )
    | ( sk_C_1 = sk_D )
    | ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['106','109','110'])).

thf('112',plain,
    ( ( r2_hidden @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( v4_relat_1 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('115',plain,(
    v4_relat_1 @ sk_C_1 @ sk_A ),
    inference('sup-',[status(thm)],['113','114'])).

thf('116',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( v4_relat_1 @ X13 @ X14 )
      | ( r1_tarski @ ( k1_relat_1 @ X13 ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('117',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['115','116'])).

thf('118',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['100','101'])).

thf('119',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_A ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,(
    ! [X7: $i,X9: $i] :
      ( ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('121',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['119','120'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('122',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) )
      | ( m1_subset_1 @ X10 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['91','96'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( sk_C_1 = sk_D )
    | ( m1_subset_1 @ ( sk_C @ sk_D @ sk_C_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['112','125'])).

thf('127',plain,(
    ! [X41: $i] :
      ( ( ( k1_funct_1 @ sk_C_1 @ X41 )
        = ( k1_funct_1 @ sk_D @ X41 ) )
      | ~ ( m1_subset_1 @ X41 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,
    ( ( sk_C_1 = sk_D )
    | ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
      = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
    = ( k1_funct_1 @ sk_D @ ( sk_C @ sk_D @ sk_C_1 ) ) ),
    inference(condensation,[status(thm)],['128'])).

thf('130',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( v1_relat_1 @ X15 )
      | ~ ( v1_funct_1 @ X15 )
      | ( X16 = X15 )
      | ( ( k1_funct_1 @ X16 @ ( sk_C @ X15 @ X16 ) )
       != ( k1_funct_1 @ X15 @ ( sk_C @ X15 @ X16 ) ) )
      | ( ( k1_relat_1 @ X16 )
       != ( k1_relat_1 @ X15 ) )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t9_funct_1])).

thf('131',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_C_1 = sk_D )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['100','101'])).

thf('133',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['91','96'])).

thf('135',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['7','83'])).

thf('136',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['107','108'])).

thf('138',plain,
    ( ( ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) )
     != ( k1_funct_1 @ sk_C_1 @ ( sk_C @ sk_D @ sk_C_1 ) ) )
    | ( sk_A != sk_A )
    | ( sk_C_1 = sk_D ) ),
    inference(demod,[status(thm)],['131','132','133','134','135','136','137'])).

thf('139',plain,(
    sk_C_1 = sk_D ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['34'])).

thf('142',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    $false ),
    inference(demod,[status(thm)],['0','139','142'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.MDo6erxzYK
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:17:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.43/1.67  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.43/1.67  % Solved by: fo/fo7.sh
% 1.43/1.67  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.43/1.67  % done 2320 iterations in 1.217s
% 1.43/1.67  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.43/1.67  % SZS output start Refutation
% 1.43/1.67  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.43/1.67  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.43/1.67  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.43/1.67  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.43/1.67  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.43/1.67  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.43/1.67  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.43/1.67  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.43/1.67  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.43/1.67  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.43/1.67  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.43/1.67  thf(sk_C_1_type, type, sk_C_1: $i).
% 1.43/1.67  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.43/1.67  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.43/1.67  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.43/1.67  thf(sk_A_type, type, sk_A: $i).
% 1.43/1.67  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.43/1.67  thf(sk_D_type, type, sk_D: $i).
% 1.43/1.67  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.43/1.67  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.43/1.67  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.43/1.67  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.43/1.67  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.43/1.67  thf(t113_funct_2, conjecture,
% 1.43/1.67    (![A:$i,B:$i,C:$i]:
% 1.43/1.67     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.43/1.67         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.43/1.67       ( ![D:$i]:
% 1.43/1.67         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.43/1.67             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.43/1.67           ( ( ![E:$i]:
% 1.43/1.67               ( ( m1_subset_1 @ E @ A ) =>
% 1.43/1.67                 ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 1.43/1.67             ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ))).
% 1.43/1.67  thf(zf_stmt_0, negated_conjecture,
% 1.43/1.67    (~( ![A:$i,B:$i,C:$i]:
% 1.43/1.67        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.43/1.67            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.43/1.67          ( ![D:$i]:
% 1.43/1.67            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.43/1.67                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.43/1.67              ( ( ![E:$i]:
% 1.43/1.67                  ( ( m1_subset_1 @ E @ A ) =>
% 1.43/1.67                    ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) =>
% 1.43/1.67                ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )),
% 1.43/1.67    inference('cnf.neg', [status(esa)], [t113_funct_2])).
% 1.43/1.67  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)),
% 1.43/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.67  thf('1', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 1.43/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.67  thf(d1_funct_2, axiom,
% 1.43/1.67    (![A:$i,B:$i,C:$i]:
% 1.43/1.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.43/1.67       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.43/1.67           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.43/1.67             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.43/1.67         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.43/1.67           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.43/1.67             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.43/1.67  thf(zf_stmt_1, axiom,
% 1.43/1.67    (![C:$i,B:$i,A:$i]:
% 1.43/1.67     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.43/1.67       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.43/1.67  thf('2', plain,
% 1.43/1.67      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.43/1.67         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 1.43/1.67          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 1.43/1.67          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 1.43/1.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.43/1.67  thf('3', plain,
% 1.43/1.67      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.43/1.67        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_D)))),
% 1.43/1.67      inference('sup-', [status(thm)], ['1', '2'])).
% 1.43/1.67  thf('4', plain,
% 1.43/1.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.43/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.67  thf(redefinition_k1_relset_1, axiom,
% 1.43/1.67    (![A:$i,B:$i,C:$i]:
% 1.43/1.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.43/1.67       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.43/1.67  thf('5', plain,
% 1.43/1.67      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.43/1.67         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 1.43/1.67          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 1.43/1.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.43/1.67  thf('6', plain,
% 1.43/1.67      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_D) = (k1_relat_1 @ sk_D))),
% 1.43/1.67      inference('sup-', [status(thm)], ['4', '5'])).
% 1.43/1.67  thf('7', plain,
% 1.43/1.67      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.43/1.67        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.43/1.67      inference('demod', [status(thm)], ['3', '6'])).
% 1.43/1.67  thf('8', plain,
% 1.43/1.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.43/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.67  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.43/1.67  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.43/1.67  thf(zf_stmt_4, axiom,
% 1.43/1.67    (![B:$i,A:$i]:
% 1.43/1.67     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.43/1.67       ( zip_tseitin_0 @ B @ A ) ))).
% 1.43/1.67  thf(zf_stmt_5, axiom,
% 1.43/1.67    (![A:$i,B:$i,C:$i]:
% 1.43/1.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.43/1.67       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.43/1.67         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.43/1.67           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.43/1.67             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.43/1.67  thf('9', plain,
% 1.43/1.67      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.43/1.67         (~ (zip_tseitin_0 @ X38 @ X39)
% 1.43/1.67          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 1.43/1.67          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 1.43/1.67      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.43/1.67  thf('10', plain,
% 1.43/1.67      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.43/1.67        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.43/1.67      inference('sup-', [status(thm)], ['8', '9'])).
% 1.43/1.67  thf('11', plain,
% 1.43/1.67      (![X33 : $i, X34 : $i]:
% 1.43/1.67         ((zip_tseitin_0 @ X33 @ X34) | ((X33) = (k1_xboole_0)))),
% 1.43/1.67      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.43/1.67  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.43/1.67  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.43/1.67      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.43/1.67  thf('13', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.43/1.67      inference('sup+', [status(thm)], ['11', '12'])).
% 1.43/1.67  thf('14', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.43/1.67      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.43/1.67  thf(t8_boole, axiom,
% 1.43/1.67    (![A:$i,B:$i]:
% 1.43/1.67     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 1.43/1.67  thf('15', plain,
% 1.43/1.67      (![X1 : $i, X2 : $i]:
% 1.43/1.67         (~ (v1_xboole_0 @ X1) | ~ (v1_xboole_0 @ X2) | ((X1) = (X2)))),
% 1.43/1.67      inference('cnf', [status(esa)], [t8_boole])).
% 1.43/1.67  thf('16', plain,
% 1.43/1.67      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.43/1.67      inference('sup-', [status(thm)], ['14', '15'])).
% 1.43/1.67  thf(t113_zfmisc_1, axiom,
% 1.43/1.67    (![A:$i,B:$i]:
% 1.43/1.67     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 1.43/1.67       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 1.43/1.67  thf('17', plain,
% 1.43/1.67      (![X4 : $i, X5 : $i]:
% 1.43/1.67         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X5) != (k1_xboole_0)))),
% 1.43/1.67      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.43/1.67  thf('18', plain,
% 1.43/1.67      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 1.43/1.67      inference('simplify', [status(thm)], ['17'])).
% 1.43/1.67  thf('19', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i]:
% 1.43/1.67         (((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.43/1.67      inference('sup+', [status(thm)], ['16', '18'])).
% 1.43/1.67  thf('20', plain,
% 1.43/1.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.43/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.67  thf('21', plain,
% 1.43/1.67      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.43/1.67        | ~ (v1_xboole_0 @ sk_B_1))),
% 1.43/1.67      inference('sup+', [status(thm)], ['19', '20'])).
% 1.43/1.67  thf('22', plain,
% 1.43/1.67      (![X0 : $i]:
% 1.43/1.67         ((zip_tseitin_0 @ sk_B_1 @ X0)
% 1.43/1.67          | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))),
% 1.43/1.67      inference('sup-', [status(thm)], ['13', '21'])).
% 1.43/1.67  thf('23', plain,
% 1.43/1.67      (![X4 : $i]: ((k2_zfmisc_1 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 1.43/1.67      inference('simplify', [status(thm)], ['17'])).
% 1.43/1.67  thf(cc4_relset_1, axiom,
% 1.43/1.67    (![A:$i,B:$i]:
% 1.43/1.67     ( ( v1_xboole_0 @ A ) =>
% 1.43/1.67       ( ![C:$i]:
% 1.43/1.67         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 1.43/1.67           ( v1_xboole_0 @ C ) ) ) ))).
% 1.43/1.67  thf('24', plain,
% 1.43/1.67      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.43/1.67         (~ (v1_xboole_0 @ X23)
% 1.43/1.67          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X23)))
% 1.43/1.67          | (v1_xboole_0 @ X24))),
% 1.43/1.67      inference('cnf', [status(esa)], [cc4_relset_1])).
% 1.43/1.67  thf('25', plain,
% 1.43/1.67      (![X1 : $i]:
% 1.43/1.67         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.43/1.67          | (v1_xboole_0 @ X1)
% 1.43/1.67          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 1.43/1.67      inference('sup-', [status(thm)], ['23', '24'])).
% 1.43/1.67  thf('26', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.43/1.67      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.43/1.67  thf('27', plain,
% 1.43/1.67      (![X1 : $i]:
% 1.43/1.67         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.43/1.67          | (v1_xboole_0 @ X1))),
% 1.43/1.67      inference('demod', [status(thm)], ['25', '26'])).
% 1.43/1.67  thf('28', plain,
% 1.43/1.67      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_D))),
% 1.43/1.67      inference('sup-', [status(thm)], ['22', '27'])).
% 1.43/1.67  thf('29', plain,
% 1.43/1.67      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.43/1.67      inference('sup-', [status(thm)], ['14', '15'])).
% 1.43/1.67  thf('30', plain,
% 1.43/1.67      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.43/1.67      inference('sup-', [status(thm)], ['14', '15'])).
% 1.43/1.67  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.43/1.67  thf('31', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.43/1.67      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.43/1.67  thf(t3_subset, axiom,
% 1.43/1.67    (![A:$i,B:$i]:
% 1.43/1.67     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.43/1.67  thf('32', plain,
% 1.43/1.67      (![X7 : $i, X9 : $i]:
% 1.43/1.67         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 1.43/1.67      inference('cnf', [status(esa)], [t3_subset])).
% 1.43/1.67  thf('33', plain,
% 1.43/1.67      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 1.43/1.67      inference('sup-', [status(thm)], ['31', '32'])).
% 1.43/1.67  thf(reflexivity_r2_relset_1, axiom,
% 1.43/1.67    (![A:$i,B:$i,C:$i,D:$i]:
% 1.43/1.67     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.43/1.67         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.43/1.67       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 1.43/1.67  thf('34', plain,
% 1.43/1.67      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 1.43/1.67         ((r2_relset_1 @ X29 @ X30 @ X31 @ X31)
% 1.43/1.67          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 1.43/1.67          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 1.43/1.67      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 1.43/1.67  thf('35', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.43/1.67         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 1.43/1.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 1.43/1.67      inference('condensation', [status(thm)], ['34'])).
% 1.43/1.67  thf('36', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 1.43/1.67      inference('sup-', [status(thm)], ['33', '35'])).
% 1.43/1.67  thf('37', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.43/1.67         ((r2_relset_1 @ X2 @ X1 @ X0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 1.43/1.67      inference('sup+', [status(thm)], ['30', '36'])).
% 1.43/1.67  thf('38', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 1.43/1.67         ((r2_relset_1 @ X3 @ X2 @ X1 @ X0)
% 1.43/1.67          | ~ (v1_xboole_0 @ X0)
% 1.43/1.67          | ~ (v1_xboole_0 @ X1))),
% 1.43/1.67      inference('sup+', [status(thm)], ['29', '37'])).
% 1.43/1.67  thf('39', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)),
% 1.43/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.67  thf('40', plain, ((~ (v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ sk_D))),
% 1.43/1.67      inference('sup-', [status(thm)], ['38', '39'])).
% 1.43/1.67  thf('41', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 1.43/1.67      inference('sup+', [status(thm)], ['11', '12'])).
% 1.43/1.67  thf('42', plain,
% 1.43/1.67      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.43/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.67  thf('43', plain,
% 1.43/1.67      (![X23 : $i, X24 : $i, X25 : $i]:
% 1.43/1.67         (~ (v1_xboole_0 @ X23)
% 1.43/1.67          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X23)))
% 1.43/1.67          | (v1_xboole_0 @ X24))),
% 1.43/1.67      inference('cnf', [status(esa)], [cc4_relset_1])).
% 1.43/1.67  thf('44', plain, (((v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ sk_B_1))),
% 1.43/1.67      inference('sup-', [status(thm)], ['42', '43'])).
% 1.43/1.67  thf('45', plain,
% 1.43/1.67      (![X0 : $i]: ((zip_tseitin_0 @ sk_B_1 @ X0) | (v1_xboole_0 @ sk_C_1))),
% 1.43/1.67      inference('sup-', [status(thm)], ['41', '44'])).
% 1.43/1.67  thf('46', plain,
% 1.43/1.67      (((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.43/1.67        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.43/1.67      inference('sup-', [status(thm)], ['8', '9'])).
% 1.43/1.67  thf('47', plain,
% 1.43/1.67      (((v1_xboole_0 @ sk_C_1) | (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A))),
% 1.43/1.67      inference('sup-', [status(thm)], ['45', '46'])).
% 1.43/1.67  thf('48', plain,
% 1.43/1.67      ((~ (zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)
% 1.43/1.67        | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.43/1.67      inference('demod', [status(thm)], ['3', '6'])).
% 1.43/1.67  thf('49', plain, (((v1_xboole_0 @ sk_C_1) | ((sk_A) = (k1_relat_1 @ sk_D)))),
% 1.43/1.67      inference('sup-', [status(thm)], ['47', '48'])).
% 1.43/1.67  thf('50', plain,
% 1.43/1.67      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.43/1.67      inference('sup-', [status(thm)], ['14', '15'])).
% 1.43/1.67  thf('51', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 1.43/1.67      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.43/1.67  thf('52', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 1.43/1.67      inference('sup+', [status(thm)], ['50', '51'])).
% 1.43/1.67  thf('53', plain,
% 1.43/1.67      (![X7 : $i, X9 : $i]:
% 1.43/1.67         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 1.43/1.67      inference('cnf', [status(esa)], [t3_subset])).
% 1.43/1.67  thf('54', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i]:
% 1.43/1.67         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.43/1.67      inference('sup-', [status(thm)], ['52', '53'])).
% 1.43/1.67  thf(cc2_relset_1, axiom,
% 1.43/1.67    (![A:$i,B:$i,C:$i]:
% 1.43/1.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.43/1.67       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.43/1.67  thf('55', plain,
% 1.43/1.67      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.43/1.67         ((v4_relat_1 @ X20 @ X21)
% 1.43/1.67          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.43/1.67      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.43/1.67  thf('56', plain,
% 1.43/1.67      (![X1 : $i, X2 : $i]: (~ (v1_xboole_0 @ X2) | (v4_relat_1 @ X2 @ X1))),
% 1.43/1.67      inference('sup-', [status(thm)], ['54', '55'])).
% 1.43/1.67  thf(d18_relat_1, axiom,
% 1.43/1.67    (![A:$i,B:$i]:
% 1.43/1.67     ( ( v1_relat_1 @ B ) =>
% 1.43/1.67       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 1.43/1.67  thf('57', plain,
% 1.43/1.67      (![X13 : $i, X14 : $i]:
% 1.43/1.67         (~ (v4_relat_1 @ X13 @ X14)
% 1.43/1.67          | (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 1.43/1.67          | ~ (v1_relat_1 @ X13))),
% 1.43/1.67      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.43/1.67  thf('58', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i]:
% 1.43/1.67         (~ (v1_xboole_0 @ X1)
% 1.43/1.67          | ~ (v1_relat_1 @ X1)
% 1.43/1.67          | (r1_tarski @ (k1_relat_1 @ X1) @ X0))),
% 1.43/1.67      inference('sup-', [status(thm)], ['56', '57'])).
% 1.43/1.67  thf('59', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i]:
% 1.43/1.67         (~ (v1_xboole_0 @ X1) | (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0)))),
% 1.43/1.67      inference('sup-', [status(thm)], ['52', '53'])).
% 1.43/1.67  thf(cc1_relset_1, axiom,
% 1.43/1.67    (![A:$i,B:$i,C:$i]:
% 1.43/1.67     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.43/1.67       ( v1_relat_1 @ C ) ))).
% 1.43/1.67  thf('60', plain,
% 1.43/1.67      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.43/1.67         ((v1_relat_1 @ X17)
% 1.43/1.67          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.43/1.67      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.43/1.67  thf('61', plain, (![X2 : $i]: (~ (v1_xboole_0 @ X2) | (v1_relat_1 @ X2))),
% 1.43/1.67      inference('sup-', [status(thm)], ['59', '60'])).
% 1.43/1.67  thf('62', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i]:
% 1.43/1.67         ((r1_tarski @ (k1_relat_1 @ X1) @ X0) | ~ (v1_xboole_0 @ X1))),
% 1.43/1.67      inference('clc', [status(thm)], ['58', '61'])).
% 1.43/1.67  thf('63', plain,
% 1.43/1.67      (![X7 : $i, X9 : $i]:
% 1.43/1.67         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 1.43/1.67      inference('cnf', [status(esa)], [t3_subset])).
% 1.43/1.67  thf('64', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i]:
% 1.43/1.67         (~ (v1_xboole_0 @ X1)
% 1.43/1.67          | (m1_subset_1 @ (k1_relat_1 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 1.43/1.67      inference('sup-', [status(thm)], ['62', '63'])).
% 1.43/1.67  thf('65', plain,
% 1.43/1.67      (![X1 : $i]:
% 1.43/1.67         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.43/1.67          | (v1_xboole_0 @ X1))),
% 1.43/1.67      inference('demod', [status(thm)], ['25', '26'])).
% 1.43/1.67  thf('66', plain,
% 1.43/1.67      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 1.43/1.67      inference('sup-', [status(thm)], ['64', '65'])).
% 1.43/1.67  thf('67', plain,
% 1.43/1.67      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ sk_D))),
% 1.43/1.67      inference('sup+', [status(thm)], ['49', '66'])).
% 1.43/1.67  thf('68', plain,
% 1.43/1.67      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.43/1.67      inference('sup-', [status(thm)], ['14', '15'])).
% 1.43/1.67  thf('69', plain,
% 1.43/1.67      (![X4 : $i, X5 : $i]:
% 1.43/1.67         (((k2_zfmisc_1 @ X4 @ X5) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 1.43/1.67      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 1.43/1.67  thf('70', plain,
% 1.43/1.67      (![X5 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X5) = (k1_xboole_0))),
% 1.43/1.67      inference('simplify', [status(thm)], ['69'])).
% 1.43/1.67  thf('71', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i]:
% 1.43/1.67         (((k2_zfmisc_1 @ X0 @ X1) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 1.43/1.67      inference('sup+', [status(thm)], ['68', '70'])).
% 1.43/1.67  thf('72', plain,
% 1.43/1.67      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.43/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.67  thf('73', plain,
% 1.43/1.67      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 1.43/1.67      inference('sup-', [status(thm)], ['14', '15'])).
% 1.43/1.67  thf('74', plain,
% 1.43/1.67      (![X1 : $i]:
% 1.43/1.67         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 1.43/1.67          | (v1_xboole_0 @ X1))),
% 1.43/1.67      inference('demod', [status(thm)], ['25', '26'])).
% 1.43/1.67  thf('75', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i]:
% 1.43/1.67         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 1.43/1.67          | ~ (v1_xboole_0 @ X0)
% 1.43/1.67          | (v1_xboole_0 @ X1))),
% 1.43/1.67      inference('sup-', [status(thm)], ['73', '74'])).
% 1.43/1.67  thf('76', plain,
% 1.43/1.67      (((v1_xboole_0 @ sk_C_1)
% 1.43/1.67        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.43/1.67      inference('sup-', [status(thm)], ['72', '75'])).
% 1.43/1.67  thf('77', plain,
% 1.43/1.67      ((~ (v1_xboole_0 @ k1_xboole_0)
% 1.43/1.67        | ~ (v1_xboole_0 @ sk_A)
% 1.43/1.67        | (v1_xboole_0 @ sk_C_1))),
% 1.43/1.67      inference('sup-', [status(thm)], ['71', '76'])).
% 1.43/1.67  thf('78', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.43/1.67      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.43/1.67  thf('79', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C_1))),
% 1.43/1.67      inference('demod', [status(thm)], ['77', '78'])).
% 1.43/1.67  thf('80', plain, ((~ (v1_xboole_0 @ sk_D) | (v1_xboole_0 @ sk_C_1))),
% 1.43/1.67      inference('clc', [status(thm)], ['67', '79'])).
% 1.43/1.67  thf('81', plain, (~ (v1_xboole_0 @ sk_D)),
% 1.43/1.67      inference('clc', [status(thm)], ['40', '80'])).
% 1.43/1.67  thf('82', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 1.43/1.67      inference('sup-', [status(thm)], ['28', '81'])).
% 1.43/1.67  thf('83', plain, ((zip_tseitin_1 @ sk_D @ sk_B_1 @ sk_A)),
% 1.43/1.67      inference('demod', [status(thm)], ['10', '82'])).
% 1.43/1.67  thf('84', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 1.43/1.67      inference('demod', [status(thm)], ['7', '83'])).
% 1.43/1.67  thf('85', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 1.43/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.67  thf('86', plain,
% 1.43/1.67      (![X35 : $i, X36 : $i, X37 : $i]:
% 1.43/1.67         (~ (v1_funct_2 @ X37 @ X35 @ X36)
% 1.43/1.67          | ((X35) = (k1_relset_1 @ X35 @ X36 @ X37))
% 1.43/1.67          | ~ (zip_tseitin_1 @ X37 @ X36 @ X35))),
% 1.43/1.67      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.43/1.67  thf('87', plain,
% 1.43/1.67      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.43/1.67        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)))),
% 1.43/1.67      inference('sup-', [status(thm)], ['85', '86'])).
% 1.43/1.67  thf('88', plain,
% 1.43/1.67      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.43/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.67  thf('89', plain,
% 1.43/1.67      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.43/1.67         (((k1_relset_1 @ X27 @ X28 @ X26) = (k1_relat_1 @ X26))
% 1.43/1.67          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 1.43/1.67      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.43/1.67  thf('90', plain,
% 1.43/1.67      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 1.43/1.67      inference('sup-', [status(thm)], ['88', '89'])).
% 1.43/1.67  thf('91', plain,
% 1.43/1.67      ((~ (zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.43/1.67        | ((sk_A) = (k1_relat_1 @ sk_C_1)))),
% 1.43/1.67      inference('demod', [status(thm)], ['87', '90'])).
% 1.43/1.67  thf('92', plain,
% 1.43/1.67      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.43/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.67  thf('93', plain,
% 1.43/1.67      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.43/1.67         (~ (zip_tseitin_0 @ X38 @ X39)
% 1.43/1.67          | (zip_tseitin_1 @ X40 @ X38 @ X39)
% 1.43/1.67          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X38))))),
% 1.43/1.67      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.43/1.67  thf('94', plain,
% 1.43/1.67      (((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)
% 1.43/1.67        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.43/1.67      inference('sup-', [status(thm)], ['92', '93'])).
% 1.43/1.67  thf('95', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 1.43/1.67      inference('sup-', [status(thm)], ['28', '81'])).
% 1.43/1.67  thf('96', plain, ((zip_tseitin_1 @ sk_C_1 @ sk_B_1 @ sk_A)),
% 1.43/1.67      inference('demod', [status(thm)], ['94', '95'])).
% 1.43/1.67  thf('97', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 1.43/1.67      inference('demod', [status(thm)], ['91', '96'])).
% 1.43/1.67  thf(t9_funct_1, axiom,
% 1.43/1.67    (![A:$i]:
% 1.43/1.67     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 1.43/1.67       ( ![B:$i]:
% 1.43/1.67         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 1.43/1.67           ( ( ( ( k1_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 1.43/1.67               ( ![C:$i]:
% 1.43/1.67                 ( ( r2_hidden @ C @ ( k1_relat_1 @ A ) ) =>
% 1.43/1.67                   ( ( k1_funct_1 @ A @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ) =>
% 1.43/1.67             ( ( A ) = ( B ) ) ) ) ) ))).
% 1.43/1.67  thf('98', plain,
% 1.43/1.67      (![X15 : $i, X16 : $i]:
% 1.43/1.67         (~ (v1_relat_1 @ X15)
% 1.43/1.67          | ~ (v1_funct_1 @ X15)
% 1.43/1.67          | ((X16) = (X15))
% 1.43/1.67          | (r2_hidden @ (sk_C @ X15 @ X16) @ (k1_relat_1 @ X16))
% 1.43/1.67          | ((k1_relat_1 @ X16) != (k1_relat_1 @ X15))
% 1.43/1.67          | ~ (v1_funct_1 @ X16)
% 1.43/1.67          | ~ (v1_relat_1 @ X16))),
% 1.43/1.67      inference('cnf', [status(esa)], [t9_funct_1])).
% 1.43/1.67  thf('99', plain,
% 1.43/1.67      (![X0 : $i]:
% 1.43/1.67         (((sk_A) != (k1_relat_1 @ X0))
% 1.43/1.67          | ~ (v1_relat_1 @ sk_C_1)
% 1.43/1.67          | ~ (v1_funct_1 @ sk_C_1)
% 1.43/1.67          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ (k1_relat_1 @ sk_C_1))
% 1.43/1.67          | ((sk_C_1) = (X0))
% 1.43/1.67          | ~ (v1_funct_1 @ X0)
% 1.43/1.67          | ~ (v1_relat_1 @ X0))),
% 1.43/1.67      inference('sup-', [status(thm)], ['97', '98'])).
% 1.43/1.67  thf('100', plain,
% 1.43/1.67      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.43/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.67  thf('101', plain,
% 1.43/1.67      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.43/1.67         ((v1_relat_1 @ X17)
% 1.43/1.67          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.43/1.67      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.43/1.67  thf('102', plain, ((v1_relat_1 @ sk_C_1)),
% 1.43/1.67      inference('sup-', [status(thm)], ['100', '101'])).
% 1.43/1.67  thf('103', plain, ((v1_funct_1 @ sk_C_1)),
% 1.43/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.67  thf('104', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 1.43/1.67      inference('demod', [status(thm)], ['91', '96'])).
% 1.43/1.67  thf('105', plain,
% 1.43/1.67      (![X0 : $i]:
% 1.43/1.67         (((sk_A) != (k1_relat_1 @ X0))
% 1.43/1.67          | (r2_hidden @ (sk_C @ X0 @ sk_C_1) @ sk_A)
% 1.43/1.67          | ((sk_C_1) = (X0))
% 1.43/1.67          | ~ (v1_funct_1 @ X0)
% 1.43/1.67          | ~ (v1_relat_1 @ X0))),
% 1.43/1.67      inference('demod', [status(thm)], ['99', '102', '103', '104'])).
% 1.43/1.67  thf('106', plain,
% 1.43/1.67      ((((sk_A) != (sk_A))
% 1.43/1.67        | ~ (v1_relat_1 @ sk_D)
% 1.43/1.67        | ~ (v1_funct_1 @ sk_D)
% 1.43/1.67        | ((sk_C_1) = (sk_D))
% 1.43/1.67        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 1.43/1.67      inference('sup-', [status(thm)], ['84', '105'])).
% 1.43/1.67  thf('107', plain,
% 1.43/1.67      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.43/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.67  thf('108', plain,
% 1.43/1.67      (![X17 : $i, X18 : $i, X19 : $i]:
% 1.43/1.67         ((v1_relat_1 @ X17)
% 1.43/1.67          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 1.43/1.67      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.43/1.67  thf('109', plain, ((v1_relat_1 @ sk_D)),
% 1.43/1.67      inference('sup-', [status(thm)], ['107', '108'])).
% 1.43/1.67  thf('110', plain, ((v1_funct_1 @ sk_D)),
% 1.43/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.67  thf('111', plain,
% 1.43/1.67      ((((sk_A) != (sk_A))
% 1.43/1.67        | ((sk_C_1) = (sk_D))
% 1.43/1.67        | (r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 1.43/1.67      inference('demod', [status(thm)], ['106', '109', '110'])).
% 1.43/1.67  thf('112', plain,
% 1.43/1.67      (((r2_hidden @ (sk_C @ sk_D @ sk_C_1) @ sk_A) | ((sk_C_1) = (sk_D)))),
% 1.43/1.67      inference('simplify', [status(thm)], ['111'])).
% 1.43/1.67  thf('113', plain,
% 1.43/1.67      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.43/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.67  thf('114', plain,
% 1.43/1.67      (![X20 : $i, X21 : $i, X22 : $i]:
% 1.43/1.67         ((v4_relat_1 @ X20 @ X21)
% 1.43/1.67          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 1.43/1.67      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.43/1.67  thf('115', plain, ((v4_relat_1 @ sk_C_1 @ sk_A)),
% 1.43/1.67      inference('sup-', [status(thm)], ['113', '114'])).
% 1.43/1.67  thf('116', plain,
% 1.43/1.67      (![X13 : $i, X14 : $i]:
% 1.43/1.67         (~ (v4_relat_1 @ X13 @ X14)
% 1.43/1.67          | (r1_tarski @ (k1_relat_1 @ X13) @ X14)
% 1.43/1.67          | ~ (v1_relat_1 @ X13))),
% 1.43/1.67      inference('cnf', [status(esa)], [d18_relat_1])).
% 1.43/1.67  thf('117', plain,
% 1.43/1.67      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A))),
% 1.43/1.67      inference('sup-', [status(thm)], ['115', '116'])).
% 1.43/1.67  thf('118', plain, ((v1_relat_1 @ sk_C_1)),
% 1.43/1.67      inference('sup-', [status(thm)], ['100', '101'])).
% 1.43/1.67  thf('119', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_A)),
% 1.43/1.67      inference('demod', [status(thm)], ['117', '118'])).
% 1.43/1.67  thf('120', plain,
% 1.43/1.67      (![X7 : $i, X9 : $i]:
% 1.43/1.67         ((m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X9)) | ~ (r1_tarski @ X7 @ X9))),
% 1.43/1.67      inference('cnf', [status(esa)], [t3_subset])).
% 1.43/1.67  thf('121', plain,
% 1.43/1.67      ((m1_subset_1 @ (k1_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_A))),
% 1.43/1.67      inference('sup-', [status(thm)], ['119', '120'])).
% 1.43/1.67  thf(t4_subset, axiom,
% 1.43/1.67    (![A:$i,B:$i,C:$i]:
% 1.43/1.67     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 1.43/1.67       ( m1_subset_1 @ A @ C ) ))).
% 1.43/1.67  thf('122', plain,
% 1.43/1.67      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.43/1.67         (~ (r2_hidden @ X10 @ X11)
% 1.43/1.67          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12))
% 1.43/1.67          | (m1_subset_1 @ X10 @ X12))),
% 1.43/1.67      inference('cnf', [status(esa)], [t4_subset])).
% 1.43/1.67  thf('123', plain,
% 1.43/1.67      (![X0 : $i]:
% 1.43/1.67         ((m1_subset_1 @ X0 @ sk_A)
% 1.43/1.67          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_1)))),
% 1.43/1.67      inference('sup-', [status(thm)], ['121', '122'])).
% 1.43/1.67  thf('124', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 1.43/1.67      inference('demod', [status(thm)], ['91', '96'])).
% 1.43/1.67  thf('125', plain,
% 1.43/1.67      (![X0 : $i]: ((m1_subset_1 @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_A))),
% 1.43/1.67      inference('demod', [status(thm)], ['123', '124'])).
% 1.43/1.67  thf('126', plain,
% 1.43/1.67      ((((sk_C_1) = (sk_D)) | (m1_subset_1 @ (sk_C @ sk_D @ sk_C_1) @ sk_A))),
% 1.43/1.67      inference('sup-', [status(thm)], ['112', '125'])).
% 1.43/1.67  thf('127', plain,
% 1.43/1.67      (![X41 : $i]:
% 1.43/1.67         (((k1_funct_1 @ sk_C_1 @ X41) = (k1_funct_1 @ sk_D @ X41))
% 1.43/1.67          | ~ (m1_subset_1 @ X41 @ sk_A))),
% 1.43/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.67  thf('128', plain,
% 1.43/1.67      ((((sk_C_1) = (sk_D))
% 1.43/1.67        | ((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 1.43/1.67            = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1))))),
% 1.43/1.67      inference('sup-', [status(thm)], ['126', '127'])).
% 1.43/1.67  thf('129', plain,
% 1.43/1.67      (((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 1.43/1.67         = (k1_funct_1 @ sk_D @ (sk_C @ sk_D @ sk_C_1)))),
% 1.43/1.67      inference('condensation', [status(thm)], ['128'])).
% 1.43/1.67  thf('130', plain,
% 1.43/1.67      (![X15 : $i, X16 : $i]:
% 1.43/1.67         (~ (v1_relat_1 @ X15)
% 1.43/1.67          | ~ (v1_funct_1 @ X15)
% 1.43/1.67          | ((X16) = (X15))
% 1.43/1.67          | ((k1_funct_1 @ X16 @ (sk_C @ X15 @ X16))
% 1.43/1.67              != (k1_funct_1 @ X15 @ (sk_C @ X15 @ X16)))
% 1.43/1.67          | ((k1_relat_1 @ X16) != (k1_relat_1 @ X15))
% 1.43/1.67          | ~ (v1_funct_1 @ X16)
% 1.43/1.67          | ~ (v1_relat_1 @ X16))),
% 1.43/1.67      inference('cnf', [status(esa)], [t9_funct_1])).
% 1.43/1.67  thf('131', plain,
% 1.43/1.67      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 1.43/1.67          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 1.43/1.67        | ~ (v1_relat_1 @ sk_C_1)
% 1.43/1.67        | ~ (v1_funct_1 @ sk_C_1)
% 1.43/1.67        | ((k1_relat_1 @ sk_C_1) != (k1_relat_1 @ sk_D))
% 1.43/1.67        | ((sk_C_1) = (sk_D))
% 1.43/1.67        | ~ (v1_funct_1 @ sk_D)
% 1.43/1.67        | ~ (v1_relat_1 @ sk_D))),
% 1.43/1.67      inference('sup-', [status(thm)], ['129', '130'])).
% 1.43/1.67  thf('132', plain, ((v1_relat_1 @ sk_C_1)),
% 1.43/1.67      inference('sup-', [status(thm)], ['100', '101'])).
% 1.43/1.67  thf('133', plain, ((v1_funct_1 @ sk_C_1)),
% 1.43/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.67  thf('134', plain, (((sk_A) = (k1_relat_1 @ sk_C_1))),
% 1.43/1.67      inference('demod', [status(thm)], ['91', '96'])).
% 1.43/1.67  thf('135', plain, (((sk_A) = (k1_relat_1 @ sk_D))),
% 1.43/1.67      inference('demod', [status(thm)], ['7', '83'])).
% 1.43/1.67  thf('136', plain, ((v1_funct_1 @ sk_D)),
% 1.43/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.67  thf('137', plain, ((v1_relat_1 @ sk_D)),
% 1.43/1.67      inference('sup-', [status(thm)], ['107', '108'])).
% 1.43/1.67  thf('138', plain,
% 1.43/1.67      ((((k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1))
% 1.43/1.67          != (k1_funct_1 @ sk_C_1 @ (sk_C @ sk_D @ sk_C_1)))
% 1.43/1.67        | ((sk_A) != (sk_A))
% 1.43/1.67        | ((sk_C_1) = (sk_D)))),
% 1.43/1.67      inference('demod', [status(thm)],
% 1.43/1.67                ['131', '132', '133', '134', '135', '136', '137'])).
% 1.43/1.67  thf('139', plain, (((sk_C_1) = (sk_D))),
% 1.43/1.67      inference('simplify', [status(thm)], ['138'])).
% 1.43/1.67  thf('140', plain,
% 1.43/1.67      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.43/1.67      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.43/1.67  thf('141', plain,
% 1.43/1.67      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.43/1.67         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 1.43/1.67          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 1.43/1.67      inference('condensation', [status(thm)], ['34'])).
% 1.43/1.67  thf('142', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_C_1)),
% 1.43/1.67      inference('sup-', [status(thm)], ['140', '141'])).
% 1.43/1.67  thf('143', plain, ($false),
% 1.43/1.67      inference('demod', [status(thm)], ['0', '139', '142'])).
% 1.43/1.67  
% 1.43/1.67  % SZS output end Refutation
% 1.43/1.67  
% 1.43/1.68  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
