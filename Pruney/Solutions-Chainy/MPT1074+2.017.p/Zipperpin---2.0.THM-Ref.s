%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KFLx6q8YfT

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:24 EST 2020

% Result     : Theorem 10.95s
% Output     : Refutation 10.95s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 695 expanded)
%              Number of leaves         :   50 ( 230 expanded)
%              Depth                    :   25
%              Number of atoms          :  943 (9081 expanded)
%              Number of equality atoms :   34 ( 175 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( ( k2_relset_1 @ X25 @ X26 @ X24 )
        = ( k2_relat_1 @ X24 ) )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

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

thf(zf_stmt_1,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( ( r2_hidden @ D @ A )
       => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) )
     => ( zip_tseitin_2 @ D @ C @ B @ A ) ) )).

thf('5',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( zip_tseitin_2 @ X39 @ X40 @ X41 @ X42 )
      | ( r2_hidden @ X39 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B @ sk_C ),
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

thf(zf_stmt_2,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('7',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ( X29
        = ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('10',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('11',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['8','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_6,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('14',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('15',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('17',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('20',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v5_relat_1 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('21',plain,(
    v5_relat_1 @ sk_D_1 @ sk_C ),
    inference('sup-',[status(thm)],['19','20'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v5_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('23',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('25',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X13 ) )
      | ( v1_relat_1 @ X12 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('27',plain,(
    ! [X16: $i,X17: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('28',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_C ),
    inference(demod,[status(thm)],['23','28'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('30',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ X0 )
      | ~ ( r1_tarski @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_C @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','31'])).

thf('33',plain,(
    ~ ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('34',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['15','34'])).

thf('36',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','35'])).

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

thf('37',plain,(
    ! [X46: $i,X47: $i,X48: $i] :
      ( ( ( k1_relat_1 @ X47 )
       != X46 )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X47 @ X48 @ X46 ) @ X47 @ X48 @ X46 )
      | ( zip_tseitin_3 @ X47 @ X48 @ X46 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('38',plain,(
    ! [X47: $i,X48: $i] :
      ( ~ ( v1_relat_1 @ X47 )
      | ~ ( v1_funct_1 @ X47 )
      | ( zip_tseitin_3 @ X47 @ X48 @ ( k1_relat_1 @ X47 ) )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X47 @ X48 @ ( k1_relat_1 @ X47 ) ) @ X47 @ X48 @ ( k1_relat_1 @ X47 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','35'])).

thf('41',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','35'])).

thf('42',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['26','27'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','44'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('46',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
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

thf('49',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( v1_funct_1 @ X35 )
      | ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X38 @ X36 )
      | ( ( k3_funct_2 @ X36 @ X37 @ X35 @ X38 )
        = ( k1_funct_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) )
        = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['47','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('58',plain,(
    ! [X49: $i] :
      ( ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X49 ) @ sk_A )
      | ~ ( m1_subset_1 @ X49 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) @ sk_A )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( zip_tseitin_2 @ X39 @ X40 @ X41 @ X42 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X40 @ X39 ) @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('65',plain,
    ( ( zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B )
    | ( zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) )
      | ~ ( zip_tseitin_3 @ X43 @ X44 @ X45 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('68',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v5_relat_1 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('70',plain,(
    v5_relat_1 @ sk_D_1 @ sk_A ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v5_relat_1 @ X14 @ X15 )
      | ( r1_tarski @ ( k2_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('72',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['26','27'])).

thf('74',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ),
    inference(demod,[status(thm)],['72','73'])).

thf('75',plain,(
    $false ),
    inference(demod,[status(thm)],['4','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.KFLx6q8YfT
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:40:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 10.95/11.20  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 10.95/11.20  % Solved by: fo/fo7.sh
% 10.95/11.20  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 10.95/11.20  % done 5671 iterations in 10.744s
% 10.95/11.20  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 10.95/11.20  % SZS output start Refutation
% 10.95/11.20  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 10.95/11.20  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 10.95/11.20  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 10.95/11.20  thf(sk_B_type, type, sk_B: $i).
% 10.95/11.20  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 10.95/11.20  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 10.95/11.20  thf(sk_D_1_type, type, sk_D_1: $i).
% 10.95/11.20  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 10.95/11.20  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 10.95/11.20  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 10.95/11.20  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 10.95/11.20  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 10.95/11.20  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 10.95/11.20  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 10.95/11.20  thf(sk_A_type, type, sk_A: $i).
% 10.95/11.20  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 10.95/11.20  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 10.95/11.20  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 10.95/11.20  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 10.95/11.20  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 10.95/11.20  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $o).
% 10.95/11.20  thf(sk_C_type, type, sk_C: $i).
% 10.95/11.20  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 10.95/11.20  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 10.95/11.20  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 10.95/11.20  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 10.95/11.20  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 10.95/11.20  thf(t191_funct_2, conjecture,
% 10.95/11.20    (![A:$i,B:$i]:
% 10.95/11.20     ( ( ~( v1_xboole_0 @ B ) ) =>
% 10.95/11.20       ( ![C:$i]:
% 10.95/11.20         ( ( ~( v1_xboole_0 @ C ) ) =>
% 10.95/11.20           ( ![D:$i]:
% 10.95/11.20             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 10.95/11.20                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 10.95/11.20               ( ( ![E:$i]:
% 10.95/11.20                   ( ( m1_subset_1 @ E @ B ) =>
% 10.95/11.20                     ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 10.95/11.20                 ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ))).
% 10.95/11.20  thf(zf_stmt_0, negated_conjecture,
% 10.95/11.20    (~( ![A:$i,B:$i]:
% 10.95/11.20        ( ( ~( v1_xboole_0 @ B ) ) =>
% 10.95/11.20          ( ![C:$i]:
% 10.95/11.20            ( ( ~( v1_xboole_0 @ C ) ) =>
% 10.95/11.20              ( ![D:$i]:
% 10.95/11.20                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 10.95/11.20                    ( m1_subset_1 @
% 10.95/11.20                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 10.95/11.20                  ( ( ![E:$i]:
% 10.95/11.20                      ( ( m1_subset_1 @ E @ B ) =>
% 10.95/11.20                        ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 10.95/11.20                    ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ) )),
% 10.95/11.20    inference('cnf.neg', [status(esa)], [t191_funct_2])).
% 10.95/11.20  thf('0', plain,
% 10.95/11.20      (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D_1) @ sk_A)),
% 10.95/11.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.95/11.20  thf('1', plain,
% 10.95/11.20      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 10.95/11.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.95/11.20  thf(redefinition_k2_relset_1, axiom,
% 10.95/11.20    (![A:$i,B:$i,C:$i]:
% 10.95/11.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.95/11.20       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 10.95/11.20  thf('2', plain,
% 10.95/11.20      (![X24 : $i, X25 : $i, X26 : $i]:
% 10.95/11.20         (((k2_relset_1 @ X25 @ X26 @ X24) = (k2_relat_1 @ X24))
% 10.95/11.20          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 10.95/11.20      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 10.95/11.20  thf('3', plain,
% 10.95/11.20      (((k2_relset_1 @ sk_B @ sk_C @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 10.95/11.20      inference('sup-', [status(thm)], ['1', '2'])).
% 10.95/11.20  thf('4', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 10.95/11.20      inference('demod', [status(thm)], ['0', '3'])).
% 10.95/11.20  thf(t5_funct_2, axiom,
% 10.95/11.20    (![A:$i,B:$i,C:$i]:
% 10.95/11.20     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 10.95/11.20       ( ( ( ![D:$i]:
% 10.95/11.20             ( ( r2_hidden @ D @ A ) =>
% 10.95/11.20               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 10.95/11.20           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 10.95/11.20         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 10.95/11.20           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 10.95/11.20  thf(zf_stmt_1, axiom,
% 10.95/11.20    (![D:$i,C:$i,B:$i,A:$i]:
% 10.95/11.20     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 10.95/11.20       ( zip_tseitin_2 @ D @ C @ B @ A ) ))).
% 10.95/11.20  thf('5', plain,
% 10.95/11.20      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 10.95/11.20         ((zip_tseitin_2 @ X39 @ X40 @ X41 @ X42) | (r2_hidden @ X39 @ X42))),
% 10.95/11.20      inference('cnf', [status(esa)], [zf_stmt_1])).
% 10.95/11.20  thf('6', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_C)),
% 10.95/11.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.95/11.20  thf(d1_funct_2, axiom,
% 10.95/11.20    (![A:$i,B:$i,C:$i]:
% 10.95/11.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.95/11.20       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 10.95/11.20           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 10.95/11.20             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 10.95/11.20         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 10.95/11.20           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 10.95/11.20             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 10.95/11.20  thf(zf_stmt_2, axiom,
% 10.95/11.20    (![C:$i,B:$i,A:$i]:
% 10.95/11.20     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 10.95/11.20       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 10.95/11.20  thf('7', plain,
% 10.95/11.20      (![X29 : $i, X30 : $i, X31 : $i]:
% 10.95/11.20         (~ (v1_funct_2 @ X31 @ X29 @ X30)
% 10.95/11.20          | ((X29) = (k1_relset_1 @ X29 @ X30 @ X31))
% 10.95/11.20          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 10.95/11.20      inference('cnf', [status(esa)], [zf_stmt_2])).
% 10.95/11.20  thf('8', plain,
% 10.95/11.20      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)
% 10.95/11.20        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_D_1)))),
% 10.95/11.20      inference('sup-', [status(thm)], ['6', '7'])).
% 10.95/11.20  thf('9', plain,
% 10.95/11.20      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 10.95/11.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.95/11.20  thf(redefinition_k1_relset_1, axiom,
% 10.95/11.20    (![A:$i,B:$i,C:$i]:
% 10.95/11.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.95/11.20       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 10.95/11.20  thf('10', plain,
% 10.95/11.20      (![X21 : $i, X22 : $i, X23 : $i]:
% 10.95/11.20         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 10.95/11.20          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 10.95/11.20      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 10.95/11.20  thf('11', plain,
% 10.95/11.20      (((k1_relset_1 @ sk_B @ sk_C @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 10.95/11.20      inference('sup-', [status(thm)], ['9', '10'])).
% 10.95/11.20  thf('12', plain,
% 10.95/11.20      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)
% 10.95/11.20        | ((sk_B) = (k1_relat_1 @ sk_D_1)))),
% 10.95/11.20      inference('demod', [status(thm)], ['8', '11'])).
% 10.95/11.20  thf('13', plain,
% 10.95/11.20      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 10.95/11.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.95/11.20  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 10.95/11.20  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 10.95/11.20  thf(zf_stmt_5, axiom,
% 10.95/11.20    (![B:$i,A:$i]:
% 10.95/11.20     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 10.95/11.20       ( zip_tseitin_0 @ B @ A ) ))).
% 10.95/11.20  thf(zf_stmt_6, axiom,
% 10.95/11.20    (![A:$i,B:$i,C:$i]:
% 10.95/11.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.95/11.20       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 10.95/11.20         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 10.95/11.20           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 10.95/11.20             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 10.95/11.20  thf('14', plain,
% 10.95/11.20      (![X32 : $i, X33 : $i, X34 : $i]:
% 10.95/11.20         (~ (zip_tseitin_0 @ X32 @ X33)
% 10.95/11.20          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 10.95/11.20          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 10.95/11.20      inference('cnf', [status(esa)], [zf_stmt_6])).
% 10.95/11.20  thf('15', plain,
% 10.95/11.20      (((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)
% 10.95/11.20        | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 10.95/11.20      inference('sup-', [status(thm)], ['13', '14'])).
% 10.95/11.20  thf('16', plain,
% 10.95/11.20      (![X27 : $i, X28 : $i]:
% 10.95/11.20         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 10.95/11.20      inference('cnf', [status(esa)], [zf_stmt_5])).
% 10.95/11.20  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 10.95/11.20  thf('17', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 10.95/11.20      inference('cnf', [status(esa)], [t2_xboole_1])).
% 10.95/11.20  thf('18', plain,
% 10.95/11.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 10.95/11.20         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 10.95/11.20      inference('sup+', [status(thm)], ['16', '17'])).
% 10.95/11.20  thf('19', plain,
% 10.95/11.20      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 10.95/11.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.95/11.20  thf(cc2_relset_1, axiom,
% 10.95/11.20    (![A:$i,B:$i,C:$i]:
% 10.95/11.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 10.95/11.20       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 10.95/11.20  thf('20', plain,
% 10.95/11.20      (![X18 : $i, X19 : $i, X20 : $i]:
% 10.95/11.20         ((v5_relat_1 @ X18 @ X20)
% 10.95/11.20          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 10.95/11.20      inference('cnf', [status(esa)], [cc2_relset_1])).
% 10.95/11.20  thf('21', plain, ((v5_relat_1 @ sk_D_1 @ sk_C)),
% 10.95/11.20      inference('sup-', [status(thm)], ['19', '20'])).
% 10.95/11.20  thf(d19_relat_1, axiom,
% 10.95/11.20    (![A:$i,B:$i]:
% 10.95/11.20     ( ( v1_relat_1 @ B ) =>
% 10.95/11.20       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 10.95/11.20  thf('22', plain,
% 10.95/11.20      (![X14 : $i, X15 : $i]:
% 10.95/11.20         (~ (v5_relat_1 @ X14 @ X15)
% 10.95/11.20          | (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 10.95/11.20          | ~ (v1_relat_1 @ X14))),
% 10.95/11.20      inference('cnf', [status(esa)], [d19_relat_1])).
% 10.95/11.20  thf('23', plain,
% 10.95/11.20      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_C))),
% 10.95/11.20      inference('sup-', [status(thm)], ['21', '22'])).
% 10.95/11.20  thf('24', plain,
% 10.95/11.20      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 10.95/11.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.95/11.20  thf(cc2_relat_1, axiom,
% 10.95/11.20    (![A:$i]:
% 10.95/11.20     ( ( v1_relat_1 @ A ) =>
% 10.95/11.20       ( ![B:$i]:
% 10.95/11.20         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 10.95/11.20  thf('25', plain,
% 10.95/11.20      (![X12 : $i, X13 : $i]:
% 10.95/11.20         (~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X13))
% 10.95/11.20          | (v1_relat_1 @ X12)
% 10.95/11.20          | ~ (v1_relat_1 @ X13))),
% 10.95/11.20      inference('cnf', [status(esa)], [cc2_relat_1])).
% 10.95/11.20  thf('26', plain,
% 10.95/11.20      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_D_1))),
% 10.95/11.20      inference('sup-', [status(thm)], ['24', '25'])).
% 10.95/11.20  thf(fc6_relat_1, axiom,
% 10.95/11.20    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 10.95/11.20  thf('27', plain,
% 10.95/11.20      (![X16 : $i, X17 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X16 @ X17))),
% 10.95/11.20      inference('cnf', [status(esa)], [fc6_relat_1])).
% 10.95/11.20  thf('28', plain, ((v1_relat_1 @ sk_D_1)),
% 10.95/11.20      inference('demod', [status(thm)], ['26', '27'])).
% 10.95/11.20  thf('29', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_C)),
% 10.95/11.20      inference('demod', [status(thm)], ['23', '28'])).
% 10.95/11.20  thf(t1_xboole_1, axiom,
% 10.95/11.20    (![A:$i,B:$i,C:$i]:
% 10.95/11.20     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 10.95/11.20       ( r1_tarski @ A @ C ) ))).
% 10.95/11.20  thf('30', plain,
% 10.95/11.20      (![X3 : $i, X4 : $i, X5 : $i]:
% 10.95/11.20         (~ (r1_tarski @ X3 @ X4)
% 10.95/11.20          | ~ (r1_tarski @ X4 @ X5)
% 10.95/11.20          | (r1_tarski @ X3 @ X5))),
% 10.95/11.20      inference('cnf', [status(esa)], [t1_xboole_1])).
% 10.95/11.20  thf('31', plain,
% 10.95/11.20      (![X0 : $i]:
% 10.95/11.20         ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ X0) | ~ (r1_tarski @ sk_C @ X0))),
% 10.95/11.20      inference('sup-', [status(thm)], ['29', '30'])).
% 10.95/11.20  thf('32', plain,
% 10.95/11.20      (![X0 : $i, X1 : $i]:
% 10.95/11.20         ((zip_tseitin_0 @ sk_C @ X1)
% 10.95/11.20          | (r1_tarski @ (k2_relat_1 @ sk_D_1) @ X0))),
% 10.95/11.20      inference('sup-', [status(thm)], ['18', '31'])).
% 10.95/11.20  thf('33', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 10.95/11.20      inference('demod', [status(thm)], ['0', '3'])).
% 10.95/11.20  thf('34', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 10.95/11.20      inference('sup-', [status(thm)], ['32', '33'])).
% 10.95/11.20  thf('35', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)),
% 10.95/11.20      inference('demod', [status(thm)], ['15', '34'])).
% 10.95/11.20  thf('36', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 10.95/11.20      inference('demod', [status(thm)], ['12', '35'])).
% 10.95/11.20  thf(zf_stmt_7, type, zip_tseitin_3 : $i > $i > $i > $o).
% 10.95/11.20  thf(zf_stmt_8, axiom,
% 10.95/11.20    (![C:$i,B:$i,A:$i]:
% 10.95/11.20     ( ( zip_tseitin_3 @ C @ B @ A ) =>
% 10.95/11.20       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 10.95/11.20         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 10.95/11.20  thf(zf_stmt_9, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 10.95/11.20  thf(zf_stmt_10, axiom,
% 10.95/11.20    (![A:$i,B:$i,C:$i]:
% 10.95/11.20     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 10.95/11.20       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 10.95/11.20           ( ![D:$i]: ( zip_tseitin_2 @ D @ C @ B @ A ) ) ) =>
% 10.95/11.20         ( zip_tseitin_3 @ C @ B @ A ) ) ))).
% 10.95/11.20  thf('37', plain,
% 10.95/11.20      (![X46 : $i, X47 : $i, X48 : $i]:
% 10.95/11.20         (((k1_relat_1 @ X47) != (X46))
% 10.95/11.20          | ~ (zip_tseitin_2 @ (sk_D @ X47 @ X48 @ X46) @ X47 @ X48 @ X46)
% 10.95/11.20          | (zip_tseitin_3 @ X47 @ X48 @ X46)
% 10.95/11.20          | ~ (v1_funct_1 @ X47)
% 10.95/11.20          | ~ (v1_relat_1 @ X47))),
% 10.95/11.20      inference('cnf', [status(esa)], [zf_stmt_10])).
% 10.95/11.20  thf('38', plain,
% 10.95/11.20      (![X47 : $i, X48 : $i]:
% 10.95/11.20         (~ (v1_relat_1 @ X47)
% 10.95/11.20          | ~ (v1_funct_1 @ X47)
% 10.95/11.20          | (zip_tseitin_3 @ X47 @ X48 @ (k1_relat_1 @ X47))
% 10.95/11.20          | ~ (zip_tseitin_2 @ (sk_D @ X47 @ X48 @ (k1_relat_1 @ X47)) @ X47 @ 
% 10.95/11.20               X48 @ (k1_relat_1 @ X47)))),
% 10.95/11.20      inference('simplify', [status(thm)], ['37'])).
% 10.95/11.20  thf('39', plain,
% 10.95/11.20      (![X0 : $i]:
% 10.95/11.20         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ 
% 10.95/11.20             (k1_relat_1 @ sk_D_1))
% 10.95/11.20          | (zip_tseitin_3 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 10.95/11.20          | ~ (v1_funct_1 @ sk_D_1)
% 10.95/11.20          | ~ (v1_relat_1 @ sk_D_1))),
% 10.95/11.20      inference('sup-', [status(thm)], ['36', '38'])).
% 10.95/11.20  thf('40', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 10.95/11.20      inference('demod', [status(thm)], ['12', '35'])).
% 10.95/11.20  thf('41', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 10.95/11.20      inference('demod', [status(thm)], ['12', '35'])).
% 10.95/11.20  thf('42', plain, ((v1_funct_1 @ sk_D_1)),
% 10.95/11.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.95/11.20  thf('43', plain, ((v1_relat_1 @ sk_D_1)),
% 10.95/11.20      inference('demod', [status(thm)], ['26', '27'])).
% 10.95/11.20  thf('44', plain,
% 10.95/11.20      (![X0 : $i]:
% 10.95/11.20         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ sk_B)
% 10.95/11.20          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 10.95/11.20      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 10.95/11.20  thf('45', plain,
% 10.95/11.20      (![X0 : $i]:
% 10.95/11.20         ((r2_hidden @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B)
% 10.95/11.20          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 10.95/11.20      inference('sup-', [status(thm)], ['5', '44'])).
% 10.95/11.20  thf(t1_subset, axiom,
% 10.95/11.20    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 10.95/11.20  thf('46', plain,
% 10.95/11.20      (![X7 : $i, X8 : $i]: ((m1_subset_1 @ X7 @ X8) | ~ (r2_hidden @ X7 @ X8))),
% 10.95/11.20      inference('cnf', [status(esa)], [t1_subset])).
% 10.95/11.20  thf('47', plain,
% 10.95/11.20      (![X0 : $i]:
% 10.95/11.20         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 10.95/11.20          | (m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B))),
% 10.95/11.20      inference('sup-', [status(thm)], ['45', '46'])).
% 10.95/11.20  thf('48', plain,
% 10.95/11.20      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 10.95/11.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.95/11.20  thf(redefinition_k3_funct_2, axiom,
% 10.95/11.20    (![A:$i,B:$i,C:$i,D:$i]:
% 10.95/11.20     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 10.95/11.20         ( v1_funct_2 @ C @ A @ B ) & 
% 10.95/11.20         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 10.95/11.20         ( m1_subset_1 @ D @ A ) ) =>
% 10.95/11.20       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 10.95/11.20  thf('49', plain,
% 10.95/11.20      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 10.95/11.20         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 10.95/11.20          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 10.95/11.20          | ~ (v1_funct_1 @ X35)
% 10.95/11.20          | (v1_xboole_0 @ X36)
% 10.95/11.20          | ~ (m1_subset_1 @ X38 @ X36)
% 10.95/11.20          | ((k3_funct_2 @ X36 @ X37 @ X35 @ X38) = (k1_funct_1 @ X35 @ X38)))),
% 10.95/11.20      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 10.95/11.20  thf('50', plain,
% 10.95/11.20      (![X0 : $i]:
% 10.95/11.20         (((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 10.95/11.20            = (k1_funct_1 @ sk_D_1 @ X0))
% 10.95/11.20          | ~ (m1_subset_1 @ X0 @ sk_B)
% 10.95/11.20          | (v1_xboole_0 @ sk_B)
% 10.95/11.20          | ~ (v1_funct_1 @ sk_D_1)
% 10.95/11.20          | ~ (v1_funct_2 @ sk_D_1 @ sk_B @ sk_C))),
% 10.95/11.20      inference('sup-', [status(thm)], ['48', '49'])).
% 10.95/11.20  thf('51', plain, ((v1_funct_1 @ sk_D_1)),
% 10.95/11.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.95/11.20  thf('52', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_C)),
% 10.95/11.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.95/11.20  thf('53', plain,
% 10.95/11.20      (![X0 : $i]:
% 10.95/11.20         (((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 10.95/11.20            = (k1_funct_1 @ sk_D_1 @ X0))
% 10.95/11.20          | ~ (m1_subset_1 @ X0 @ sk_B)
% 10.95/11.20          | (v1_xboole_0 @ sk_B))),
% 10.95/11.20      inference('demod', [status(thm)], ['50', '51', '52'])).
% 10.95/11.20  thf('54', plain, (~ (v1_xboole_0 @ sk_B)),
% 10.95/11.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.95/11.20  thf('55', plain,
% 10.95/11.20      (![X0 : $i]:
% 10.95/11.20         (~ (m1_subset_1 @ X0 @ sk_B)
% 10.95/11.20          | ((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 10.95/11.20              = (k1_funct_1 @ sk_D_1 @ X0)))),
% 10.95/11.20      inference('clc', [status(thm)], ['53', '54'])).
% 10.95/11.20  thf('56', plain,
% 10.95/11.20      (![X0 : $i]:
% 10.95/11.20         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 10.95/11.20          | ((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B))
% 10.95/11.20              = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B))))),
% 10.95/11.20      inference('sup-', [status(thm)], ['47', '55'])).
% 10.95/11.20  thf('57', plain,
% 10.95/11.20      (![X0 : $i]:
% 10.95/11.20         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 10.95/11.20          | (m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B))),
% 10.95/11.20      inference('sup-', [status(thm)], ['45', '46'])).
% 10.95/11.20  thf('58', plain,
% 10.95/11.20      (![X49 : $i]:
% 10.95/11.20         ((r2_hidden @ (k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X49) @ sk_A)
% 10.95/11.20          | ~ (m1_subset_1 @ X49 @ sk_B))),
% 10.95/11.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 10.95/11.20  thf('59', plain,
% 10.95/11.20      (![X0 : $i]:
% 10.95/11.20         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 10.95/11.20          | (r2_hidden @ 
% 10.95/11.20             (k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 10.95/11.20             sk_A))),
% 10.95/11.20      inference('sup-', [status(thm)], ['57', '58'])).
% 10.95/11.20  thf('60', plain,
% 10.95/11.20      (![X0 : $i]:
% 10.95/11.20         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 10.95/11.20           sk_A)
% 10.95/11.20          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 10.95/11.20          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 10.95/11.20      inference('sup+', [status(thm)], ['56', '59'])).
% 10.95/11.20  thf('61', plain,
% 10.95/11.20      (![X0 : $i]:
% 10.95/11.20         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 10.95/11.20          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 10.95/11.20             sk_A))),
% 10.95/11.20      inference('simplify', [status(thm)], ['60'])).
% 10.95/11.20  thf('62', plain,
% 10.95/11.20      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 10.95/11.20         ((zip_tseitin_2 @ X39 @ X40 @ X41 @ X42)
% 10.95/11.20          | ~ (r2_hidden @ (k1_funct_1 @ X40 @ X39) @ X41))),
% 10.95/11.20      inference('cnf', [status(esa)], [zf_stmt_1])).
% 10.95/11.20  thf('63', plain,
% 10.95/11.20      (![X0 : $i, X1 : $i]:
% 10.95/11.20         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 10.95/11.20          | (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ sk_A @ X1))),
% 10.95/11.20      inference('sup-', [status(thm)], ['61', '62'])).
% 10.95/11.20  thf('64', plain,
% 10.95/11.20      (![X0 : $i]:
% 10.95/11.20         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ sk_B)
% 10.95/11.20          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 10.95/11.20      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 10.95/11.20  thf('65', plain,
% 10.95/11.20      (((zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B)
% 10.95/11.20        | (zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B))),
% 10.95/11.20      inference('sup-', [status(thm)], ['63', '64'])).
% 10.95/11.20  thf('66', plain, ((zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B)),
% 10.95/11.20      inference('simplify', [status(thm)], ['65'])).
% 10.95/11.20  thf('67', plain,
% 10.95/11.20      (![X43 : $i, X44 : $i, X45 : $i]:
% 10.95/11.20         ((m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 10.95/11.20          | ~ (zip_tseitin_3 @ X43 @ X44 @ X45))),
% 10.95/11.20      inference('cnf', [status(esa)], [zf_stmt_8])).
% 10.95/11.20  thf('68', plain,
% 10.95/11.20      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 10.95/11.20      inference('sup-', [status(thm)], ['66', '67'])).
% 10.95/11.20  thf('69', plain,
% 10.95/11.20      (![X18 : $i, X19 : $i, X20 : $i]:
% 10.95/11.20         ((v5_relat_1 @ X18 @ X20)
% 10.95/11.20          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 10.95/11.20      inference('cnf', [status(esa)], [cc2_relset_1])).
% 10.95/11.20  thf('70', plain, ((v5_relat_1 @ sk_D_1 @ sk_A)),
% 10.95/11.20      inference('sup-', [status(thm)], ['68', '69'])).
% 10.95/11.20  thf('71', plain,
% 10.95/11.20      (![X14 : $i, X15 : $i]:
% 10.95/11.20         (~ (v5_relat_1 @ X14 @ X15)
% 10.95/11.20          | (r1_tarski @ (k2_relat_1 @ X14) @ X15)
% 10.95/11.20          | ~ (v1_relat_1 @ X14))),
% 10.95/11.20      inference('cnf', [status(esa)], [d19_relat_1])).
% 10.95/11.20  thf('72', plain,
% 10.95/11.20      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A))),
% 10.95/11.20      inference('sup-', [status(thm)], ['70', '71'])).
% 10.95/11.20  thf('73', plain, ((v1_relat_1 @ sk_D_1)),
% 10.95/11.20      inference('demod', [status(thm)], ['26', '27'])).
% 10.95/11.20  thf('74', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 10.95/11.20      inference('demod', [status(thm)], ['72', '73'])).
% 10.95/11.20  thf('75', plain, ($false), inference('demod', [status(thm)], ['4', '74'])).
% 10.95/11.20  
% 10.95/11.20  % SZS output end Refutation
% 10.95/11.20  
% 10.95/11.21  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
