%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AFU0DQ91t7

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:25 EST 2020

% Result     : Theorem 1.94s
% Output     : Refutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :  127 (1124 expanded)
%              Number of leaves         :   48 ( 361 expanded)
%              Depth                    :   24
%              Number of atoms          :  989 (14624 expanded)
%              Number of equality atoms :   40 ( 415 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( zip_tseitin_2 @ X34 @ X35 @ X36 @ X37 )
      | ( r2_hidden @ X34 @ X37 ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_funct_2 @ X26 @ X24 @ X25 )
      | ( X24
        = ( k1_relset_1 @ X24 @ X25 @ X26 ) )
      | ~ ( zip_tseitin_1 @ X26 @ X25 @ X24 ) ) ),
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
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( zip_tseitin_0 @ X27 @ X28 )
      | ( zip_tseitin_1 @ X29 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('15',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X13 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('18',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 ) @ sk_C ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X22: $i,X23: $i] :
      ( ( zip_tseitin_0 @ X22 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('22',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 )
        = sk_C )
      | ( zip_tseitin_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','25'])).

thf('27',plain,(
    ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C @ sk_D_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ sk_C @ sk_A )
      | ( zip_tseitin_0 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['21','22'])).

thf('30',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference(clc,[status(thm)],['28','29'])).

thf('31',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['15','30'])).

thf('32',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','31'])).

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

thf('33',plain,(
    ! [X41: $i,X42: $i,X43: $i] :
      ( ( ( k1_relat_1 @ X42 )
       != X41 )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X42 @ X43 @ X41 ) @ X42 @ X43 @ X41 )
      | ( zip_tseitin_3 @ X42 @ X43 @ X41 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('34',plain,(
    ! [X42: $i,X43: $i] :
      ( ~ ( v1_relat_1 @ X42 )
      | ~ ( v1_funct_1 @ X42 )
      | ( zip_tseitin_3 @ X42 @ X43 @ ( k1_relat_1 @ X42 ) )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X42 @ X43 @ ( k1_relat_1 @ X42 ) ) @ X42 @ X43 @ ( k1_relat_1 @ X42 ) ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['32','34'])).

thf('36',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','31'])).

thf('37',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','31'])).

thf('38',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('40',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('42',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('43',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['35','36','37','38','43'])).

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
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X32 )
      | ~ ( v1_funct_1 @ X30 )
      | ( v1_xboole_0 @ X31 )
      | ~ ( m1_subset_1 @ X33 @ X31 )
      | ( ( k3_funct_2 @ X31 @ X32 @ X30 @ X33 )
        = ( k1_funct_1 @ X30 @ X33 ) ) ) ),
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
    ! [X44: $i] :
      ( ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X44 ) @ sk_A )
      | ~ ( m1_subset_1 @ X44 @ sk_B ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( zip_tseitin_2 @ X34 @ X35 @ X36 @ X37 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X35 @ X34 ) @ X36 ) ) ),
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
    inference(demod,[status(thm)],['35','36','37','38','43'])).

thf('65',plain,
    ( ( zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B )
    | ( zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['65'])).

thf('67',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X39 ) ) )
      | ~ ( zip_tseitin_3 @ X38 @ X39 @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('68',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X13 @ X14 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('70',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('72',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('73',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('76',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['4','76'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.AFU0DQ91t7
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:14:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.94/2.19  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.94/2.19  % Solved by: fo/fo7.sh
% 1.94/2.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.94/2.19  % done 1296 iterations in 1.702s
% 1.94/2.19  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.94/2.19  % SZS output start Refutation
% 1.94/2.19  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.94/2.19  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.94/2.19  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.94/2.19  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.94/2.19  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.94/2.19  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.94/2.19  thf(sk_B_type, type, sk_B: $i).
% 1.94/2.19  thf(sk_D_1_type, type, sk_D_1: $i).
% 1.94/2.19  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 1.94/2.19  thf(sk_C_type, type, sk_C: $i).
% 1.94/2.19  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.94/2.19  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 1.94/2.19  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 1.94/2.19  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.94/2.19  thf(sk_A_type, type, sk_A: $i).
% 1.94/2.19  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.94/2.19  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.94/2.19  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.94/2.19  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.94/2.19  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.94/2.19  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.94/2.19  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $o).
% 1.94/2.19  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.94/2.19  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.94/2.19  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.94/2.19  thf(t191_funct_2, conjecture,
% 1.94/2.19    (![A:$i,B:$i]:
% 1.94/2.19     ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.94/2.19       ( ![C:$i]:
% 1.94/2.19         ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.94/2.19           ( ![D:$i]:
% 1.94/2.19             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 1.94/2.19                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.94/2.19               ( ( ![E:$i]:
% 1.94/2.19                   ( ( m1_subset_1 @ E @ B ) =>
% 1.94/2.19                     ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 1.94/2.19                 ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ))).
% 1.94/2.19  thf(zf_stmt_0, negated_conjecture,
% 1.94/2.19    (~( ![A:$i,B:$i]:
% 1.94/2.19        ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.94/2.19          ( ![C:$i]:
% 1.94/2.19            ( ( ~( v1_xboole_0 @ C ) ) =>
% 1.94/2.19              ( ![D:$i]:
% 1.94/2.19                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 1.94/2.19                    ( m1_subset_1 @
% 1.94/2.19                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.94/2.19                  ( ( ![E:$i]:
% 1.94/2.19                      ( ( m1_subset_1 @ E @ B ) =>
% 1.94/2.19                        ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 1.94/2.19                    ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ) )),
% 1.94/2.19    inference('cnf.neg', [status(esa)], [t191_funct_2])).
% 1.94/2.19  thf('0', plain,
% 1.94/2.19      (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D_1) @ sk_A)),
% 1.94/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.19  thf('1', plain,
% 1.94/2.19      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.94/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.19  thf(redefinition_k2_relset_1, axiom,
% 1.94/2.19    (![A:$i,B:$i,C:$i]:
% 1.94/2.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.94/2.19       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.94/2.19  thf('2', plain,
% 1.94/2.19      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.94/2.19         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 1.94/2.19          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 1.94/2.19      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.94/2.19  thf('3', plain,
% 1.94/2.19      (((k2_relset_1 @ sk_B @ sk_C @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 1.94/2.19      inference('sup-', [status(thm)], ['1', '2'])).
% 1.94/2.19  thf('4', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 1.94/2.19      inference('demod', [status(thm)], ['0', '3'])).
% 1.94/2.19  thf(t5_funct_2, axiom,
% 1.94/2.19    (![A:$i,B:$i,C:$i]:
% 1.94/2.19     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 1.94/2.19       ( ( ( ![D:$i]:
% 1.94/2.19             ( ( r2_hidden @ D @ A ) =>
% 1.94/2.19               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 1.94/2.19           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 1.94/2.19         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.94/2.19           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 1.94/2.19  thf(zf_stmt_1, axiom,
% 1.94/2.19    (![D:$i,C:$i,B:$i,A:$i]:
% 1.94/2.19     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 1.94/2.19       ( zip_tseitin_2 @ D @ C @ B @ A ) ))).
% 1.94/2.19  thf('5', plain,
% 1.94/2.19      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 1.94/2.19         ((zip_tseitin_2 @ X34 @ X35 @ X36 @ X37) | (r2_hidden @ X34 @ X37))),
% 1.94/2.19      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.94/2.19  thf('6', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_C)),
% 1.94/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.19  thf(d1_funct_2, axiom,
% 1.94/2.19    (![A:$i,B:$i,C:$i]:
% 1.94/2.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.94/2.19       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.94/2.19           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.94/2.19             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.94/2.19         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.94/2.19           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.94/2.19             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.94/2.19  thf(zf_stmt_2, axiom,
% 1.94/2.19    (![C:$i,B:$i,A:$i]:
% 1.94/2.19     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.94/2.19       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.94/2.19  thf('7', plain,
% 1.94/2.19      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.94/2.19         (~ (v1_funct_2 @ X26 @ X24 @ X25)
% 1.94/2.19          | ((X24) = (k1_relset_1 @ X24 @ X25 @ X26))
% 1.94/2.19          | ~ (zip_tseitin_1 @ X26 @ X25 @ X24))),
% 1.94/2.19      inference('cnf', [status(esa)], [zf_stmt_2])).
% 1.94/2.19  thf('8', plain,
% 1.94/2.19      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)
% 1.94/2.19        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_D_1)))),
% 1.94/2.19      inference('sup-', [status(thm)], ['6', '7'])).
% 1.94/2.19  thf('9', plain,
% 1.94/2.19      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.94/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.19  thf(redefinition_k1_relset_1, axiom,
% 1.94/2.19    (![A:$i,B:$i,C:$i]:
% 1.94/2.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.94/2.19       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.94/2.19  thf('10', plain,
% 1.94/2.19      (![X16 : $i, X17 : $i, X18 : $i]:
% 1.94/2.19         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 1.94/2.19          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 1.94/2.19      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.94/2.19  thf('11', plain,
% 1.94/2.19      (((k1_relset_1 @ sk_B @ sk_C @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 1.94/2.19      inference('sup-', [status(thm)], ['9', '10'])).
% 1.94/2.19  thf('12', plain,
% 1.94/2.19      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)
% 1.94/2.19        | ((sk_B) = (k1_relat_1 @ sk_D_1)))),
% 1.94/2.19      inference('demod', [status(thm)], ['8', '11'])).
% 1.94/2.19  thf('13', plain,
% 1.94/2.19      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.94/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.19  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.94/2.19  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 1.94/2.19  thf(zf_stmt_5, axiom,
% 1.94/2.19    (![B:$i,A:$i]:
% 1.94/2.19     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.94/2.19       ( zip_tseitin_0 @ B @ A ) ))).
% 1.94/2.19  thf(zf_stmt_6, axiom,
% 1.94/2.19    (![A:$i,B:$i,C:$i]:
% 1.94/2.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.94/2.19       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.94/2.19         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.94/2.19           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.94/2.19             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.94/2.19  thf('14', plain,
% 1.94/2.19      (![X27 : $i, X28 : $i, X29 : $i]:
% 1.94/2.19         (~ (zip_tseitin_0 @ X27 @ X28)
% 1.94/2.19          | (zip_tseitin_1 @ X29 @ X27 @ X28)
% 1.94/2.19          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X27))))),
% 1.94/2.19      inference('cnf', [status(esa)], [zf_stmt_6])).
% 1.94/2.19  thf('15', plain,
% 1.94/2.19      (((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)
% 1.94/2.19        | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 1.94/2.19      inference('sup-', [status(thm)], ['13', '14'])).
% 1.94/2.19  thf('16', plain,
% 1.94/2.19      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.94/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.19  thf(dt_k2_relset_1, axiom,
% 1.94/2.19    (![A:$i,B:$i,C:$i]:
% 1.94/2.19     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.94/2.19       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 1.94/2.19  thf('17', plain,
% 1.94/2.19      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.94/2.19         ((m1_subset_1 @ (k2_relset_1 @ X13 @ X14 @ X15) @ (k1_zfmisc_1 @ X14))
% 1.94/2.19          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.94/2.19      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 1.94/2.19  thf('18', plain,
% 1.94/2.19      ((m1_subset_1 @ (k2_relset_1 @ sk_B @ sk_C @ sk_D_1) @ 
% 1.94/2.19        (k1_zfmisc_1 @ sk_C))),
% 1.94/2.19      inference('sup-', [status(thm)], ['16', '17'])).
% 1.94/2.19  thf(t3_subset, axiom,
% 1.94/2.19    (![A:$i,B:$i]:
% 1.94/2.19     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.94/2.19  thf('19', plain,
% 1.94/2.19      (![X6 : $i, X7 : $i]:
% 1.94/2.19         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 1.94/2.19      inference('cnf', [status(esa)], [t3_subset])).
% 1.94/2.19  thf('20', plain, ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D_1) @ sk_C)),
% 1.94/2.19      inference('sup-', [status(thm)], ['18', '19'])).
% 1.94/2.19  thf('21', plain,
% 1.94/2.19      (![X22 : $i, X23 : $i]:
% 1.94/2.19         ((zip_tseitin_0 @ X22 @ X23) | ((X22) = (k1_xboole_0)))),
% 1.94/2.19      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.94/2.19  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 1.94/2.19  thf('22', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 1.94/2.19      inference('cnf', [status(esa)], [t2_xboole_1])).
% 1.94/2.19  thf('23', plain,
% 1.94/2.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.19         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 1.94/2.19      inference('sup+', [status(thm)], ['21', '22'])).
% 1.94/2.19  thf(d10_xboole_0, axiom,
% 1.94/2.19    (![A:$i,B:$i]:
% 1.94/2.19     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.94/2.19  thf('24', plain,
% 1.94/2.19      (![X0 : $i, X2 : $i]:
% 1.94/2.19         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 1.94/2.19      inference('cnf', [status(esa)], [d10_xboole_0])).
% 1.94/2.19  thf('25', plain,
% 1.94/2.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.19         ((zip_tseitin_0 @ X1 @ X2) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 1.94/2.19      inference('sup-', [status(thm)], ['23', '24'])).
% 1.94/2.19  thf('26', plain,
% 1.94/2.19      (![X0 : $i]:
% 1.94/2.19         (((k2_relset_1 @ sk_B @ sk_C @ sk_D_1) = (sk_C))
% 1.94/2.19          | (zip_tseitin_0 @ sk_C @ X0))),
% 1.94/2.19      inference('sup-', [status(thm)], ['20', '25'])).
% 1.94/2.19  thf('27', plain,
% 1.94/2.19      (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D_1) @ sk_A)),
% 1.94/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.19  thf('28', plain,
% 1.94/2.19      (![X0 : $i]: (~ (r1_tarski @ sk_C @ sk_A) | (zip_tseitin_0 @ sk_C @ X0))),
% 1.94/2.19      inference('sup-', [status(thm)], ['26', '27'])).
% 1.94/2.19  thf('29', plain,
% 1.94/2.19      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.94/2.19         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 1.94/2.19      inference('sup+', [status(thm)], ['21', '22'])).
% 1.94/2.19  thf('30', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 1.94/2.19      inference('clc', [status(thm)], ['28', '29'])).
% 1.94/2.19  thf('31', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)),
% 1.94/2.19      inference('demod', [status(thm)], ['15', '30'])).
% 1.94/2.19  thf('32', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 1.94/2.19      inference('demod', [status(thm)], ['12', '31'])).
% 1.94/2.19  thf(zf_stmt_7, type, zip_tseitin_3 : $i > $i > $i > $o).
% 1.94/2.19  thf(zf_stmt_8, axiom,
% 1.94/2.19    (![C:$i,B:$i,A:$i]:
% 1.94/2.19     ( ( zip_tseitin_3 @ C @ B @ A ) =>
% 1.94/2.19       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.94/2.19         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 1.94/2.19  thf(zf_stmt_9, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 1.94/2.19  thf(zf_stmt_10, axiom,
% 1.94/2.19    (![A:$i,B:$i,C:$i]:
% 1.94/2.19     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 1.94/2.19       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 1.94/2.19           ( ![D:$i]: ( zip_tseitin_2 @ D @ C @ B @ A ) ) ) =>
% 1.94/2.19         ( zip_tseitin_3 @ C @ B @ A ) ) ))).
% 1.94/2.19  thf('33', plain,
% 1.94/2.19      (![X41 : $i, X42 : $i, X43 : $i]:
% 1.94/2.19         (((k1_relat_1 @ X42) != (X41))
% 1.94/2.19          | ~ (zip_tseitin_2 @ (sk_D @ X42 @ X43 @ X41) @ X42 @ X43 @ X41)
% 1.94/2.19          | (zip_tseitin_3 @ X42 @ X43 @ X41)
% 1.94/2.19          | ~ (v1_funct_1 @ X42)
% 1.94/2.19          | ~ (v1_relat_1 @ X42))),
% 1.94/2.19      inference('cnf', [status(esa)], [zf_stmt_10])).
% 1.94/2.19  thf('34', plain,
% 1.94/2.19      (![X42 : $i, X43 : $i]:
% 1.94/2.19         (~ (v1_relat_1 @ X42)
% 1.94/2.19          | ~ (v1_funct_1 @ X42)
% 1.94/2.19          | (zip_tseitin_3 @ X42 @ X43 @ (k1_relat_1 @ X42))
% 1.94/2.19          | ~ (zip_tseitin_2 @ (sk_D @ X42 @ X43 @ (k1_relat_1 @ X42)) @ X42 @ 
% 1.94/2.19               X43 @ (k1_relat_1 @ X42)))),
% 1.94/2.19      inference('simplify', [status(thm)], ['33'])).
% 1.94/2.19  thf('35', plain,
% 1.94/2.19      (![X0 : $i]:
% 1.94/2.19         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ 
% 1.94/2.19             (k1_relat_1 @ sk_D_1))
% 1.94/2.19          | (zip_tseitin_3 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 1.94/2.19          | ~ (v1_funct_1 @ sk_D_1)
% 1.94/2.19          | ~ (v1_relat_1 @ sk_D_1))),
% 1.94/2.19      inference('sup-', [status(thm)], ['32', '34'])).
% 1.94/2.19  thf('36', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 1.94/2.19      inference('demod', [status(thm)], ['12', '31'])).
% 1.94/2.19  thf('37', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 1.94/2.19      inference('demod', [status(thm)], ['12', '31'])).
% 1.94/2.19  thf('38', plain, ((v1_funct_1 @ sk_D_1)),
% 1.94/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.19  thf('39', plain,
% 1.94/2.19      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.94/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.19  thf(cc2_relat_1, axiom,
% 1.94/2.19    (![A:$i]:
% 1.94/2.19     ( ( v1_relat_1 @ A ) =>
% 1.94/2.19       ( ![B:$i]:
% 1.94/2.19         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.94/2.19  thf('40', plain,
% 1.94/2.19      (![X9 : $i, X10 : $i]:
% 1.94/2.19         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 1.94/2.19          | (v1_relat_1 @ X9)
% 1.94/2.19          | ~ (v1_relat_1 @ X10))),
% 1.94/2.19      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.94/2.19  thf('41', plain,
% 1.94/2.19      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_D_1))),
% 1.94/2.19      inference('sup-', [status(thm)], ['39', '40'])).
% 1.94/2.19  thf(fc6_relat_1, axiom,
% 1.94/2.19    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.94/2.19  thf('42', plain,
% 1.94/2.19      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 1.94/2.19      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.94/2.19  thf('43', plain, ((v1_relat_1 @ sk_D_1)),
% 1.94/2.19      inference('demod', [status(thm)], ['41', '42'])).
% 1.94/2.19  thf('44', plain,
% 1.94/2.19      (![X0 : $i]:
% 1.94/2.19         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ sk_B)
% 1.94/2.19          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 1.94/2.19      inference('demod', [status(thm)], ['35', '36', '37', '38', '43'])).
% 1.94/2.19  thf('45', plain,
% 1.94/2.19      (![X0 : $i]:
% 1.94/2.19         ((r2_hidden @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B)
% 1.94/2.19          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 1.94/2.19      inference('sup-', [status(thm)], ['5', '44'])).
% 1.94/2.19  thf(t1_subset, axiom,
% 1.94/2.19    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 1.94/2.19  thf('46', plain,
% 1.94/2.19      (![X4 : $i, X5 : $i]: ((m1_subset_1 @ X4 @ X5) | ~ (r2_hidden @ X4 @ X5))),
% 1.94/2.19      inference('cnf', [status(esa)], [t1_subset])).
% 1.94/2.19  thf('47', plain,
% 1.94/2.19      (![X0 : $i]:
% 1.94/2.19         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 1.94/2.19          | (m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B))),
% 1.94/2.19      inference('sup-', [status(thm)], ['45', '46'])).
% 1.94/2.19  thf('48', plain,
% 1.94/2.19      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 1.94/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.19  thf(redefinition_k3_funct_2, axiom,
% 1.94/2.19    (![A:$i,B:$i,C:$i,D:$i]:
% 1.94/2.19     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 1.94/2.19         ( v1_funct_2 @ C @ A @ B ) & 
% 1.94/2.19         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.94/2.19         ( m1_subset_1 @ D @ A ) ) =>
% 1.94/2.19       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 1.94/2.19  thf('49', plain,
% 1.94/2.19      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.94/2.19         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 1.94/2.19          | ~ (v1_funct_2 @ X30 @ X31 @ X32)
% 1.94/2.19          | ~ (v1_funct_1 @ X30)
% 1.94/2.19          | (v1_xboole_0 @ X31)
% 1.94/2.19          | ~ (m1_subset_1 @ X33 @ X31)
% 1.94/2.19          | ((k3_funct_2 @ X31 @ X32 @ X30 @ X33) = (k1_funct_1 @ X30 @ X33)))),
% 1.94/2.19      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 1.94/2.19  thf('50', plain,
% 1.94/2.19      (![X0 : $i]:
% 1.94/2.19         (((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 1.94/2.19            = (k1_funct_1 @ sk_D_1 @ X0))
% 1.94/2.19          | ~ (m1_subset_1 @ X0 @ sk_B)
% 1.94/2.19          | (v1_xboole_0 @ sk_B)
% 1.94/2.19          | ~ (v1_funct_1 @ sk_D_1)
% 1.94/2.19          | ~ (v1_funct_2 @ sk_D_1 @ sk_B @ sk_C))),
% 1.94/2.19      inference('sup-', [status(thm)], ['48', '49'])).
% 1.94/2.19  thf('51', plain, ((v1_funct_1 @ sk_D_1)),
% 1.94/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.19  thf('52', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_C)),
% 1.94/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.19  thf('53', plain,
% 1.94/2.19      (![X0 : $i]:
% 1.94/2.19         (((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 1.94/2.19            = (k1_funct_1 @ sk_D_1 @ X0))
% 1.94/2.19          | ~ (m1_subset_1 @ X0 @ sk_B)
% 1.94/2.19          | (v1_xboole_0 @ sk_B))),
% 1.94/2.19      inference('demod', [status(thm)], ['50', '51', '52'])).
% 1.94/2.19  thf('54', plain, (~ (v1_xboole_0 @ sk_B)),
% 1.94/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.19  thf('55', plain,
% 1.94/2.19      (![X0 : $i]:
% 1.94/2.19         (~ (m1_subset_1 @ X0 @ sk_B)
% 1.94/2.19          | ((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 1.94/2.19              = (k1_funct_1 @ sk_D_1 @ X0)))),
% 1.94/2.19      inference('clc', [status(thm)], ['53', '54'])).
% 1.94/2.19  thf('56', plain,
% 1.94/2.19      (![X0 : $i]:
% 1.94/2.19         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 1.94/2.19          | ((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B))
% 1.94/2.19              = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B))))),
% 1.94/2.19      inference('sup-', [status(thm)], ['47', '55'])).
% 1.94/2.19  thf('57', plain,
% 1.94/2.19      (![X0 : $i]:
% 1.94/2.19         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 1.94/2.19          | (m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B))),
% 1.94/2.19      inference('sup-', [status(thm)], ['45', '46'])).
% 1.94/2.19  thf('58', plain,
% 1.94/2.19      (![X44 : $i]:
% 1.94/2.19         ((r2_hidden @ (k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X44) @ sk_A)
% 1.94/2.19          | ~ (m1_subset_1 @ X44 @ sk_B))),
% 1.94/2.19      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.94/2.19  thf('59', plain,
% 1.94/2.19      (![X0 : $i]:
% 1.94/2.19         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 1.94/2.19          | (r2_hidden @ 
% 1.94/2.19             (k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 1.94/2.19             sk_A))),
% 1.94/2.19      inference('sup-', [status(thm)], ['57', '58'])).
% 1.94/2.19  thf('60', plain,
% 1.94/2.19      (![X0 : $i]:
% 1.94/2.19         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 1.94/2.19           sk_A)
% 1.94/2.19          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 1.94/2.19          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 1.94/2.19      inference('sup+', [status(thm)], ['56', '59'])).
% 1.94/2.19  thf('61', plain,
% 1.94/2.19      (![X0 : $i]:
% 1.94/2.19         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 1.94/2.19          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 1.94/2.19             sk_A))),
% 1.94/2.19      inference('simplify', [status(thm)], ['60'])).
% 1.94/2.19  thf('62', plain,
% 1.94/2.19      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 1.94/2.19         ((zip_tseitin_2 @ X34 @ X35 @ X36 @ X37)
% 1.94/2.19          | ~ (r2_hidden @ (k1_funct_1 @ X35 @ X34) @ X36))),
% 1.94/2.19      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.94/2.19  thf('63', plain,
% 1.94/2.19      (![X0 : $i, X1 : $i]:
% 1.94/2.19         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 1.94/2.19          | (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ sk_A @ X1))),
% 1.94/2.19      inference('sup-', [status(thm)], ['61', '62'])).
% 1.94/2.19  thf('64', plain,
% 1.94/2.19      (![X0 : $i]:
% 1.94/2.19         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ sk_B)
% 1.94/2.19          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 1.94/2.19      inference('demod', [status(thm)], ['35', '36', '37', '38', '43'])).
% 1.94/2.19  thf('65', plain,
% 1.94/2.19      (((zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B)
% 1.94/2.19        | (zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B))),
% 1.94/2.19      inference('sup-', [status(thm)], ['63', '64'])).
% 1.94/2.19  thf('66', plain, ((zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B)),
% 1.94/2.19      inference('simplify', [status(thm)], ['65'])).
% 1.94/2.19  thf('67', plain,
% 1.94/2.19      (![X38 : $i, X39 : $i, X40 : $i]:
% 1.94/2.19         ((m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X39)))
% 1.94/2.19          | ~ (zip_tseitin_3 @ X38 @ X39 @ X40))),
% 1.94/2.19      inference('cnf', [status(esa)], [zf_stmt_8])).
% 1.94/2.19  thf('68', plain,
% 1.94/2.19      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.94/2.19      inference('sup-', [status(thm)], ['66', '67'])).
% 1.94/2.19  thf('69', plain,
% 1.94/2.19      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.94/2.19         ((m1_subset_1 @ (k2_relset_1 @ X13 @ X14 @ X15) @ (k1_zfmisc_1 @ X14))
% 1.94/2.19          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 1.94/2.19      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 1.94/2.19  thf('70', plain,
% 1.94/2.19      ((m1_subset_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_D_1) @ 
% 1.94/2.19        (k1_zfmisc_1 @ sk_A))),
% 1.94/2.19      inference('sup-', [status(thm)], ['68', '69'])).
% 1.94/2.19  thf('71', plain,
% 1.94/2.19      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.94/2.19      inference('sup-', [status(thm)], ['66', '67'])).
% 1.94/2.19  thf('72', plain,
% 1.94/2.19      (![X19 : $i, X20 : $i, X21 : $i]:
% 1.94/2.19         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 1.94/2.19          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 1.94/2.19      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.94/2.19  thf('73', plain,
% 1.94/2.19      (((k2_relset_1 @ sk_B @ sk_A @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 1.94/2.19      inference('sup-', [status(thm)], ['71', '72'])).
% 1.94/2.19  thf('74', plain,
% 1.94/2.19      ((m1_subset_1 @ (k2_relat_1 @ sk_D_1) @ (k1_zfmisc_1 @ sk_A))),
% 1.94/2.19      inference('demod', [status(thm)], ['70', '73'])).
% 1.94/2.19  thf('75', plain,
% 1.94/2.19      (![X6 : $i, X7 : $i]:
% 1.94/2.19         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 1.94/2.19      inference('cnf', [status(esa)], [t3_subset])).
% 1.94/2.19  thf('76', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 1.94/2.19      inference('sup-', [status(thm)], ['74', '75'])).
% 1.94/2.19  thf('77', plain, ($false), inference('demod', [status(thm)], ['4', '76'])).
% 1.94/2.19  
% 1.94/2.19  % SZS output end Refutation
% 1.94/2.19  
% 1.94/2.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
