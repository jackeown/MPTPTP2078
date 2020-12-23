%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.z9Avr6HYKw

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:25 EST 2020

% Result     : Theorem 8.76s
% Output     : Refutation 8.76s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 891 expanded)
%              Number of leaves         :   50 ( 290 expanded)
%              Depth                    :   21
%              Number of atoms          :  926 (11628 expanded)
%              Number of equality atoms :   36 ( 289 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ~ ( r1_tarski @ ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 )
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
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( zip_tseitin_2 @ X36 @ X37 @ X38 @ X39 )
      | ( r2_hidden @ X36 @ X39 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('6',plain,(
    ! [X4: $i,X5: $i] :
      ( ( m1_subset_1 @ X4 @ X5 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( zip_tseitin_2 @ X1 @ X3 @ X2 @ X0 )
      | ( m1_subset_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C ),
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

thf('9',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('10',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k1_relset_1 @ X19 @ X20 @ X18 )
        = ( k1_relat_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('13',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relat_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
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

thf('16',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('17',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1 )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('19',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('20',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['18','23'])).

thf('25',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1 ),
    inference(demod,[status(thm)],['17','26'])).

thf('28',plain,
    ( sk_B_1
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['14','27'])).

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

thf('29',plain,(
    ! [X43: $i,X44: $i,X45: $i] :
      ( ( ( k1_relat_1 @ X44 )
       != X43 )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X44 @ X45 @ X43 ) @ X44 @ X45 @ X43 )
      | ( zip_tseitin_3 @ X44 @ X45 @ X43 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('30',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( v1_relat_1 @ X44 )
      | ~ ( v1_funct_1 @ X44 )
      | ( zip_tseitin_3 @ X44 @ X45 @ ( k1_relat_1 @ X44 ) )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X44 @ X45 @ ( k1_relat_1 @ X44 ) ) @ X44 @ X45 @ ( k1_relat_1 @ X44 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B_1 ) @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,
    ( sk_B_1
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['14','27'])).

thf('33',plain,
    ( sk_B_1
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['14','27'])).

thf('34',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('36',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( v1_relat_1 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('38',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('39',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B_1 ) @ sk_D_1 @ X0 @ sk_B_1 )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['31','32','33','34','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B_1 ) @ sk_B_1 )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
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

thf('43',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( v1_funct_1 @ X32 )
      | ( v1_xboole_0 @ X33 )
      | ~ ( m1_subset_1 @ X35 @ X33 )
      | ( ( k3_funct_2 @ X33 @ X34 @ X32 @ X35 )
        = ( k1_funct_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( ( k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1 )
      | ( ( k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B_1 ) )
        = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['41','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B_1 ) @ sk_B_1 )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','40'])).

thf('52',plain,(
    ! [X46: $i] :
      ( ( r2_hidden @ ( k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_1 @ X46 ) @ sk_A )
      | ~ ( m1_subset_1 @ X46 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B_1 ) ) @ sk_A )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1 )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['50','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B_1 ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ( zip_tseitin_2 @ X36 @ X37 @ X38 @ X39 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X37 @ X36 ) @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('57',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1 )
      | ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B_1 ) @ sk_D_1 @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B_1 ) @ sk_D_1 @ X0 @ sk_B_1 )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['31','32','33','34','39'])).

thf('59',plain,
    ( ( zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B_1 )
    | ( zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B_1 ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X41 ) ) )
      | ~ ( zip_tseitin_3 @ X40 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('62',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('63',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X15 @ X16 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('64',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('66',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('67',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['64','67'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('69',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('70',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['4','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.z9Avr6HYKw
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:11:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 8.76/9.00  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 8.76/9.00  % Solved by: fo/fo7.sh
% 8.76/9.00  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 8.76/9.00  % done 3801 iterations in 8.571s
% 8.76/9.00  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 8.76/9.00  % SZS output start Refutation
% 8.76/9.00  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 8.76/9.00  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 8.76/9.00  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 8.76/9.00  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 8.76/9.00  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 8.76/9.00  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 8.76/9.00  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 8.76/9.00  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 8.76/9.00  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 8.76/9.00  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 8.76/9.00  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 8.76/9.00  thf(sk_A_type, type, sk_A: $i).
% 8.76/9.00  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 8.76/9.00  thf(sk_B_1_type, type, sk_B_1: $i).
% 8.76/9.00  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 8.76/9.00  thf(sk_B_type, type, sk_B: $i > $i).
% 8.76/9.00  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $o).
% 8.76/9.00  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 8.76/9.00  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 8.76/9.00  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 8.76/9.00  thf(sk_C_type, type, sk_C: $i).
% 8.76/9.00  thf(sk_D_1_type, type, sk_D_1: $i).
% 8.76/9.00  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 8.76/9.00  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 8.76/9.00  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 8.76/9.00  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 8.76/9.00  thf(t191_funct_2, conjecture,
% 8.76/9.00    (![A:$i,B:$i]:
% 8.76/9.00     ( ( ~( v1_xboole_0 @ B ) ) =>
% 8.76/9.00       ( ![C:$i]:
% 8.76/9.00         ( ( ~( v1_xboole_0 @ C ) ) =>
% 8.76/9.00           ( ![D:$i]:
% 8.76/9.00             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 8.76/9.00                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 8.76/9.00               ( ( ![E:$i]:
% 8.76/9.00                   ( ( m1_subset_1 @ E @ B ) =>
% 8.76/9.00                     ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 8.76/9.00                 ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ))).
% 8.76/9.00  thf(zf_stmt_0, negated_conjecture,
% 8.76/9.00    (~( ![A:$i,B:$i]:
% 8.76/9.00        ( ( ~( v1_xboole_0 @ B ) ) =>
% 8.76/9.00          ( ![C:$i]:
% 8.76/9.00            ( ( ~( v1_xboole_0 @ C ) ) =>
% 8.76/9.00              ( ![D:$i]:
% 8.76/9.00                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 8.76/9.00                    ( m1_subset_1 @
% 8.76/9.00                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 8.76/9.00                  ( ( ![E:$i]:
% 8.76/9.00                      ( ( m1_subset_1 @ E @ B ) =>
% 8.76/9.00                        ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 8.76/9.00                    ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ) )),
% 8.76/9.00    inference('cnf.neg', [status(esa)], [t191_funct_2])).
% 8.76/9.00  thf('0', plain,
% 8.76/9.00      (~ (r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1) @ sk_A)),
% 8.76/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.76/9.00  thf('1', plain,
% 8.76/9.00      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 8.76/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.76/9.00  thf(redefinition_k2_relset_1, axiom,
% 8.76/9.00    (![A:$i,B:$i,C:$i]:
% 8.76/9.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.76/9.00       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 8.76/9.00  thf('2', plain,
% 8.76/9.00      (![X21 : $i, X22 : $i, X23 : $i]:
% 8.76/9.00         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 8.76/9.00          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 8.76/9.00      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 8.76/9.00  thf('3', plain,
% 8.76/9.00      (((k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 8.76/9.00      inference('sup-', [status(thm)], ['1', '2'])).
% 8.76/9.00  thf('4', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 8.76/9.00      inference('demod', [status(thm)], ['0', '3'])).
% 8.76/9.00  thf(t5_funct_2, axiom,
% 8.76/9.00    (![A:$i,B:$i,C:$i]:
% 8.76/9.00     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 8.76/9.00       ( ( ( ![D:$i]:
% 8.76/9.00             ( ( r2_hidden @ D @ A ) =>
% 8.76/9.00               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 8.76/9.00           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 8.76/9.00         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 8.76/9.00           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 8.76/9.00  thf(zf_stmt_1, axiom,
% 8.76/9.00    (![D:$i,C:$i,B:$i,A:$i]:
% 8.76/9.00     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 8.76/9.00       ( zip_tseitin_2 @ D @ C @ B @ A ) ))).
% 8.76/9.00  thf('5', plain,
% 8.76/9.00      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 8.76/9.00         ((zip_tseitin_2 @ X36 @ X37 @ X38 @ X39) | (r2_hidden @ X36 @ X39))),
% 8.76/9.00      inference('cnf', [status(esa)], [zf_stmt_1])).
% 8.76/9.00  thf(t1_subset, axiom,
% 8.76/9.00    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 8.76/9.00  thf('6', plain,
% 8.76/9.00      (![X4 : $i, X5 : $i]: ((m1_subset_1 @ X4 @ X5) | ~ (r2_hidden @ X4 @ X5))),
% 8.76/9.00      inference('cnf', [status(esa)], [t1_subset])).
% 8.76/9.00  thf('7', plain,
% 8.76/9.00      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 8.76/9.00         ((zip_tseitin_2 @ X1 @ X3 @ X2 @ X0) | (m1_subset_1 @ X1 @ X0))),
% 8.76/9.00      inference('sup-', [status(thm)], ['5', '6'])).
% 8.76/9.00  thf('8', plain, ((v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C)),
% 8.76/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.76/9.00  thf(d1_funct_2, axiom,
% 8.76/9.00    (![A:$i,B:$i,C:$i]:
% 8.76/9.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.76/9.00       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 8.76/9.00           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 8.76/9.00             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 8.76/9.00         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 8.76/9.00           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 8.76/9.00             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 8.76/9.00  thf(zf_stmt_2, axiom,
% 8.76/9.00    (![C:$i,B:$i,A:$i]:
% 8.76/9.00     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 8.76/9.00       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 8.76/9.00  thf('9', plain,
% 8.76/9.00      (![X26 : $i, X27 : $i, X28 : $i]:
% 8.76/9.00         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 8.76/9.00          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 8.76/9.00          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 8.76/9.00      inference('cnf', [status(esa)], [zf_stmt_2])).
% 8.76/9.00  thf('10', plain,
% 8.76/9.00      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1)
% 8.76/9.00        | ((sk_B_1) = (k1_relset_1 @ sk_B_1 @ sk_C @ sk_D_1)))),
% 8.76/9.00      inference('sup-', [status(thm)], ['8', '9'])).
% 8.76/9.00  thf('11', plain,
% 8.76/9.00      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 8.76/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.76/9.00  thf(redefinition_k1_relset_1, axiom,
% 8.76/9.00    (![A:$i,B:$i,C:$i]:
% 8.76/9.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.76/9.00       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 8.76/9.00  thf('12', plain,
% 8.76/9.00      (![X18 : $i, X19 : $i, X20 : $i]:
% 8.76/9.00         (((k1_relset_1 @ X19 @ X20 @ X18) = (k1_relat_1 @ X18))
% 8.76/9.00          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 8.76/9.00      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 8.76/9.00  thf('13', plain,
% 8.76/9.00      (((k1_relset_1 @ sk_B_1 @ sk_C @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 8.76/9.00      inference('sup-', [status(thm)], ['11', '12'])).
% 8.76/9.00  thf('14', plain,
% 8.76/9.00      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1)
% 8.76/9.00        | ((sk_B_1) = (k1_relat_1 @ sk_D_1)))),
% 8.76/9.00      inference('demod', [status(thm)], ['10', '13'])).
% 8.76/9.00  thf('15', plain,
% 8.76/9.00      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 8.76/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.76/9.00  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 8.76/9.00  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 8.76/9.00  thf(zf_stmt_5, axiom,
% 8.76/9.00    (![B:$i,A:$i]:
% 8.76/9.00     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 8.76/9.00       ( zip_tseitin_0 @ B @ A ) ))).
% 8.76/9.00  thf(zf_stmt_6, axiom,
% 8.76/9.00    (![A:$i,B:$i,C:$i]:
% 8.76/9.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.76/9.00       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 8.76/9.00         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 8.76/9.00           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 8.76/9.00             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 8.76/9.00  thf('16', plain,
% 8.76/9.00      (![X29 : $i, X30 : $i, X31 : $i]:
% 8.76/9.00         (~ (zip_tseitin_0 @ X29 @ X30)
% 8.76/9.00          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 8.76/9.00          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 8.76/9.00      inference('cnf', [status(esa)], [zf_stmt_6])).
% 8.76/9.00  thf('17', plain,
% 8.76/9.00      (((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1)
% 8.76/9.00        | ~ (zip_tseitin_0 @ sk_C @ sk_B_1))),
% 8.76/9.00      inference('sup-', [status(thm)], ['15', '16'])).
% 8.76/9.00  thf('18', plain,
% 8.76/9.00      (![X24 : $i, X25 : $i]:
% 8.76/9.00         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 8.76/9.00      inference('cnf', [status(esa)], [zf_stmt_5])).
% 8.76/9.00  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 8.76/9.00  thf('19', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 8.76/9.00      inference('cnf', [status(esa)], [t2_xboole_1])).
% 8.76/9.00  thf(d1_xboole_0, axiom,
% 8.76/9.00    (![A:$i]:
% 8.76/9.00     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 8.76/9.00  thf('20', plain,
% 8.76/9.00      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 8.76/9.00      inference('cnf', [status(esa)], [d1_xboole_0])).
% 8.76/9.00  thf(t7_ordinal1, axiom,
% 8.76/9.00    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 8.76/9.00  thf('21', plain,
% 8.76/9.00      (![X13 : $i, X14 : $i]:
% 8.76/9.00         (~ (r2_hidden @ X13 @ X14) | ~ (r1_tarski @ X14 @ X13))),
% 8.76/9.00      inference('cnf', [status(esa)], [t7_ordinal1])).
% 8.76/9.00  thf('22', plain,
% 8.76/9.00      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 8.76/9.00      inference('sup-', [status(thm)], ['20', '21'])).
% 8.76/9.00  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 8.76/9.00      inference('sup-', [status(thm)], ['19', '22'])).
% 8.76/9.00  thf('24', plain,
% 8.76/9.00      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 8.76/9.00      inference('sup+', [status(thm)], ['18', '23'])).
% 8.76/9.00  thf('25', plain, (~ (v1_xboole_0 @ sk_C)),
% 8.76/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.76/9.00  thf('26', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 8.76/9.00      inference('sup-', [status(thm)], ['24', '25'])).
% 8.76/9.00  thf('27', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1)),
% 8.76/9.00      inference('demod', [status(thm)], ['17', '26'])).
% 8.76/9.00  thf('28', plain, (((sk_B_1) = (k1_relat_1 @ sk_D_1))),
% 8.76/9.00      inference('demod', [status(thm)], ['14', '27'])).
% 8.76/9.00  thf(zf_stmt_7, type, zip_tseitin_3 : $i > $i > $i > $o).
% 8.76/9.00  thf(zf_stmt_8, axiom,
% 8.76/9.00    (![C:$i,B:$i,A:$i]:
% 8.76/9.00     ( ( zip_tseitin_3 @ C @ B @ A ) =>
% 8.76/9.00       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 8.76/9.00         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 8.76/9.00  thf(zf_stmt_9, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 8.76/9.00  thf(zf_stmt_10, axiom,
% 8.76/9.00    (![A:$i,B:$i,C:$i]:
% 8.76/9.00     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 8.76/9.00       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 8.76/9.00           ( ![D:$i]: ( zip_tseitin_2 @ D @ C @ B @ A ) ) ) =>
% 8.76/9.00         ( zip_tseitin_3 @ C @ B @ A ) ) ))).
% 8.76/9.00  thf('29', plain,
% 8.76/9.00      (![X43 : $i, X44 : $i, X45 : $i]:
% 8.76/9.00         (((k1_relat_1 @ X44) != (X43))
% 8.76/9.00          | ~ (zip_tseitin_2 @ (sk_D @ X44 @ X45 @ X43) @ X44 @ X45 @ X43)
% 8.76/9.00          | (zip_tseitin_3 @ X44 @ X45 @ X43)
% 8.76/9.00          | ~ (v1_funct_1 @ X44)
% 8.76/9.00          | ~ (v1_relat_1 @ X44))),
% 8.76/9.00      inference('cnf', [status(esa)], [zf_stmt_10])).
% 8.76/9.00  thf('30', plain,
% 8.76/9.00      (![X44 : $i, X45 : $i]:
% 8.76/9.00         (~ (v1_relat_1 @ X44)
% 8.76/9.00          | ~ (v1_funct_1 @ X44)
% 8.76/9.00          | (zip_tseitin_3 @ X44 @ X45 @ (k1_relat_1 @ X44))
% 8.76/9.00          | ~ (zip_tseitin_2 @ (sk_D @ X44 @ X45 @ (k1_relat_1 @ X44)) @ X44 @ 
% 8.76/9.00               X45 @ (k1_relat_1 @ X44)))),
% 8.76/9.00      inference('simplify', [status(thm)], ['29'])).
% 8.76/9.00  thf('31', plain,
% 8.76/9.00      (![X0 : $i]:
% 8.76/9.00         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B_1) @ sk_D_1 @ X0 @ 
% 8.76/9.00             (k1_relat_1 @ sk_D_1))
% 8.76/9.00          | (zip_tseitin_3 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 8.76/9.00          | ~ (v1_funct_1 @ sk_D_1)
% 8.76/9.00          | ~ (v1_relat_1 @ sk_D_1))),
% 8.76/9.00      inference('sup-', [status(thm)], ['28', '30'])).
% 8.76/9.00  thf('32', plain, (((sk_B_1) = (k1_relat_1 @ sk_D_1))),
% 8.76/9.00      inference('demod', [status(thm)], ['14', '27'])).
% 8.76/9.00  thf('33', plain, (((sk_B_1) = (k1_relat_1 @ sk_D_1))),
% 8.76/9.00      inference('demod', [status(thm)], ['14', '27'])).
% 8.76/9.00  thf('34', plain, ((v1_funct_1 @ sk_D_1)),
% 8.76/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.76/9.00  thf('35', plain,
% 8.76/9.00      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 8.76/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.76/9.00  thf(cc2_relat_1, axiom,
% 8.76/9.00    (![A:$i]:
% 8.76/9.00     ( ( v1_relat_1 @ A ) =>
% 8.76/9.00       ( ![B:$i]:
% 8.76/9.00         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 8.76/9.00  thf('36', plain,
% 8.76/9.00      (![X9 : $i, X10 : $i]:
% 8.76/9.00         (~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 8.76/9.00          | (v1_relat_1 @ X9)
% 8.76/9.00          | ~ (v1_relat_1 @ X10))),
% 8.76/9.00      inference('cnf', [status(esa)], [cc2_relat_1])).
% 8.76/9.00  thf('37', plain,
% 8.76/9.00      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)) | (v1_relat_1 @ sk_D_1))),
% 8.76/9.00      inference('sup-', [status(thm)], ['35', '36'])).
% 8.76/9.00  thf(fc6_relat_1, axiom,
% 8.76/9.00    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 8.76/9.00  thf('38', plain,
% 8.76/9.00      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 8.76/9.00      inference('cnf', [status(esa)], [fc6_relat_1])).
% 8.76/9.00  thf('39', plain, ((v1_relat_1 @ sk_D_1)),
% 8.76/9.00      inference('demod', [status(thm)], ['37', '38'])).
% 8.76/9.00  thf('40', plain,
% 8.76/9.00      (![X0 : $i]:
% 8.76/9.00         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B_1) @ sk_D_1 @ X0 @ 
% 8.76/9.00             sk_B_1)
% 8.76/9.00          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1))),
% 8.76/9.00      inference('demod', [status(thm)], ['31', '32', '33', '34', '39'])).
% 8.76/9.00  thf('41', plain,
% 8.76/9.00      (![X0 : $i]:
% 8.76/9.00         ((m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B_1) @ sk_B_1)
% 8.76/9.00          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1))),
% 8.76/9.00      inference('sup-', [status(thm)], ['7', '40'])).
% 8.76/9.00  thf('42', plain,
% 8.76/9.00      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 8.76/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.76/9.00  thf(redefinition_k3_funct_2, axiom,
% 8.76/9.00    (![A:$i,B:$i,C:$i,D:$i]:
% 8.76/9.00     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 8.76/9.00         ( v1_funct_2 @ C @ A @ B ) & 
% 8.76/9.00         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 8.76/9.00         ( m1_subset_1 @ D @ A ) ) =>
% 8.76/9.00       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 8.76/9.00  thf('43', plain,
% 8.76/9.00      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 8.76/9.00         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 8.76/9.00          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 8.76/9.00          | ~ (v1_funct_1 @ X32)
% 8.76/9.00          | (v1_xboole_0 @ X33)
% 8.76/9.00          | ~ (m1_subset_1 @ X35 @ X33)
% 8.76/9.00          | ((k3_funct_2 @ X33 @ X34 @ X32 @ X35) = (k1_funct_1 @ X32 @ X35)))),
% 8.76/9.00      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 8.76/9.00  thf('44', plain,
% 8.76/9.00      (![X0 : $i]:
% 8.76/9.00         (((k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_1 @ X0)
% 8.76/9.00            = (k1_funct_1 @ sk_D_1 @ X0))
% 8.76/9.00          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 8.76/9.00          | (v1_xboole_0 @ sk_B_1)
% 8.76/9.00          | ~ (v1_funct_1 @ sk_D_1)
% 8.76/9.00          | ~ (v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C))),
% 8.76/9.00      inference('sup-', [status(thm)], ['42', '43'])).
% 8.76/9.00  thf('45', plain, ((v1_funct_1 @ sk_D_1)),
% 8.76/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.76/9.00  thf('46', plain, ((v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C)),
% 8.76/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.76/9.00  thf('47', plain,
% 8.76/9.00      (![X0 : $i]:
% 8.76/9.00         (((k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_1 @ X0)
% 8.76/9.00            = (k1_funct_1 @ sk_D_1 @ X0))
% 8.76/9.00          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 8.76/9.00          | (v1_xboole_0 @ sk_B_1))),
% 8.76/9.00      inference('demod', [status(thm)], ['44', '45', '46'])).
% 8.76/9.00  thf('48', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 8.76/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.76/9.00  thf('49', plain,
% 8.76/9.00      (![X0 : $i]:
% 8.76/9.00         (~ (m1_subset_1 @ X0 @ sk_B_1)
% 8.76/9.00          | ((k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_1 @ X0)
% 8.76/9.00              = (k1_funct_1 @ sk_D_1 @ X0)))),
% 8.76/9.00      inference('clc', [status(thm)], ['47', '48'])).
% 8.76/9.00  thf('50', plain,
% 8.76/9.00      (![X0 : $i]:
% 8.76/9.00         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1)
% 8.76/9.00          | ((k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_1 @ 
% 8.76/9.00              (sk_D @ sk_D_1 @ X0 @ sk_B_1))
% 8.76/9.00              = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B_1))))),
% 8.76/9.00      inference('sup-', [status(thm)], ['41', '49'])).
% 8.76/9.00  thf('51', plain,
% 8.76/9.00      (![X0 : $i]:
% 8.76/9.00         ((m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B_1) @ sk_B_1)
% 8.76/9.00          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1))),
% 8.76/9.00      inference('sup-', [status(thm)], ['7', '40'])).
% 8.76/9.00  thf('52', plain,
% 8.76/9.00      (![X46 : $i]:
% 8.76/9.00         ((r2_hidden @ (k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_1 @ X46) @ sk_A)
% 8.76/9.00          | ~ (m1_subset_1 @ X46 @ sk_B_1))),
% 8.76/9.00      inference('cnf', [status(esa)], [zf_stmt_0])).
% 8.76/9.00  thf('53', plain,
% 8.76/9.00      (![X0 : $i]:
% 8.76/9.00         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1)
% 8.76/9.00          | (r2_hidden @ 
% 8.76/9.00             (k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_1 @ 
% 8.76/9.00              (sk_D @ sk_D_1 @ X0 @ sk_B_1)) @ 
% 8.76/9.00             sk_A))),
% 8.76/9.00      inference('sup-', [status(thm)], ['51', '52'])).
% 8.76/9.00  thf('54', plain,
% 8.76/9.00      (![X0 : $i]:
% 8.76/9.00         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B_1)) @ 
% 8.76/9.00           sk_A)
% 8.76/9.00          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1)
% 8.76/9.00          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1))),
% 8.76/9.00      inference('sup+', [status(thm)], ['50', '53'])).
% 8.76/9.00  thf('55', plain,
% 8.76/9.00      (![X0 : $i]:
% 8.76/9.00         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1)
% 8.76/9.00          | (r2_hidden @ 
% 8.76/9.00             (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B_1)) @ sk_A))),
% 8.76/9.00      inference('simplify', [status(thm)], ['54'])).
% 8.76/9.00  thf('56', plain,
% 8.76/9.00      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 8.76/9.00         ((zip_tseitin_2 @ X36 @ X37 @ X38 @ X39)
% 8.76/9.00          | ~ (r2_hidden @ (k1_funct_1 @ X37 @ X36) @ X38))),
% 8.76/9.00      inference('cnf', [status(esa)], [zf_stmt_1])).
% 8.76/9.00  thf('57', plain,
% 8.76/9.00      (![X0 : $i, X1 : $i]:
% 8.76/9.00         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1)
% 8.76/9.00          | (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B_1) @ sk_D_1 @ sk_A @ X1))),
% 8.76/9.00      inference('sup-', [status(thm)], ['55', '56'])).
% 8.76/9.00  thf('58', plain,
% 8.76/9.00      (![X0 : $i]:
% 8.76/9.00         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B_1) @ sk_D_1 @ X0 @ 
% 8.76/9.00             sk_B_1)
% 8.76/9.00          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1))),
% 8.76/9.00      inference('demod', [status(thm)], ['31', '32', '33', '34', '39'])).
% 8.76/9.00  thf('59', plain,
% 8.76/9.00      (((zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B_1)
% 8.76/9.00        | (zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B_1))),
% 8.76/9.00      inference('sup-', [status(thm)], ['57', '58'])).
% 8.76/9.00  thf('60', plain, ((zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B_1)),
% 8.76/9.00      inference('simplify', [status(thm)], ['59'])).
% 8.76/9.00  thf('61', plain,
% 8.76/9.00      (![X40 : $i, X41 : $i, X42 : $i]:
% 8.76/9.00         ((m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X41)))
% 8.76/9.00          | ~ (zip_tseitin_3 @ X40 @ X41 @ X42))),
% 8.76/9.00      inference('cnf', [status(esa)], [zf_stmt_8])).
% 8.76/9.00  thf('62', plain,
% 8.76/9.00      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 8.76/9.00      inference('sup-', [status(thm)], ['60', '61'])).
% 8.76/9.00  thf(dt_k2_relset_1, axiom,
% 8.76/9.00    (![A:$i,B:$i,C:$i]:
% 8.76/9.00     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 8.76/9.00       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 8.76/9.00  thf('63', plain,
% 8.76/9.00      (![X15 : $i, X16 : $i, X17 : $i]:
% 8.76/9.00         ((m1_subset_1 @ (k2_relset_1 @ X15 @ X16 @ X17) @ (k1_zfmisc_1 @ X16))
% 8.76/9.00          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 8.76/9.00      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 8.76/9.00  thf('64', plain,
% 8.76/9.00      ((m1_subset_1 @ (k2_relset_1 @ sk_B_1 @ sk_A @ sk_D_1) @ 
% 8.76/9.00        (k1_zfmisc_1 @ sk_A))),
% 8.76/9.00      inference('sup-', [status(thm)], ['62', '63'])).
% 8.76/9.00  thf('65', plain,
% 8.76/9.00      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 8.76/9.00      inference('sup-', [status(thm)], ['60', '61'])).
% 8.76/9.00  thf('66', plain,
% 8.76/9.00      (![X21 : $i, X22 : $i, X23 : $i]:
% 8.76/9.00         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 8.76/9.00          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 8.76/9.00      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 8.76/9.00  thf('67', plain,
% 8.76/9.00      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 8.76/9.00      inference('sup-', [status(thm)], ['65', '66'])).
% 8.76/9.00  thf('68', plain,
% 8.76/9.00      ((m1_subset_1 @ (k2_relat_1 @ sk_D_1) @ (k1_zfmisc_1 @ sk_A))),
% 8.76/9.00      inference('demod', [status(thm)], ['64', '67'])).
% 8.76/9.00  thf(t3_subset, axiom,
% 8.76/9.00    (![A:$i,B:$i]:
% 8.76/9.00     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 8.76/9.00  thf('69', plain,
% 8.76/9.00      (![X6 : $i, X7 : $i]:
% 8.76/9.00         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 8.76/9.00      inference('cnf', [status(esa)], [t3_subset])).
% 8.76/9.00  thf('70', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 8.76/9.00      inference('sup-', [status(thm)], ['68', '69'])).
% 8.76/9.00  thf('71', plain, ($false), inference('demod', [status(thm)], ['4', '70'])).
% 8.76/9.00  
% 8.76/9.00  % SZS output end Refutation
% 8.76/9.00  
% 8.86/9.01  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
