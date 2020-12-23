%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LjsP2amyHk

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:23 EST 2020

% Result     : Theorem 7.22s
% Output     : Refutation 7.22s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 855 expanded)
%              Number of leaves         :   49 ( 284 expanded)
%              Depth                    :   20
%              Number of atoms          :  908 (11472 expanded)
%              Number of equality atoms :   35 ( 271 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X22 @ X20 )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( zip_tseitin_2 @ X35 @ X36 @ X37 @ X38 )
      | ( r2_hidden @ X35 @ X38 ) ) ),
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
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('10',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1 )
    | ( sk_B_1
      = ( k1_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
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

thf('12',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('13',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1 )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('15',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['14','15'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('17',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('18',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X9 @ X10 )
      | ~ ( r1_tarski @ X10 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1 ),
    inference(demod,[status(thm)],['13','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k1_relset_1 @ X18 @ X19 @ X17 )
        = ( k1_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('26',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_C @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,
    ( sk_B_1
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['10','23','26'])).

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

thf('28',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( ( k1_relat_1 @ X43 )
       != X42 )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X43 @ X44 @ X42 ) @ X43 @ X44 @ X42 )
      | ( zip_tseitin_3 @ X43 @ X44 @ X42 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_relat_1 @ X43 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('29',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( v1_relat_1 @ X43 )
      | ~ ( v1_funct_1 @ X43 )
      | ( zip_tseitin_3 @ X43 @ X44 @ ( k1_relat_1 @ X43 ) )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X43 @ X44 @ ( k1_relat_1 @ X43 ) ) @ X43 @ X44 @ ( k1_relat_1 @ X43 ) ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B_1 ) @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['27','29'])).

thf('31',plain,
    ( sk_B_1
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['10','23','26'])).

thf('32',plain,
    ( sk_B_1
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['10','23','26'])).

thf('33',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('35',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('36',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B_1 ) @ sk_D_1 @ X0 @ sk_B_1 )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['30','31','32','33','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B_1 ) @ sk_B_1 )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','37'])).

thf('39',plain,(
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

thf('40',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( v1_funct_1 @ X31 )
      | ( v1_xboole_0 @ X32 )
      | ~ ( m1_subset_1 @ X34 @ X32 )
      | ( ( k3_funct_2 @ X32 @ X33 @ X31 @ X34 )
        = ( k1_funct_1 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B_1 )
      | ( ( k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1 )
      | ( ( k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B_1 ) )
        = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['38','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B_1 ) @ sk_B_1 )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','37'])).

thf('49',plain,(
    ! [X45: $i] :
      ( ( r2_hidden @ ( k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_1 @ X45 ) @ sk_A )
      | ~ ( m1_subset_1 @ X45 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B_1 ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B_1 ) ) @ sk_A )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1 )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1 ) ) ),
    inference('sup+',[status(thm)],['47','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1 )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B_1 ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( zip_tseitin_2 @ X35 @ X36 @ X37 @ X38 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X36 @ X35 ) @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1 )
      | ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B_1 ) @ sk_D_1 @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B_1 ) @ sk_D_1 @ X0 @ sk_B_1 )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['30','31','32','33','36'])).

thf('56',plain,
    ( ( zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B_1 )
    | ( zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B_1 ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) )
      | ~ ( zip_tseitin_3 @ X39 @ X40 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('59',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('60',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X14 @ X15 @ X16 ) @ ( k1_zfmisc_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('61',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('63',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X22 @ X20 )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('64',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['61','64'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('66',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('67',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    $false ),
    inference(demod,[status(thm)],['4','67'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.LjsP2amyHk
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:02:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 7.22/7.42  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 7.22/7.42  % Solved by: fo/fo7.sh
% 7.22/7.42  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.22/7.42  % done 3573 iterations in 6.960s
% 7.22/7.42  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 7.22/7.42  % SZS output start Refutation
% 7.22/7.42  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 7.22/7.42  thf(sk_B_1_type, type, sk_B_1: $i).
% 7.22/7.42  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.22/7.42  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 7.22/7.42  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 7.22/7.42  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $o).
% 7.22/7.42  thf(sk_A_type, type, sk_A: $i).
% 7.22/7.42  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.22/7.42  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 7.22/7.42  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 7.22/7.42  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 7.22/7.42  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 7.22/7.42  thf(sk_D_1_type, type, sk_D_1: $i).
% 7.22/7.42  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 7.22/7.42  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 7.22/7.42  thf(sk_B_type, type, sk_B: $i > $i).
% 7.22/7.42  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 7.22/7.42  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 7.22/7.42  thf(sk_C_type, type, sk_C: $i).
% 7.22/7.42  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 7.22/7.42  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 7.22/7.42  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 7.22/7.42  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 7.22/7.42  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 7.22/7.42  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.22/7.42  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 7.22/7.42  thf(t191_funct_2, conjecture,
% 7.22/7.42    (![A:$i,B:$i]:
% 7.22/7.42     ( ( ~( v1_xboole_0 @ B ) ) =>
% 7.22/7.42       ( ![C:$i]:
% 7.22/7.42         ( ( ~( v1_xboole_0 @ C ) ) =>
% 7.22/7.42           ( ![D:$i]:
% 7.22/7.42             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 7.22/7.42                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 7.22/7.42               ( ( ![E:$i]:
% 7.22/7.42                   ( ( m1_subset_1 @ E @ B ) =>
% 7.22/7.42                     ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 7.22/7.42                 ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ))).
% 7.22/7.42  thf(zf_stmt_0, negated_conjecture,
% 7.22/7.42    (~( ![A:$i,B:$i]:
% 7.22/7.42        ( ( ~( v1_xboole_0 @ B ) ) =>
% 7.22/7.42          ( ![C:$i]:
% 7.22/7.42            ( ( ~( v1_xboole_0 @ C ) ) =>
% 7.22/7.42              ( ![D:$i]:
% 7.22/7.42                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 7.22/7.42                    ( m1_subset_1 @
% 7.22/7.42                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 7.22/7.42                  ( ( ![E:$i]:
% 7.22/7.42                      ( ( m1_subset_1 @ E @ B ) =>
% 7.22/7.42                        ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 7.22/7.42                    ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ) )),
% 7.22/7.42    inference('cnf.neg', [status(esa)], [t191_funct_2])).
% 7.22/7.42  thf('0', plain,
% 7.22/7.42      (~ (r1_tarski @ (k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1) @ sk_A)),
% 7.22/7.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.22/7.42  thf('1', plain,
% 7.22/7.42      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 7.22/7.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.22/7.42  thf(redefinition_k2_relset_1, axiom,
% 7.22/7.42    (![A:$i,B:$i,C:$i]:
% 7.22/7.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.22/7.42       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 7.22/7.42  thf('2', plain,
% 7.22/7.42      (![X20 : $i, X21 : $i, X22 : $i]:
% 7.22/7.42         (((k2_relset_1 @ X21 @ X22 @ X20) = (k2_relat_1 @ X20))
% 7.22/7.42          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 7.22/7.42      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 7.22/7.42  thf('3', plain,
% 7.22/7.42      (((k2_relset_1 @ sk_B_1 @ sk_C @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 7.22/7.42      inference('sup-', [status(thm)], ['1', '2'])).
% 7.22/7.42  thf('4', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 7.22/7.42      inference('demod', [status(thm)], ['0', '3'])).
% 7.22/7.42  thf(t5_funct_2, axiom,
% 7.22/7.42    (![A:$i,B:$i,C:$i]:
% 7.22/7.42     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 7.22/7.42       ( ( ( ![D:$i]:
% 7.22/7.42             ( ( r2_hidden @ D @ A ) =>
% 7.22/7.42               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 7.22/7.42           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 7.22/7.42         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 7.22/7.42           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 7.22/7.42  thf(zf_stmt_1, axiom,
% 7.22/7.42    (![D:$i,C:$i,B:$i,A:$i]:
% 7.22/7.42     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 7.22/7.42       ( zip_tseitin_2 @ D @ C @ B @ A ) ))).
% 7.22/7.42  thf('5', plain,
% 7.22/7.42      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 7.22/7.42         ((zip_tseitin_2 @ X35 @ X36 @ X37 @ X38) | (r2_hidden @ X35 @ X38))),
% 7.22/7.42      inference('cnf', [status(esa)], [zf_stmt_1])).
% 7.22/7.42  thf(t1_subset, axiom,
% 7.22/7.42    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 7.22/7.42  thf('6', plain,
% 7.22/7.42      (![X4 : $i, X5 : $i]: ((m1_subset_1 @ X4 @ X5) | ~ (r2_hidden @ X4 @ X5))),
% 7.22/7.42      inference('cnf', [status(esa)], [t1_subset])).
% 7.22/7.42  thf('7', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 7.22/7.42         ((zip_tseitin_2 @ X1 @ X3 @ X2 @ X0) | (m1_subset_1 @ X1 @ X0))),
% 7.22/7.42      inference('sup-', [status(thm)], ['5', '6'])).
% 7.22/7.42  thf('8', plain, ((v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C)),
% 7.22/7.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.22/7.42  thf(d1_funct_2, axiom,
% 7.22/7.42    (![A:$i,B:$i,C:$i]:
% 7.22/7.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.22/7.42       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 7.22/7.42           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 7.22/7.42             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 7.22/7.42         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 7.22/7.42           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 7.22/7.42             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 7.22/7.42  thf(zf_stmt_2, axiom,
% 7.22/7.42    (![C:$i,B:$i,A:$i]:
% 7.22/7.42     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 7.22/7.42       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 7.22/7.42  thf('9', plain,
% 7.22/7.42      (![X25 : $i, X26 : $i, X27 : $i]:
% 7.22/7.42         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 7.22/7.42          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 7.22/7.42          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 7.22/7.42      inference('cnf', [status(esa)], [zf_stmt_2])).
% 7.22/7.42  thf('10', plain,
% 7.22/7.42      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1)
% 7.22/7.42        | ((sk_B_1) = (k1_relset_1 @ sk_B_1 @ sk_C @ sk_D_1)))),
% 7.22/7.42      inference('sup-', [status(thm)], ['8', '9'])).
% 7.22/7.42  thf('11', plain,
% 7.22/7.42      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 7.22/7.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.22/7.42  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 7.22/7.42  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 7.22/7.42  thf(zf_stmt_5, axiom,
% 7.22/7.42    (![B:$i,A:$i]:
% 7.22/7.42     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 7.22/7.42       ( zip_tseitin_0 @ B @ A ) ))).
% 7.22/7.42  thf(zf_stmt_6, axiom,
% 7.22/7.42    (![A:$i,B:$i,C:$i]:
% 7.22/7.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.22/7.42       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 7.22/7.42         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 7.22/7.42           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 7.22/7.42             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 7.22/7.42  thf('12', plain,
% 7.22/7.42      (![X28 : $i, X29 : $i, X30 : $i]:
% 7.22/7.42         (~ (zip_tseitin_0 @ X28 @ X29)
% 7.22/7.42          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 7.22/7.42          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 7.22/7.42      inference('cnf', [status(esa)], [zf_stmt_6])).
% 7.22/7.42  thf('13', plain,
% 7.22/7.42      (((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1)
% 7.22/7.42        | ~ (zip_tseitin_0 @ sk_C @ sk_B_1))),
% 7.22/7.42      inference('sup-', [status(thm)], ['11', '12'])).
% 7.22/7.42  thf('14', plain,
% 7.22/7.42      (![X23 : $i, X24 : $i]:
% 7.22/7.42         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 7.22/7.42      inference('cnf', [status(esa)], [zf_stmt_5])).
% 7.22/7.42  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 7.22/7.42  thf('15', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 7.22/7.42      inference('cnf', [status(esa)], [t2_xboole_1])).
% 7.22/7.42  thf('16', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.22/7.42         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 7.22/7.42      inference('sup+', [status(thm)], ['14', '15'])).
% 7.22/7.42  thf(d1_xboole_0, axiom,
% 7.22/7.42    (![A:$i]:
% 7.22/7.42     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 7.22/7.42  thf('17', plain,
% 7.22/7.42      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 7.22/7.42      inference('cnf', [status(esa)], [d1_xboole_0])).
% 7.22/7.42  thf(t7_ordinal1, axiom,
% 7.22/7.42    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 7.22/7.42  thf('18', plain,
% 7.22/7.42      (![X9 : $i, X10 : $i]:
% 7.22/7.42         (~ (r2_hidden @ X9 @ X10) | ~ (r1_tarski @ X10 @ X9))),
% 7.22/7.42      inference('cnf', [status(esa)], [t7_ordinal1])).
% 7.22/7.42  thf('19', plain,
% 7.22/7.42      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 7.22/7.42      inference('sup-', [status(thm)], ['17', '18'])).
% 7.22/7.42  thf('20', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X0 @ X1) | (v1_xboole_0 @ X0))),
% 7.22/7.42      inference('sup-', [status(thm)], ['16', '19'])).
% 7.22/7.42  thf('21', plain, (~ (v1_xboole_0 @ sk_C)),
% 7.22/7.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.22/7.42  thf('22', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 7.22/7.42      inference('sup-', [status(thm)], ['20', '21'])).
% 7.22/7.42  thf('23', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B_1)),
% 7.22/7.42      inference('demod', [status(thm)], ['13', '22'])).
% 7.22/7.42  thf('24', plain,
% 7.22/7.42      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 7.22/7.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.22/7.42  thf(redefinition_k1_relset_1, axiom,
% 7.22/7.42    (![A:$i,B:$i,C:$i]:
% 7.22/7.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.22/7.42       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 7.22/7.42  thf('25', plain,
% 7.22/7.42      (![X17 : $i, X18 : $i, X19 : $i]:
% 7.22/7.42         (((k1_relset_1 @ X18 @ X19 @ X17) = (k1_relat_1 @ X17))
% 7.22/7.42          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 7.22/7.42      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 7.22/7.42  thf('26', plain,
% 7.22/7.42      (((k1_relset_1 @ sk_B_1 @ sk_C @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 7.22/7.42      inference('sup-', [status(thm)], ['24', '25'])).
% 7.22/7.42  thf('27', plain, (((sk_B_1) = (k1_relat_1 @ sk_D_1))),
% 7.22/7.42      inference('demod', [status(thm)], ['10', '23', '26'])).
% 7.22/7.42  thf(zf_stmt_7, type, zip_tseitin_3 : $i > $i > $i > $o).
% 7.22/7.42  thf(zf_stmt_8, axiom,
% 7.22/7.42    (![C:$i,B:$i,A:$i]:
% 7.22/7.42     ( ( zip_tseitin_3 @ C @ B @ A ) =>
% 7.22/7.42       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 7.22/7.42         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 7.22/7.42  thf(zf_stmt_9, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 7.22/7.42  thf(zf_stmt_10, axiom,
% 7.22/7.42    (![A:$i,B:$i,C:$i]:
% 7.22/7.42     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 7.22/7.42       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 7.22/7.42           ( ![D:$i]: ( zip_tseitin_2 @ D @ C @ B @ A ) ) ) =>
% 7.22/7.42         ( zip_tseitin_3 @ C @ B @ A ) ) ))).
% 7.22/7.42  thf('28', plain,
% 7.22/7.42      (![X42 : $i, X43 : $i, X44 : $i]:
% 7.22/7.42         (((k1_relat_1 @ X43) != (X42))
% 7.22/7.42          | ~ (zip_tseitin_2 @ (sk_D @ X43 @ X44 @ X42) @ X43 @ X44 @ X42)
% 7.22/7.42          | (zip_tseitin_3 @ X43 @ X44 @ X42)
% 7.22/7.42          | ~ (v1_funct_1 @ X43)
% 7.22/7.42          | ~ (v1_relat_1 @ X43))),
% 7.22/7.42      inference('cnf', [status(esa)], [zf_stmt_10])).
% 7.22/7.42  thf('29', plain,
% 7.22/7.42      (![X43 : $i, X44 : $i]:
% 7.22/7.42         (~ (v1_relat_1 @ X43)
% 7.22/7.42          | ~ (v1_funct_1 @ X43)
% 7.22/7.42          | (zip_tseitin_3 @ X43 @ X44 @ (k1_relat_1 @ X43))
% 7.22/7.42          | ~ (zip_tseitin_2 @ (sk_D @ X43 @ X44 @ (k1_relat_1 @ X43)) @ X43 @ 
% 7.22/7.42               X44 @ (k1_relat_1 @ X43)))),
% 7.22/7.42      inference('simplify', [status(thm)], ['28'])).
% 7.22/7.42  thf('30', plain,
% 7.22/7.42      (![X0 : $i]:
% 7.22/7.42         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B_1) @ sk_D_1 @ X0 @ 
% 7.22/7.42             (k1_relat_1 @ sk_D_1))
% 7.22/7.42          | (zip_tseitin_3 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 7.22/7.42          | ~ (v1_funct_1 @ sk_D_1)
% 7.22/7.42          | ~ (v1_relat_1 @ sk_D_1))),
% 7.22/7.42      inference('sup-', [status(thm)], ['27', '29'])).
% 7.22/7.42  thf('31', plain, (((sk_B_1) = (k1_relat_1 @ sk_D_1))),
% 7.22/7.42      inference('demod', [status(thm)], ['10', '23', '26'])).
% 7.22/7.42  thf('32', plain, (((sk_B_1) = (k1_relat_1 @ sk_D_1))),
% 7.22/7.42      inference('demod', [status(thm)], ['10', '23', '26'])).
% 7.22/7.42  thf('33', plain, ((v1_funct_1 @ sk_D_1)),
% 7.22/7.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.22/7.42  thf('34', plain,
% 7.22/7.42      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 7.22/7.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.22/7.42  thf(cc1_relset_1, axiom,
% 7.22/7.42    (![A:$i,B:$i,C:$i]:
% 7.22/7.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.22/7.42       ( v1_relat_1 @ C ) ))).
% 7.22/7.42  thf('35', plain,
% 7.22/7.42      (![X11 : $i, X12 : $i, X13 : $i]:
% 7.22/7.42         ((v1_relat_1 @ X11)
% 7.22/7.42          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 7.22/7.42      inference('cnf', [status(esa)], [cc1_relset_1])).
% 7.22/7.42  thf('36', plain, ((v1_relat_1 @ sk_D_1)),
% 7.22/7.42      inference('sup-', [status(thm)], ['34', '35'])).
% 7.22/7.42  thf('37', plain,
% 7.22/7.42      (![X0 : $i]:
% 7.22/7.42         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B_1) @ sk_D_1 @ X0 @ 
% 7.22/7.42             sk_B_1)
% 7.22/7.42          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1))),
% 7.22/7.42      inference('demod', [status(thm)], ['30', '31', '32', '33', '36'])).
% 7.22/7.42  thf('38', plain,
% 7.22/7.42      (![X0 : $i]:
% 7.22/7.42         ((m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B_1) @ sk_B_1)
% 7.22/7.42          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1))),
% 7.22/7.42      inference('sup-', [status(thm)], ['7', '37'])).
% 7.22/7.42  thf('39', plain,
% 7.22/7.42      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C)))),
% 7.22/7.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.22/7.42  thf(redefinition_k3_funct_2, axiom,
% 7.22/7.42    (![A:$i,B:$i,C:$i,D:$i]:
% 7.22/7.42     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 7.22/7.42         ( v1_funct_2 @ C @ A @ B ) & 
% 7.22/7.42         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 7.22/7.42         ( m1_subset_1 @ D @ A ) ) =>
% 7.22/7.42       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 7.22/7.42  thf('40', plain,
% 7.22/7.42      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 7.22/7.42         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 7.22/7.42          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 7.22/7.42          | ~ (v1_funct_1 @ X31)
% 7.22/7.42          | (v1_xboole_0 @ X32)
% 7.22/7.42          | ~ (m1_subset_1 @ X34 @ X32)
% 7.22/7.42          | ((k3_funct_2 @ X32 @ X33 @ X31 @ X34) = (k1_funct_1 @ X31 @ X34)))),
% 7.22/7.42      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 7.22/7.42  thf('41', plain,
% 7.22/7.42      (![X0 : $i]:
% 7.22/7.42         (((k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_1 @ X0)
% 7.22/7.42            = (k1_funct_1 @ sk_D_1 @ X0))
% 7.22/7.42          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 7.22/7.42          | (v1_xboole_0 @ sk_B_1)
% 7.22/7.42          | ~ (v1_funct_1 @ sk_D_1)
% 7.22/7.42          | ~ (v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C))),
% 7.22/7.42      inference('sup-', [status(thm)], ['39', '40'])).
% 7.22/7.42  thf('42', plain, ((v1_funct_1 @ sk_D_1)),
% 7.22/7.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.22/7.42  thf('43', plain, ((v1_funct_2 @ sk_D_1 @ sk_B_1 @ sk_C)),
% 7.22/7.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.22/7.42  thf('44', plain,
% 7.22/7.42      (![X0 : $i]:
% 7.22/7.42         (((k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_1 @ X0)
% 7.22/7.42            = (k1_funct_1 @ sk_D_1 @ X0))
% 7.22/7.42          | ~ (m1_subset_1 @ X0 @ sk_B_1)
% 7.22/7.42          | (v1_xboole_0 @ sk_B_1))),
% 7.22/7.42      inference('demod', [status(thm)], ['41', '42', '43'])).
% 7.22/7.42  thf('45', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 7.22/7.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.22/7.42  thf('46', plain,
% 7.22/7.42      (![X0 : $i]:
% 7.22/7.42         (~ (m1_subset_1 @ X0 @ sk_B_1)
% 7.22/7.42          | ((k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_1 @ X0)
% 7.22/7.42              = (k1_funct_1 @ sk_D_1 @ X0)))),
% 7.22/7.42      inference('clc', [status(thm)], ['44', '45'])).
% 7.22/7.42  thf('47', plain,
% 7.22/7.42      (![X0 : $i]:
% 7.22/7.42         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1)
% 7.22/7.42          | ((k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_1 @ 
% 7.22/7.42              (sk_D @ sk_D_1 @ X0 @ sk_B_1))
% 7.22/7.42              = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B_1))))),
% 7.22/7.42      inference('sup-', [status(thm)], ['38', '46'])).
% 7.22/7.42  thf('48', plain,
% 7.22/7.42      (![X0 : $i]:
% 7.22/7.42         ((m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B_1) @ sk_B_1)
% 7.22/7.42          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1))),
% 7.22/7.42      inference('sup-', [status(thm)], ['7', '37'])).
% 7.22/7.42  thf('49', plain,
% 7.22/7.42      (![X45 : $i]:
% 7.22/7.42         ((r2_hidden @ (k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_1 @ X45) @ sk_A)
% 7.22/7.42          | ~ (m1_subset_1 @ X45 @ sk_B_1))),
% 7.22/7.42      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.22/7.42  thf('50', plain,
% 7.22/7.42      (![X0 : $i]:
% 7.22/7.42         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1)
% 7.22/7.42          | (r2_hidden @ 
% 7.22/7.42             (k3_funct_2 @ sk_B_1 @ sk_C @ sk_D_1 @ 
% 7.22/7.42              (sk_D @ sk_D_1 @ X0 @ sk_B_1)) @ 
% 7.22/7.42             sk_A))),
% 7.22/7.42      inference('sup-', [status(thm)], ['48', '49'])).
% 7.22/7.42  thf('51', plain,
% 7.22/7.42      (![X0 : $i]:
% 7.22/7.42         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B_1)) @ 
% 7.22/7.42           sk_A)
% 7.22/7.42          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1)
% 7.22/7.42          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1))),
% 7.22/7.42      inference('sup+', [status(thm)], ['47', '50'])).
% 7.22/7.42  thf('52', plain,
% 7.22/7.42      (![X0 : $i]:
% 7.22/7.42         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1)
% 7.22/7.42          | (r2_hidden @ 
% 7.22/7.42             (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B_1)) @ sk_A))),
% 7.22/7.42      inference('simplify', [status(thm)], ['51'])).
% 7.22/7.42  thf('53', plain,
% 7.22/7.42      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 7.22/7.42         ((zip_tseitin_2 @ X35 @ X36 @ X37 @ X38)
% 7.22/7.42          | ~ (r2_hidden @ (k1_funct_1 @ X36 @ X35) @ X37))),
% 7.22/7.42      inference('cnf', [status(esa)], [zf_stmt_1])).
% 7.22/7.42  thf('54', plain,
% 7.22/7.42      (![X0 : $i, X1 : $i]:
% 7.22/7.42         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1)
% 7.22/7.42          | (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B_1) @ sk_D_1 @ sk_A @ X1))),
% 7.22/7.42      inference('sup-', [status(thm)], ['52', '53'])).
% 7.22/7.42  thf('55', plain,
% 7.22/7.42      (![X0 : $i]:
% 7.22/7.42         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B_1) @ sk_D_1 @ X0 @ 
% 7.22/7.42             sk_B_1)
% 7.22/7.42          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B_1))),
% 7.22/7.42      inference('demod', [status(thm)], ['30', '31', '32', '33', '36'])).
% 7.22/7.42  thf('56', plain,
% 7.22/7.42      (((zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B_1)
% 7.22/7.42        | (zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B_1))),
% 7.22/7.42      inference('sup-', [status(thm)], ['54', '55'])).
% 7.22/7.42  thf('57', plain, ((zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B_1)),
% 7.22/7.42      inference('simplify', [status(thm)], ['56'])).
% 7.22/7.42  thf('58', plain,
% 7.22/7.42      (![X39 : $i, X40 : $i, X41 : $i]:
% 7.22/7.42         ((m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 7.22/7.42          | ~ (zip_tseitin_3 @ X39 @ X40 @ X41))),
% 7.22/7.42      inference('cnf', [status(esa)], [zf_stmt_8])).
% 7.22/7.42  thf('59', plain,
% 7.22/7.42      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 7.22/7.42      inference('sup-', [status(thm)], ['57', '58'])).
% 7.22/7.42  thf(dt_k2_relset_1, axiom,
% 7.22/7.42    (![A:$i,B:$i,C:$i]:
% 7.22/7.42     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.22/7.42       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 7.22/7.42  thf('60', plain,
% 7.22/7.42      (![X14 : $i, X15 : $i, X16 : $i]:
% 7.22/7.42         ((m1_subset_1 @ (k2_relset_1 @ X14 @ X15 @ X16) @ (k1_zfmisc_1 @ X15))
% 7.22/7.42          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 7.22/7.42      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 7.22/7.42  thf('61', plain,
% 7.22/7.42      ((m1_subset_1 @ (k2_relset_1 @ sk_B_1 @ sk_A @ sk_D_1) @ 
% 7.22/7.42        (k1_zfmisc_1 @ sk_A))),
% 7.22/7.42      inference('sup-', [status(thm)], ['59', '60'])).
% 7.22/7.42  thf('62', plain,
% 7.22/7.42      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 7.22/7.42      inference('sup-', [status(thm)], ['57', '58'])).
% 7.22/7.42  thf('63', plain,
% 7.22/7.42      (![X20 : $i, X21 : $i, X22 : $i]:
% 7.22/7.42         (((k2_relset_1 @ X21 @ X22 @ X20) = (k2_relat_1 @ X20))
% 7.22/7.42          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 7.22/7.42      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 7.22/7.42  thf('64', plain,
% 7.22/7.42      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 7.22/7.42      inference('sup-', [status(thm)], ['62', '63'])).
% 7.22/7.42  thf('65', plain,
% 7.22/7.42      ((m1_subset_1 @ (k2_relat_1 @ sk_D_1) @ (k1_zfmisc_1 @ sk_A))),
% 7.22/7.42      inference('demod', [status(thm)], ['61', '64'])).
% 7.22/7.42  thf(t3_subset, axiom,
% 7.22/7.42    (![A:$i,B:$i]:
% 7.22/7.42     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 7.22/7.42  thf('66', plain,
% 7.22/7.42      (![X6 : $i, X7 : $i]:
% 7.22/7.42         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 7.22/7.42      inference('cnf', [status(esa)], [t3_subset])).
% 7.22/7.42  thf('67', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 7.22/7.42      inference('sup-', [status(thm)], ['65', '66'])).
% 7.22/7.42  thf('68', plain, ($false), inference('demod', [status(thm)], ['4', '67'])).
% 7.22/7.42  
% 7.22/7.42  % SZS output end Refutation
% 7.22/7.42  
% 7.27/7.43  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
