%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a1kcb73PFl

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:25 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 782 expanded)
%              Number of leaves         :   47 ( 253 expanded)
%              Depth                    :   20
%              Number of atoms          :  895 (11042 expanded)
%              Number of equality atoms :   36 ( 289 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( zip_tseitin_2 @ X30 @ X31 @ X32 @ X33 )
      | ( r2_hidden @ X30 @ X33 ) ) ),
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
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_2 @ X22 @ X20 @ X21 )
      | ( X20
        = ( k1_relset_1 @ X20 @ X21 @ X22 ) )
      | ~ ( zip_tseitin_1 @ X22 @ X21 @ X20 ) ) ),
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
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( ( k1_relset_1 @ X13 @ X14 @ X12 )
        = ( k1_relat_1 @ X12 ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
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
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( zip_tseitin_0 @ X23 @ X24 )
      | ( zip_tseitin_1 @ X25 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('15',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X18: $i,X19: $i] :
      ( ( zip_tseitin_0 @ X18 @ X19 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('17',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['15','20'])).

thf('22',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','21'])).

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

thf('23',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k1_relat_1 @ X38 )
       != X37 )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X38 @ X39 @ X37 ) @ X38 @ X39 @ X37 )
      | ( zip_tseitin_3 @ X38 @ X39 @ X37 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_relat_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('24',plain,(
    ! [X38: $i,X39: $i] :
      ( ~ ( v1_relat_1 @ X38 )
      | ~ ( v1_funct_1 @ X38 )
      | ( zip_tseitin_3 @ X38 @ X39 @ ( k1_relat_1 @ X38 ) )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X38 @ X39 @ ( k1_relat_1 @ X38 ) ) @ X38 @ X39 @ ( k1_relat_1 @ X38 ) ) ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['22','24'])).

thf('26',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','21'])).

thf('27',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['12','21'])).

thf('28',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('30',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) )
      | ( v1_relat_1 @ X5 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('32',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('33',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26','27','28','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','34'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
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

thf('39',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X27 @ X28 )
      | ~ ( v1_funct_1 @ X26 )
      | ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X29 @ X27 )
      | ( ( k3_funct_2 @ X27 @ X28 @ X26 @ X29 )
        = ( k1_funct_1 @ X26 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) )
        = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['37','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('48',plain,(
    ! [X40: $i] :
      ( ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X40 ) @ sk_A )
      | ~ ( m1_subset_1 @ X40 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) @ sk_A )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['46','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( zip_tseitin_2 @ X30 @ X31 @ X32 @ X33 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X31 @ X30 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['25','26','27','28','33'])).

thf('55',plain,
    ( ( zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B )
    | ( zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ~ ( zip_tseitin_3 @ X34 @ X35 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('58',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('59',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X9 @ X10 @ X11 ) @ ( k1_zfmisc_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('60',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('62',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('63',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['60','63'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('65',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('66',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    $false ),
    inference(demod,[status(thm)],['4','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.a1kcb73PFl
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:07:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.58  % Solved by: fo/fo7.sh
% 0.20/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.58  % done 126 iterations in 0.125s
% 0.20/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.58  % SZS output start Refutation
% 0.20/0.58  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.20/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.58  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.20/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.58  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.20/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.58  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.58  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.58  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $o).
% 0.20/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.58  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.20/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.20/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.58  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 0.20/0.58  thf(t191_funct_2, conjecture,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.58       ( ![C:$i]:
% 0.20/0.58         ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.20/0.58           ( ![D:$i]:
% 0.20/0.58             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.20/0.58                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.20/0.58               ( ( ![E:$i]:
% 0.20/0.58                   ( ( m1_subset_1 @ E @ B ) =>
% 0.20/0.58                     ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 0.20/0.58                 ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ))).
% 0.20/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.58    (~( ![A:$i,B:$i]:
% 0.20/0.58        ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.58          ( ![C:$i]:
% 0.20/0.58            ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.20/0.58              ( ![D:$i]:
% 0.20/0.58                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.20/0.58                    ( m1_subset_1 @
% 0.20/0.58                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.20/0.58                  ( ( ![E:$i]:
% 0.20/0.58                      ( ( m1_subset_1 @ E @ B ) =>
% 0.20/0.58                        ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 0.20/0.58                    ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ) )),
% 0.20/0.58    inference('cnf.neg', [status(esa)], [t191_funct_2])).
% 0.20/0.58  thf('0', plain,
% 0.20/0.58      (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D_1) @ sk_A)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('1', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.58       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.58  thf('2', plain,
% 0.20/0.58      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.58         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 0.20/0.58          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.20/0.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.58  thf('3', plain,
% 0.20/0.58      (((k2_relset_1 @ sk_B @ sk_C @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.20/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.58  thf('4', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 0.20/0.58      inference('demod', [status(thm)], ['0', '3'])).
% 0.20/0.58  thf(t5_funct_2, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 0.20/0.58       ( ( ( ![D:$i]:
% 0.20/0.58             ( ( r2_hidden @ D @ A ) =>
% 0.20/0.58               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 0.20/0.58           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.20/0.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.58           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 0.20/0.58  thf(zf_stmt_1, axiom,
% 0.20/0.58    (![D:$i,C:$i,B:$i,A:$i]:
% 0.20/0.58     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 0.20/0.58       ( zip_tseitin_2 @ D @ C @ B @ A ) ))).
% 0.20/0.58  thf('5', plain,
% 0.20/0.58      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.58         ((zip_tseitin_2 @ X30 @ X31 @ X32 @ X33) | (r2_hidden @ X30 @ X33))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.58  thf('6', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_C)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(d1_funct_2, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.58       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.58           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.20/0.58             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.20/0.58         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.58           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.20/0.58             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.20/0.58  thf(zf_stmt_2, axiom,
% 0.20/0.58    (![C:$i,B:$i,A:$i]:
% 0.20/0.58     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.20/0.58       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.20/0.58  thf('7', plain,
% 0.20/0.58      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.58         (~ (v1_funct_2 @ X22 @ X20 @ X21)
% 0.20/0.58          | ((X20) = (k1_relset_1 @ X20 @ X21 @ X22))
% 0.20/0.58          | ~ (zip_tseitin_1 @ X22 @ X21 @ X20))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.20/0.58  thf('8', plain,
% 0.20/0.58      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)
% 0.20/0.58        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_D_1)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.58  thf('9', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.58       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.58  thf('10', plain,
% 0.20/0.58      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.58         (((k1_relset_1 @ X13 @ X14 @ X12) = (k1_relat_1 @ X12))
% 0.20/0.58          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.20/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.58  thf('11', plain,
% 0.20/0.58      (((k1_relset_1 @ sk_B @ sk_C @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.20/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.58  thf('12', plain,
% 0.20/0.58      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)
% 0.20/0.58        | ((sk_B) = (k1_relat_1 @ sk_D_1)))),
% 0.20/0.58      inference('demod', [status(thm)], ['8', '11'])).
% 0.20/0.58  thf('13', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.20/0.58  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.20/0.58  thf(zf_stmt_5, axiom,
% 0.20/0.58    (![B:$i,A:$i]:
% 0.20/0.58     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.20/0.58       ( zip_tseitin_0 @ B @ A ) ))).
% 0.20/0.58  thf(zf_stmt_6, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.58       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.20/0.58         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.20/0.58           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.20/0.58             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.20/0.58  thf('14', plain,
% 0.20/0.58      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.20/0.58         (~ (zip_tseitin_0 @ X23 @ X24)
% 0.20/0.58          | (zip_tseitin_1 @ X25 @ X23 @ X24)
% 0.20/0.58          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23))))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.20/0.58  thf('15', plain,
% 0.20/0.58      (((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)
% 0.20/0.58        | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 0.20/0.58      inference('sup-', [status(thm)], ['13', '14'])).
% 0.20/0.58  thf('16', plain,
% 0.20/0.58      (![X18 : $i, X19 : $i]:
% 0.20/0.58         ((zip_tseitin_0 @ X18 @ X19) | ((X18) = (k1_xboole_0)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.20/0.58  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.20/0.58  thf('17', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.20/0.58  thf('18', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.20/0.58      inference('sup+', [status(thm)], ['16', '17'])).
% 0.20/0.58  thf('19', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('20', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 0.20/0.58      inference('sup-', [status(thm)], ['18', '19'])).
% 0.20/0.58  thf('21', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)),
% 0.20/0.58      inference('demod', [status(thm)], ['15', '20'])).
% 0.20/0.58  thf('22', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 0.20/0.58      inference('demod', [status(thm)], ['12', '21'])).
% 0.20/0.58  thf(zf_stmt_7, type, zip_tseitin_3 : $i > $i > $i > $o).
% 0.20/0.58  thf(zf_stmt_8, axiom,
% 0.20/0.58    (![C:$i,B:$i,A:$i]:
% 0.20/0.58     ( ( zip_tseitin_3 @ C @ B @ A ) =>
% 0.20/0.58       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.20/0.58  thf(zf_stmt_9, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 0.20/0.58  thf(zf_stmt_10, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.20/0.58       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.20/0.58           ( ![D:$i]: ( zip_tseitin_2 @ D @ C @ B @ A ) ) ) =>
% 0.20/0.58         ( zip_tseitin_3 @ C @ B @ A ) ) ))).
% 0.20/0.58  thf('23', plain,
% 0.20/0.58      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.20/0.58         (((k1_relat_1 @ X38) != (X37))
% 0.20/0.58          | ~ (zip_tseitin_2 @ (sk_D @ X38 @ X39 @ X37) @ X38 @ X39 @ X37)
% 0.20/0.58          | (zip_tseitin_3 @ X38 @ X39 @ X37)
% 0.20/0.58          | ~ (v1_funct_1 @ X38)
% 0.20/0.58          | ~ (v1_relat_1 @ X38))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_10])).
% 0.20/0.58  thf('24', plain,
% 0.20/0.58      (![X38 : $i, X39 : $i]:
% 0.20/0.58         (~ (v1_relat_1 @ X38)
% 0.20/0.58          | ~ (v1_funct_1 @ X38)
% 0.20/0.58          | (zip_tseitin_3 @ X38 @ X39 @ (k1_relat_1 @ X38))
% 0.20/0.58          | ~ (zip_tseitin_2 @ (sk_D @ X38 @ X39 @ (k1_relat_1 @ X38)) @ X38 @ 
% 0.20/0.58               X39 @ (k1_relat_1 @ X38)))),
% 0.20/0.58      inference('simplify', [status(thm)], ['23'])).
% 0.20/0.58  thf('25', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ 
% 0.20/0.58             (k1_relat_1 @ sk_D_1))
% 0.20/0.58          | (zip_tseitin_3 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.20/0.58          | ~ (v1_funct_1 @ sk_D_1)
% 0.20/0.58          | ~ (v1_relat_1 @ sk_D_1))),
% 0.20/0.58      inference('sup-', [status(thm)], ['22', '24'])).
% 0.20/0.58  thf('26', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 0.20/0.58      inference('demod', [status(thm)], ['12', '21'])).
% 0.20/0.58  thf('27', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 0.20/0.58      inference('demod', [status(thm)], ['12', '21'])).
% 0.20/0.58  thf('28', plain, ((v1_funct_1 @ sk_D_1)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('29', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(cc2_relat_1, axiom,
% 0.20/0.58    (![A:$i]:
% 0.20/0.58     ( ( v1_relat_1 @ A ) =>
% 0.20/0.58       ( ![B:$i]:
% 0.20/0.58         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.58  thf('30', plain,
% 0.20/0.58      (![X5 : $i, X6 : $i]:
% 0.20/0.58         (~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6))
% 0.20/0.58          | (v1_relat_1 @ X5)
% 0.20/0.58          | ~ (v1_relat_1 @ X6))),
% 0.20/0.58      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.58  thf('31', plain,
% 0.20/0.58      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)) | (v1_relat_1 @ sk_D_1))),
% 0.20/0.58      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.58  thf(fc6_relat_1, axiom,
% 0.20/0.58    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.58  thf('32', plain,
% 0.20/0.58      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.20/0.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.58  thf('33', plain, ((v1_relat_1 @ sk_D_1)),
% 0.20/0.58      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.58  thf('34', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ sk_B)
% 0.20/0.58          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 0.20/0.58      inference('demod', [status(thm)], ['25', '26', '27', '28', '33'])).
% 0.20/0.58  thf('35', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((r2_hidden @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B)
% 0.20/0.58          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 0.20/0.58      inference('sup-', [status(thm)], ['5', '34'])).
% 0.20/0.58  thf(t1_subset, axiom,
% 0.20/0.58    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.20/0.58  thf('36', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.20/0.58      inference('cnf', [status(esa)], [t1_subset])).
% 0.20/0.58  thf('37', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.20/0.58          | (m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B))),
% 0.20/0.58      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.58  thf('38', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf(redefinition_k3_funct_2, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.58     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.20/0.58         ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.58         ( m1_subset_1 @ D @ A ) ) =>
% 0.20/0.58       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.20/0.58  thf('39', plain,
% 0.20/0.58      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.58         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.20/0.58          | ~ (v1_funct_2 @ X26 @ X27 @ X28)
% 0.20/0.58          | ~ (v1_funct_1 @ X26)
% 0.20/0.58          | (v1_xboole_0 @ X27)
% 0.20/0.58          | ~ (m1_subset_1 @ X29 @ X27)
% 0.20/0.58          | ((k3_funct_2 @ X27 @ X28 @ X26 @ X29) = (k1_funct_1 @ X26 @ X29)))),
% 0.20/0.58      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.20/0.58  thf('40', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 0.20/0.58            = (k1_funct_1 @ sk_D_1 @ X0))
% 0.20/0.58          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.20/0.58          | (v1_xboole_0 @ sk_B)
% 0.20/0.58          | ~ (v1_funct_1 @ sk_D_1)
% 0.20/0.58          | ~ (v1_funct_2 @ sk_D_1 @ sk_B @ sk_C))),
% 0.20/0.58      inference('sup-', [status(thm)], ['38', '39'])).
% 0.20/0.58  thf('41', plain, ((v1_funct_1 @ sk_D_1)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('42', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_C)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('43', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 0.20/0.58            = (k1_funct_1 @ sk_D_1 @ X0))
% 0.20/0.58          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.20/0.58          | (v1_xboole_0 @ sk_B))),
% 0.20/0.58      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.20/0.58  thf('44', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('45', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.20/0.58          | ((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 0.20/0.58              = (k1_funct_1 @ sk_D_1 @ X0)))),
% 0.20/0.58      inference('clc', [status(thm)], ['43', '44'])).
% 0.20/0.58  thf('46', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.20/0.58          | ((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B))
% 0.20/0.58              = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B))))),
% 0.20/0.58      inference('sup-', [status(thm)], ['37', '45'])).
% 0.20/0.58  thf('47', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.20/0.58          | (m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B))),
% 0.20/0.58      inference('sup-', [status(thm)], ['35', '36'])).
% 0.20/0.58  thf('48', plain,
% 0.20/0.58      (![X40 : $i]:
% 0.20/0.58         ((r2_hidden @ (k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X40) @ sk_A)
% 0.20/0.58          | ~ (m1_subset_1 @ X40 @ sk_B))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.58  thf('49', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.20/0.58          | (r2_hidden @ 
% 0.20/0.58             (k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 0.20/0.58             sk_A))),
% 0.20/0.58      inference('sup-', [status(thm)], ['47', '48'])).
% 0.20/0.58  thf('50', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 0.20/0.58           sk_A)
% 0.20/0.58          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.20/0.58          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 0.20/0.58      inference('sup+', [status(thm)], ['46', '49'])).
% 0.20/0.58  thf('51', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.20/0.58          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 0.20/0.58             sk_A))),
% 0.20/0.58      inference('simplify', [status(thm)], ['50'])).
% 0.20/0.58  thf('52', plain,
% 0.20/0.58      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.58         ((zip_tseitin_2 @ X30 @ X31 @ X32 @ X33)
% 0.20/0.58          | ~ (r2_hidden @ (k1_funct_1 @ X31 @ X30) @ X32))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.20/0.58  thf('53', plain,
% 0.20/0.58      (![X0 : $i, X1 : $i]:
% 0.20/0.58         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.20/0.58          | (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ sk_A @ X1))),
% 0.20/0.58      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.58  thf('54', plain,
% 0.20/0.58      (![X0 : $i]:
% 0.20/0.58         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ sk_B)
% 0.20/0.58          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 0.20/0.58      inference('demod', [status(thm)], ['25', '26', '27', '28', '33'])).
% 0.20/0.58  thf('55', plain,
% 0.20/0.58      (((zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B)
% 0.20/0.58        | (zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B))),
% 0.20/0.58      inference('sup-', [status(thm)], ['53', '54'])).
% 0.20/0.58  thf('56', plain, ((zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B)),
% 0.20/0.58      inference('simplify', [status(thm)], ['55'])).
% 0.20/0.58  thf('57', plain,
% 0.20/0.58      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.20/0.58         ((m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 0.20/0.58          | ~ (zip_tseitin_3 @ X34 @ X35 @ X36))),
% 0.20/0.58      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.20/0.58  thf('58', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.58  thf(dt_k2_relset_1, axiom,
% 0.20/0.58    (![A:$i,B:$i,C:$i]:
% 0.20/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.58       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.20/0.58  thf('59', plain,
% 0.20/0.58      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.20/0.58         ((m1_subset_1 @ (k2_relset_1 @ X9 @ X10 @ X11) @ (k1_zfmisc_1 @ X10))
% 0.20/0.58          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.20/0.58      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.20/0.58  thf('60', plain,
% 0.20/0.58      ((m1_subset_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_D_1) @ 
% 0.20/0.58        (k1_zfmisc_1 @ sk_A))),
% 0.20/0.58      inference('sup-', [status(thm)], ['58', '59'])).
% 0.20/0.58  thf('61', plain,
% 0.20/0.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.20/0.58      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.58  thf('62', plain,
% 0.20/0.58      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.20/0.58         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 0.20/0.58          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.20/0.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.58  thf('63', plain,
% 0.20/0.58      (((k2_relset_1 @ sk_B @ sk_A @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.20/0.58      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.58  thf('64', plain,
% 0.20/0.58      ((m1_subset_1 @ (k2_relat_1 @ sk_D_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.20/0.58      inference('demod', [status(thm)], ['60', '63'])).
% 0.20/0.58  thf(t3_subset, axiom,
% 0.20/0.58    (![A:$i,B:$i]:
% 0.20/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.58  thf('65', plain,
% 0.20/0.58      (![X2 : $i, X3 : $i]:
% 0.20/0.58         ((r1_tarski @ X2 @ X3) | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.20/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.58  thf('66', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 0.20/0.58      inference('sup-', [status(thm)], ['64', '65'])).
% 0.20/0.58  thf('67', plain, ($false), inference('demod', [status(thm)], ['4', '66'])).
% 0.20/0.58  
% 0.20/0.58  % SZS output end Refutation
% 0.20/0.58  
% 0.20/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
