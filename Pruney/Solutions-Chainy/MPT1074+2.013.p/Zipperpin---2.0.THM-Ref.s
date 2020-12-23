%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.idDAuj9DaM

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:24 EST 2020

% Result     : Theorem 0.40s
% Output     : Refutation 0.40s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 746 expanded)
%              Number of leaves         :   46 ( 247 expanded)
%              Depth                    :   20
%              Number of atoms          :  873 (10814 expanded)
%              Number of equality atoms :   35 ( 271 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

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
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( zip_tseitin_2 @ X29 @ X30 @ X31 @ X32 )
      | ( r2_hidden @ X29 @ X32 ) ) ),
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
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ( X19
        = ( k1_relset_1 @ X19 @ X20 @ X21 ) )
      | ~ ( zip_tseitin_1 @ X21 @ X20 @ X19 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
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

thf('10',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( zip_tseitin_0 @ X22 @ X23 )
      | ( zip_tseitin_1 @ X24 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('11',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( ( zip_tseitin_0 @ X17 @ X18 )
      | ( X17 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('13',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','13'])).

thf('15',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C @ X0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B ),
    inference(demod,[status(thm)],['11','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('19',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( ( k1_relset_1 @ X12 @ X13 @ X11 )
        = ( k1_relat_1 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('20',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['8','17','20'])).

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

thf('22',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k1_relat_1 @ X37 )
       != X36 )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X37 @ X38 @ X36 ) @ X37 @ X38 @ X36 )
      | ( zip_tseitin_3 @ X37 @ X38 @ X36 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('23',plain,(
    ! [X37: $i,X38: $i] :
      ( ~ ( v1_relat_1 @ X37 )
      | ~ ( v1_funct_1 @ X37 )
      | ( zip_tseitin_3 @ X37 @ X38 @ ( k1_relat_1 @ X37 ) )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X37 @ X38 @ ( k1_relat_1 @ X37 ) ) @ X37 @ X38 @ ( k1_relat_1 @ X37 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['21','23'])).

thf('25',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['8','17','20'])).

thf('26',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['8','17','20'])).

thf('27',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('29',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('30',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25','26','27','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','31'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
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

thf('36',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X25 @ X26 @ X27 )
      | ~ ( v1_funct_1 @ X25 )
      | ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X28 @ X26 )
      | ( ( k3_funct_2 @ X26 @ X27 @ X25 @ X28 )
        = ( k1_funct_1 @ X25 @ X28 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) )
        = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['34','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('45',plain,(
    ! [X39: $i] :
      ( ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X39 ) @ sk_A )
      | ~ ( m1_subset_1 @ X39 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) @ sk_A )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['47'])).

thf('49',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ( zip_tseitin_2 @ X29 @ X30 @ X31 @ X32 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X30 @ X29 ) @ X31 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25','26','27','30'])).

thf('52',plain,
    ( ( zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B )
    | ( zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( zip_tseitin_3 @ X33 @ X34 @ X35 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('55',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('56',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X8 @ X9 @ X10 ) @ ( k1_zfmisc_1 @ X9 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('57',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('59',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('60',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(demod,[status(thm)],['57','60'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('62',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r1_tarski @ X2 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('63',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    $false ),
    inference(demod,[status(thm)],['4','63'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.idDAuj9DaM
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:01:36 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.40/0.58  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.40/0.58  % Solved by: fo/fo7.sh
% 0.40/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.40/0.58  % done 126 iterations in 0.140s
% 0.40/0.58  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.40/0.58  % SZS output start Refutation
% 0.40/0.58  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.40/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.40/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.40/0.58  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $o).
% 0.40/0.58  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.40/0.58  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.40/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.40/0.58  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.40/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.40/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.40/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.40/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.40/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.40/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.40/0.58  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.40/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.40/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.40/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.40/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.40/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.40/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.40/0.58  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 0.40/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.40/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.40/0.58  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.40/0.58  thf(t191_funct_2, conjecture,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.40/0.58       ( ![C:$i]:
% 0.40/0.58         ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.40/0.58           ( ![D:$i]:
% 0.40/0.58             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.40/0.58                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.40/0.58               ( ( ![E:$i]:
% 0.40/0.58                   ( ( m1_subset_1 @ E @ B ) =>
% 0.40/0.58                     ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 0.40/0.58                 ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.40/0.58    (~( ![A:$i,B:$i]:
% 0.40/0.58        ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.40/0.58          ( ![C:$i]:
% 0.40/0.58            ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.40/0.58              ( ![D:$i]:
% 0.40/0.58                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.40/0.58                    ( m1_subset_1 @
% 0.40/0.58                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.40/0.58                  ( ( ![E:$i]:
% 0.40/0.58                      ( ( m1_subset_1 @ E @ B ) =>
% 0.40/0.58                        ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 0.40/0.58                    ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ) )),
% 0.40/0.58    inference('cnf.neg', [status(esa)], [t191_funct_2])).
% 0.40/0.58  thf('0', plain,
% 0.40/0.58      (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D_1) @ sk_A)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('1', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(redefinition_k2_relset_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.58       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.40/0.58  thf('2', plain,
% 0.40/0.58      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.40/0.58         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.40/0.58          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.40/0.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.40/0.58  thf('3', plain,
% 0.40/0.58      (((k2_relset_1 @ sk_B @ sk_C @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.40/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.40/0.58  thf('4', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 0.40/0.58      inference('demod', [status(thm)], ['0', '3'])).
% 0.40/0.58  thf(t5_funct_2, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 0.40/0.58       ( ( ( ![D:$i]:
% 0.40/0.58             ( ( r2_hidden @ D @ A ) =>
% 0.40/0.58               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 0.40/0.58           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.40/0.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.40/0.58           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_1, axiom,
% 0.40/0.58    (![D:$i,C:$i,B:$i,A:$i]:
% 0.40/0.58     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 0.40/0.58       ( zip_tseitin_2 @ D @ C @ B @ A ) ))).
% 0.40/0.58  thf('5', plain,
% 0.40/0.58      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.40/0.58         ((zip_tseitin_2 @ X29 @ X30 @ X31 @ X32) | (r2_hidden @ X29 @ X32))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.40/0.58  thf('6', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_C)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(d1_funct_2, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.58       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.40/0.58           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.40/0.58             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.40/0.58         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.40/0.58           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.40/0.58             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_2, axiom,
% 0.40/0.58    (![C:$i,B:$i,A:$i]:
% 0.40/0.58     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.40/0.58       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.40/0.58  thf('7', plain,
% 0.40/0.58      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.40/0.58         (~ (v1_funct_2 @ X21 @ X19 @ X20)
% 0.40/0.58          | ((X19) = (k1_relset_1 @ X19 @ X20 @ X21))
% 0.40/0.58          | ~ (zip_tseitin_1 @ X21 @ X20 @ X19))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.40/0.58  thf('8', plain,
% 0.40/0.58      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)
% 0.40/0.58        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_D_1)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.40/0.58  thf('9', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.40/0.58  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.40/0.58  thf(zf_stmt_5, axiom,
% 0.40/0.58    (![B:$i,A:$i]:
% 0.40/0.58     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.40/0.58       ( zip_tseitin_0 @ B @ A ) ))).
% 0.40/0.58  thf(zf_stmt_6, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.58       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.40/0.58         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.40/0.58           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.40/0.58             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.40/0.58  thf('10', plain,
% 0.40/0.58      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.40/0.58         (~ (zip_tseitin_0 @ X22 @ X23)
% 0.40/0.58          | (zip_tseitin_1 @ X24 @ X22 @ X23)
% 0.40/0.58          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X22))))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.40/0.58  thf('11', plain,
% 0.40/0.58      (((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)
% 0.40/0.58        | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.40/0.58  thf('12', plain,
% 0.40/0.58      (![X17 : $i, X18 : $i]:
% 0.40/0.58         ((zip_tseitin_0 @ X17 @ X18) | ((X17) = (k1_xboole_0)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.40/0.58  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.40/0.58  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.40/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.40/0.58  thf('14', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.40/0.58      inference('sup+', [status(thm)], ['12', '13'])).
% 0.40/0.58  thf('15', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('16', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 0.40/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.40/0.58  thf('17', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)),
% 0.40/0.58      inference('demod', [status(thm)], ['11', '16'])).
% 0.40/0.58  thf('18', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(redefinition_k1_relset_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.58       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.40/0.58  thf('19', plain,
% 0.40/0.58      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.40/0.58         (((k1_relset_1 @ X12 @ X13 @ X11) = (k1_relat_1 @ X11))
% 0.40/0.58          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.40/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.40/0.58  thf('20', plain,
% 0.40/0.58      (((k1_relset_1 @ sk_B @ sk_C @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.40/0.58      inference('sup-', [status(thm)], ['18', '19'])).
% 0.40/0.58  thf('21', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 0.40/0.58      inference('demod', [status(thm)], ['8', '17', '20'])).
% 0.40/0.58  thf(zf_stmt_7, type, zip_tseitin_3 : $i > $i > $i > $o).
% 0.40/0.58  thf(zf_stmt_8, axiom,
% 0.40/0.58    (![C:$i,B:$i,A:$i]:
% 0.40/0.58     ( ( zip_tseitin_3 @ C @ B @ A ) =>
% 0.40/0.58       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.40/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.40/0.58  thf(zf_stmt_9, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 0.40/0.58  thf(zf_stmt_10, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.40/0.58       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.40/0.58           ( ![D:$i]: ( zip_tseitin_2 @ D @ C @ B @ A ) ) ) =>
% 0.40/0.58         ( zip_tseitin_3 @ C @ B @ A ) ) ))).
% 0.40/0.58  thf('22', plain,
% 0.40/0.58      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.40/0.58         (((k1_relat_1 @ X37) != (X36))
% 0.40/0.58          | ~ (zip_tseitin_2 @ (sk_D @ X37 @ X38 @ X36) @ X37 @ X38 @ X36)
% 0.40/0.58          | (zip_tseitin_3 @ X37 @ X38 @ X36)
% 0.40/0.58          | ~ (v1_funct_1 @ X37)
% 0.40/0.58          | ~ (v1_relat_1 @ X37))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_10])).
% 0.40/0.58  thf('23', plain,
% 0.40/0.58      (![X37 : $i, X38 : $i]:
% 0.40/0.58         (~ (v1_relat_1 @ X37)
% 0.40/0.58          | ~ (v1_funct_1 @ X37)
% 0.40/0.58          | (zip_tseitin_3 @ X37 @ X38 @ (k1_relat_1 @ X37))
% 0.40/0.58          | ~ (zip_tseitin_2 @ (sk_D @ X37 @ X38 @ (k1_relat_1 @ X37)) @ X37 @ 
% 0.40/0.58               X38 @ (k1_relat_1 @ X37)))),
% 0.40/0.58      inference('simplify', [status(thm)], ['22'])).
% 0.40/0.58  thf('24', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ 
% 0.40/0.58             (k1_relat_1 @ sk_D_1))
% 0.40/0.58          | (zip_tseitin_3 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.40/0.58          | ~ (v1_funct_1 @ sk_D_1)
% 0.40/0.58          | ~ (v1_relat_1 @ sk_D_1))),
% 0.40/0.58      inference('sup-', [status(thm)], ['21', '23'])).
% 0.40/0.58  thf('25', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 0.40/0.58      inference('demod', [status(thm)], ['8', '17', '20'])).
% 0.40/0.58  thf('26', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 0.40/0.58      inference('demod', [status(thm)], ['8', '17', '20'])).
% 0.40/0.58  thf('27', plain, ((v1_funct_1 @ sk_D_1)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('28', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(cc1_relset_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.58       ( v1_relat_1 @ C ) ))).
% 0.40/0.58  thf('29', plain,
% 0.40/0.58      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.40/0.58         ((v1_relat_1 @ X5)
% 0.40/0.58          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.40/0.58      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.40/0.58  thf('30', plain, ((v1_relat_1 @ sk_D_1)),
% 0.40/0.58      inference('sup-', [status(thm)], ['28', '29'])).
% 0.40/0.58  thf('31', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ sk_B)
% 0.40/0.58          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 0.40/0.58      inference('demod', [status(thm)], ['24', '25', '26', '27', '30'])).
% 0.40/0.58  thf('32', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((r2_hidden @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B)
% 0.40/0.58          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['5', '31'])).
% 0.40/0.58  thf(t1_subset, axiom,
% 0.40/0.58    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.40/0.58  thf('33', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.40/0.58      inference('cnf', [status(esa)], [t1_subset])).
% 0.40/0.58  thf('34', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.40/0.58          | (m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['32', '33'])).
% 0.40/0.58  thf('35', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf(redefinition_k3_funct_2, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.40/0.58     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.40/0.58         ( v1_funct_2 @ C @ A @ B ) & 
% 0.40/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.40/0.58         ( m1_subset_1 @ D @ A ) ) =>
% 0.40/0.58       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.40/0.58  thf('36', plain,
% 0.40/0.58      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.40/0.58          | ~ (v1_funct_2 @ X25 @ X26 @ X27)
% 0.40/0.58          | ~ (v1_funct_1 @ X25)
% 0.40/0.58          | (v1_xboole_0 @ X26)
% 0.40/0.58          | ~ (m1_subset_1 @ X28 @ X26)
% 0.40/0.58          | ((k3_funct_2 @ X26 @ X27 @ X25 @ X28) = (k1_funct_1 @ X25 @ X28)))),
% 0.40/0.58      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.40/0.58  thf('37', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 0.40/0.58            = (k1_funct_1 @ sk_D_1 @ X0))
% 0.40/0.58          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.40/0.58          | (v1_xboole_0 @ sk_B)
% 0.40/0.58          | ~ (v1_funct_1 @ sk_D_1)
% 0.40/0.58          | ~ (v1_funct_2 @ sk_D_1 @ sk_B @ sk_C))),
% 0.40/0.58      inference('sup-', [status(thm)], ['35', '36'])).
% 0.40/0.58  thf('38', plain, ((v1_funct_1 @ sk_D_1)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('39', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_C)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('40', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 0.40/0.58            = (k1_funct_1 @ sk_D_1 @ X0))
% 0.40/0.58          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.40/0.58          | (v1_xboole_0 @ sk_B))),
% 0.40/0.58      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.40/0.58  thf('41', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('42', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.40/0.58          | ((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 0.40/0.58              = (k1_funct_1 @ sk_D_1 @ X0)))),
% 0.40/0.58      inference('clc', [status(thm)], ['40', '41'])).
% 0.40/0.58  thf('43', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.40/0.58          | ((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B))
% 0.40/0.58              = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B))))),
% 0.40/0.58      inference('sup-', [status(thm)], ['34', '42'])).
% 0.40/0.58  thf('44', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.40/0.58          | (m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['32', '33'])).
% 0.40/0.58  thf('45', plain,
% 0.40/0.58      (![X39 : $i]:
% 0.40/0.58         ((r2_hidden @ (k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X39) @ sk_A)
% 0.40/0.58          | ~ (m1_subset_1 @ X39 @ sk_B))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.40/0.58  thf('46', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.40/0.58          | (r2_hidden @ 
% 0.40/0.58             (k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 0.40/0.58             sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['44', '45'])).
% 0.40/0.58  thf('47', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 0.40/0.58           sk_A)
% 0.40/0.58          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.40/0.58          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 0.40/0.58      inference('sup+', [status(thm)], ['43', '46'])).
% 0.40/0.58  thf('48', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.40/0.58          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 0.40/0.58             sk_A))),
% 0.40/0.58      inference('simplify', [status(thm)], ['47'])).
% 0.40/0.58  thf('49', plain,
% 0.40/0.58      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.40/0.58         ((zip_tseitin_2 @ X29 @ X30 @ X31 @ X32)
% 0.40/0.58          | ~ (r2_hidden @ (k1_funct_1 @ X30 @ X29) @ X31))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.40/0.58  thf('50', plain,
% 0.40/0.58      (![X0 : $i, X1 : $i]:
% 0.40/0.58         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.40/0.58          | (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ sk_A @ X1))),
% 0.40/0.58      inference('sup-', [status(thm)], ['48', '49'])).
% 0.40/0.58  thf('51', plain,
% 0.40/0.58      (![X0 : $i]:
% 0.40/0.58         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ sk_B)
% 0.40/0.58          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 0.40/0.58      inference('demod', [status(thm)], ['24', '25', '26', '27', '30'])).
% 0.40/0.58  thf('52', plain,
% 0.40/0.58      (((zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B)
% 0.40/0.58        | (zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B))),
% 0.40/0.58      inference('sup-', [status(thm)], ['50', '51'])).
% 0.40/0.58  thf('53', plain, ((zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B)),
% 0.40/0.58      inference('simplify', [status(thm)], ['52'])).
% 0.40/0.58  thf('54', plain,
% 0.40/0.58      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.40/0.58         ((m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.40/0.58          | ~ (zip_tseitin_3 @ X33 @ X34 @ X35))),
% 0.40/0.58      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.40/0.58  thf('55', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['53', '54'])).
% 0.40/0.58  thf(dt_k2_relset_1, axiom,
% 0.40/0.58    (![A:$i,B:$i,C:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.40/0.58       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.40/0.58  thf('56', plain,
% 0.40/0.58      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.40/0.58         ((m1_subset_1 @ (k2_relset_1 @ X8 @ X9 @ X10) @ (k1_zfmisc_1 @ X9))
% 0.40/0.58          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.40/0.58      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.40/0.58  thf('57', plain,
% 0.40/0.58      ((m1_subset_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_D_1) @ 
% 0.40/0.58        (k1_zfmisc_1 @ sk_A))),
% 0.40/0.58      inference('sup-', [status(thm)], ['55', '56'])).
% 0.40/0.58  thf('58', plain,
% 0.40/0.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.40/0.58      inference('sup-', [status(thm)], ['53', '54'])).
% 0.40/0.58  thf('59', plain,
% 0.40/0.58      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.40/0.58         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 0.40/0.58          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.40/0.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.40/0.58  thf('60', plain,
% 0.40/0.58      (((k2_relset_1 @ sk_B @ sk_A @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.40/0.58      inference('sup-', [status(thm)], ['58', '59'])).
% 0.40/0.58  thf('61', plain,
% 0.40/0.58      ((m1_subset_1 @ (k2_relat_1 @ sk_D_1) @ (k1_zfmisc_1 @ sk_A))),
% 0.40/0.58      inference('demod', [status(thm)], ['57', '60'])).
% 0.40/0.58  thf(t3_subset, axiom,
% 0.40/0.58    (![A:$i,B:$i]:
% 0.40/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.40/0.58  thf('62', plain,
% 0.40/0.58      (![X2 : $i, X3 : $i]:
% 0.40/0.58         ((r1_tarski @ X2 @ X3) | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3)))),
% 0.40/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.40/0.58  thf('63', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 0.40/0.58      inference('sup-', [status(thm)], ['61', '62'])).
% 0.40/0.58  thf('64', plain, ($false), inference('demod', [status(thm)], ['4', '63'])).
% 0.40/0.58  
% 0.40/0.58  % SZS output end Refutation
% 0.40/0.58  
% 0.42/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
