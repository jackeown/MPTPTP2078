%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ru83zGbwWq

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:22 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 404 expanded)
%              Number of leaves         :   48 ( 145 expanded)
%              Depth                    :   20
%              Number of atoms          :  845 (5623 expanded)
%              Number of equality atoms :   33 ( 139 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( zip_tseitin_2 @ X28 @ X29 @ X30 @ X31 )
      | ( r2_hidden @ X28 @ X31 ) ) ),
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
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_funct_2 @ X20 @ X18 @ X19 )
      | ( X18
        = ( k1_relset_1 @ X18 @ X19 @ X20 ) )
      | ~ ( zip_tseitin_1 @ X20 @ X19 @ X18 ) ) ),
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
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( zip_tseitin_0 @ X21 @ X22 )
      | ( zip_tseitin_1 @ X23 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('11',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X16: $i,X17: $i] :
      ( ( zip_tseitin_0 @ X16 @ X17 )
      | ( X16 = k1_xboole_0 ) ) ),
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k1_relset_1 @ X11 @ X12 @ X10 )
        = ( k1_relat_1 @ X10 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
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
    ! [X35: $i,X36: $i,X37: $i] :
      ( ( ( k1_relat_1 @ X36 )
       != X35 )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X36 @ X37 @ X35 ) @ X36 @ X37 @ X35 )
      | ( zip_tseitin_3 @ X36 @ X37 @ X35 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('23',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v1_relat_1 @ X36 )
      | ~ ( v1_funct_1 @ X36 )
      | ( zip_tseitin_3 @ X36 @ X37 @ ( k1_relat_1 @ X36 ) )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X36 @ X37 @ ( k1_relat_1 @ X36 ) ) @ X36 @ X37 @ ( k1_relat_1 @ X36 ) ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
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
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X24 @ X25 @ X26 )
      | ~ ( v1_funct_1 @ X24 )
      | ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X27 @ X25 )
      | ( ( k3_funct_2 @ X25 @ X26 @ X24 @ X27 )
        = ( k1_funct_1 @ X24 @ X27 ) ) ) ),
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
    ! [X38: $i] :
      ( ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X38 ) @ sk_A )
      | ~ ( m1_subset_1 @ X38 @ sk_B ) ) ),
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
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( zip_tseitin_2 @ X28 @ X29 @ X30 @ X31 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X29 @ X28 ) @ X30 ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( zip_tseitin_3 @ X32 @ X33 @ X34 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('55',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('56',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v5_relat_1 @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('57',plain,(
    v5_relat_1 @ sk_D_1 @ sk_A ),
    inference('sup-',[status(thm)],['55','56'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('58',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v5_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k2_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('59',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['28','29'])).

thf('61',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['4','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Ru83zGbwWq
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:12:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.39/0.58  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.39/0.58  % Solved by: fo/fo7.sh
% 0.39/0.58  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.58  % done 116 iterations in 0.118s
% 0.39/0.58  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.39/0.58  % SZS output start Refutation
% 0.39/0.58  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.58  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.58  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.39/0.58  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.58  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.58  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.58  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.39/0.58  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.39/0.58  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 0.39/0.58  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.58  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.39/0.58  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.58  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.58  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.58  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.39/0.58  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.39/0.58  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $o).
% 0.39/0.58  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.58  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.58  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.58  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.58  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.39/0.58  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.39/0.58  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.39/0.58  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.39/0.58  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.58  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.58  thf(t191_funct_2, conjecture,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.39/0.58       ( ![C:$i]:
% 0.39/0.58         ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.39/0.58           ( ![D:$i]:
% 0.39/0.58             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.39/0.58                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.39/0.58               ( ( ![E:$i]:
% 0.39/0.58                   ( ( m1_subset_1 @ E @ B ) =>
% 0.39/0.58                     ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 0.39/0.58                 ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.58    (~( ![A:$i,B:$i]:
% 0.39/0.58        ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.39/0.58          ( ![C:$i]:
% 0.39/0.58            ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.39/0.58              ( ![D:$i]:
% 0.39/0.58                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.39/0.58                    ( m1_subset_1 @
% 0.39/0.58                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.39/0.58                  ( ( ![E:$i]:
% 0.39/0.58                      ( ( m1_subset_1 @ E @ B ) =>
% 0.39/0.58                        ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 0.39/0.58                    ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ) )),
% 0.39/0.58    inference('cnf.neg', [status(esa)], [t191_funct_2])).
% 0.39/0.58  thf('0', plain,
% 0.39/0.58      (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C @ sk_D_1) @ sk_A)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('1', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(redefinition_k2_relset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.58       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.39/0.58  thf('2', plain,
% 0.39/0.58      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.39/0.58         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 0.39/0.58          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.39/0.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.39/0.58  thf('3', plain,
% 0.39/0.58      (((k2_relset_1 @ sk_B @ sk_C @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 0.39/0.58      inference('sup-', [status(thm)], ['1', '2'])).
% 0.39/0.58  thf('4', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 0.39/0.58      inference('demod', [status(thm)], ['0', '3'])).
% 0.39/0.58  thf(t5_funct_2, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 0.39/0.58       ( ( ( ![D:$i]:
% 0.39/0.58             ( ( r2_hidden @ D @ A ) =>
% 0.39/0.58               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 0.39/0.58           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 0.39/0.58         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.39/0.58           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_1, axiom,
% 0.39/0.58    (![D:$i,C:$i,B:$i,A:$i]:
% 0.39/0.58     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 0.39/0.58       ( zip_tseitin_2 @ D @ C @ B @ A ) ))).
% 0.39/0.58  thf('5', plain,
% 0.39/0.58      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.39/0.58         ((zip_tseitin_2 @ X28 @ X29 @ X30 @ X31) | (r2_hidden @ X28 @ X31))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.58  thf('6', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(d1_funct_2, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.58       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.39/0.58           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.39/0.58             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.39/0.58         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.58           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.39/0.58             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_2, axiom,
% 0.39/0.58    (![C:$i,B:$i,A:$i]:
% 0.39/0.58     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.39/0.58       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.39/0.58  thf('7', plain,
% 0.39/0.58      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.39/0.58         (~ (v1_funct_2 @ X20 @ X18 @ X19)
% 0.39/0.58          | ((X18) = (k1_relset_1 @ X18 @ X19 @ X20))
% 0.39/0.58          | ~ (zip_tseitin_1 @ X20 @ X19 @ X18))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.39/0.58  thf('8', plain,
% 0.39/0.58      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)
% 0.39/0.58        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C @ sk_D_1)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['6', '7'])).
% 0.39/0.58  thf('9', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.39/0.58  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.39/0.58  thf(zf_stmt_5, axiom,
% 0.39/0.58    (![B:$i,A:$i]:
% 0.39/0.58     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.39/0.58       ( zip_tseitin_0 @ B @ A ) ))).
% 0.39/0.58  thf(zf_stmt_6, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.58       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.39/0.58         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.39/0.58           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.39/0.58             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.39/0.58  thf('10', plain,
% 0.39/0.58      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.39/0.58         (~ (zip_tseitin_0 @ X21 @ X22)
% 0.39/0.58          | (zip_tseitin_1 @ X23 @ X21 @ X22)
% 0.39/0.58          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X21))))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_6])).
% 0.39/0.58  thf('11', plain,
% 0.39/0.58      (((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)
% 0.39/0.58        | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.39/0.58  thf('12', plain,
% 0.39/0.58      (![X16 : $i, X17 : $i]:
% 0.39/0.58         ((zip_tseitin_0 @ X16 @ X17) | ((X16) = (k1_xboole_0)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.39/0.58  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.39/0.58  thf('13', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.58  thf('14', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.39/0.58      inference('sup+', [status(thm)], ['12', '13'])).
% 0.39/0.58  thf('15', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('16', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C @ X0)),
% 0.39/0.58      inference('sup-', [status(thm)], ['14', '15'])).
% 0.39/0.58  thf('17', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_C @ sk_B)),
% 0.39/0.58      inference('demod', [status(thm)], ['11', '16'])).
% 0.39/0.58  thf('18', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(redefinition_k1_relset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.58       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.39/0.58  thf('19', plain,
% 0.39/0.58      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.39/0.58         (((k1_relset_1 @ X11 @ X12 @ X10) = (k1_relat_1 @ X10))
% 0.39/0.58          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.39/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.39/0.58  thf('20', plain,
% 0.39/0.58      (((k1_relset_1 @ sk_B @ sk_C @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 0.39/0.58      inference('sup-', [status(thm)], ['18', '19'])).
% 0.39/0.58  thf('21', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 0.39/0.58      inference('demod', [status(thm)], ['8', '17', '20'])).
% 0.39/0.58  thf(zf_stmt_7, type, zip_tseitin_3 : $i > $i > $i > $o).
% 0.39/0.58  thf(zf_stmt_8, axiom,
% 0.39/0.58    (![C:$i,B:$i,A:$i]:
% 0.39/0.58     ( ( zip_tseitin_3 @ C @ B @ A ) =>
% 0.39/0.58       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.39/0.58  thf(zf_stmt_9, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 0.39/0.58  thf(zf_stmt_10, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.39/0.58       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.39/0.58           ( ![D:$i]: ( zip_tseitin_2 @ D @ C @ B @ A ) ) ) =>
% 0.39/0.58         ( zip_tseitin_3 @ C @ B @ A ) ) ))).
% 0.39/0.58  thf('22', plain,
% 0.39/0.58      (![X35 : $i, X36 : $i, X37 : $i]:
% 0.39/0.58         (((k1_relat_1 @ X36) != (X35))
% 0.39/0.58          | ~ (zip_tseitin_2 @ (sk_D @ X36 @ X37 @ X35) @ X36 @ X37 @ X35)
% 0.39/0.58          | (zip_tseitin_3 @ X36 @ X37 @ X35)
% 0.39/0.58          | ~ (v1_funct_1 @ X36)
% 0.39/0.58          | ~ (v1_relat_1 @ X36))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_10])).
% 0.39/0.58  thf('23', plain,
% 0.39/0.58      (![X36 : $i, X37 : $i]:
% 0.39/0.58         (~ (v1_relat_1 @ X36)
% 0.39/0.58          | ~ (v1_funct_1 @ X36)
% 0.39/0.58          | (zip_tseitin_3 @ X36 @ X37 @ (k1_relat_1 @ X36))
% 0.39/0.58          | ~ (zip_tseitin_2 @ (sk_D @ X36 @ X37 @ (k1_relat_1 @ X36)) @ X36 @ 
% 0.39/0.58               X37 @ (k1_relat_1 @ X36)))),
% 0.39/0.58      inference('simplify', [status(thm)], ['22'])).
% 0.39/0.58  thf('24', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ 
% 0.39/0.58             (k1_relat_1 @ sk_D_1))
% 0.39/0.58          | (zip_tseitin_3 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 0.39/0.58          | ~ (v1_funct_1 @ sk_D_1)
% 0.39/0.58          | ~ (v1_relat_1 @ sk_D_1))),
% 0.39/0.58      inference('sup-', [status(thm)], ['21', '23'])).
% 0.39/0.58  thf('25', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 0.39/0.58      inference('demod', [status(thm)], ['8', '17', '20'])).
% 0.39/0.58  thf('26', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 0.39/0.58      inference('demod', [status(thm)], ['8', '17', '20'])).
% 0.39/0.58  thf('27', plain, ((v1_funct_1 @ sk_D_1)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('28', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(cc1_relset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.58       ( v1_relat_1 @ C ) ))).
% 0.39/0.58  thf('29', plain,
% 0.39/0.58      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.39/0.58         ((v1_relat_1 @ X4)
% 0.39/0.58          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 0.39/0.58      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.39/0.58  thf('30', plain, ((v1_relat_1 @ sk_D_1)),
% 0.39/0.58      inference('sup-', [status(thm)], ['28', '29'])).
% 0.39/0.58  thf('31', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ sk_B)
% 0.39/0.58          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 0.39/0.58      inference('demod', [status(thm)], ['24', '25', '26', '27', '30'])).
% 0.39/0.58  thf('32', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((r2_hidden @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B)
% 0.39/0.58          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['5', '31'])).
% 0.39/0.58  thf(t1_subset, axiom,
% 0.39/0.58    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.39/0.58  thf('33', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.39/0.58      inference('cnf', [status(esa)], [t1_subset])).
% 0.39/0.58  thf('34', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.39/0.58          | (m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['32', '33'])).
% 0.39/0.58  thf('35', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf(redefinition_k3_funct_2, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.58     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.39/0.58         ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.39/0.58         ( m1_subset_1 @ D @ A ) ) =>
% 0.39/0.58       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.39/0.58  thf('36', plain,
% 0.39/0.58      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.39/0.58          | ~ (v1_funct_2 @ X24 @ X25 @ X26)
% 0.39/0.58          | ~ (v1_funct_1 @ X24)
% 0.39/0.58          | (v1_xboole_0 @ X25)
% 0.39/0.58          | ~ (m1_subset_1 @ X27 @ X25)
% 0.39/0.58          | ((k3_funct_2 @ X25 @ X26 @ X24 @ X27) = (k1_funct_1 @ X24 @ X27)))),
% 0.39/0.58      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.39/0.58  thf('37', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 0.39/0.58            = (k1_funct_1 @ sk_D_1 @ X0))
% 0.39/0.58          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.39/0.58          | (v1_xboole_0 @ sk_B)
% 0.39/0.58          | ~ (v1_funct_1 @ sk_D_1)
% 0.39/0.58          | ~ (v1_funct_2 @ sk_D_1 @ sk_B @ sk_C))),
% 0.39/0.58      inference('sup-', [status(thm)], ['35', '36'])).
% 0.39/0.58  thf('38', plain, ((v1_funct_1 @ sk_D_1)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('39', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_C)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('40', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 0.39/0.58            = (k1_funct_1 @ sk_D_1 @ X0))
% 0.39/0.58          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.39/0.58          | (v1_xboole_0 @ sk_B))),
% 0.39/0.58      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.39/0.58  thf('41', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('42', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.39/0.58          | ((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X0)
% 0.39/0.58              = (k1_funct_1 @ sk_D_1 @ X0)))),
% 0.39/0.58      inference('clc', [status(thm)], ['40', '41'])).
% 0.39/0.58  thf('43', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.39/0.58          | ((k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B))
% 0.39/0.58              = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B))))),
% 0.39/0.58      inference('sup-', [status(thm)], ['34', '42'])).
% 0.39/0.58  thf('44', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.39/0.58          | (m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['32', '33'])).
% 0.39/0.58  thf('45', plain,
% 0.39/0.58      (![X38 : $i]:
% 0.39/0.58         ((r2_hidden @ (k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ X38) @ sk_A)
% 0.39/0.58          | ~ (m1_subset_1 @ X38 @ sk_B))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.58  thf('46', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.39/0.58          | (r2_hidden @ 
% 0.39/0.58             (k3_funct_2 @ sk_B @ sk_C @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 0.39/0.58             sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['44', '45'])).
% 0.39/0.58  thf('47', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 0.39/0.58           sk_A)
% 0.39/0.58          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.39/0.58          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 0.39/0.58      inference('sup+', [status(thm)], ['43', '46'])).
% 0.39/0.58  thf('48', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.39/0.58          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 0.39/0.58             sk_A))),
% 0.39/0.58      inference('simplify', [status(thm)], ['47'])).
% 0.39/0.58  thf('49', plain,
% 0.39/0.58      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.39/0.58         ((zip_tseitin_2 @ X28 @ X29 @ X30 @ X31)
% 0.39/0.58          | ~ (r2_hidden @ (k1_funct_1 @ X29 @ X28) @ X30))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.39/0.58  thf('50', plain,
% 0.39/0.58      (![X0 : $i, X1 : $i]:
% 0.39/0.58         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 0.39/0.58          | (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ sk_A @ X1))),
% 0.39/0.58      inference('sup-', [status(thm)], ['48', '49'])).
% 0.39/0.58  thf('51', plain,
% 0.39/0.58      (![X0 : $i]:
% 0.39/0.58         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ sk_B)
% 0.39/0.58          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 0.39/0.58      inference('demod', [status(thm)], ['24', '25', '26', '27', '30'])).
% 0.39/0.58  thf('52', plain,
% 0.39/0.58      (((zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B)
% 0.39/0.58        | (zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B))),
% 0.39/0.58      inference('sup-', [status(thm)], ['50', '51'])).
% 0.39/0.58  thf('53', plain, ((zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B)),
% 0.39/0.58      inference('simplify', [status(thm)], ['52'])).
% 0.39/0.58  thf('54', plain,
% 0.39/0.58      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.39/0.58         ((m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.39/0.58          | ~ (zip_tseitin_3 @ X32 @ X33 @ X34))),
% 0.39/0.58      inference('cnf', [status(esa)], [zf_stmt_8])).
% 0.39/0.58  thf('55', plain,
% 0.39/0.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.39/0.58      inference('sup-', [status(thm)], ['53', '54'])).
% 0.39/0.58  thf(cc2_relset_1, axiom,
% 0.39/0.58    (![A:$i,B:$i,C:$i]:
% 0.39/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.58       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.39/0.58  thf('56', plain,
% 0.39/0.58      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.39/0.58         ((v5_relat_1 @ X7 @ X9)
% 0.39/0.58          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.39/0.58      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.39/0.58  thf('57', plain, ((v5_relat_1 @ sk_D_1 @ sk_A)),
% 0.39/0.58      inference('sup-', [status(thm)], ['55', '56'])).
% 0.39/0.58  thf(d19_relat_1, axiom,
% 0.39/0.58    (![A:$i,B:$i]:
% 0.39/0.58     ( ( v1_relat_1 @ B ) =>
% 0.39/0.58       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.39/0.58  thf('58', plain,
% 0.39/0.58      (![X2 : $i, X3 : $i]:
% 0.39/0.58         (~ (v5_relat_1 @ X2 @ X3)
% 0.39/0.58          | (r1_tarski @ (k2_relat_1 @ X2) @ X3)
% 0.39/0.58          | ~ (v1_relat_1 @ X2))),
% 0.39/0.58      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.39/0.58  thf('59', plain,
% 0.39/0.58      ((~ (v1_relat_1 @ sk_D_1) | (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A))),
% 0.39/0.58      inference('sup-', [status(thm)], ['57', '58'])).
% 0.39/0.58  thf('60', plain, ((v1_relat_1 @ sk_D_1)),
% 0.39/0.58      inference('sup-', [status(thm)], ['28', '29'])).
% 0.39/0.58  thf('61', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 0.39/0.58      inference('demod', [status(thm)], ['59', '60'])).
% 0.39/0.58  thf('62', plain, ($false), inference('demod', [status(thm)], ['4', '61'])).
% 0.39/0.58  
% 0.39/0.58  % SZS output end Refutation
% 0.39/0.58  
% 0.42/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
