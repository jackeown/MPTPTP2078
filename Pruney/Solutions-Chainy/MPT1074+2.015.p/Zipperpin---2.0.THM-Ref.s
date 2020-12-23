%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8v6IIbrnFq

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:24 EST 2020

% Result     : Theorem 3.37s
% Output     : Refutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 964 expanded)
%              Number of leaves         :   51 ( 321 expanded)
%              Depth                    :   24
%              Number of atoms          :  951 (12255 expanded)
%              Number of equality atoms :   35 ( 271 expanded)
%              Maximal formula depth    :   18 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_2_type,type,(
    zip_tseitin_2: $i > $i > $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_3_type,type,(
    zip_tseitin_3: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

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
    ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_1 ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_1 )
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
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( zip_tseitin_2 @ X38 @ X39 @ X40 @ X41 )
      | ( r2_hidden @ X38 @ X41 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('6',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B @ sk_C_1 ),
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
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('8',plain,
    ( ~ ( zip_tseitin_1 @ sk_D_1 @ sk_C_1 @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_C_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
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
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_6])).

thf('11',plain,
    ( ( zip_tseitin_1 @ sk_D_1 @ sk_C_1 @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('13',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('15',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( r1_tarski @ X13 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('16',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r1_tarski @ X0 @ ( sk_C @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['13','16'])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('18',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( r1_xboole_0 @ X5 @ X6 )
      | ~ ( r1_tarski @ X5 @ X6 )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('21',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['12','21'])).

thf('23',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_C_1 @ X0 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    zip_tseitin_1 @ sk_D_1 @ sk_C_1 @ sk_B ),
    inference(demod,[status(thm)],['11','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('27',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('28',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C_1 @ sk_D_1 )
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['8','25','28'])).

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

thf('30',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ( ( k1_relat_1 @ X46 )
       != X45 )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X46 @ X47 @ X45 ) @ X46 @ X47 @ X45 )
      | ( zip_tseitin_3 @ X46 @ X47 @ X45 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_10])).

thf('31',plain,(
    ! [X46: $i,X47: $i] :
      ( ~ ( v1_relat_1 @ X46 )
      | ~ ( v1_funct_1 @ X46 )
      | ( zip_tseitin_3 @ X46 @ X47 @ ( k1_relat_1 @ X46 ) )
      | ~ ( zip_tseitin_2 @ ( sk_D @ X46 @ X47 @ ( k1_relat_1 @ X46 ) ) @ X46 @ X47 @ ( k1_relat_1 @ X46 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ ( k1_relat_1 @ sk_D_1 ) )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['8','25','28'])).

thf('34',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['8','25','28'])).

thf('35',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('37',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('38',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33','34','35','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['5','39'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('41',plain,(
    ! [X7: $i,X8: $i] :
      ( ( m1_subset_1 @ X7 @ X8 )
      | ~ ( r2_hidden @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ),
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

thf('44',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X35 @ X36 )
      | ~ ( v1_funct_1 @ X34 )
      | ( v1_xboole_0 @ X35 )
      | ~ ( m1_subset_1 @ X37 @ X35 )
      | ( ( k3_funct_2 @ X35 @ X36 @ X34 @ X37 )
        = ( k1_funct_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ~ ( v1_funct_2 @ sk_D_1 @ sk_B @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_2 @ sk_D_1 @ sk_B @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_1 @ X0 )
        = ( k1_funct_1 @ sk_D_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) )
        = ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['42','50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('53',plain,(
    ! [X48: $i] :
      ( ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_1 @ X48 ) @ sk_A )
      | ~ ( m1_subset_1 @ X48 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( r2_hidden @ ( k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) @ sk_A )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference('sup+',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( r2_hidden @ ( k1_funct_1 @ sk_D_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) ) @ sk_A ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( zip_tseitin_2 @ X38 @ X39 @ X40 @ X41 )
      | ~ ( r2_hidden @ ( k1_funct_1 @ X39 @ X38 ) @ X40 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ sk_A @ X1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( zip_tseitin_2 @ ( sk_D @ sk_D_1 @ X0 @ sk_B ) @ sk_D_1 @ X0 @ sk_B )
      | ( zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['32','33','34','35','38'])).

thf('60',plain,
    ( ( zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B )
    | ( zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X43 ) ) )
      | ~ ( zip_tseitin_3 @ X42 @ X43 @ X44 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_8])).

thf('63',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('64',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X17 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('65',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_B @ sk_A @ sk_D_1 ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('66',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r1_tarski @ X9 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('67',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_B @ sk_A @ sk_D_1 ) @ sk_A ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('69',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k2_relset_1 @ X24 @ X25 @ X23 )
        = ( k2_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('70',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D_1 )
    = ( k2_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D_1 ) @ sk_A ),
    inference(demod,[status(thm)],['67','70'])).

thf('72',plain,(
    $false ),
    inference(demod,[status(thm)],['4','71'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.8v6IIbrnFq
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:58:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 3.37/3.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 3.37/3.57  % Solved by: fo/fo7.sh
% 3.37/3.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.37/3.57  % done 2665 iterations in 3.115s
% 3.37/3.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 3.37/3.57  % SZS output start Refutation
% 3.37/3.57  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 3.37/3.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 3.37/3.57  thf(sk_C_1_type, type, sk_C_1: $i).
% 3.37/3.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.37/3.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.37/3.57  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 3.37/3.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.37/3.57  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 3.37/3.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.37/3.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.37/3.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.37/3.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.37/3.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.37/3.57  thf(sk_A_type, type, sk_A: $i).
% 3.37/3.57  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 3.37/3.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 3.37/3.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.37/3.57  thf(sk_D_1_type, type, sk_D_1: $i).
% 3.37/3.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.37/3.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.37/3.57  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 3.37/3.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.37/3.57  thf(zip_tseitin_2_type, type, zip_tseitin_2: $i > $i > $i > $i > $o).
% 3.37/3.57  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.37/3.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 3.37/3.57  thf(zip_tseitin_3_type, type, zip_tseitin_3: $i > $i > $i > $o).
% 3.37/3.57  thf(sk_B_type, type, sk_B: $i).
% 3.37/3.57  thf(t191_funct_2, conjecture,
% 3.37/3.57    (![A:$i,B:$i]:
% 3.37/3.57     ( ( ~( v1_xboole_0 @ B ) ) =>
% 3.37/3.57       ( ![C:$i]:
% 3.37/3.57         ( ( ~( v1_xboole_0 @ C ) ) =>
% 3.37/3.57           ( ![D:$i]:
% 3.37/3.57             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 3.37/3.57                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.37/3.57               ( ( ![E:$i]:
% 3.37/3.57                   ( ( m1_subset_1 @ E @ B ) =>
% 3.37/3.57                     ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 3.37/3.57                 ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ))).
% 3.37/3.57  thf(zf_stmt_0, negated_conjecture,
% 3.37/3.57    (~( ![A:$i,B:$i]:
% 3.37/3.57        ( ( ~( v1_xboole_0 @ B ) ) =>
% 3.37/3.57          ( ![C:$i]:
% 3.37/3.57            ( ( ~( v1_xboole_0 @ C ) ) =>
% 3.37/3.57              ( ![D:$i]:
% 3.37/3.57                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 3.37/3.57                    ( m1_subset_1 @
% 3.37/3.57                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.37/3.57                  ( ( ![E:$i]:
% 3.37/3.57                      ( ( m1_subset_1 @ E @ B ) =>
% 3.37/3.57                        ( r2_hidden @ ( k3_funct_2 @ B @ C @ D @ E ) @ A ) ) ) =>
% 3.37/3.57                    ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ A ) ) ) ) ) ) ) )),
% 3.37/3.57    inference('cnf.neg', [status(esa)], [t191_funct_2])).
% 3.37/3.57  thf('0', plain,
% 3.37/3.57      (~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_1) @ sk_A)),
% 3.37/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.57  thf('1', plain,
% 3.37/3.57      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 3.37/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.57  thf(redefinition_k2_relset_1, axiom,
% 3.37/3.57    (![A:$i,B:$i,C:$i]:
% 3.37/3.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.37/3.57       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.37/3.57  thf('2', plain,
% 3.37/3.57      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.37/3.57         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 3.37/3.57          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 3.37/3.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.37/3.57  thf('3', plain,
% 3.37/3.57      (((k2_relset_1 @ sk_B @ sk_C_1 @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 3.37/3.57      inference('sup-', [status(thm)], ['1', '2'])).
% 3.37/3.57  thf('4', plain, (~ (r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 3.37/3.57      inference('demod', [status(thm)], ['0', '3'])).
% 3.37/3.57  thf(t5_funct_2, axiom,
% 3.37/3.57    (![A:$i,B:$i,C:$i]:
% 3.37/3.57     ( ( ( v1_funct_1 @ C ) & ( v1_relat_1 @ C ) ) =>
% 3.37/3.57       ( ( ( ![D:$i]:
% 3.37/3.57             ( ( r2_hidden @ D @ A ) =>
% 3.37/3.57               ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) ) & 
% 3.37/3.57           ( ( k1_relat_1 @ C ) = ( A ) ) ) =>
% 3.37/3.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.37/3.57           ( v1_funct_2 @ C @ A @ B ) & ( v1_funct_1 @ C ) ) ) ))).
% 3.37/3.57  thf(zf_stmt_1, axiom,
% 3.37/3.57    (![D:$i,C:$i,B:$i,A:$i]:
% 3.37/3.57     ( ( ( r2_hidden @ D @ A ) => ( r2_hidden @ ( k1_funct_1 @ C @ D ) @ B ) ) =>
% 3.37/3.57       ( zip_tseitin_2 @ D @ C @ B @ A ) ))).
% 3.37/3.57  thf('5', plain,
% 3.37/3.57      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 3.37/3.57         ((zip_tseitin_2 @ X38 @ X39 @ X40 @ X41) | (r2_hidden @ X38 @ X41))),
% 3.37/3.57      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.37/3.57  thf('6', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_C_1)),
% 3.37/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.57  thf(d1_funct_2, axiom,
% 3.37/3.57    (![A:$i,B:$i,C:$i]:
% 3.37/3.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.37/3.57       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.37/3.57           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 3.37/3.57             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 3.37/3.57         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.37/3.57           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 3.37/3.57             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 3.37/3.57  thf(zf_stmt_2, axiom,
% 3.37/3.57    (![C:$i,B:$i,A:$i]:
% 3.37/3.57     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 3.37/3.57       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 3.37/3.57  thf('7', plain,
% 3.37/3.57      (![X28 : $i, X29 : $i, X30 : $i]:
% 3.37/3.57         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 3.37/3.57          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 3.37/3.57          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 3.37/3.57      inference('cnf', [status(esa)], [zf_stmt_2])).
% 3.37/3.57  thf('8', plain,
% 3.37/3.57      ((~ (zip_tseitin_1 @ sk_D_1 @ sk_C_1 @ sk_B)
% 3.37/3.57        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_C_1 @ sk_D_1)))),
% 3.37/3.57      inference('sup-', [status(thm)], ['6', '7'])).
% 3.37/3.57  thf('9', plain,
% 3.37/3.57      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 3.37/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.57  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 3.37/3.57  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 3.37/3.57  thf(zf_stmt_5, axiom,
% 3.37/3.57    (![B:$i,A:$i]:
% 3.37/3.57     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 3.37/3.57       ( zip_tseitin_0 @ B @ A ) ))).
% 3.37/3.57  thf(zf_stmt_6, axiom,
% 3.37/3.57    (![A:$i,B:$i,C:$i]:
% 3.37/3.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.37/3.57       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 3.37/3.57         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 3.37/3.57           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 3.37/3.57             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 3.37/3.57  thf('10', plain,
% 3.37/3.57      (![X31 : $i, X32 : $i, X33 : $i]:
% 3.37/3.57         (~ (zip_tseitin_0 @ X31 @ X32)
% 3.37/3.57          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 3.37/3.57          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 3.37/3.57      inference('cnf', [status(esa)], [zf_stmt_6])).
% 3.37/3.57  thf('11', plain,
% 3.37/3.57      (((zip_tseitin_1 @ sk_D_1 @ sk_C_1 @ sk_B)
% 3.37/3.57        | ~ (zip_tseitin_0 @ sk_C_1 @ sk_B))),
% 3.37/3.57      inference('sup-', [status(thm)], ['9', '10'])).
% 3.37/3.57  thf('12', plain,
% 3.37/3.57      (![X26 : $i, X27 : $i]:
% 3.37/3.57         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 3.37/3.57      inference('cnf', [status(esa)], [zf_stmt_5])).
% 3.37/3.57  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 3.37/3.57  thf('13', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 3.37/3.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.37/3.57  thf(t3_xboole_0, axiom,
% 3.37/3.57    (![A:$i,B:$i]:
% 3.37/3.57     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 3.37/3.57            ( r1_xboole_0 @ A @ B ) ) ) & 
% 3.37/3.57       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 3.37/3.57            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 3.37/3.57  thf('14', plain,
% 3.37/3.57      (![X0 : $i, X1 : $i]:
% 3.37/3.57         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 3.37/3.57      inference('cnf', [status(esa)], [t3_xboole_0])).
% 3.37/3.57  thf(t7_ordinal1, axiom,
% 3.37/3.57    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.37/3.57  thf('15', plain,
% 3.37/3.57      (![X12 : $i, X13 : $i]:
% 3.37/3.57         (~ (r2_hidden @ X12 @ X13) | ~ (r1_tarski @ X13 @ X12))),
% 3.37/3.57      inference('cnf', [status(esa)], [t7_ordinal1])).
% 3.37/3.57  thf('16', plain,
% 3.37/3.57      (![X0 : $i, X1 : $i]:
% 3.37/3.57         ((r1_xboole_0 @ X0 @ X1) | ~ (r1_tarski @ X0 @ (sk_C @ X1 @ X0)))),
% 3.37/3.57      inference('sup-', [status(thm)], ['14', '15'])).
% 3.37/3.57  thf('17', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 3.37/3.57      inference('sup-', [status(thm)], ['13', '16'])).
% 3.37/3.57  thf(t69_xboole_1, axiom,
% 3.37/3.57    (![A:$i,B:$i]:
% 3.37/3.57     ( ( ~( v1_xboole_0 @ B ) ) =>
% 3.37/3.57       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 3.37/3.57  thf('18', plain,
% 3.37/3.57      (![X5 : $i, X6 : $i]:
% 3.37/3.57         (~ (r1_xboole_0 @ X5 @ X6)
% 3.37/3.57          | ~ (r1_tarski @ X5 @ X6)
% 3.37/3.57          | (v1_xboole_0 @ X5))),
% 3.37/3.57      inference('cnf', [status(esa)], [t69_xboole_1])).
% 3.37/3.57  thf('19', plain,
% 3.37/3.57      (![X0 : $i]:
% 3.37/3.57         ((v1_xboole_0 @ k1_xboole_0) | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 3.37/3.57      inference('sup-', [status(thm)], ['17', '18'])).
% 3.37/3.57  thf('20', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 3.37/3.57      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.37/3.57  thf('21', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.37/3.57      inference('demod', [status(thm)], ['19', '20'])).
% 3.37/3.57  thf('22', plain,
% 3.37/3.57      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 3.37/3.57      inference('sup+', [status(thm)], ['12', '21'])).
% 3.37/3.57  thf('23', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 3.37/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.57  thf('24', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_C_1 @ X0)),
% 3.37/3.57      inference('sup-', [status(thm)], ['22', '23'])).
% 3.37/3.57  thf('25', plain, ((zip_tseitin_1 @ sk_D_1 @ sk_C_1 @ sk_B)),
% 3.37/3.57      inference('demod', [status(thm)], ['11', '24'])).
% 3.37/3.57  thf('26', plain,
% 3.37/3.57      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 3.37/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.57  thf(redefinition_k1_relset_1, axiom,
% 3.37/3.57    (![A:$i,B:$i,C:$i]:
% 3.37/3.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.37/3.57       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 3.37/3.57  thf('27', plain,
% 3.37/3.57      (![X20 : $i, X21 : $i, X22 : $i]:
% 3.37/3.57         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 3.37/3.57          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 3.37/3.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 3.37/3.57  thf('28', plain,
% 3.37/3.57      (((k1_relset_1 @ sk_B @ sk_C_1 @ sk_D_1) = (k1_relat_1 @ sk_D_1))),
% 3.37/3.57      inference('sup-', [status(thm)], ['26', '27'])).
% 3.37/3.57  thf('29', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 3.37/3.57      inference('demod', [status(thm)], ['8', '25', '28'])).
% 3.37/3.57  thf(zf_stmt_7, type, zip_tseitin_3 : $i > $i > $i > $o).
% 3.37/3.57  thf(zf_stmt_8, axiom,
% 3.37/3.57    (![C:$i,B:$i,A:$i]:
% 3.37/3.57     ( ( zip_tseitin_3 @ C @ B @ A ) =>
% 3.37/3.57       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.37/3.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 3.37/3.57  thf(zf_stmt_9, type, zip_tseitin_2 : $i > $i > $i > $i > $o).
% 3.37/3.57  thf(zf_stmt_10, axiom,
% 3.37/3.57    (![A:$i,B:$i,C:$i]:
% 3.37/3.57     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 3.37/3.57       ( ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 3.37/3.57           ( ![D:$i]: ( zip_tseitin_2 @ D @ C @ B @ A ) ) ) =>
% 3.37/3.57         ( zip_tseitin_3 @ C @ B @ A ) ) ))).
% 3.37/3.57  thf('30', plain,
% 3.37/3.57      (![X45 : $i, X46 : $i, X47 : $i]:
% 3.37/3.57         (((k1_relat_1 @ X46) != (X45))
% 3.37/3.57          | ~ (zip_tseitin_2 @ (sk_D @ X46 @ X47 @ X45) @ X46 @ X47 @ X45)
% 3.37/3.57          | (zip_tseitin_3 @ X46 @ X47 @ X45)
% 3.37/3.57          | ~ (v1_funct_1 @ X46)
% 3.37/3.57          | ~ (v1_relat_1 @ X46))),
% 3.37/3.57      inference('cnf', [status(esa)], [zf_stmt_10])).
% 3.37/3.57  thf('31', plain,
% 3.37/3.57      (![X46 : $i, X47 : $i]:
% 3.37/3.57         (~ (v1_relat_1 @ X46)
% 3.37/3.57          | ~ (v1_funct_1 @ X46)
% 3.37/3.57          | (zip_tseitin_3 @ X46 @ X47 @ (k1_relat_1 @ X46))
% 3.37/3.57          | ~ (zip_tseitin_2 @ (sk_D @ X46 @ X47 @ (k1_relat_1 @ X46)) @ X46 @ 
% 3.37/3.57               X47 @ (k1_relat_1 @ X46)))),
% 3.37/3.57      inference('simplify', [status(thm)], ['30'])).
% 3.37/3.57  thf('32', plain,
% 3.37/3.57      (![X0 : $i]:
% 3.37/3.57         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ 
% 3.37/3.57             (k1_relat_1 @ sk_D_1))
% 3.37/3.57          | (zip_tseitin_3 @ sk_D_1 @ X0 @ (k1_relat_1 @ sk_D_1))
% 3.37/3.57          | ~ (v1_funct_1 @ sk_D_1)
% 3.37/3.57          | ~ (v1_relat_1 @ sk_D_1))),
% 3.37/3.57      inference('sup-', [status(thm)], ['29', '31'])).
% 3.37/3.57  thf('33', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 3.37/3.57      inference('demod', [status(thm)], ['8', '25', '28'])).
% 3.37/3.57  thf('34', plain, (((sk_B) = (k1_relat_1 @ sk_D_1))),
% 3.37/3.57      inference('demod', [status(thm)], ['8', '25', '28'])).
% 3.37/3.57  thf('35', plain, ((v1_funct_1 @ sk_D_1)),
% 3.37/3.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.57  thf('36', plain,
% 3.37/3.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf(cc1_relset_1, axiom,
% 3.37/3.58    (![A:$i,B:$i,C:$i]:
% 3.37/3.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.37/3.58       ( v1_relat_1 @ C ) ))).
% 3.37/3.58  thf('37', plain,
% 3.37/3.58      (![X14 : $i, X15 : $i, X16 : $i]:
% 3.37/3.58         ((v1_relat_1 @ X14)
% 3.37/3.58          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 3.37/3.58      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.37/3.58  thf('38', plain, ((v1_relat_1 @ sk_D_1)),
% 3.37/3.58      inference('sup-', [status(thm)], ['36', '37'])).
% 3.37/3.58  thf('39', plain,
% 3.37/3.58      (![X0 : $i]:
% 3.37/3.58         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ sk_B)
% 3.37/3.58          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 3.37/3.58      inference('demod', [status(thm)], ['32', '33', '34', '35', '38'])).
% 3.37/3.58  thf('40', plain,
% 3.37/3.58      (![X0 : $i]:
% 3.37/3.58         ((r2_hidden @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B)
% 3.37/3.58          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 3.37/3.58      inference('sup-', [status(thm)], ['5', '39'])).
% 3.37/3.58  thf(t1_subset, axiom,
% 3.37/3.58    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 3.37/3.58  thf('41', plain,
% 3.37/3.58      (![X7 : $i, X8 : $i]: ((m1_subset_1 @ X7 @ X8) | ~ (r2_hidden @ X7 @ X8))),
% 3.37/3.58      inference('cnf', [status(esa)], [t1_subset])).
% 3.37/3.58  thf('42', plain,
% 3.37/3.58      (![X0 : $i]:
% 3.37/3.58         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 3.37/3.58          | (m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B))),
% 3.37/3.58      inference('sup-', [status(thm)], ['40', '41'])).
% 3.37/3.58  thf('43', plain,
% 3.37/3.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C_1)))),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf(redefinition_k3_funct_2, axiom,
% 3.37/3.58    (![A:$i,B:$i,C:$i,D:$i]:
% 3.37/3.58     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 3.37/3.58         ( v1_funct_2 @ C @ A @ B ) & 
% 3.37/3.58         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.37/3.58         ( m1_subset_1 @ D @ A ) ) =>
% 3.37/3.58       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 3.37/3.58  thf('44', plain,
% 3.37/3.58      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 3.37/3.58         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 3.37/3.58          | ~ (v1_funct_2 @ X34 @ X35 @ X36)
% 3.37/3.58          | ~ (v1_funct_1 @ X34)
% 3.37/3.58          | (v1_xboole_0 @ X35)
% 3.37/3.58          | ~ (m1_subset_1 @ X37 @ X35)
% 3.37/3.58          | ((k3_funct_2 @ X35 @ X36 @ X34 @ X37) = (k1_funct_1 @ X34 @ X37)))),
% 3.37/3.58      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 3.37/3.58  thf('45', plain,
% 3.37/3.58      (![X0 : $i]:
% 3.37/3.58         (((k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_1 @ X0)
% 3.37/3.58            = (k1_funct_1 @ sk_D_1 @ X0))
% 3.37/3.58          | ~ (m1_subset_1 @ X0 @ sk_B)
% 3.37/3.58          | (v1_xboole_0 @ sk_B)
% 3.37/3.58          | ~ (v1_funct_1 @ sk_D_1)
% 3.37/3.58          | ~ (v1_funct_2 @ sk_D_1 @ sk_B @ sk_C_1))),
% 3.37/3.58      inference('sup-', [status(thm)], ['43', '44'])).
% 3.37/3.58  thf('46', plain, ((v1_funct_1 @ sk_D_1)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('47', plain, ((v1_funct_2 @ sk_D_1 @ sk_B @ sk_C_1)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('48', plain,
% 3.37/3.58      (![X0 : $i]:
% 3.37/3.58         (((k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_1 @ X0)
% 3.37/3.58            = (k1_funct_1 @ sk_D_1 @ X0))
% 3.37/3.58          | ~ (m1_subset_1 @ X0 @ sk_B)
% 3.37/3.58          | (v1_xboole_0 @ sk_B))),
% 3.37/3.58      inference('demod', [status(thm)], ['45', '46', '47'])).
% 3.37/3.58  thf('49', plain, (~ (v1_xboole_0 @ sk_B)),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('50', plain,
% 3.37/3.58      (![X0 : $i]:
% 3.37/3.58         (~ (m1_subset_1 @ X0 @ sk_B)
% 3.37/3.58          | ((k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_1 @ X0)
% 3.37/3.58              = (k1_funct_1 @ sk_D_1 @ X0)))),
% 3.37/3.58      inference('clc', [status(thm)], ['48', '49'])).
% 3.37/3.58  thf('51', plain,
% 3.37/3.58      (![X0 : $i]:
% 3.37/3.58         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 3.37/3.58          | ((k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B))
% 3.37/3.58              = (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B))))),
% 3.37/3.58      inference('sup-', [status(thm)], ['42', '50'])).
% 3.37/3.58  thf('52', plain,
% 3.37/3.58      (![X0 : $i]:
% 3.37/3.58         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 3.37/3.58          | (m1_subset_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_B))),
% 3.37/3.58      inference('sup-', [status(thm)], ['40', '41'])).
% 3.37/3.58  thf('53', plain,
% 3.37/3.58      (![X48 : $i]:
% 3.37/3.58         ((r2_hidden @ (k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_1 @ X48) @ sk_A)
% 3.37/3.58          | ~ (m1_subset_1 @ X48 @ sk_B))),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.37/3.58  thf('54', plain,
% 3.37/3.58      (![X0 : $i]:
% 3.37/3.58         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 3.37/3.58          | (r2_hidden @ 
% 3.37/3.58             (k3_funct_2 @ sk_B @ sk_C_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 3.37/3.58             sk_A))),
% 3.37/3.58      inference('sup-', [status(thm)], ['52', '53'])).
% 3.37/3.58  thf('55', plain,
% 3.37/3.58      (![X0 : $i]:
% 3.37/3.58         ((r2_hidden @ (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 3.37/3.58           sk_A)
% 3.37/3.58          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 3.37/3.58          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 3.37/3.58      inference('sup+', [status(thm)], ['51', '54'])).
% 3.37/3.58  thf('56', plain,
% 3.37/3.58      (![X0 : $i]:
% 3.37/3.58         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 3.37/3.58          | (r2_hidden @ (k1_funct_1 @ sk_D_1 @ (sk_D @ sk_D_1 @ X0 @ sk_B)) @ 
% 3.37/3.58             sk_A))),
% 3.37/3.58      inference('simplify', [status(thm)], ['55'])).
% 3.37/3.58  thf('57', plain,
% 3.37/3.58      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 3.37/3.58         ((zip_tseitin_2 @ X38 @ X39 @ X40 @ X41)
% 3.37/3.58          | ~ (r2_hidden @ (k1_funct_1 @ X39 @ X38) @ X40))),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 3.37/3.58  thf('58', plain,
% 3.37/3.58      (![X0 : $i, X1 : $i]:
% 3.37/3.58         ((zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B)
% 3.37/3.58          | (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ sk_A @ X1))),
% 3.37/3.58      inference('sup-', [status(thm)], ['56', '57'])).
% 3.37/3.58  thf('59', plain,
% 3.37/3.58      (![X0 : $i]:
% 3.37/3.58         (~ (zip_tseitin_2 @ (sk_D @ sk_D_1 @ X0 @ sk_B) @ sk_D_1 @ X0 @ sk_B)
% 3.37/3.58          | (zip_tseitin_3 @ sk_D_1 @ X0 @ sk_B))),
% 3.37/3.58      inference('demod', [status(thm)], ['32', '33', '34', '35', '38'])).
% 3.37/3.58  thf('60', plain,
% 3.37/3.58      (((zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B)
% 3.37/3.58        | (zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B))),
% 3.37/3.58      inference('sup-', [status(thm)], ['58', '59'])).
% 3.37/3.58  thf('61', plain, ((zip_tseitin_3 @ sk_D_1 @ sk_A @ sk_B)),
% 3.37/3.58      inference('simplify', [status(thm)], ['60'])).
% 3.37/3.58  thf('62', plain,
% 3.37/3.58      (![X42 : $i, X43 : $i, X44 : $i]:
% 3.37/3.58         ((m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X43)))
% 3.37/3.58          | ~ (zip_tseitin_3 @ X42 @ X43 @ X44))),
% 3.37/3.58      inference('cnf', [status(esa)], [zf_stmt_8])).
% 3.37/3.58  thf('63', plain,
% 3.37/3.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.37/3.58      inference('sup-', [status(thm)], ['61', '62'])).
% 3.37/3.58  thf(dt_k2_relset_1, axiom,
% 3.37/3.58    (![A:$i,B:$i,C:$i]:
% 3.37/3.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.37/3.58       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 3.37/3.58  thf('64', plain,
% 3.37/3.58      (![X17 : $i, X18 : $i, X19 : $i]:
% 3.37/3.58         ((m1_subset_1 @ (k2_relset_1 @ X17 @ X18 @ X19) @ (k1_zfmisc_1 @ X18))
% 3.37/3.58          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 3.37/3.58      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 3.37/3.58  thf('65', plain,
% 3.37/3.58      ((m1_subset_1 @ (k2_relset_1 @ sk_B @ sk_A @ sk_D_1) @ 
% 3.37/3.58        (k1_zfmisc_1 @ sk_A))),
% 3.37/3.58      inference('sup-', [status(thm)], ['63', '64'])).
% 3.37/3.58  thf(t3_subset, axiom,
% 3.37/3.58    (![A:$i,B:$i]:
% 3.37/3.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.37/3.58  thf('66', plain,
% 3.37/3.58      (![X9 : $i, X10 : $i]:
% 3.37/3.58         ((r1_tarski @ X9 @ X10) | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 3.37/3.58      inference('cnf', [status(esa)], [t3_subset])).
% 3.37/3.58  thf('67', plain, ((r1_tarski @ (k2_relset_1 @ sk_B @ sk_A @ sk_D_1) @ sk_A)),
% 3.37/3.58      inference('sup-', [status(thm)], ['65', '66'])).
% 3.37/3.58  thf('68', plain,
% 3.37/3.58      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 3.37/3.58      inference('sup-', [status(thm)], ['61', '62'])).
% 3.37/3.58  thf('69', plain,
% 3.37/3.58      (![X23 : $i, X24 : $i, X25 : $i]:
% 3.37/3.58         (((k2_relset_1 @ X24 @ X25 @ X23) = (k2_relat_1 @ X23))
% 3.37/3.58          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 3.37/3.58      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.37/3.58  thf('70', plain,
% 3.37/3.58      (((k2_relset_1 @ sk_B @ sk_A @ sk_D_1) = (k2_relat_1 @ sk_D_1))),
% 3.37/3.58      inference('sup-', [status(thm)], ['68', '69'])).
% 3.37/3.58  thf('71', plain, ((r1_tarski @ (k2_relat_1 @ sk_D_1) @ sk_A)),
% 3.37/3.58      inference('demod', [status(thm)], ['67', '70'])).
% 3.37/3.58  thf('72', plain, ($false), inference('demod', [status(thm)], ['4', '71'])).
% 3.37/3.58  
% 3.37/3.58  % SZS output end Refutation
% 3.37/3.58  
% 3.37/3.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
