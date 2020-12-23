%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Shoxo4ZzTX

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:51 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 125 expanded)
%              Number of leaves         :   41 (  56 expanded)
%              Depth                    :   13
%              Number of atoms          :  638 (1458 expanded)
%              Number of equality atoms :   35 (  63 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t176_funct_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ A )
                 => ( ( k7_partfun1 @ B @ C @ D )
                    = ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ A @ B )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ A )
                   => ( ( k7_partfun1 @ B @ C @ D )
                      = ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t176_funct_2])).

thf('0',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v5_relat_1 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_C @ sk_B_1 ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('5',plain,
    ( ( v1_xboole_0 @ sk_A_1 )
    | ( r2_hidden @ sk_D @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v1_xboole_0 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ sk_D @ sk_A_1 ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B_1 ),
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

thf('9',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X21 @ X22 )
      | ( X21
        = ( k1_relset_1 @ X21 @ X22 @ X23 ) )
      | ~ ( zip_tseitin_1 @ X23 @ X22 @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A_1 )
    | ( sk_A_1
      = ( k1_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
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

thf('12',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( zip_tseitin_0 @ X24 @ X25 )
      | ( zip_tseitin_1 @ X26 @ X24 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('13',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A_1 )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( ( zip_tseitin_0 @ X19 @ X20 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('15',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('16',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( sk_B @ X0 ) @ X0 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf('17',plain,(
    ! [X2: $i,X3: $i] :
      ( ( r2_hidden @ X2 @ X3 )
      | ( v1_xboole_0 @ X3 )
      | ~ ( m1_subset_1 @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('19',plain,(
    ! [X1: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ~ ( r2_hidden @ X7 @ X8 )
      | ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','21'])).

thf('23',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['15','22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['14','23'])).

thf('25',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A_1 ),
    inference(demod,[status(thm)],['13','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('29',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('30',plain,
    ( ( k1_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( sk_A_1
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['10','27','30'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('32',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X27 @ ( k1_relat_1 @ X28 ) )
      | ( ( k7_partfun1 @ X29 @ X28 @ X27 )
        = ( k1_funct_1 @ X28 @ X27 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v5_relat_1 @ X28 @ X29 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('33',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A_1 )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v5_relat_1 @ sk_C @ X1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k7_partfun1 @ X1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('35',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v1_relat_1 @ X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('36',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A_1 )
      | ~ ( v5_relat_1 @ sk_C @ X1 )
      | ( ( k7_partfun1 @ X1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['33','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k7_partfun1 @ X0 @ sk_C @ sk_D )
        = ( k1_funct_1 @ sk_C @ sk_D ) )
      | ~ ( v5_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','38'])).

thf('40',plain,
    ( ( k7_partfun1 @ sk_B_1 @ sk_C @ sk_D )
    = ( k1_funct_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['2','39'])).

thf('41',plain,(
    ( k7_partfun1 @ sk_B_1 @ sk_C @ sk_D )
 != ( k3_funct_2 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ sk_D @ sk_A_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A_1 @ sk_B_1 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X32 )
      | ~ ( v1_funct_1 @ X30 )
      | ( v1_xboole_0 @ X31 )
      | ~ ( m1_subset_1 @ X33 @ X31 )
      | ( ( k3_funct_2 @ X31 @ X32 @ X30 @ X33 )
        = ( k1_funct_1 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A_1 @ sk_B_1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_A_1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ sk_A_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_2 @ sk_C @ sk_A_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A_1 @ sk_B_1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A_1 )
      | ( v1_xboole_0 @ sk_A_1 ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ~ ( v1_xboole_0 @ sk_A_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A_1 )
      | ( ( k3_funct_2 @ sk_A_1 @ sk_B_1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) ) ) ),
    inference(clc,[status(thm)],['48','49'])).

thf('51',plain,
    ( ( k3_funct_2 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_D )
    = ( k1_funct_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['42','50'])).

thf('52',plain,(
    ( k7_partfun1 @ sk_B_1 @ sk_C @ sk_D )
 != ( k1_funct_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['41','51'])).

thf('53',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['40','52'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Shoxo4ZzTX
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:42:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.46/0.68  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.68  % Solved by: fo/fo7.sh
% 0.46/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.68  % done 288 iterations in 0.232s
% 0.46/0.68  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.68  % SZS output start Refutation
% 0.46/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.68  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.46/0.68  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.68  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.68  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.46/0.68  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.68  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.68  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.68  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.46/0.68  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.68  thf(sk_B_type, type, sk_B: $i > $i).
% 0.46/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.68  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.68  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.46/0.68  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.46/0.68  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.46/0.68  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.46/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.68  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.68  thf(t176_funct_2, conjecture,
% 0.46/0.68    (![A:$i]:
% 0.46/0.68     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.68       ( ![B:$i]:
% 0.46/0.68         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.46/0.68           ( ![C:$i]:
% 0.46/0.68             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.68                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.68               ( ![D:$i]:
% 0.46/0.68                 ( ( m1_subset_1 @ D @ A ) =>
% 0.46/0.68                   ( ( k7_partfun1 @ B @ C @ D ) =
% 0.46/0.68                     ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.46/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.68    (~( ![A:$i]:
% 0.46/0.68        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.68          ( ![B:$i]:
% 0.46/0.68            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.46/0.68              ( ![C:$i]:
% 0.46/0.68                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.68                    ( m1_subset_1 @
% 0.46/0.68                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.68                  ( ![D:$i]:
% 0.46/0.68                    ( ( m1_subset_1 @ D @ A ) =>
% 0.46/0.68                      ( ( k7_partfun1 @ B @ C @ D ) =
% 0.46/0.68                        ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ) )),
% 0.46/0.68    inference('cnf.neg', [status(esa)], [t176_funct_2])).
% 0.46/0.68  thf('0', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(cc2_relset_1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.68       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.68  thf('1', plain,
% 0.46/0.68      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.46/0.68         ((v5_relat_1 @ X13 @ X15)
% 0.46/0.68          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.46/0.68      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.68  thf('2', plain, ((v5_relat_1 @ sk_C @ sk_B_1)),
% 0.46/0.68      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.68  thf('3', plain, ((m1_subset_1 @ sk_D @ sk_A_1)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(t2_subset, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( m1_subset_1 @ A @ B ) =>
% 0.46/0.68       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.46/0.68  thf('4', plain,
% 0.46/0.68      (![X2 : $i, X3 : $i]:
% 0.46/0.68         ((r2_hidden @ X2 @ X3)
% 0.46/0.68          | (v1_xboole_0 @ X3)
% 0.46/0.68          | ~ (m1_subset_1 @ X2 @ X3))),
% 0.46/0.68      inference('cnf', [status(esa)], [t2_subset])).
% 0.46/0.68  thf('5', plain, (((v1_xboole_0 @ sk_A_1) | (r2_hidden @ sk_D @ sk_A_1))),
% 0.46/0.68      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.68  thf('6', plain, (~ (v1_xboole_0 @ sk_A_1)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('7', plain, ((r2_hidden @ sk_D @ sk_A_1)),
% 0.46/0.68      inference('clc', [status(thm)], ['5', '6'])).
% 0.46/0.68  thf('8', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B_1)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(d1_funct_2, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.68       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.68           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.46/0.68             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.46/0.68         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.68           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.46/0.68             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.46/0.68  thf(zf_stmt_1, axiom,
% 0.46/0.68    (![C:$i,B:$i,A:$i]:
% 0.46/0.68     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.46/0.68       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.46/0.68  thf('9', plain,
% 0.46/0.68      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.68         (~ (v1_funct_2 @ X23 @ X21 @ X22)
% 0.46/0.68          | ((X21) = (k1_relset_1 @ X21 @ X22 @ X23))
% 0.46/0.68          | ~ (zip_tseitin_1 @ X23 @ X22 @ X21))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.46/0.68  thf('10', plain,
% 0.46/0.68      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A_1)
% 0.46/0.68        | ((sk_A_1) = (k1_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.68  thf('11', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.46/0.68  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.46/0.68  thf(zf_stmt_4, axiom,
% 0.46/0.68    (![B:$i,A:$i]:
% 0.46/0.68     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.46/0.68       ( zip_tseitin_0 @ B @ A ) ))).
% 0.46/0.68  thf(zf_stmt_5, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.68       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.46/0.68         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.46/0.68           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.46/0.68             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.46/0.68  thf('12', plain,
% 0.46/0.68      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.46/0.68         (~ (zip_tseitin_0 @ X24 @ X25)
% 0.46/0.68          | (zip_tseitin_1 @ X26 @ X24 @ X25)
% 0.46/0.68          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24))))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.46/0.68  thf('13', plain,
% 0.46/0.68      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A_1)
% 0.46/0.68        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A_1))),
% 0.46/0.68      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.68  thf('14', plain,
% 0.46/0.68      (![X19 : $i, X20 : $i]:
% 0.46/0.68         ((zip_tseitin_0 @ X19 @ X20) | ((X19) = (k1_xboole_0)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.46/0.68  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.46/0.68  thf('15', plain, ((v1_xboole_0 @ sk_A)),
% 0.46/0.68      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.46/0.68  thf(existence_m1_subset_1, axiom,
% 0.46/0.68    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 0.46/0.68  thf('16', plain, (![X0 : $i]: (m1_subset_1 @ (sk_B @ X0) @ X0)),
% 0.46/0.68      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 0.46/0.68  thf('17', plain,
% 0.46/0.68      (![X2 : $i, X3 : $i]:
% 0.46/0.68         ((r2_hidden @ X2 @ X3)
% 0.46/0.68          | (v1_xboole_0 @ X3)
% 0.46/0.68          | ~ (m1_subset_1 @ X2 @ X3))),
% 0.46/0.68      inference('cnf', [status(esa)], [t2_subset])).
% 0.46/0.68  thf('18', plain,
% 0.46/0.68      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['16', '17'])).
% 0.46/0.68  thf(t4_subset_1, axiom,
% 0.46/0.68    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.46/0.68  thf('19', plain,
% 0.46/0.68      (![X1 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X1))),
% 0.46/0.68      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.46/0.68  thf(t5_subset, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.46/0.68          ( v1_xboole_0 @ C ) ) ))).
% 0.46/0.68  thf('20', plain,
% 0.46/0.68      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X7 @ X8)
% 0.46/0.68          | ~ (v1_xboole_0 @ X9)
% 0.46/0.68          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ X9)))),
% 0.46/0.68      inference('cnf', [status(esa)], [t5_subset])).
% 0.46/0.68  thf('21', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['19', '20'])).
% 0.46/0.68  thf('22', plain,
% 0.46/0.68      (![X0 : $i]: ((v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['18', '21'])).
% 0.46/0.68  thf('23', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.68      inference('sup-', [status(thm)], ['15', '22'])).
% 0.46/0.68  thf('24', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.46/0.68      inference('sup+', [status(thm)], ['14', '23'])).
% 0.46/0.68  thf('25', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('26', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 0.46/0.68      inference('sup-', [status(thm)], ['24', '25'])).
% 0.46/0.68  thf('27', plain, ((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A_1)),
% 0.46/0.68      inference('demod', [status(thm)], ['13', '26'])).
% 0.46/0.68  thf('28', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(redefinition_k1_relset_1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.68       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.46/0.68  thf('29', plain,
% 0.46/0.68      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.46/0.68         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.46/0.68          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.46/0.68      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.68  thf('30', plain,
% 0.46/0.68      (((k1_relset_1 @ sk_A_1 @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.46/0.68      inference('sup-', [status(thm)], ['28', '29'])).
% 0.46/0.68  thf('31', plain, (((sk_A_1) = (k1_relat_1 @ sk_C))),
% 0.46/0.68      inference('demod', [status(thm)], ['10', '27', '30'])).
% 0.46/0.68  thf(d8_partfun1, axiom,
% 0.46/0.68    (![A:$i,B:$i]:
% 0.46/0.68     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 0.46/0.68       ( ![C:$i]:
% 0.46/0.68         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 0.46/0.68           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 0.46/0.68  thf('32', plain,
% 0.46/0.68      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X27 @ (k1_relat_1 @ X28))
% 0.46/0.68          | ((k7_partfun1 @ X29 @ X28 @ X27) = (k1_funct_1 @ X28 @ X27))
% 0.46/0.68          | ~ (v1_funct_1 @ X28)
% 0.46/0.68          | ~ (v5_relat_1 @ X28 @ X29)
% 0.46/0.68          | ~ (v1_relat_1 @ X28))),
% 0.46/0.68      inference('cnf', [status(esa)], [d8_partfun1])).
% 0.46/0.68  thf('33', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X0 @ sk_A_1)
% 0.46/0.68          | ~ (v1_relat_1 @ sk_C)
% 0.46/0.68          | ~ (v5_relat_1 @ sk_C @ X1)
% 0.46/0.68          | ~ (v1_funct_1 @ sk_C)
% 0.46/0.68          | ((k7_partfun1 @ X1 @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0)))),
% 0.46/0.68      inference('sup-', [status(thm)], ['31', '32'])).
% 0.46/0.68  thf('34', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(cc1_relset_1, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i]:
% 0.46/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.68       ( v1_relat_1 @ C ) ))).
% 0.46/0.68  thf('35', plain,
% 0.46/0.68      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.68         ((v1_relat_1 @ X10)
% 0.46/0.68          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.46/0.68      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.68  thf('36', plain, ((v1_relat_1 @ sk_C)),
% 0.46/0.68      inference('sup-', [status(thm)], ['34', '35'])).
% 0.46/0.68  thf('37', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('38', plain,
% 0.46/0.68      (![X0 : $i, X1 : $i]:
% 0.46/0.68         (~ (r2_hidden @ X0 @ sk_A_1)
% 0.46/0.68          | ~ (v5_relat_1 @ sk_C @ X1)
% 0.46/0.68          | ((k7_partfun1 @ X1 @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0)))),
% 0.46/0.68      inference('demod', [status(thm)], ['33', '36', '37'])).
% 0.46/0.68  thf('39', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (((k7_partfun1 @ X0 @ sk_C @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))
% 0.46/0.68          | ~ (v5_relat_1 @ sk_C @ X0))),
% 0.46/0.68      inference('sup-', [status(thm)], ['7', '38'])).
% 0.46/0.68  thf('40', plain,
% 0.46/0.68      (((k7_partfun1 @ sk_B_1 @ sk_C @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))),
% 0.46/0.68      inference('sup-', [status(thm)], ['2', '39'])).
% 0.46/0.68  thf('41', plain,
% 0.46/0.68      (((k7_partfun1 @ sk_B_1 @ sk_C @ sk_D)
% 0.46/0.68         != (k3_funct_2 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_D))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('42', plain, ((m1_subset_1 @ sk_D @ sk_A_1)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('43', plain,
% 0.46/0.68      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A_1 @ sk_B_1)))),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf(redefinition_k3_funct_2, axiom,
% 0.46/0.68    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.68     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.46/0.68         ( v1_funct_2 @ C @ A @ B ) & 
% 0.46/0.68         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.46/0.68         ( m1_subset_1 @ D @ A ) ) =>
% 0.46/0.68       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.46/0.68  thf('44', plain,
% 0.46/0.68      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.46/0.68          | ~ (v1_funct_2 @ X30 @ X31 @ X32)
% 0.46/0.68          | ~ (v1_funct_1 @ X30)
% 0.46/0.68          | (v1_xboole_0 @ X31)
% 0.46/0.68          | ~ (m1_subset_1 @ X33 @ X31)
% 0.46/0.68          | ((k3_funct_2 @ X31 @ X32 @ X30 @ X33) = (k1_funct_1 @ X30 @ X33)))),
% 0.46/0.68      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.46/0.68  thf('45', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (((k3_funct_2 @ sk_A_1 @ sk_B_1 @ sk_C @ X0)
% 0.46/0.68            = (k1_funct_1 @ sk_C @ X0))
% 0.46/0.68          | ~ (m1_subset_1 @ X0 @ sk_A_1)
% 0.46/0.68          | (v1_xboole_0 @ sk_A_1)
% 0.46/0.68          | ~ (v1_funct_1 @ sk_C)
% 0.46/0.68          | ~ (v1_funct_2 @ sk_C @ sk_A_1 @ sk_B_1))),
% 0.46/0.68      inference('sup-', [status(thm)], ['43', '44'])).
% 0.46/0.68  thf('46', plain, ((v1_funct_1 @ sk_C)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('47', plain, ((v1_funct_2 @ sk_C @ sk_A_1 @ sk_B_1)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('48', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (((k3_funct_2 @ sk_A_1 @ sk_B_1 @ sk_C @ X0)
% 0.46/0.68            = (k1_funct_1 @ sk_C @ X0))
% 0.46/0.68          | ~ (m1_subset_1 @ X0 @ sk_A_1)
% 0.46/0.68          | (v1_xboole_0 @ sk_A_1))),
% 0.46/0.68      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.46/0.68  thf('49', plain, (~ (v1_xboole_0 @ sk_A_1)),
% 0.46/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.68  thf('50', plain,
% 0.46/0.68      (![X0 : $i]:
% 0.46/0.68         (~ (m1_subset_1 @ X0 @ sk_A_1)
% 0.46/0.68          | ((k3_funct_2 @ sk_A_1 @ sk_B_1 @ sk_C @ X0)
% 0.46/0.68              = (k1_funct_1 @ sk_C @ X0)))),
% 0.46/0.68      inference('clc', [status(thm)], ['48', '49'])).
% 0.46/0.68  thf('51', plain,
% 0.46/0.68      (((k3_funct_2 @ sk_A_1 @ sk_B_1 @ sk_C @ sk_D)
% 0.46/0.68         = (k1_funct_1 @ sk_C @ sk_D))),
% 0.46/0.68      inference('sup-', [status(thm)], ['42', '50'])).
% 0.46/0.68  thf('52', plain,
% 0.46/0.68      (((k7_partfun1 @ sk_B_1 @ sk_C @ sk_D) != (k1_funct_1 @ sk_C @ sk_D))),
% 0.46/0.68      inference('demod', [status(thm)], ['41', '51'])).
% 0.46/0.68  thf('53', plain, ($false),
% 0.46/0.68      inference('simplify_reflect-', [status(thm)], ['40', '52'])).
% 0.46/0.68  
% 0.46/0.68  % SZS output end Refutation
% 0.46/0.68  
% 0.56/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
