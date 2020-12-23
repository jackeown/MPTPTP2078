%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WPngfOV4w8

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:51 EST 2020

% Result     : Theorem 1.14s
% Output     : Refutation 1.14s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 126 expanded)
%              Number of leaves         :   41 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :  658 (1478 expanded)
%              Number of equality atoms :   36 (  64 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

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
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v5_relat_1 @ X18 @ X20 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v5_relat_1 @ sk_C @ sk_B_1 ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('4',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('5',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(clc,[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
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
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ( X26
        = ( k1_relset_1 @ X26 @ X27 @ X28 ) )
      | ~ ( zip_tseitin_1 @ X28 @ X27 @ X26 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('10',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('12',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('13',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['10','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('16',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ~ ( zip_tseitin_0 @ X29 @ X30 )
      | ( zip_tseitin_1 @ X31 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('17',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X24: $i,X25: $i] :
      ( ( zip_tseitin_0 @ X24 @ X25 )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('19',plain,(
    ! [X4: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['18','19'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('21',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ X1 @ X2 )
      | ( r1_tarski @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('23',plain,(
    ! [X3: $i] :
      ( m1_subset_1 @ ( sk_B @ X3 ) @ X3 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf('24',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r2_hidden @ X5 @ X6 )
      | ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('26',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( r1_tarski @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_B_1 @ X0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ),
    inference(demod,[status(thm)],['17','30'])).

thf('32',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['14','31'])).

thf(d8_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A )
        & ( v1_funct_1 @ B ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) )
         => ( ( k7_partfun1 @ A @ B @ C )
            = ( k1_funct_1 @ B @ C ) ) ) ) )).

thf('33',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X32 @ ( k1_relat_1 @ X33 ) )
      | ( ( k7_partfun1 @ X34 @ X33 @ X32 )
        = ( k1_funct_1 @ X33 @ X32 ) )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( v5_relat_1 @ X33 @ X34 )
      | ~ ( v1_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d8_partfun1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_C )
      | ~ ( v5_relat_1 @ sk_C @ X1 )
      | ~ ( v1_funct_1 @ sk_C )
      | ( ( k7_partfun1 @ X1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('36',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('37',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_A )
      | ~ ( v5_relat_1 @ sk_C @ X1 )
      | ( ( k7_partfun1 @ X1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) ) ) ),
    inference(demod,[status(thm)],['34','37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( ( k7_partfun1 @ X0 @ sk_C @ sk_D )
        = ( k1_funct_1 @ sk_C @ sk_D ) )
      | ~ ( v5_relat_1 @ sk_C @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','39'])).

thf('41',plain,
    ( ( k7_partfun1 @ sk_B_1 @ sk_C @ sk_D )
    = ( k1_funct_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['2','40'])).

thf('42',plain,(
    ( k7_partfun1 @ sk_B_1 @ sk_C @ sk_D )
 != ( k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
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

thf('45',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( v1_funct_1 @ X35 )
      | ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X38 @ X36 )
      | ( ( k3_funct_2 @ X36 @ X37 @ X35 @ X38 )
        = ( k1_funct_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_C )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ X0 )
        = ( k1_funct_1 @ sk_C @ X0 ) ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ sk_D )
    = ( k1_funct_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['43','51'])).

thf('53',plain,(
    ( k7_partfun1 @ sk_B_1 @ sk_C @ sk_D )
 != ( k1_funct_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['42','52'])).

thf('54',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['41','53'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.WPngfOV4w8
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:52:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 1.14/1.32  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.14/1.32  % Solved by: fo/fo7.sh
% 1.14/1.32  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.14/1.32  % done 620 iterations in 0.869s
% 1.14/1.32  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.14/1.32  % SZS output start Refutation
% 1.14/1.32  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.14/1.32  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.14/1.32  thf(sk_D_type, type, sk_D: $i).
% 1.14/1.32  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.14/1.32  thf(sk_C_type, type, sk_C: $i).
% 1.14/1.32  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.14/1.32  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 1.14/1.32  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.14/1.32  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.14/1.32  thf(sk_B_1_type, type, sk_B_1: $i).
% 1.14/1.32  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.14/1.32  thf(sk_A_type, type, sk_A: $i).
% 1.14/1.32  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.14/1.32  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.14/1.32  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 1.14/1.32  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.14/1.32  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 1.14/1.32  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 1.14/1.32  thf(sk_B_type, type, sk_B: $i > $i).
% 1.14/1.32  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 1.14/1.32  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 1.14/1.32  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.14/1.32  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 1.14/1.32  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.14/1.32  thf(t176_funct_2, conjecture,
% 1.14/1.32    (![A:$i]:
% 1.14/1.32     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.14/1.32       ( ![B:$i]:
% 1.14/1.32         ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.14/1.32           ( ![C:$i]:
% 1.14/1.32             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.14/1.32                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.14/1.32               ( ![D:$i]:
% 1.14/1.32                 ( ( m1_subset_1 @ D @ A ) =>
% 1.14/1.32                   ( ( k7_partfun1 @ B @ C @ D ) =
% 1.14/1.32                     ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ))).
% 1.14/1.32  thf(zf_stmt_0, negated_conjecture,
% 1.14/1.32    (~( ![A:$i]:
% 1.14/1.32        ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.14/1.32          ( ![B:$i]:
% 1.14/1.32            ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.14/1.32              ( ![C:$i]:
% 1.14/1.32                ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.14/1.32                    ( m1_subset_1 @
% 1.14/1.32                      C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.14/1.32                  ( ![D:$i]:
% 1.14/1.32                    ( ( m1_subset_1 @ D @ A ) =>
% 1.14/1.32                      ( ( k7_partfun1 @ B @ C @ D ) =
% 1.14/1.32                        ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ) )),
% 1.14/1.32    inference('cnf.neg', [status(esa)], [t176_funct_2])).
% 1.14/1.32  thf('0', plain,
% 1.14/1.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf(cc2_relset_1, axiom,
% 1.14/1.32    (![A:$i,B:$i,C:$i]:
% 1.14/1.32     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.14/1.32       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.14/1.32  thf('1', plain,
% 1.14/1.32      (![X18 : $i, X19 : $i, X20 : $i]:
% 1.14/1.32         ((v5_relat_1 @ X18 @ X20)
% 1.14/1.32          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 1.14/1.32      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.14/1.32  thf('2', plain, ((v5_relat_1 @ sk_C @ sk_B_1)),
% 1.14/1.32      inference('sup-', [status(thm)], ['0', '1'])).
% 1.14/1.32  thf('3', plain, ((m1_subset_1 @ sk_D @ sk_A)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf(t2_subset, axiom,
% 1.14/1.32    (![A:$i,B:$i]:
% 1.14/1.32     ( ( m1_subset_1 @ A @ B ) =>
% 1.14/1.32       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 1.14/1.32  thf('4', plain,
% 1.14/1.32      (![X5 : $i, X6 : $i]:
% 1.14/1.32         ((r2_hidden @ X5 @ X6)
% 1.14/1.32          | (v1_xboole_0 @ X6)
% 1.14/1.32          | ~ (m1_subset_1 @ X5 @ X6))),
% 1.14/1.32      inference('cnf', [status(esa)], [t2_subset])).
% 1.14/1.32  thf('5', plain, (((v1_xboole_0 @ sk_A) | (r2_hidden @ sk_D @ sk_A))),
% 1.14/1.32      inference('sup-', [status(thm)], ['3', '4'])).
% 1.14/1.32  thf('6', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('7', plain, ((r2_hidden @ sk_D @ sk_A)),
% 1.14/1.32      inference('clc', [status(thm)], ['5', '6'])).
% 1.14/1.32  thf('8', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf(d1_funct_2, axiom,
% 1.14/1.32    (![A:$i,B:$i,C:$i]:
% 1.14/1.32     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.14/1.32       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.14/1.32           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 1.14/1.32             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 1.14/1.32         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.14/1.32           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 1.14/1.32             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 1.14/1.32  thf(zf_stmt_1, axiom,
% 1.14/1.32    (![C:$i,B:$i,A:$i]:
% 1.14/1.32     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 1.14/1.32       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 1.14/1.32  thf('9', plain,
% 1.14/1.32      (![X26 : $i, X27 : $i, X28 : $i]:
% 1.14/1.32         (~ (v1_funct_2 @ X28 @ X26 @ X27)
% 1.14/1.32          | ((X26) = (k1_relset_1 @ X26 @ X27 @ X28))
% 1.14/1.32          | ~ (zip_tseitin_1 @ X28 @ X27 @ X26))),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_1])).
% 1.14/1.32  thf('10', plain,
% 1.14/1.32      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 1.14/1.32        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 1.14/1.32      inference('sup-', [status(thm)], ['8', '9'])).
% 1.14/1.32  thf('11', plain,
% 1.14/1.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf(redefinition_k1_relset_1, axiom,
% 1.14/1.32    (![A:$i,B:$i,C:$i]:
% 1.14/1.32     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.14/1.32       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 1.14/1.32  thf('12', plain,
% 1.14/1.32      (![X21 : $i, X22 : $i, X23 : $i]:
% 1.14/1.32         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 1.14/1.32          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 1.14/1.32      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 1.14/1.32  thf('13', plain,
% 1.14/1.32      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 1.14/1.32      inference('sup-', [status(thm)], ['11', '12'])).
% 1.14/1.32  thf('14', plain,
% 1.14/1.32      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 1.14/1.32        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 1.14/1.32      inference('demod', [status(thm)], ['10', '13'])).
% 1.14/1.32  thf('15', plain,
% 1.14/1.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 1.14/1.32  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 1.14/1.32  thf(zf_stmt_4, axiom,
% 1.14/1.32    (![B:$i,A:$i]:
% 1.14/1.32     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 1.14/1.32       ( zip_tseitin_0 @ B @ A ) ))).
% 1.14/1.32  thf(zf_stmt_5, axiom,
% 1.14/1.32    (![A:$i,B:$i,C:$i]:
% 1.14/1.32     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.14/1.32       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 1.14/1.32         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 1.14/1.32           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 1.14/1.32             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 1.14/1.32  thf('16', plain,
% 1.14/1.32      (![X29 : $i, X30 : $i, X31 : $i]:
% 1.14/1.32         (~ (zip_tseitin_0 @ X29 @ X30)
% 1.14/1.32          | (zip_tseitin_1 @ X31 @ X29 @ X30)
% 1.14/1.32          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X29))))),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_5])).
% 1.14/1.32  thf('17', plain,
% 1.14/1.32      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 1.14/1.32        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 1.14/1.32      inference('sup-', [status(thm)], ['15', '16'])).
% 1.14/1.32  thf('18', plain,
% 1.14/1.32      (![X24 : $i, X25 : $i]:
% 1.14/1.32         ((zip_tseitin_0 @ X24 @ X25) | ((X24) = (k1_xboole_0)))),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_4])).
% 1.14/1.32  thf(t4_subset_1, axiom,
% 1.14/1.32    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 1.14/1.32  thf('19', plain,
% 1.14/1.32      (![X4 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X4))),
% 1.14/1.32      inference('cnf', [status(esa)], [t4_subset_1])).
% 1.14/1.32  thf('20', plain,
% 1.14/1.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.14/1.32         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)) | (zip_tseitin_0 @ X0 @ X2))),
% 1.14/1.32      inference('sup+', [status(thm)], ['18', '19'])).
% 1.14/1.32  thf(t3_subset, axiom,
% 1.14/1.32    (![A:$i,B:$i]:
% 1.14/1.32     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 1.14/1.32  thf('21', plain,
% 1.14/1.32      (![X7 : $i, X8 : $i]:
% 1.14/1.32         ((r1_tarski @ X7 @ X8) | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 1.14/1.32      inference('cnf', [status(esa)], [t3_subset])).
% 1.14/1.32  thf('22', plain,
% 1.14/1.32      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.14/1.32         ((zip_tseitin_0 @ X1 @ X2) | (r1_tarski @ X1 @ X0))),
% 1.14/1.32      inference('sup-', [status(thm)], ['20', '21'])).
% 1.14/1.32  thf(existence_m1_subset_1, axiom,
% 1.14/1.32    (![A:$i]: ( ?[B:$i]: ( m1_subset_1 @ B @ A ) ))).
% 1.14/1.32  thf('23', plain, (![X3 : $i]: (m1_subset_1 @ (sk_B @ X3) @ X3)),
% 1.14/1.32      inference('cnf', [status(esa)], [existence_m1_subset_1])).
% 1.14/1.32  thf('24', plain,
% 1.14/1.32      (![X5 : $i, X6 : $i]:
% 1.14/1.32         ((r2_hidden @ X5 @ X6)
% 1.14/1.32          | (v1_xboole_0 @ X6)
% 1.14/1.32          | ~ (m1_subset_1 @ X5 @ X6))),
% 1.14/1.32      inference('cnf', [status(esa)], [t2_subset])).
% 1.14/1.32  thf('25', plain,
% 1.14/1.32      (![X0 : $i]: ((v1_xboole_0 @ X0) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 1.14/1.32      inference('sup-', [status(thm)], ['23', '24'])).
% 1.14/1.32  thf(t7_ordinal1, axiom,
% 1.14/1.32    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 1.14/1.32  thf('26', plain,
% 1.14/1.32      (![X13 : $i, X14 : $i]:
% 1.14/1.32         (~ (r2_hidden @ X13 @ X14) | ~ (r1_tarski @ X14 @ X13))),
% 1.14/1.32      inference('cnf', [status(esa)], [t7_ordinal1])).
% 1.14/1.32  thf('27', plain,
% 1.14/1.32      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 1.14/1.32      inference('sup-', [status(thm)], ['25', '26'])).
% 1.14/1.32  thf('28', plain,
% 1.14/1.32      (![X0 : $i, X1 : $i]: ((zip_tseitin_0 @ X0 @ X1) | (v1_xboole_0 @ X0))),
% 1.14/1.32      inference('sup-', [status(thm)], ['22', '27'])).
% 1.14/1.32  thf('29', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('30', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_B_1 @ X0)),
% 1.14/1.32      inference('sup-', [status(thm)], ['28', '29'])).
% 1.14/1.32  thf('31', plain, ((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)),
% 1.14/1.32      inference('demod', [status(thm)], ['17', '30'])).
% 1.14/1.32  thf('32', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 1.14/1.32      inference('demod', [status(thm)], ['14', '31'])).
% 1.14/1.32  thf(d8_partfun1, axiom,
% 1.14/1.32    (![A:$i,B:$i]:
% 1.14/1.32     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) & ( v1_funct_1 @ B ) ) =>
% 1.14/1.32       ( ![C:$i]:
% 1.14/1.32         ( ( r2_hidden @ C @ ( k1_relat_1 @ B ) ) =>
% 1.14/1.32           ( ( k7_partfun1 @ A @ B @ C ) = ( k1_funct_1 @ B @ C ) ) ) ) ))).
% 1.14/1.32  thf('33', plain,
% 1.14/1.32      (![X32 : $i, X33 : $i, X34 : $i]:
% 1.14/1.32         (~ (r2_hidden @ X32 @ (k1_relat_1 @ X33))
% 1.14/1.32          | ((k7_partfun1 @ X34 @ X33 @ X32) = (k1_funct_1 @ X33 @ X32))
% 1.14/1.32          | ~ (v1_funct_1 @ X33)
% 1.14/1.32          | ~ (v5_relat_1 @ X33 @ X34)
% 1.14/1.32          | ~ (v1_relat_1 @ X33))),
% 1.14/1.32      inference('cnf', [status(esa)], [d8_partfun1])).
% 1.14/1.32  thf('34', plain,
% 1.14/1.32      (![X0 : $i, X1 : $i]:
% 1.14/1.32         (~ (r2_hidden @ X0 @ sk_A)
% 1.14/1.32          | ~ (v1_relat_1 @ sk_C)
% 1.14/1.32          | ~ (v5_relat_1 @ sk_C @ X1)
% 1.14/1.32          | ~ (v1_funct_1 @ sk_C)
% 1.14/1.32          | ((k7_partfun1 @ X1 @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0)))),
% 1.14/1.32      inference('sup-', [status(thm)], ['32', '33'])).
% 1.14/1.32  thf('35', plain,
% 1.14/1.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf(cc1_relset_1, axiom,
% 1.14/1.32    (![A:$i,B:$i,C:$i]:
% 1.14/1.32     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.14/1.32       ( v1_relat_1 @ C ) ))).
% 1.14/1.32  thf('36', plain,
% 1.14/1.32      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.14/1.32         ((v1_relat_1 @ X15)
% 1.14/1.32          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.14/1.32      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.14/1.32  thf('37', plain, ((v1_relat_1 @ sk_C)),
% 1.14/1.32      inference('sup-', [status(thm)], ['35', '36'])).
% 1.14/1.32  thf('38', plain, ((v1_funct_1 @ sk_C)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('39', plain,
% 1.14/1.32      (![X0 : $i, X1 : $i]:
% 1.14/1.32         (~ (r2_hidden @ X0 @ sk_A)
% 1.14/1.32          | ~ (v5_relat_1 @ sk_C @ X1)
% 1.14/1.32          | ((k7_partfun1 @ X1 @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0)))),
% 1.14/1.32      inference('demod', [status(thm)], ['34', '37', '38'])).
% 1.14/1.32  thf('40', plain,
% 1.14/1.32      (![X0 : $i]:
% 1.14/1.32         (((k7_partfun1 @ X0 @ sk_C @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))
% 1.14/1.32          | ~ (v5_relat_1 @ sk_C @ X0))),
% 1.14/1.32      inference('sup-', [status(thm)], ['7', '39'])).
% 1.14/1.32  thf('41', plain,
% 1.14/1.32      (((k7_partfun1 @ sk_B_1 @ sk_C @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))),
% 1.14/1.32      inference('sup-', [status(thm)], ['2', '40'])).
% 1.14/1.32  thf('42', plain,
% 1.14/1.32      (((k7_partfun1 @ sk_B_1 @ sk_C @ sk_D)
% 1.14/1.32         != (k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ sk_D))),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('43', plain, ((m1_subset_1 @ sk_D @ sk_A)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('44', plain,
% 1.14/1.32      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf(redefinition_k3_funct_2, axiom,
% 1.14/1.32    (![A:$i,B:$i,C:$i,D:$i]:
% 1.14/1.32     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 1.14/1.32         ( v1_funct_2 @ C @ A @ B ) & 
% 1.14/1.32         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.14/1.32         ( m1_subset_1 @ D @ A ) ) =>
% 1.14/1.32       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 1.14/1.32  thf('45', plain,
% 1.14/1.32      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.14/1.32         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 1.14/1.32          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 1.14/1.32          | ~ (v1_funct_1 @ X35)
% 1.14/1.32          | (v1_xboole_0 @ X36)
% 1.14/1.32          | ~ (m1_subset_1 @ X38 @ X36)
% 1.14/1.32          | ((k3_funct_2 @ X36 @ X37 @ X35 @ X38) = (k1_funct_1 @ X35 @ X38)))),
% 1.14/1.32      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 1.14/1.32  thf('46', plain,
% 1.14/1.32      (![X0 : $i]:
% 1.14/1.32         (((k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0))
% 1.14/1.32          | ~ (m1_subset_1 @ X0 @ sk_A)
% 1.14/1.32          | (v1_xboole_0 @ sk_A)
% 1.14/1.32          | ~ (v1_funct_1 @ sk_C)
% 1.14/1.32          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1))),
% 1.14/1.32      inference('sup-', [status(thm)], ['44', '45'])).
% 1.14/1.32  thf('47', plain, ((v1_funct_1 @ sk_C)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('48', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('49', plain,
% 1.14/1.32      (![X0 : $i]:
% 1.14/1.32         (((k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ X0) = (k1_funct_1 @ sk_C @ X0))
% 1.14/1.32          | ~ (m1_subset_1 @ X0 @ sk_A)
% 1.14/1.32          | (v1_xboole_0 @ sk_A))),
% 1.14/1.32      inference('demod', [status(thm)], ['46', '47', '48'])).
% 1.14/1.32  thf('50', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.14/1.32      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.14/1.32  thf('51', plain,
% 1.14/1.32      (![X0 : $i]:
% 1.14/1.32         (~ (m1_subset_1 @ X0 @ sk_A)
% 1.14/1.32          | ((k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ X0)
% 1.14/1.32              = (k1_funct_1 @ sk_C @ X0)))),
% 1.14/1.32      inference('clc', [status(thm)], ['49', '50'])).
% 1.14/1.32  thf('52', plain,
% 1.14/1.32      (((k3_funct_2 @ sk_A @ sk_B_1 @ sk_C @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))),
% 1.14/1.32      inference('sup-', [status(thm)], ['43', '51'])).
% 1.14/1.32  thf('53', plain,
% 1.14/1.32      (((k7_partfun1 @ sk_B_1 @ sk_C @ sk_D) != (k1_funct_1 @ sk_C @ sk_D))),
% 1.14/1.32      inference('demod', [status(thm)], ['42', '52'])).
% 1.14/1.32  thf('54', plain, ($false),
% 1.14/1.32      inference('simplify_reflect-', [status(thm)], ['41', '53'])).
% 1.14/1.32  
% 1.14/1.32  % SZS output end Refutation
% 1.14/1.32  
% 1.14/1.33  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
