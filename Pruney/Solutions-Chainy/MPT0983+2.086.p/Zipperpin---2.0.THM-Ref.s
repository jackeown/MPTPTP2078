%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EblBxFuy4w

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:14 EST 2020

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 292 expanded)
%              Number of leaves         :   42 ( 103 expanded)
%              Depth                    :   20
%              Number of atoms          : 1120 (5455 expanded)
%              Number of equality atoms :   37 (  69 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(t29_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
           => ( ( v2_funct_1 @ C )
              & ( v2_funct_2 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
             => ( ( v2_funct_1 @ C )
                & ( v2_funct_2 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t29_funct_2])).

thf('0',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('3',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('4',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('7',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['5','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( X20 = X23 )
      | ~ ( r2_relset_1 @ X21 @ X22 @ X20 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['4','15'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('17',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('18',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('19',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t26_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ B @ C )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) )
           => ( ( ( C = k1_xboole_0 )
                & ( B != k1_xboole_0 ) )
              | ( v2_funct_1 @ D ) ) ) ) ) )).

thf('22',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X41 @ X39 @ X39 @ X40 @ X42 @ X38 ) )
      | ( v2_funct_1 @ X42 )
      | ( X40 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X42 @ X41 @ X39 )
      | ~ ( v1_funct_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['20','26'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('28',plain,(
    ! [X10: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('29',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('30',plain,(
    ! [X10: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X10 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['27','30','31','32','33'])).

thf('35',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('36',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('37',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X4 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('38',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('39',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( v1_xboole_0 @ X8 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ~ ( r2_hidden @ X0 @ sk_C ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['36','41'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('44',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['3','44'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('46',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('47',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('48',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('49',plain,(
    ! [X33: $i] :
      ( ( k6_partfun1 @ X33 )
      = ( k6_relat_1 @ X33 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('50',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X10: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X10 ) ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('52',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['50','51'])).

thf('53',plain,(
    v2_funct_1 @ sk_C ),
    inference(demod,[status(thm)],['2','47','52'])).

thf('54',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('55',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['53','54'])).

thf('56',plain,(
    ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['1','55'])).

thf('57',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['16','19'])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t24_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( r2_relset_1 @ B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ ( k6_partfun1 @ B ) )
           => ( ( k2_relset_1 @ A @ B @ C )
              = B ) ) ) ) )).

thf('59',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( r2_relset_1 @ X35 @ X35 @ ( k1_partfun1 @ X35 @ X36 @ X36 @ X35 @ X34 @ X37 ) @ ( k6_partfun1 @ X35 ) )
      | ( ( k2_relset_1 @ X36 @ X35 @ X37 )
        = X35 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X37 @ X36 @ X35 )
      | ~ ( v1_funct_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['60','61','62'])).

thf('64',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['57','63'])).

thf('65',plain,(
    ! [X24: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X24 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('66',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ( r2_relset_1 @ X21 @ X22 @ X20 @ X23 )
      | ( X20 != X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('67',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( r2_relset_1 @ X21 @ X22 @ X23 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('70',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( ( k2_relset_1 @ X18 @ X19 @ X17 )
        = ( k2_relat_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('71',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['64','68','71','72','73','74'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('76',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k2_relat_1 @ X26 )
       != X25 )
      | ( v2_funct_2 @ X26 @ X25 )
      | ~ ( v5_relat_1 @ X26 @ X25 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('77',plain,(
    ! [X26: $i] :
      ( ~ ( v1_relat_1 @ X26 )
      | ~ ( v5_relat_1 @ X26 @ ( k2_relat_1 @ X26 ) )
      | ( v2_funct_2 @ X26 @ ( k2_relat_1 @ X26 ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['75','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('80',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v5_relat_1 @ X14 @ X16 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('81',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['64','68','71','72','73','74'])).

thf('83',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('84',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('85',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['78','81','82','85'])).

thf('87',plain,(
    $false ),
    inference(demod,[status(thm)],['56','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EblBxFuy4w
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:02:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.71/0.89  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.71/0.89  % Solved by: fo/fo7.sh
% 0.71/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.71/0.89  % done 818 iterations in 0.405s
% 0.71/0.89  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.71/0.89  % SZS output start Refutation
% 0.71/0.89  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.71/0.89  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.71/0.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.71/0.89  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.71/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.71/0.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.71/0.89  thf(sk_D_type, type, sk_D: $i).
% 0.71/0.89  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.71/0.89  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.71/0.89  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.71/0.89  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.71/0.89  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.71/0.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.71/0.89  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.71/0.89  thf(sk_C_type, type, sk_C: $i).
% 0.71/0.89  thf(sk_B_type, type, sk_B: $i > $i).
% 0.71/0.89  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.71/0.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.71/0.89  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.71/0.89  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.71/0.89  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.71/0.89  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.71/0.89  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.71/0.89  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.71/0.89  thf(t29_funct_2, conjecture,
% 0.71/0.89    (![A:$i,B:$i,C:$i]:
% 0.71/0.89     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.71/0.89         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.71/0.89       ( ![D:$i]:
% 0.71/0.89         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.71/0.89             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.71/0.89           ( ( r2_relset_1 @
% 0.71/0.89               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.71/0.89               ( k6_partfun1 @ A ) ) =>
% 0.71/0.89             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 0.71/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.71/0.89    (~( ![A:$i,B:$i,C:$i]:
% 0.71/0.89        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.71/0.89            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.71/0.89          ( ![D:$i]:
% 0.71/0.89            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.71/0.89                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.71/0.89              ( ( r2_relset_1 @
% 0.71/0.89                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.71/0.89                  ( k6_partfun1 @ A ) ) =>
% 0.71/0.89                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 0.71/0.89    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 0.71/0.89  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('1', plain,
% 0.71/0.89      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 0.71/0.89      inference('split', [status(esa)], ['0'])).
% 0.71/0.89  thf('2', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.71/0.89      inference('split', [status(esa)], ['0'])).
% 0.71/0.89  thf(d1_xboole_0, axiom,
% 0.71/0.89    (![A:$i]:
% 0.71/0.89     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.71/0.89  thf('3', plain,
% 0.71/0.89      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.71/0.89      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.71/0.89  thf('4', plain,
% 0.71/0.89      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.71/0.89        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.71/0.89        (k6_partfun1 @ sk_A))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('5', plain,
% 0.71/0.89      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('6', plain,
% 0.71/0.89      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf(dt_k1_partfun1, axiom,
% 0.71/0.89    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.71/0.89     ( ( ( v1_funct_1 @ E ) & 
% 0.71/0.89         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.71/0.89         ( v1_funct_1 @ F ) & 
% 0.71/0.89         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.71/0.89       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.71/0.89         ( m1_subset_1 @
% 0.71/0.89           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.71/0.89           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.71/0.89  thf('7', plain,
% 0.71/0.89      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i]:
% 0.71/0.89         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.71/0.89          | ~ (v1_funct_1 @ X27)
% 0.71/0.89          | ~ (v1_funct_1 @ X30)
% 0.71/0.89          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.71/0.89          | (m1_subset_1 @ (k1_partfun1 @ X28 @ X29 @ X31 @ X32 @ X27 @ X30) @ 
% 0.71/0.89             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X32))))),
% 0.71/0.89      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.71/0.89  thf('8', plain,
% 0.71/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.89         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 0.71/0.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.71/0.89          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.71/0.89          | ~ (v1_funct_1 @ X1)
% 0.71/0.89          | ~ (v1_funct_1 @ sk_C))),
% 0.71/0.89      inference('sup-', [status(thm)], ['6', '7'])).
% 0.71/0.89  thf('9', plain, ((v1_funct_1 @ sk_C)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('10', plain,
% 0.71/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.71/0.89         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 0.71/0.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.71/0.89          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.71/0.89          | ~ (v1_funct_1 @ X1))),
% 0.71/0.89      inference('demod', [status(thm)], ['8', '9'])).
% 0.71/0.89  thf('11', plain,
% 0.71/0.89      ((~ (v1_funct_1 @ sk_D)
% 0.71/0.89        | (m1_subset_1 @ 
% 0.71/0.89           (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.71/0.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.71/0.89      inference('sup-', [status(thm)], ['5', '10'])).
% 0.71/0.89  thf('12', plain, ((v1_funct_1 @ sk_D)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('13', plain,
% 0.71/0.89      ((m1_subset_1 @ 
% 0.71/0.89        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.71/0.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.71/0.89      inference('demod', [status(thm)], ['11', '12'])).
% 0.71/0.89  thf(redefinition_r2_relset_1, axiom,
% 0.71/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.89     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.71/0.89         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.71/0.89       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.71/0.89  thf('14', plain,
% 0.71/0.89      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.71/0.89         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.71/0.89          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.71/0.89          | ((X20) = (X23))
% 0.71/0.89          | ~ (r2_relset_1 @ X21 @ X22 @ X20 @ X23))),
% 0.71/0.89      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.71/0.89  thf('15', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.71/0.89             (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ X0)
% 0.71/0.89          | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) = (X0))
% 0.71/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.71/0.89      inference('sup-', [status(thm)], ['13', '14'])).
% 0.71/0.89  thf('16', plain,
% 0.71/0.89      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.71/0.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.71/0.89        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 0.71/0.89            = (k6_partfun1 @ sk_A)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['4', '15'])).
% 0.71/0.89  thf(t29_relset_1, axiom,
% 0.71/0.89    (![A:$i]:
% 0.71/0.89     ( m1_subset_1 @
% 0.71/0.89       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.71/0.89  thf('17', plain,
% 0.71/0.89      (![X24 : $i]:
% 0.71/0.89         (m1_subset_1 @ (k6_relat_1 @ X24) @ 
% 0.71/0.89          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))),
% 0.71/0.89      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.71/0.89  thf(redefinition_k6_partfun1, axiom,
% 0.71/0.89    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.71/0.89  thf('18', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.71/0.89      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.71/0.89  thf('19', plain,
% 0.71/0.89      (![X24 : $i]:
% 0.71/0.89         (m1_subset_1 @ (k6_partfun1 @ X24) @ 
% 0.71/0.89          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))),
% 0.71/0.89      inference('demod', [status(thm)], ['17', '18'])).
% 0.71/0.89  thf('20', plain,
% 0.71/0.89      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 0.71/0.89         = (k6_partfun1 @ sk_A))),
% 0.71/0.89      inference('demod', [status(thm)], ['16', '19'])).
% 0.71/0.89  thf('21', plain,
% 0.71/0.89      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf(t26_funct_2, axiom,
% 0.71/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.89     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.71/0.89         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.71/0.89       ( ![E:$i]:
% 0.71/0.89         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.71/0.89             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.71/0.89           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 0.71/0.89             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 0.71/0.89               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 0.71/0.89  thf('22', plain,
% 0.71/0.89      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.71/0.89         (~ (v1_funct_1 @ X38)
% 0.71/0.89          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 0.71/0.89          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.71/0.89          | ~ (v2_funct_1 @ (k1_partfun1 @ X41 @ X39 @ X39 @ X40 @ X42 @ X38))
% 0.71/0.89          | (v2_funct_1 @ X42)
% 0.71/0.89          | ((X40) = (k1_xboole_0))
% 0.71/0.89          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X39)))
% 0.71/0.89          | ~ (v1_funct_2 @ X42 @ X41 @ X39)
% 0.71/0.89          | ~ (v1_funct_1 @ X42))),
% 0.71/0.89      inference('cnf', [status(esa)], [t26_funct_2])).
% 0.71/0.89  thf('23', plain,
% 0.71/0.89      (![X0 : $i, X1 : $i]:
% 0.71/0.89         (~ (v1_funct_1 @ X0)
% 0.71/0.89          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 0.71/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 0.71/0.89          | ((sk_A) = (k1_xboole_0))
% 0.71/0.89          | (v2_funct_1 @ X0)
% 0.71/0.89          | ~ (v2_funct_1 @ 
% 0.71/0.89               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D))
% 0.71/0.89          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 0.71/0.89          | ~ (v1_funct_1 @ sk_D))),
% 0.71/0.89      inference('sup-', [status(thm)], ['21', '22'])).
% 0.71/0.89  thf('24', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('25', plain, ((v1_funct_1 @ sk_D)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('26', plain,
% 0.71/0.89      (![X0 : $i, X1 : $i]:
% 0.71/0.89         (~ (v1_funct_1 @ X0)
% 0.71/0.89          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 0.71/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 0.71/0.89          | ((sk_A) = (k1_xboole_0))
% 0.71/0.89          | (v2_funct_1 @ X0)
% 0.71/0.89          | ~ (v2_funct_1 @ 
% 0.71/0.89               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D)))),
% 0.71/0.89      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.71/0.89  thf('27', plain,
% 0.71/0.89      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.71/0.89        | (v2_funct_1 @ sk_C)
% 0.71/0.89        | ((sk_A) = (k1_xboole_0))
% 0.71/0.89        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.71/0.89        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 0.71/0.89        | ~ (v1_funct_1 @ sk_C))),
% 0.71/0.89      inference('sup-', [status(thm)], ['20', '26'])).
% 0.71/0.89  thf(fc4_funct_1, axiom,
% 0.71/0.89    (![A:$i]:
% 0.71/0.89     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.71/0.89       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.71/0.89  thf('28', plain, (![X10 : $i]: (v2_funct_1 @ (k6_relat_1 @ X10))),
% 0.71/0.89      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.71/0.89  thf('29', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.71/0.89      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.71/0.89  thf('30', plain, (![X10 : $i]: (v2_funct_1 @ (k6_partfun1 @ X10))),
% 0.71/0.89      inference('demod', [status(thm)], ['28', '29'])).
% 0.71/0.89  thf('31', plain,
% 0.71/0.89      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('32', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('33', plain, ((v1_funct_1 @ sk_C)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('34', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.71/0.89      inference('demod', [status(thm)], ['27', '30', '31', '32', '33'])).
% 0.71/0.89  thf('35', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.71/0.89      inference('split', [status(esa)], ['0'])).
% 0.71/0.89  thf('36', plain, ((((sk_A) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['34', '35'])).
% 0.71/0.89  thf(fc4_zfmisc_1, axiom,
% 0.71/0.89    (![A:$i,B:$i]:
% 0.71/0.89     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.71/0.89  thf('37', plain,
% 0.71/0.89      (![X4 : $i, X5 : $i]:
% 0.71/0.89         (~ (v1_xboole_0 @ X4) | (v1_xboole_0 @ (k2_zfmisc_1 @ X4 @ X5)))),
% 0.71/0.89      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 0.71/0.89  thf('38', plain,
% 0.71/0.89      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf(t5_subset, axiom,
% 0.71/0.89    (![A:$i,B:$i,C:$i]:
% 0.71/0.89     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.71/0.89          ( v1_xboole_0 @ C ) ) ))).
% 0.71/0.89  thf('39', plain,
% 0.71/0.89      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.71/0.89         (~ (r2_hidden @ X6 @ X7)
% 0.71/0.89          | ~ (v1_xboole_0 @ X8)
% 0.71/0.89          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.71/0.89      inference('cnf', [status(esa)], [t5_subset])).
% 0.71/0.89  thf('40', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.71/0.89          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.71/0.89      inference('sup-', [status(thm)], ['38', '39'])).
% 0.71/0.89  thf('41', plain,
% 0.71/0.89      (![X0 : $i]: (~ (v1_xboole_0 @ sk_A) | ~ (r2_hidden @ X0 @ sk_C))),
% 0.71/0.89      inference('sup-', [status(thm)], ['37', '40'])).
% 0.71/0.89  thf('42', plain,
% 0.71/0.89      ((![X0 : $i]: (~ (v1_xboole_0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_C)))
% 0.71/0.89         <= (~ ((v2_funct_1 @ sk_C)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['36', '41'])).
% 0.71/0.89  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.71/0.89  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.71/0.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.71/0.89  thf('44', plain,
% 0.71/0.89      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.71/0.89      inference('demod', [status(thm)], ['42', '43'])).
% 0.71/0.89  thf('45', plain, (((v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['3', '44'])).
% 0.71/0.89  thf(l13_xboole_0, axiom,
% 0.71/0.89    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.71/0.89  thf('46', plain,
% 0.71/0.89      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.71/0.89      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.71/0.89  thf('47', plain, ((((sk_C) = (k1_xboole_0))) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.71/0.89      inference('sup-', [status(thm)], ['45', '46'])).
% 0.71/0.89  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.71/0.89  thf('48', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.71/0.89      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.71/0.89  thf('49', plain, (![X33 : $i]: ((k6_partfun1 @ X33) = (k6_relat_1 @ X33))),
% 0.71/0.89      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.71/0.89  thf('50', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.71/0.89      inference('demod', [status(thm)], ['48', '49'])).
% 0.71/0.89  thf('51', plain, (![X10 : $i]: (v2_funct_1 @ (k6_partfun1 @ X10))),
% 0.71/0.89      inference('demod', [status(thm)], ['28', '29'])).
% 0.71/0.89  thf('52', plain, ((v2_funct_1 @ k1_xboole_0)),
% 0.71/0.89      inference('sup+', [status(thm)], ['50', '51'])).
% 0.71/0.89  thf('53', plain, (((v2_funct_1 @ sk_C))),
% 0.71/0.89      inference('demod', [status(thm)], ['2', '47', '52'])).
% 0.71/0.89  thf('54', plain, (~ ((v2_funct_2 @ sk_D @ sk_A)) | ~ ((v2_funct_1 @ sk_C))),
% 0.71/0.89      inference('split', [status(esa)], ['0'])).
% 0.71/0.89  thf('55', plain, (~ ((v2_funct_2 @ sk_D @ sk_A))),
% 0.71/0.89      inference('sat_resolution*', [status(thm)], ['53', '54'])).
% 0.71/0.89  thf('56', plain, (~ (v2_funct_2 @ sk_D @ sk_A)),
% 0.71/0.89      inference('simpl_trail', [status(thm)], ['1', '55'])).
% 0.71/0.89  thf('57', plain,
% 0.71/0.89      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 0.71/0.89         = (k6_partfun1 @ sk_A))),
% 0.71/0.89      inference('demod', [status(thm)], ['16', '19'])).
% 0.71/0.89  thf('58', plain,
% 0.71/0.89      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf(t24_funct_2, axiom,
% 0.71/0.89    (![A:$i,B:$i,C:$i]:
% 0.71/0.89     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.71/0.89         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.71/0.89       ( ![D:$i]:
% 0.71/0.89         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.71/0.89             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.71/0.89           ( ( r2_relset_1 @
% 0.71/0.89               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.71/0.89               ( k6_partfun1 @ B ) ) =>
% 0.71/0.89             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.71/0.89  thf('59', plain,
% 0.71/0.89      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.71/0.89         (~ (v1_funct_1 @ X34)
% 0.71/0.89          | ~ (v1_funct_2 @ X34 @ X35 @ X36)
% 0.71/0.89          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.71/0.89          | ~ (r2_relset_1 @ X35 @ X35 @ 
% 0.71/0.89               (k1_partfun1 @ X35 @ X36 @ X36 @ X35 @ X34 @ X37) @ 
% 0.71/0.89               (k6_partfun1 @ X35))
% 0.71/0.89          | ((k2_relset_1 @ X36 @ X35 @ X37) = (X35))
% 0.71/0.89          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 0.71/0.89          | ~ (v1_funct_2 @ X37 @ X36 @ X35)
% 0.71/0.89          | ~ (v1_funct_1 @ X37))),
% 0.71/0.89      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.71/0.89  thf('60', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         (~ (v1_funct_1 @ X0)
% 0.71/0.89          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 0.71/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 0.71/0.89          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 0.71/0.89          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.71/0.89               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 0.71/0.89               (k6_partfun1 @ sk_A))
% 0.71/0.89          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 0.71/0.89          | ~ (v1_funct_1 @ sk_C))),
% 0.71/0.89      inference('sup-', [status(thm)], ['58', '59'])).
% 0.71/0.89  thf('61', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('62', plain, ((v1_funct_1 @ sk_C)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('63', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         (~ (v1_funct_1 @ X0)
% 0.71/0.89          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 0.71/0.89          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 0.71/0.89          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 0.71/0.89          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.71/0.89               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 0.71/0.89               (k6_partfun1 @ sk_A)))),
% 0.71/0.89      inference('demod', [status(thm)], ['60', '61', '62'])).
% 0.71/0.89  thf('64', plain,
% 0.71/0.89      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 0.71/0.89           (k6_partfun1 @ sk_A))
% 0.71/0.89        | ((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (sk_A))
% 0.71/0.89        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 0.71/0.89        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 0.71/0.89        | ~ (v1_funct_1 @ sk_D))),
% 0.71/0.89      inference('sup-', [status(thm)], ['57', '63'])).
% 0.71/0.89  thf('65', plain,
% 0.71/0.89      (![X24 : $i]:
% 0.71/0.89         (m1_subset_1 @ (k6_partfun1 @ X24) @ 
% 0.71/0.89          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X24)))),
% 0.71/0.89      inference('demod', [status(thm)], ['17', '18'])).
% 0.71/0.89  thf('66', plain,
% 0.71/0.89      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.71/0.89         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.71/0.89          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.71/0.89          | (r2_relset_1 @ X21 @ X22 @ X20 @ X23)
% 0.71/0.89          | ((X20) != (X23)))),
% 0.71/0.89      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.71/0.89  thf('67', plain,
% 0.71/0.89      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.71/0.89         ((r2_relset_1 @ X21 @ X22 @ X23 @ X23)
% 0.71/0.89          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.71/0.89      inference('simplify', [status(thm)], ['66'])).
% 0.71/0.89  thf('68', plain,
% 0.71/0.89      (![X0 : $i]:
% 0.71/0.89         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.71/0.89      inference('sup-', [status(thm)], ['65', '67'])).
% 0.71/0.89  thf('69', plain,
% 0.71/0.89      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf(redefinition_k2_relset_1, axiom,
% 0.71/0.89    (![A:$i,B:$i,C:$i]:
% 0.71/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.89       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.71/0.89  thf('70', plain,
% 0.71/0.89      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.71/0.89         (((k2_relset_1 @ X18 @ X19 @ X17) = (k2_relat_1 @ X17))
% 0.71/0.89          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.71/0.89      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.71/0.89  thf('71', plain,
% 0.71/0.89      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.71/0.89      inference('sup-', [status(thm)], ['69', '70'])).
% 0.71/0.89  thf('72', plain,
% 0.71/0.89      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('73', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('74', plain, ((v1_funct_1 @ sk_D)),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf('75', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.71/0.89      inference('demod', [status(thm)], ['64', '68', '71', '72', '73', '74'])).
% 0.71/0.89  thf(d3_funct_2, axiom,
% 0.71/0.89    (![A:$i,B:$i]:
% 0.71/0.89     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.71/0.89       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.71/0.89  thf('76', plain,
% 0.71/0.89      (![X25 : $i, X26 : $i]:
% 0.71/0.89         (((k2_relat_1 @ X26) != (X25))
% 0.71/0.89          | (v2_funct_2 @ X26 @ X25)
% 0.71/0.89          | ~ (v5_relat_1 @ X26 @ X25)
% 0.71/0.89          | ~ (v1_relat_1 @ X26))),
% 0.71/0.89      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.71/0.89  thf('77', plain,
% 0.71/0.89      (![X26 : $i]:
% 0.71/0.89         (~ (v1_relat_1 @ X26)
% 0.71/0.89          | ~ (v5_relat_1 @ X26 @ (k2_relat_1 @ X26))
% 0.71/0.89          | (v2_funct_2 @ X26 @ (k2_relat_1 @ X26)))),
% 0.71/0.89      inference('simplify', [status(thm)], ['76'])).
% 0.71/0.89  thf('78', plain,
% 0.71/0.89      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 0.71/0.89        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 0.71/0.89        | ~ (v1_relat_1 @ sk_D))),
% 0.71/0.89      inference('sup-', [status(thm)], ['75', '77'])).
% 0.71/0.89  thf('79', plain,
% 0.71/0.89      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf(cc2_relset_1, axiom,
% 0.71/0.89    (![A:$i,B:$i,C:$i]:
% 0.71/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.89       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.71/0.89  thf('80', plain,
% 0.71/0.89      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.71/0.89         ((v5_relat_1 @ X14 @ X16)
% 0.71/0.89          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.71/0.89      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.71/0.89  thf('81', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.71/0.89      inference('sup-', [status(thm)], ['79', '80'])).
% 0.71/0.89  thf('82', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.71/0.89      inference('demod', [status(thm)], ['64', '68', '71', '72', '73', '74'])).
% 0.71/0.89  thf('83', plain,
% 0.71/0.89      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.71/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.89  thf(cc1_relset_1, axiom,
% 0.71/0.89    (![A:$i,B:$i,C:$i]:
% 0.71/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.89       ( v1_relat_1 @ C ) ))).
% 0.71/0.89  thf('84', plain,
% 0.71/0.89      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.71/0.89         ((v1_relat_1 @ X11)
% 0.71/0.89          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.71/0.89      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.71/0.89  thf('85', plain, ((v1_relat_1 @ sk_D)),
% 0.71/0.89      inference('sup-', [status(thm)], ['83', '84'])).
% 0.71/0.89  thf('86', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 0.71/0.89      inference('demod', [status(thm)], ['78', '81', '82', '85'])).
% 0.71/0.89  thf('87', plain, ($false), inference('demod', [status(thm)], ['56', '86'])).
% 0.71/0.89  
% 0.71/0.89  % SZS output end Refutation
% 0.71/0.89  
% 0.71/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
