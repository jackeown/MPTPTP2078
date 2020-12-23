%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AZFs7Wx4xt

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:09 EST 2020

% Result     : Theorem 0.41s
% Output     : Refutation 0.41s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 222 expanded)
%              Number of leaves         :   25 (  74 expanded)
%              Depth                    :   15
%              Number of atoms          :  744 (3140 expanded)
%              Number of equality atoms :   66 ( 222 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t142_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( r1_partfun1 @ C @ D )
           => ( ( ( B = k1_xboole_0 )
                & ( A != k1_xboole_0 ) )
              | ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ( r1_partfun1 @ C @ D )
             => ( ( ( B = k1_xboole_0 )
                  & ( A != k1_xboole_0 ) )
                | ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t142_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( v1_partfun1 @ X17 @ X18 )
      | ~ ( v1_funct_2 @ X17 @ X18 @ X19 )
      | ~ ( v1_funct_1 @ X17 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('4',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B_1 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t148_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( ( v1_partfun1 @ C @ A )
              & ( v1_partfun1 @ D @ A )
              & ( r1_partfun1 @ C @ D ) )
           => ( C = D ) ) ) ) )).

thf('9',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_funct_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( X25 = X22 )
      | ~ ( r1_partfun1 @ X25 @ X22 )
      | ~ ( v1_partfun1 @ X22 @ X23 )
      | ~ ( v1_partfun1 @ X25 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t148_partfun1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( X0 = sk_D )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,
    ( ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ~ ( r1_partfun1 @ sk_C_1 @ sk_D )
    | ( sk_C_1 = sk_D )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['1','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r1_partfun1 @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v1_partfun1 @ sk_C_1 @ sk_A )
    | ( sk_C_1 = sk_D )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( v1_partfun1 @ X17 @ X18 )
      | ~ ( v1_funct_2 @ X17 @ X18 @ X19 )
      | ~ ( v1_funct_1 @ X17 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C_1 )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_partfun1 @ sk_C_1 @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C_1 = sk_D ) ),
    inference(clc,[status(thm)],['17','23'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('25',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('26',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( sk_B_1 != k1_xboole_0 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('28',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ sk_B_1 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,
    ( ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_B_1 ) )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['28'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('30',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('31',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
   <= ( sk_B_1 != k1_xboole_0 ) ),
    inference('simplify_reflect+',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('33',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_1 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('35',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('36',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('37',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,
    ( ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['36','37'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('39',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_C_1 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('41',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k2_zfmisc_1 @ X8 @ X9 )
        = k1_xboole_0 )
      | ( X8 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('42',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('44',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_C_1 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','42','43'])).

thf('45',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','44'])).

thf('46',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('47',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k1_xboole_0 = sk_C_1 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('50',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['34','49'])).

thf('51',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('52',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('53',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('56',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) )
        | ~ ( r2_hidden @ X0 @ sk_D ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X9: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X9 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('58',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('59',plain,
    ( ! [X0: $i] :
        ~ ( r2_hidden @ X0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57','58'])).

thf('60',plain,
    ( ( v1_xboole_0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('62',plain,
    ( ( k1_xboole_0 = sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','62'])).

thf('64',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('65',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('66',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ( r2_relset_1 @ X13 @ X14 @ X15 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['66'])).

thf('68',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,
    ( ( r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_1 @ sk_C_1 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['64','68'])).

thf('70',plain,
    ( ( k1_xboole_0 = sk_C_1 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('71',plain,
    ( ( k1_xboole_0 = sk_C_1 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','48'])).

thf('72',plain,
    ( ( r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['69','70','71'])).

thf('73',plain,(
    sk_A != k1_xboole_0 ),
    inference(demod,[status(thm)],['63','72'])).

thf('74',plain,
    ( ( sk_B_1 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['26'])).

thf('75',plain,(
    sk_B_1 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['73','74'])).

thf('76',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simpl_trail,[status(thm)],['31','75'])).

thf('77',plain,(
    sk_C_1 = sk_D ),
    inference(clc,[status(thm)],['24','76'])).

thf('78',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_C_1 ),
    inference('sup-',[status(thm)],['65','67'])).

thf('79',plain,(
    $false ),
    inference(demod,[status(thm)],['0','77','78'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AZFs7Wx4xt
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:54:56 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.41/0.61  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.41/0.61  % Solved by: fo/fo7.sh
% 0.41/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.41/0.61  % done 324 iterations in 0.160s
% 0.41/0.61  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.41/0.61  % SZS output start Refutation
% 0.41/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.41/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.41/0.61  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.41/0.61  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.41/0.61  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.41/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.41/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.41/0.61  thf(sk_D_type, type, sk_D: $i).
% 0.41/0.61  thf(sk_B_type, type, sk_B: $i > $i).
% 0.41/0.61  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.41/0.61  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.41/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.41/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.41/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.41/0.61  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.41/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.41/0.61  thf(t142_funct_2, conjecture,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.41/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.61       ( ![D:$i]:
% 0.41/0.61         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.41/0.61             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.61           ( ( r1_partfun1 @ C @ D ) =>
% 0.41/0.61             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.41/0.61               ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.41/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.41/0.61    (~( ![A:$i,B:$i,C:$i]:
% 0.41/0.61        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.41/0.61            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.61          ( ![D:$i]:
% 0.41/0.61            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.41/0.61                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.61              ( ( r1_partfun1 @ C @ D ) =>
% 0.41/0.61                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.41/0.61                  ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ) )),
% 0.41/0.61    inference('cnf.neg', [status(esa)], [t142_funct_2])).
% 0.41/0.61  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('1', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('2', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(cc5_funct_2, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.41/0.61       ( ![C:$i]:
% 0.41/0.61         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.41/0.61           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.41/0.61             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.41/0.61  thf('3', plain,
% 0.41/0.61      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.41/0.61          | (v1_partfun1 @ X17 @ X18)
% 0.41/0.61          | ~ (v1_funct_2 @ X17 @ X18 @ X19)
% 0.41/0.61          | ~ (v1_funct_1 @ X17)
% 0.41/0.61          | (v1_xboole_0 @ X19))),
% 0.41/0.61      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.41/0.61  thf('4', plain,
% 0.41/0.61      (((v1_xboole_0 @ sk_B_1)
% 0.41/0.61        | ~ (v1_funct_1 @ sk_D)
% 0.41/0.61        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B_1)
% 0.41/0.61        | (v1_partfun1 @ sk_D @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['2', '3'])).
% 0.41/0.61  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('7', plain, (((v1_xboole_0 @ sk_B_1) | (v1_partfun1 @ sk_D @ sk_A))),
% 0.41/0.61      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.41/0.61  thf('8', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(t148_partfun1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ( ( v1_funct_1 @ C ) & 
% 0.41/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.61       ( ![D:$i]:
% 0.41/0.61         ( ( ( v1_funct_1 @ D ) & 
% 0.41/0.61             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.61           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 0.41/0.61               ( r1_partfun1 @ C @ D ) ) =>
% 0.41/0.61             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.41/0.61  thf('9', plain,
% 0.41/0.61      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.41/0.61         (~ (v1_funct_1 @ X22)
% 0.41/0.61          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.41/0.61          | ((X25) = (X22))
% 0.41/0.61          | ~ (r1_partfun1 @ X25 @ X22)
% 0.41/0.61          | ~ (v1_partfun1 @ X22 @ X23)
% 0.41/0.61          | ~ (v1_partfun1 @ X25 @ X23)
% 0.41/0.61          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.41/0.61          | ~ (v1_funct_1 @ X25))),
% 0.41/0.61      inference('cnf', [status(esa)], [t148_partfun1])).
% 0.41/0.61  thf('10', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (v1_funct_1 @ X0)
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.41/0.61          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.41/0.61          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.41/0.61          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.41/0.61          | ((X0) = (sk_D))
% 0.41/0.61          | ~ (v1_funct_1 @ sk_D))),
% 0.41/0.61      inference('sup-', [status(thm)], ['8', '9'])).
% 0.41/0.61  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('12', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         (~ (v1_funct_1 @ X0)
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.41/0.61          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.41/0.61          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.41/0.61          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.41/0.61          | ((X0) = (sk_D)))),
% 0.41/0.61      inference('demod', [status(thm)], ['10', '11'])).
% 0.41/0.61  thf('13', plain,
% 0.41/0.61      (![X0 : $i]:
% 0.41/0.61         ((v1_xboole_0 @ sk_B_1)
% 0.41/0.61          | ((X0) = (sk_D))
% 0.41/0.61          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.41/0.61          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.41/0.61          | ~ (v1_funct_1 @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['7', '12'])).
% 0.41/0.61  thf('14', plain,
% 0.41/0.61      ((~ (v1_funct_1 @ sk_C_1)
% 0.41/0.61        | ~ (v1_partfun1 @ sk_C_1 @ sk_A)
% 0.41/0.61        | ~ (r1_partfun1 @ sk_C_1 @ sk_D)
% 0.41/0.61        | ((sk_C_1) = (sk_D))
% 0.41/0.61        | (v1_xboole_0 @ sk_B_1))),
% 0.41/0.61      inference('sup-', [status(thm)], ['1', '13'])).
% 0.41/0.61  thf('15', plain, ((v1_funct_1 @ sk_C_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('16', plain, ((r1_partfun1 @ sk_C_1 @ sk_D)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('17', plain,
% 0.41/0.61      ((~ (v1_partfun1 @ sk_C_1 @ sk_A)
% 0.41/0.61        | ((sk_C_1) = (sk_D))
% 0.41/0.61        | (v1_xboole_0 @ sk_B_1))),
% 0.41/0.61      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.41/0.61  thf('18', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('19', plain,
% 0.41/0.61      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.41/0.61         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.41/0.61          | (v1_partfun1 @ X17 @ X18)
% 0.41/0.61          | ~ (v1_funct_2 @ X17 @ X18 @ X19)
% 0.41/0.61          | ~ (v1_funct_1 @ X17)
% 0.41/0.61          | (v1_xboole_0 @ X19))),
% 0.41/0.61      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.41/0.61  thf('20', plain,
% 0.41/0.61      (((v1_xboole_0 @ sk_B_1)
% 0.41/0.61        | ~ (v1_funct_1 @ sk_C_1)
% 0.41/0.61        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 0.41/0.61        | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.41/0.61      inference('sup-', [status(thm)], ['18', '19'])).
% 0.41/0.61  thf('21', plain, ((v1_funct_1 @ sk_C_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('22', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('23', plain, (((v1_xboole_0 @ sk_B_1) | (v1_partfun1 @ sk_C_1 @ sk_A))),
% 0.41/0.61      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.41/0.61  thf('24', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_C_1) = (sk_D)))),
% 0.41/0.61      inference('clc', [status(thm)], ['17', '23'])).
% 0.41/0.61  thf(t8_boole, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.41/0.61  thf('25', plain,
% 0.41/0.61      (![X3 : $i, X4 : $i]:
% 0.41/0.61         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 0.41/0.61      inference('cnf', [status(esa)], [t8_boole])).
% 0.41/0.61  thf('26', plain, ((((sk_B_1) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('27', plain,
% 0.41/0.61      ((((sk_B_1) != (k1_xboole_0))) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.41/0.61      inference('split', [status(esa)], ['26'])).
% 0.41/0.61  thf('28', plain,
% 0.41/0.61      ((![X0 : $i]:
% 0.41/0.61          (((X0) != (k1_xboole_0))
% 0.41/0.61           | ~ (v1_xboole_0 @ sk_B_1)
% 0.41/0.61           | ~ (v1_xboole_0 @ X0)))
% 0.41/0.61         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['25', '27'])).
% 0.41/0.61  thf('29', plain,
% 0.41/0.61      (((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_B_1)))
% 0.41/0.61         <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.41/0.61      inference('simplify', [status(thm)], ['28'])).
% 0.41/0.61  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.41/0.61  thf('30', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.41/0.61  thf('31', plain,
% 0.41/0.61      ((~ (v1_xboole_0 @ sk_B_1)) <= (~ (((sk_B_1) = (k1_xboole_0))))),
% 0.41/0.61      inference('simplify_reflect+', [status(thm)], ['29', '30'])).
% 0.41/0.61  thf('32', plain,
% 0.41/0.61      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('split', [status(esa)], ['26'])).
% 0.41/0.61  thf('33', plain, (~ (r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D)),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('34', plain,
% 0.41/0.61      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_1 @ sk_D))
% 0.41/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['32', '33'])).
% 0.41/0.61  thf(d1_xboole_0, axiom,
% 0.41/0.61    (![A:$i]:
% 0.41/0.61     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.41/0.61  thf('35', plain,
% 0.41/0.61      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.41/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.61  thf('36', plain,
% 0.41/0.61      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('split', [status(esa)], ['26'])).
% 0.41/0.61  thf('37', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('38', plain,
% 0.41/0.61      (((m1_subset_1 @ sk_C_1 @ 
% 0.41/0.61         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 0.41/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('sup+', [status(thm)], ['36', '37'])).
% 0.41/0.61  thf(t5_subset, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i]:
% 0.41/0.61     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.41/0.61          ( v1_xboole_0 @ C ) ) ))).
% 0.41/0.61  thf('39', plain,
% 0.41/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X10 @ X11)
% 0.41/0.61          | ~ (v1_xboole_0 @ X12)
% 0.41/0.61          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.41/0.61      inference('cnf', [status(esa)], [t5_subset])).
% 0.41/0.61  thf('40', plain,
% 0.41/0.61      ((![X0 : $i]:
% 0.41/0.61          (~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))
% 0.41/0.61           | ~ (r2_hidden @ X0 @ sk_C_1)))
% 0.41/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['38', '39'])).
% 0.41/0.61  thf(t113_zfmisc_1, axiom,
% 0.41/0.61    (![A:$i,B:$i]:
% 0.41/0.61     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.41/0.61       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.41/0.61  thf('41', plain,
% 0.41/0.61      (![X8 : $i, X9 : $i]:
% 0.41/0.61         (((k2_zfmisc_1 @ X8 @ X9) = (k1_xboole_0)) | ((X8) != (k1_xboole_0)))),
% 0.41/0.61      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.41/0.61  thf('42', plain,
% 0.41/0.61      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 0.41/0.61      inference('simplify', [status(thm)], ['41'])).
% 0.41/0.61  thf('43', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.41/0.61  thf('44', plain,
% 0.41/0.61      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C_1))
% 0.41/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('demod', [status(thm)], ['40', '42', '43'])).
% 0.41/0.61  thf('45', plain, (((v1_xboole_0 @ sk_C_1)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['35', '44'])).
% 0.41/0.61  thf('46', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.41/0.61  thf('47', plain,
% 0.41/0.61      (![X3 : $i, X4 : $i]:
% 0.41/0.61         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 0.41/0.61      inference('cnf', [status(esa)], [t8_boole])).
% 0.41/0.61  thf('48', plain,
% 0.41/0.61      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['46', '47'])).
% 0.41/0.61  thf('49', plain,
% 0.41/0.61      ((((k1_xboole_0) = (sk_C_1))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['45', '48'])).
% 0.41/0.61  thf('50', plain,
% 0.41/0.61      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 @ sk_D))
% 0.41/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('demod', [status(thm)], ['34', '49'])).
% 0.41/0.61  thf('51', plain,
% 0.41/0.61      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.41/0.61      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.41/0.61  thf('52', plain,
% 0.41/0.61      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('split', [status(esa)], ['26'])).
% 0.41/0.61  thf('53', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf('54', plain,
% 0.41/0.61      (((m1_subset_1 @ sk_D @ 
% 0.41/0.61         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))))
% 0.41/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('sup+', [status(thm)], ['52', '53'])).
% 0.41/0.61  thf('55', plain,
% 0.41/0.61      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.41/0.61         (~ (r2_hidden @ X10 @ X11)
% 0.41/0.61          | ~ (v1_xboole_0 @ X12)
% 0.41/0.61          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.41/0.61      inference('cnf', [status(esa)], [t5_subset])).
% 0.41/0.61  thf('56', plain,
% 0.41/0.61      ((![X0 : $i]:
% 0.41/0.61          (~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))
% 0.41/0.61           | ~ (r2_hidden @ X0 @ sk_D)))
% 0.41/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['54', '55'])).
% 0.41/0.61  thf('57', plain,
% 0.41/0.61      (![X9 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X9) = (k1_xboole_0))),
% 0.41/0.61      inference('simplify', [status(thm)], ['41'])).
% 0.41/0.61  thf('58', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.41/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.41/0.61  thf('59', plain,
% 0.41/0.61      ((![X0 : $i]: ~ (r2_hidden @ X0 @ sk_D)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('demod', [status(thm)], ['56', '57', '58'])).
% 0.41/0.61  thf('60', plain, (((v1_xboole_0 @ sk_D)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['51', '59'])).
% 0.41/0.61  thf('61', plain,
% 0.41/0.61      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.41/0.61      inference('sup-', [status(thm)], ['46', '47'])).
% 0.41/0.61  thf('62', plain,
% 0.41/0.61      ((((k1_xboole_0) = (sk_D))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['60', '61'])).
% 0.41/0.61  thf('63', plain,
% 0.41/0.61      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 @ k1_xboole_0))
% 0.41/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('demod', [status(thm)], ['50', '62'])).
% 0.41/0.61  thf('64', plain,
% 0.41/0.61      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('split', [status(esa)], ['26'])).
% 0.41/0.61  thf('65', plain,
% 0.41/0.61      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.41/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.41/0.61  thf(reflexivity_r2_relset_1, axiom,
% 0.41/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.41/0.61     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.41/0.61         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.41/0.61       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.41/0.61  thf('66', plain,
% 0.41/0.61      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.41/0.61         ((r2_relset_1 @ X13 @ X14 @ X15 @ X15)
% 0.41/0.61          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14)))
% 0.41/0.61          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.41/0.61      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.41/0.61  thf('67', plain,
% 0.41/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.41/0.61         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.41/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.41/0.61      inference('condensation', [status(thm)], ['66'])).
% 0.41/0.61  thf('68', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_C_1)),
% 0.41/0.61      inference('sup-', [status(thm)], ['65', '67'])).
% 0.41/0.61  thf('69', plain,
% 0.41/0.61      (((r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ sk_C_1 @ sk_C_1))
% 0.41/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('sup+', [status(thm)], ['64', '68'])).
% 0.41/0.61  thf('70', plain,
% 0.41/0.61      ((((k1_xboole_0) = (sk_C_1))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['45', '48'])).
% 0.41/0.61  thf('71', plain,
% 0.41/0.61      ((((k1_xboole_0) = (sk_C_1))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('sup-', [status(thm)], ['45', '48'])).
% 0.41/0.61  thf('72', plain,
% 0.41/0.61      (((r2_relset_1 @ k1_xboole_0 @ sk_B_1 @ k1_xboole_0 @ k1_xboole_0))
% 0.41/0.61         <= ((((sk_A) = (k1_xboole_0))))),
% 0.41/0.61      inference('demod', [status(thm)], ['69', '70', '71'])).
% 0.41/0.61  thf('73', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.41/0.61      inference('demod', [status(thm)], ['63', '72'])).
% 0.41/0.61  thf('74', plain,
% 0.41/0.61      (~ (((sk_B_1) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.41/0.61      inference('split', [status(esa)], ['26'])).
% 0.41/0.61  thf('75', plain, (~ (((sk_B_1) = (k1_xboole_0)))),
% 0.41/0.61      inference('sat_resolution*', [status(thm)], ['73', '74'])).
% 0.41/0.61  thf('76', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.41/0.61      inference('simpl_trail', [status(thm)], ['31', '75'])).
% 0.41/0.61  thf('77', plain, (((sk_C_1) = (sk_D))),
% 0.41/0.61      inference('clc', [status(thm)], ['24', '76'])).
% 0.41/0.61  thf('78', plain, ((r2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_C_1)),
% 0.41/0.61      inference('sup-', [status(thm)], ['65', '67'])).
% 0.41/0.61  thf('79', plain, ($false),
% 0.41/0.61      inference('demod', [status(thm)], ['0', '77', '78'])).
% 0.41/0.61  
% 0.41/0.61  % SZS output end Refutation
% 0.41/0.61  
% 0.41/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
