%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EbzbvbZZKE

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  127 (1780 expanded)
%              Number of leaves         :   24 ( 487 expanded)
%              Depth                    :   25
%              Number of atoms          : 1989 (39600 expanded)
%              Number of equality atoms :  126 (1508 expanded)
%              Maximal formula depth    :   16 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t146_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( r1_partfun1 @ B @ C )
          <=> ! [D: $i] :
                ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ A @ B ) )
               => ( ( k1_funct_1 @ B @ D )
                  = ( k1_funct_1 @ C @ D ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( r1_partfun1 @ B @ C )
            <=> ! [D: $i] :
                  ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ A @ B ) )
                 => ( ( k1_funct_1 @ B @ D )
                    = ( k1_funct_1 @ C @ D ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t146_funct_2])).

thf('0',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_D )
     != ( k1_funct_1 @ sk_C @ sk_D ) )
    | ~ ( r1_partfun1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_D )
     != ( k1_funct_1 @ sk_C @ sk_D ) )
    | ~ ( r1_partfun1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,
    ( ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
    | ~ ( r1_partfun1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
    | ~ ( r1_partfun1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['2'])).

thf('4',plain,(
    ! [X11: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
      | ( ( k1_funct_1 @ sk_B @ X11 )
        = ( k1_funct_1 @ sk_C @ X11 ) )
      | ( r1_partfun1 @ sk_B @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( r1_partfun1 @ sk_B @ sk_C )
   <= ( r1_partfun1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t145_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ C ) )
     => ! [D: $i] :
          ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
            & ( v1_funct_2 @ D @ A @ B )
            & ( v1_funct_1 @ D ) )
         => ( ( ( B = k1_xboole_0 )
             => ( A = k1_xboole_0 ) )
           => ( ( r1_partfun1 @ C @ D )
            <=> ! [E: $i] :
                  ( ( r2_hidden @ E @ ( k1_relset_1 @ A @ B @ C ) )
                 => ( ( k1_funct_1 @ C @ E )
                    = ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('8',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ D @ C @ B @ A )
     => ( ( r1_partfun1 @ C @ D )
      <=> ! [E: $i] :
            ( ( r2_hidden @ E @ ( k1_relset_1 @ A @ B @ C ) )
           => ( ( k1_funct_1 @ C @ E )
              = ( k1_funct_1 @ D @ E ) ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( zip_tseitin_0 @ B @ A )
           => ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ~ ( v1_funct_1 @ X7 )
      | ~ ( v1_funct_2 @ X7 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ( zip_tseitin_1 @ X7 @ X10 @ X9 @ X8 )
      | ~ ( zip_tseitin_0 @ X9 @ X8 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) )
      | ~ ( v1_funct_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( zip_tseitin_0 @ sk_A @ sk_A )
      | ( zip_tseitin_1 @ sk_C @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( zip_tseitin_0 @ sk_A @ sk_A )
      | ( zip_tseitin_1 @ sk_C @ X0 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( sk_A = k1_xboole_0 )
      | ( zip_tseitin_1 @ sk_C @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','13'])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['6','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
   <= ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference(split,[status(esa)],['2'])).

thf('19',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ~ ( r1_partfun1 @ X4 @ X5 )
      | ( ( k1_funct_1 @ X4 @ X6 )
        = ( k1_funct_1 @ X5 @ X6 ) )
      | ~ ( r2_hidden @ X6 @ ( k1_relset_1 @ X2 @ X3 @ X4 ) )
      | ~ ( zip_tseitin_1 @ X5 @ X4 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('20',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_1 @ X0 @ sk_B @ sk_A @ sk_A )
        | ( ( k1_funct_1 @ sk_B @ sk_D )
          = ( k1_funct_1 @ X0 @ sk_D ) )
        | ~ ( r1_partfun1 @ sk_B @ X0 ) )
   <= ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ~ ( r1_partfun1 @ sk_B @ sk_C )
      | ( ( k1_funct_1 @ sk_B @ sk_D )
        = ( k1_funct_1 @ sk_C @ sk_D ) ) )
   <= ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','20'])).

thf('22',plain,
    ( ( ( ( k1_funct_1 @ sk_B @ sk_D )
        = ( k1_funct_1 @ sk_C @ sk_D ) )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( r1_partfun1 @ sk_B @ sk_C )
      & ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['5','21'])).

thf('23',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_D )
     != ( k1_funct_1 @ sk_C @ sk_D ) )
   <= ( ( k1_funct_1 @ sk_B @ sk_D )
     != ( k1_funct_1 @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('24',plain,
    ( ( ( ( k1_funct_1 @ sk_C @ sk_D )
       != ( k1_funct_1 @ sk_C @ sk_D ) )
      | ( sk_A = k1_xboole_0 ) )
   <= ( ( ( k1_funct_1 @ sk_B @ sk_D )
       != ( k1_funct_1 @ sk_C @ sk_D ) )
      & ( r1_partfun1 @ sk_B @ sk_C )
      & ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( ( k1_funct_1 @ sk_B @ sk_D )
       != ( k1_funct_1 @ sk_C @ sk_D ) )
      & ( r1_partfun1 @ sk_B @ sk_C )
      & ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( ( ( k1_funct_1 @ sk_B @ sk_D )
       != ( k1_funct_1 @ sk_C @ sk_D ) )
      & ( r1_partfun1 @ sk_B @ sk_C )
      & ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['25','26'])).

thf('28',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( ( k1_funct_1 @ sk_B @ sk_D )
       != ( k1_funct_1 @ sk_C @ sk_D ) )
      & ( r1_partfun1 @ sk_B @ sk_C )
      & ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('29',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) )
   <= ( ( ( k1_funct_1 @ sk_B @ sk_D )
       != ( k1_funct_1 @ sk_C @ sk_D ) )
      & ( r1_partfun1 @ sk_B @ sk_C )
      & ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( ( k1_funct_1 @ sk_B @ sk_D )
       != ( k1_funct_1 @ sk_C @ sk_D ) )
      & ( r1_partfun1 @ sk_B @ sk_C )
      & ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( zip_tseitin_0 @ sk_A @ sk_A )
      | ( zip_tseitin_1 @ sk_C @ X0 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('32',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_0 @ sk_A @ k1_xboole_0 )
        | ( zip_tseitin_1 @ sk_C @ X0 @ sk_A @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 ) )
   <= ( ( ( k1_funct_1 @ sk_B @ sk_D )
       != ( k1_funct_1 @ sk_C @ sk_D ) )
      & ( r1_partfun1 @ sk_B @ sk_C )
      & ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( ( k1_funct_1 @ sk_B @ sk_D )
       != ( k1_funct_1 @ sk_C @ sk_D ) )
      & ( r1_partfun1 @ sk_B @ sk_C )
      & ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ X0 @ X1 )
      | ( X1 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('35',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( ( k1_funct_1 @ sk_B @ sk_D )
       != ( k1_funct_1 @ sk_C @ sk_D ) )
      & ( r1_partfun1 @ sk_B @ sk_C )
      & ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('37',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( ( k1_funct_1 @ sk_B @ sk_D )
       != ( k1_funct_1 @ sk_C @ sk_D ) )
      & ( r1_partfun1 @ sk_B @ sk_C )
      & ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('38',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( ( k1_funct_1 @ sk_B @ sk_D )
       != ( k1_funct_1 @ sk_C @ sk_D ) )
      & ( r1_partfun1 @ sk_B @ sk_C )
      & ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('39',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( ( k1_funct_1 @ sk_B @ sk_D )
       != ( k1_funct_1 @ sk_C @ sk_D ) )
      & ( r1_partfun1 @ sk_B @ sk_C )
      & ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('40',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_1 @ sk_C @ X0 @ k1_xboole_0 @ k1_xboole_0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) )
        | ~ ( v1_funct_1 @ X0 ) )
   <= ( ( ( k1_funct_1 @ sk_B @ sk_D )
       != ( k1_funct_1 @ sk_C @ sk_D ) )
      & ( r1_partfun1 @ sk_B @ sk_C )
      & ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['32','33','35','36','37','38','39'])).

thf('41',plain,
    ( ( ~ ( v1_funct_1 @ sk_B )
      | ( zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( ( k1_funct_1 @ sk_B @ sk_D )
       != ( k1_funct_1 @ sk_C @ sk_D ) )
      & ( r1_partfun1 @ sk_B @ sk_C )
      & ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['29','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0 @ k1_xboole_0 )
   <= ( ( ( k1_funct_1 @ sk_B @ sk_D )
       != ( k1_funct_1 @ sk_C @ sk_D ) )
      & ( r1_partfun1 @ sk_B @ sk_C )
      & ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( ( k1_funct_1 @ sk_B @ sk_D )
       != ( k1_funct_1 @ sk_C @ sk_D ) )
      & ( r1_partfun1 @ sk_B @ sk_C )
      & ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('45',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_1 @ X0 @ sk_B @ sk_A @ sk_A )
        | ( ( k1_funct_1 @ sk_B @ sk_D )
          = ( k1_funct_1 @ X0 @ sk_D ) )
        | ~ ( r1_partfun1 @ sk_B @ X0 ) )
   <= ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('46',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_1 @ X0 @ sk_B @ sk_A @ k1_xboole_0 )
        | ~ ( r1_partfun1 @ sk_B @ X0 )
        | ( ( k1_funct_1 @ sk_B @ sk_D )
          = ( k1_funct_1 @ X0 @ sk_D ) ) )
   <= ( ( ( k1_funct_1 @ sk_B @ sk_D )
       != ( k1_funct_1 @ sk_C @ sk_D ) )
      & ( r1_partfun1 @ sk_B @ sk_C )
      & ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ( ( k1_funct_1 @ sk_B @ sk_D )
       != ( k1_funct_1 @ sk_C @ sk_D ) )
      & ( r1_partfun1 @ sk_B @ sk_C )
      & ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('48',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_1 @ X0 @ sk_B @ k1_xboole_0 @ k1_xboole_0 )
        | ~ ( r1_partfun1 @ sk_B @ X0 )
        | ( ( k1_funct_1 @ sk_B @ sk_D )
          = ( k1_funct_1 @ X0 @ sk_D ) ) )
   <= ( ( ( k1_funct_1 @ sk_B @ sk_D )
       != ( k1_funct_1 @ sk_C @ sk_D ) )
      & ( r1_partfun1 @ sk_B @ sk_C )
      & ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( ( ( k1_funct_1 @ sk_B @ sk_D )
        = ( k1_funct_1 @ sk_C @ sk_D ) )
      | ~ ( r1_partfun1 @ sk_B @ sk_C ) )
   <= ( ( ( k1_funct_1 @ sk_B @ sk_D )
       != ( k1_funct_1 @ sk_C @ sk_D ) )
      & ( r1_partfun1 @ sk_B @ sk_C )
      & ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf('50',plain,
    ( ( r1_partfun1 @ sk_B @ sk_C )
   <= ( r1_partfun1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf('51',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_D )
      = ( k1_funct_1 @ sk_C @ sk_D ) )
   <= ( ( ( k1_funct_1 @ sk_B @ sk_D )
       != ( k1_funct_1 @ sk_C @ sk_D ) )
      & ( r1_partfun1 @ sk_B @ sk_C )
      & ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( ( k1_funct_1 @ sk_B @ sk_D )
     != ( k1_funct_1 @ sk_C @ sk_D ) )
   <= ( ( k1_funct_1 @ sk_B @ sk_D )
     != ( k1_funct_1 @ sk_C @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('53',plain,
    ( ~ ( r2_hidden @ sk_D @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
    | ~ ( r1_partfun1 @ sk_B @ sk_C )
    | ( ( k1_funct_1 @ sk_B @ sk_D )
      = ( k1_funct_1 @ sk_C @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ! [X11: $i] :
        ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X11 )
          = ( k1_funct_1 @ sk_C @ X11 ) ) )
    | ( r1_partfun1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['4'])).

thf('55',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('56',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ ( sk_E @ X2 @ X3 @ X4 @ X5 ) @ ( k1_relset_1 @ X2 @ X3 @ X4 ) )
      | ( r1_partfun1 @ X4 @ X5 )
      | ~ ( zip_tseitin_1 @ X5 @ X4 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('57',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( r1_partfun1 @ sk_B @ sk_C )
    | ( r2_hidden @ ( sk_E @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ! [X11: $i] :
        ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X11 )
          = ( k1_funct_1 @ sk_C @ X11 ) ) )
   <= ! [X11: $i] :
        ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X11 )
          = ( k1_funct_1 @ sk_C @ X11 ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('59',plain,
    ( ( ( r1_partfun1 @ sk_B @ sk_C )
      | ( sk_A = k1_xboole_0 )
      | ( ( k1_funct_1 @ sk_B @ ( sk_E @ sk_A @ sk_A @ sk_B @ sk_C ) )
        = ( k1_funct_1 @ sk_C @ ( sk_E @ sk_A @ sk_A @ sk_B @ sk_C ) ) ) )
   <= ! [X11: $i] :
        ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X11 )
          = ( k1_funct_1 @ sk_C @ X11 ) ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( ( k1_funct_1 @ X4 @ ( sk_E @ X2 @ X3 @ X4 @ X5 ) )
       != ( k1_funct_1 @ X5 @ ( sk_E @ X2 @ X3 @ X4 @ X5 ) ) )
      | ( r1_partfun1 @ X4 @ X5 )
      | ~ ( zip_tseitin_1 @ X5 @ X4 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('61',plain,
    ( ( ( ( k1_funct_1 @ sk_C @ ( sk_E @ sk_A @ sk_A @ sk_B @ sk_C ) )
       != ( k1_funct_1 @ sk_C @ ( sk_E @ sk_A @ sk_A @ sk_B @ sk_C ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( r1_partfun1 @ sk_B @ sk_C )
      | ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A @ sk_A )
      | ( r1_partfun1 @ sk_B @ sk_C ) )
   <= ! [X11: $i] :
        ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X11 )
          = ( k1_funct_1 @ sk_C @ X11 ) ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A @ sk_A )
      | ( r1_partfun1 @ sk_B @ sk_C )
      | ( sk_A = k1_xboole_0 ) )
   <= ! [X11: $i] :
        ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X11 )
          = ( k1_funct_1 @ sk_C @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['61'])).

thf('63',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A @ sk_A )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('64',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( r1_partfun1 @ sk_B @ sk_C ) )
   <= ! [X11: $i] :
        ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X11 )
          = ( k1_funct_1 @ sk_C @ X11 ) ) ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( r1_partfun1 @ sk_B @ sk_C )
   <= ~ ( r1_partfun1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('66',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ~ ( r1_partfun1 @ sk_B @ sk_C )
      & ! [X11: $i] :
          ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
          | ( ( k1_funct_1 @ sk_B @ X11 )
            = ( k1_funct_1 @ sk_C @ X11 ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) )
   <= ( ~ ( r1_partfun1 @ sk_B @ sk_C )
      & ! [X11: $i] :
          ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
          | ( ( k1_funct_1 @ sk_B @ X11 )
            = ( k1_funct_1 @ sk_C @ X11 ) ) ) ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ~ ( r1_partfun1 @ sk_B @ sk_C )
      & ! [X11: $i] :
          ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
          | ( ( k1_funct_1 @ sk_B @ X11 )
            = ( k1_funct_1 @ sk_C @ X11 ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('70',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) )
   <= ( ~ ( r1_partfun1 @ sk_B @ sk_C )
      & ! [X11: $i] :
          ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
          | ( ( k1_funct_1 @ sk_B @ X11 )
            = ( k1_funct_1 @ sk_C @ X11 ) ) ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ~ ( r1_partfun1 @ sk_B @ sk_C )
      & ! [X11: $i] :
          ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
          | ( ( k1_funct_1 @ sk_B @ X11 )
            = ( k1_funct_1 @ sk_C @ X11 ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( zip_tseitin_0 @ sk_A @ sk_A )
      | ( zip_tseitin_1 @ sk_C @ X0 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('73',plain,
    ( ! [X0: $i] :
        ( ~ ( zip_tseitin_0 @ sk_A @ k1_xboole_0 )
        | ( zip_tseitin_1 @ sk_C @ X0 @ sk_A @ sk_A )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
        | ~ ( v1_funct_1 @ X0 ) )
   <= ( ~ ( r1_partfun1 @ sk_B @ sk_C )
      & ! [X11: $i] :
          ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
          | ( ( k1_funct_1 @ sk_B @ X11 )
            = ( k1_funct_1 @ sk_C @ X11 ) ) ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ~ ( r1_partfun1 @ sk_B @ sk_C )
      & ! [X11: $i] :
          ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
          | ( ( k1_funct_1 @ sk_B @ X11 )
            = ( k1_funct_1 @ sk_C @ X11 ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('75',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ X0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('76',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ~ ( r1_partfun1 @ sk_B @ sk_C )
      & ! [X11: $i] :
          ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
          | ( ( k1_funct_1 @ sk_B @ X11 )
            = ( k1_funct_1 @ sk_C @ X11 ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('77',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ~ ( r1_partfun1 @ sk_B @ sk_C )
      & ! [X11: $i] :
          ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
          | ( ( k1_funct_1 @ sk_B @ X11 )
            = ( k1_funct_1 @ sk_C @ X11 ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('78',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ~ ( r1_partfun1 @ sk_B @ sk_C )
      & ! [X11: $i] :
          ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
          | ( ( k1_funct_1 @ sk_B @ X11 )
            = ( k1_funct_1 @ sk_C @ X11 ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('79',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ~ ( r1_partfun1 @ sk_B @ sk_C )
      & ! [X11: $i] :
          ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
          | ( ( k1_funct_1 @ sk_B @ X11 )
            = ( k1_funct_1 @ sk_C @ X11 ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('80',plain,
    ( ! [X0: $i] :
        ( ( zip_tseitin_1 @ sk_C @ X0 @ k1_xboole_0 @ k1_xboole_0 )
        | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) )
        | ~ ( v1_funct_1 @ X0 ) )
   <= ( ~ ( r1_partfun1 @ sk_B @ sk_C )
      & ! [X11: $i] :
          ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
          | ( ( k1_funct_1 @ sk_B @ X11 )
            = ( k1_funct_1 @ sk_C @ X11 ) ) ) ) ),
    inference(demod,[status(thm)],['73','74','75','76','77','78','79'])).

thf('81',plain,
    ( ( ~ ( v1_funct_1 @ sk_B )
      | ( zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0 @ k1_xboole_0 ) )
   <= ( ~ ( r1_partfun1 @ sk_B @ sk_C )
      & ! [X11: $i] :
          ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
          | ( ( k1_funct_1 @ sk_B @ X11 )
            = ( k1_funct_1 @ sk_C @ X11 ) ) ) ) ),
    inference('sup-',[status(thm)],['70','80'])).

thf('82',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0 @ k1_xboole_0 )
   <= ( ~ ( r1_partfun1 @ sk_B @ sk_C )
      & ! [X11: $i] :
          ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
          | ( ( k1_funct_1 @ sk_B @ X11 )
            = ( k1_funct_1 @ sk_C @ X11 ) ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ ( sk_E @ X2 @ X3 @ X4 @ X5 ) @ ( k1_relset_1 @ X2 @ X3 @ X4 ) )
      | ( r1_partfun1 @ X4 @ X5 )
      | ~ ( zip_tseitin_1 @ X5 @ X4 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('85',plain,
    ( ( ( r1_partfun1 @ sk_B @ sk_C )
      | ( r2_hidden @ ( sk_E @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_C ) @ ( k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B ) ) )
   <= ( ~ ( r1_partfun1 @ sk_B @ sk_C )
      & ! [X11: $i] :
          ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
          | ( ( k1_funct_1 @ sk_B @ X11 )
            = ( k1_funct_1 @ sk_C @ X11 ) ) ) ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ~ ( r1_partfun1 @ sk_B @ sk_C )
   <= ~ ( r1_partfun1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('87',plain,
    ( ( r2_hidden @ ( sk_E @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_C ) @ ( k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B ) )
   <= ( ~ ( r1_partfun1 @ sk_B @ sk_C )
      & ! [X11: $i] :
          ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
          | ( ( k1_funct_1 @ sk_B @ X11 )
            = ( k1_funct_1 @ sk_C @ X11 ) ) ) ) ),
    inference(clc,[status(thm)],['85','86'])).

thf('88',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ~ ( r1_partfun1 @ sk_B @ sk_C )
      & ! [X11: $i] :
          ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
          | ( ( k1_funct_1 @ sk_B @ X11 )
            = ( k1_funct_1 @ sk_C @ X11 ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('89',plain,
    ( ! [X11: $i] :
        ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X11 )
          = ( k1_funct_1 @ sk_C @ X11 ) ) )
   <= ! [X11: $i] :
        ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X11 )
          = ( k1_funct_1 @ sk_C @ X11 ) ) ) ),
    inference(split,[status(esa)],['4'])).

thf('90',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_relset_1 @ sk_A @ k1_xboole_0 @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X0 )
          = ( k1_funct_1 @ sk_C @ X0 ) ) )
   <= ( ~ ( r1_partfun1 @ sk_B @ sk_C )
      & ! [X11: $i] :
          ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
          | ( ( k1_funct_1 @ sk_B @ X11 )
            = ( k1_funct_1 @ sk_C @ X11 ) ) ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( ~ ( r1_partfun1 @ sk_B @ sk_C )
      & ! [X11: $i] :
          ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
          | ( ( k1_funct_1 @ sk_B @ X11 )
            = ( k1_funct_1 @ sk_C @ X11 ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('92',plain,
    ( ! [X0: $i] :
        ( ~ ( r2_hidden @ X0 @ ( k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B ) )
        | ( ( k1_funct_1 @ sk_B @ X0 )
          = ( k1_funct_1 @ sk_C @ X0 ) ) )
   <= ( ~ ( r1_partfun1 @ sk_B @ sk_C )
      & ! [X11: $i] :
          ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
          | ( ( k1_funct_1 @ sk_B @ X11 )
            = ( k1_funct_1 @ sk_C @ X11 ) ) ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_E @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_C ) )
      = ( k1_funct_1 @ sk_C @ ( sk_E @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_C ) ) )
   <= ( ~ ( r1_partfun1 @ sk_B @ sk_C )
      & ! [X11: $i] :
          ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
          | ( ( k1_funct_1 @ sk_B @ X11 )
            = ( k1_funct_1 @ sk_C @ X11 ) ) ) ) ),
    inference('sup-',[status(thm)],['87','92'])).

thf('94',plain,(
    ! [X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( ( k1_funct_1 @ X4 @ ( sk_E @ X2 @ X3 @ X4 @ X5 ) )
       != ( k1_funct_1 @ X5 @ ( sk_E @ X2 @ X3 @ X4 @ X5 ) ) )
      | ( r1_partfun1 @ X4 @ X5 )
      | ~ ( zip_tseitin_1 @ X5 @ X4 @ X3 @ X2 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('95',plain,
    ( ( ( ( k1_funct_1 @ sk_C @ ( sk_E @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_C ) )
       != ( k1_funct_1 @ sk_C @ ( sk_E @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_C ) ) )
      | ~ ( zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0 @ k1_xboole_0 )
      | ( r1_partfun1 @ sk_B @ sk_C ) )
   <= ( ~ ( r1_partfun1 @ sk_B @ sk_C )
      & ! [X11: $i] :
          ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
          | ( ( k1_funct_1 @ sk_B @ X11 )
            = ( k1_funct_1 @ sk_C @ X11 ) ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0 @ k1_xboole_0 )
   <= ( ~ ( r1_partfun1 @ sk_B @ sk_C )
      & ! [X11: $i] :
          ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
          | ( ( k1_funct_1 @ sk_B @ X11 )
            = ( k1_funct_1 @ sk_C @ X11 ) ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('97',plain,
    ( ( ( ( k1_funct_1 @ sk_C @ ( sk_E @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_C ) )
       != ( k1_funct_1 @ sk_C @ ( sk_E @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_C ) ) )
      | ( r1_partfun1 @ sk_B @ sk_C ) )
   <= ( ~ ( r1_partfun1 @ sk_B @ sk_C )
      & ! [X11: $i] :
          ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
          | ( ( k1_funct_1 @ sk_B @ X11 )
            = ( k1_funct_1 @ sk_C @ X11 ) ) ) ) ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ( r1_partfun1 @ sk_B @ sk_C )
   <= ( ~ ( r1_partfun1 @ sk_B @ sk_C )
      & ! [X11: $i] :
          ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
          | ( ( k1_funct_1 @ sk_B @ X11 )
            = ( k1_funct_1 @ sk_C @ X11 ) ) ) ) ),
    inference(simplify,[status(thm)],['97'])).

thf('99',plain,
    ( ~ ( r1_partfun1 @ sk_B @ sk_C )
   <= ~ ( r1_partfun1 @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('100',plain,
    ( ~ ! [X11: $i] :
          ( ~ ( r2_hidden @ X11 @ ( k1_relset_1 @ sk_A @ sk_A @ sk_B ) )
          | ( ( k1_funct_1 @ sk_B @ X11 )
            = ( k1_funct_1 @ sk_C @ X11 ) ) )
    | ( r1_partfun1 @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['98','99'])).

thf('101',plain,(
    $false ),
    inference('sat_resolution*',[status(thm)],['1','3','53','54','100'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.EbzbvbZZKE
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:56:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.21/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.50  % Solved by: fo/fo7.sh
% 0.21/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.50  % done 86 iterations in 0.042s
% 0.21/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.50  % SZS output start Refutation
% 0.21/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.50  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.21/0.50  thf(sk_E_type, type, sk_E: $i > $i > $i > $i > $i).
% 0.21/0.50  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $i > $o).
% 0.21/0.50  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.50  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.50  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.21/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.50  thf(t146_funct_2, conjecture,
% 0.21/0.50    (![A:$i,B:$i]:
% 0.21/0.50     ( ( ( v1_funct_1 @ B ) & 
% 0.21/0.50         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.50       ( ![C:$i]:
% 0.21/0.50         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.21/0.50             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.50           ( ( r1_partfun1 @ B @ C ) <=>
% 0.21/0.50             ( ![D:$i]:
% 0.21/0.50               ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ A @ B ) ) =>
% 0.21/0.50                 ( ( k1_funct_1 @ B @ D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.50    (~( ![A:$i,B:$i]:
% 0.21/0.50        ( ( ( v1_funct_1 @ B ) & 
% 0.21/0.50            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.50          ( ![C:$i]:
% 0.21/0.50            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 0.21/0.50                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.50              ( ( r1_partfun1 @ B @ C ) <=>
% 0.21/0.50                ( ![D:$i]:
% 0.21/0.50                  ( ( r2_hidden @ D @ ( k1_relset_1 @ A @ A @ B ) ) =>
% 0.21/0.50                    ( ( k1_funct_1 @ B @ D ) = ( k1_funct_1 @ C @ D ) ) ) ) ) ) ) ) )),
% 0.21/0.50    inference('cnf.neg', [status(esa)], [t146_funct_2])).
% 0.21/0.50  thf('0', plain,
% 0.21/0.50      ((((k1_funct_1 @ sk_B @ sk_D) != (k1_funct_1 @ sk_C @ sk_D))
% 0.21/0.50        | ~ (r1_partfun1 @ sk_B @ sk_C))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('1', plain,
% 0.21/0.50      (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))) | 
% 0.21/0.50       ~ ((r1_partfun1 @ sk_B @ sk_C))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('2', plain,
% 0.21/0.50      (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50        | ~ (r1_partfun1 @ sk_B @ sk_C))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('3', plain,
% 0.21/0.50      (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))) | 
% 0.21/0.50       ~ ((r1_partfun1 @ sk_B @ sk_C))),
% 0.21/0.50      inference('split', [status(esa)], ['2'])).
% 0.21/0.50  thf('4', plain,
% 0.21/0.50      (![X11 : $i]:
% 0.21/0.50         (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50          | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11))
% 0.21/0.50          | (r1_partfun1 @ sk_B @ sk_C))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('5', plain,
% 0.21/0.50      (((r1_partfun1 @ sk_B @ sk_C)) <= (((r1_partfun1 @ sk_B @ sk_C)))),
% 0.21/0.50      inference('split', [status(esa)], ['4'])).
% 0.21/0.50  thf('6', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(t145_funct_2, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.50         ( v1_funct_1 @ C ) ) =>
% 0.21/0.50       ( ![D:$i]:
% 0.21/0.50         ( ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.50             ( v1_funct_2 @ D @ A @ B ) & ( v1_funct_1 @ D ) ) =>
% 0.21/0.50           ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.50             ( ( r1_partfun1 @ C @ D ) <=>
% 0.21/0.50               ( ![E:$i]:
% 0.21/0.50                 ( ( r2_hidden @ E @ ( k1_relset_1 @ A @ B @ C ) ) =>
% 0.21/0.50                   ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_1, axiom,
% 0.21/0.50    (![B:$i,A:$i]:
% 0.21/0.50     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.50       ( zip_tseitin_0 @ B @ A ) ))).
% 0.21/0.50  thf('7', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((zip_tseitin_0 @ X0 @ X1) | ((X0) = (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.50  thf('8', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $i > $o).
% 0.21/0.50  thf(zf_stmt_3, axiom,
% 0.21/0.50    (![D:$i,C:$i,B:$i,A:$i]:
% 0.21/0.50     ( ( zip_tseitin_1 @ D @ C @ B @ A ) =>
% 0.21/0.50       ( ( r1_partfun1 @ C @ D ) <=>
% 0.21/0.50         ( ![E:$i]:
% 0.21/0.50           ( ( r2_hidden @ E @ ( k1_relset_1 @ A @ B @ C ) ) =>
% 0.21/0.50             ( ( k1_funct_1 @ C @ E ) = ( k1_funct_1 @ D @ E ) ) ) ) ) ))).
% 0.21/0.50  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.21/0.50  thf(zf_stmt_5, axiom,
% 0.21/0.50    (![A:$i,B:$i,C:$i]:
% 0.21/0.50     ( ( ( v1_funct_1 @ C ) & 
% 0.21/0.50         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.50       ( ![D:$i]:
% 0.21/0.50         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.50             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.50           ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ D @ C @ B @ A ) ) ) ) ))).
% 0.21/0.50  thf('9', plain,
% 0.21/0.50      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.21/0.50         (~ (v1_funct_1 @ X7)
% 0.21/0.50          | ~ (v1_funct_2 @ X7 @ X8 @ X9)
% 0.21/0.50          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.21/0.50          | (zip_tseitin_1 @ X7 @ X10 @ X9 @ X8)
% 0.21/0.50          | ~ (zip_tseitin_0 @ X9 @ X8)
% 0.21/0.50          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9)))
% 0.21/0.50          | ~ (v1_funct_1 @ X10))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.50  thf('10', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_funct_1 @ X0)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.21/0.50          | ~ (zip_tseitin_0 @ sk_A @ sk_A)
% 0.21/0.50          | (zip_tseitin_1 @ sk_C @ X0 @ sk_A @ sk_A)
% 0.21/0.50          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 0.21/0.50          | ~ (v1_funct_1 @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.50  thf('11', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('12', plain, ((v1_funct_1 @ sk_C)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('13', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_funct_1 @ X0)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.21/0.50          | ~ (zip_tseitin_0 @ sk_A @ sk_A)
% 0.21/0.50          | (zip_tseitin_1 @ sk_C @ X0 @ sk_A @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.21/0.50  thf('14', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (((sk_A) = (k1_xboole_0))
% 0.21/0.50          | (zip_tseitin_1 @ sk_C @ X0 @ sk_A @ sk_A)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.21/0.50          | ~ (v1_funct_1 @ X0))),
% 0.21/0.50      inference('sup-', [status(thm)], ['7', '13'])).
% 0.21/0.50  thf('15', plain,
% 0.21/0.50      ((~ (v1_funct_1 @ sk_B)
% 0.21/0.50        | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A @ sk_A)
% 0.21/0.50        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['6', '14'])).
% 0.21/0.50  thf('16', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('17', plain,
% 0.21/0.50      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A @ sk_A) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.50  thf('18', plain,
% 0.21/0.50      (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B)))
% 0.21/0.50         <= (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.21/0.50      inference('split', [status(esa)], ['2'])).
% 0.21/0.50  thf('19', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.50         (~ (r1_partfun1 @ X4 @ X5)
% 0.21/0.50          | ((k1_funct_1 @ X4 @ X6) = (k1_funct_1 @ X5 @ X6))
% 0.21/0.50          | ~ (r2_hidden @ X6 @ (k1_relset_1 @ X2 @ X3 @ X4))
% 0.21/0.50          | ~ (zip_tseitin_1 @ X5 @ X4 @ X3 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.50  thf('20', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          (~ (zip_tseitin_1 @ X0 @ sk_B @ sk_A @ sk_A)
% 0.21/0.50           | ((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ X0 @ sk_D))
% 0.21/0.50           | ~ (r1_partfun1 @ sk_B @ X0)))
% 0.21/0.50         <= (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.50  thf('21', plain,
% 0.21/0.50      (((((sk_A) = (k1_xboole_0))
% 0.21/0.50         | ~ (r1_partfun1 @ sk_B @ sk_C)
% 0.21/0.50         | ((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))))
% 0.21/0.50         <= (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['17', '20'])).
% 0.21/0.50  thf('22', plain,
% 0.21/0.50      (((((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))
% 0.21/0.50         | ((sk_A) = (k1_xboole_0))))
% 0.21/0.50         <= (((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             ((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['5', '21'])).
% 0.21/0.50  thf('23', plain,
% 0.21/0.50      ((((k1_funct_1 @ sk_B @ sk_D) != (k1_funct_1 @ sk_C @ sk_D)))
% 0.21/0.50         <= (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('24', plain,
% 0.21/0.50      (((((k1_funct_1 @ sk_C @ sk_D) != (k1_funct_1 @ sk_C @ sk_D))
% 0.21/0.50         | ((sk_A) = (k1_xboole_0))))
% 0.21/0.50         <= (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))) & 
% 0.21/0.50             ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             ((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.50  thf('25', plain,
% 0.21/0.50      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.50         <= (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))) & 
% 0.21/0.50             ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             ((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.50  thf('26', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('27', plain,
% 0.21/0.50      (((m1_subset_1 @ sk_B @ 
% 0.21/0.50         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0))))
% 0.21/0.50         <= (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))) & 
% 0.21/0.50             ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             ((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.21/0.50      inference('sup+', [status(thm)], ['25', '26'])).
% 0.21/0.50  thf('28', plain,
% 0.21/0.50      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.50         <= (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))) & 
% 0.21/0.50             ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             ((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.50  thf('29', plain,
% 0.21/0.50      (((m1_subset_1 @ sk_B @ 
% 0.21/0.50         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0))))
% 0.21/0.50         <= (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))) & 
% 0.21/0.50             ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             ((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.21/0.50      inference('demod', [status(thm)], ['27', '28'])).
% 0.21/0.50  thf('30', plain,
% 0.21/0.50      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.50         <= (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))) & 
% 0.21/0.50             ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             ((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.50  thf('31', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_funct_1 @ X0)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.21/0.50          | ~ (zip_tseitin_0 @ sk_A @ sk_A)
% 0.21/0.50          | (zip_tseitin_1 @ sk_C @ X0 @ sk_A @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.21/0.50  thf('32', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          (~ (zip_tseitin_0 @ sk_A @ k1_xboole_0)
% 0.21/0.50           | (zip_tseitin_1 @ sk_C @ X0 @ sk_A @ sk_A)
% 0.21/0.50           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.21/0.50           | ~ (v1_funct_1 @ X0)))
% 0.21/0.50         <= (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))) & 
% 0.21/0.50             ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             ((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['30', '31'])).
% 0.21/0.50  thf('33', plain,
% 0.21/0.50      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.50         <= (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))) & 
% 0.21/0.50             ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             ((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.50  thf('34', plain,
% 0.21/0.50      (![X0 : $i, X1 : $i]:
% 0.21/0.50         ((zip_tseitin_0 @ X0 @ X1) | ((X1) != (k1_xboole_0)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.50  thf('35', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ k1_xboole_0)),
% 0.21/0.50      inference('simplify', [status(thm)], ['34'])).
% 0.21/0.50  thf('36', plain,
% 0.21/0.50      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.50         <= (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))) & 
% 0.21/0.50             ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             ((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.50  thf('37', plain,
% 0.21/0.50      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.50         <= (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))) & 
% 0.21/0.50             ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             ((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.50  thf('38', plain,
% 0.21/0.50      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.50         <= (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))) & 
% 0.21/0.50             ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             ((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.50  thf('39', plain,
% 0.21/0.50      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.50         <= (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))) & 
% 0.21/0.50             ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             ((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.50  thf('40', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          ((zip_tseitin_1 @ sk_C @ X0 @ k1_xboole_0 @ k1_xboole_0)
% 0.21/0.50           | ~ (m1_subset_1 @ X0 @ 
% 0.21/0.50                (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))
% 0.21/0.50           | ~ (v1_funct_1 @ X0)))
% 0.21/0.50         <= (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))) & 
% 0.21/0.50             ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             ((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.21/0.50      inference('demod', [status(thm)],
% 0.21/0.50                ['32', '33', '35', '36', '37', '38', '39'])).
% 0.21/0.50  thf('41', plain,
% 0.21/0.50      (((~ (v1_funct_1 @ sk_B)
% 0.21/0.50         | (zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0 @ k1_xboole_0)))
% 0.21/0.50         <= (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))) & 
% 0.21/0.50             ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             ((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['29', '40'])).
% 0.21/0.50  thf('42', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('43', plain,
% 0.21/0.50      (((zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0 @ k1_xboole_0))
% 0.21/0.50         <= (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))) & 
% 0.21/0.50             ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             ((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.21/0.50      inference('demod', [status(thm)], ['41', '42'])).
% 0.21/0.50  thf('44', plain,
% 0.21/0.50      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.50         <= (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))) & 
% 0.21/0.50             ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             ((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.50  thf('45', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          (~ (zip_tseitin_1 @ X0 @ sk_B @ sk_A @ sk_A)
% 0.21/0.50           | ((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ X0 @ sk_D))
% 0.21/0.50           | ~ (r1_partfun1 @ sk_B @ X0)))
% 0.21/0.50         <= (((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.50  thf('46', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          (~ (zip_tseitin_1 @ X0 @ sk_B @ sk_A @ k1_xboole_0)
% 0.21/0.50           | ~ (r1_partfun1 @ sk_B @ X0)
% 0.21/0.50           | ((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ X0 @ sk_D))))
% 0.21/0.50         <= (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))) & 
% 0.21/0.50             ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             ((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.50  thf('47', plain,
% 0.21/0.50      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.50         <= (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))) & 
% 0.21/0.50             ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             ((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['24'])).
% 0.21/0.50  thf('48', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          (~ (zip_tseitin_1 @ X0 @ sk_B @ k1_xboole_0 @ k1_xboole_0)
% 0.21/0.50           | ~ (r1_partfun1 @ sk_B @ X0)
% 0.21/0.50           | ((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ X0 @ sk_D))))
% 0.21/0.50         <= (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))) & 
% 0.21/0.50             ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             ((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.21/0.50      inference('demod', [status(thm)], ['46', '47'])).
% 0.21/0.50  thf('49', plain,
% 0.21/0.50      (((((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))
% 0.21/0.50         | ~ (r1_partfun1 @ sk_B @ sk_C)))
% 0.21/0.50         <= (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))) & 
% 0.21/0.50             ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             ((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['43', '48'])).
% 0.21/0.50  thf('50', plain,
% 0.21/0.50      (((r1_partfun1 @ sk_B @ sk_C)) <= (((r1_partfun1 @ sk_B @ sk_C)))),
% 0.21/0.50      inference('split', [status(esa)], ['4'])).
% 0.21/0.50  thf('51', plain,
% 0.21/0.50      ((((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C @ sk_D)))
% 0.21/0.50         <= (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))) & 
% 0.21/0.50             ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             ((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))))),
% 0.21/0.50      inference('demod', [status(thm)], ['49', '50'])).
% 0.21/0.50  thf('52', plain,
% 0.21/0.50      ((((k1_funct_1 @ sk_B @ sk_D) != (k1_funct_1 @ sk_C @ sk_D)))
% 0.21/0.50         <= (~ (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C @ sk_D))))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('53', plain,
% 0.21/0.50      (~ ((r2_hidden @ sk_D @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))) | 
% 0.21/0.50       ~ ((r1_partfun1 @ sk_B @ sk_C)) | 
% 0.21/0.50       (((k1_funct_1 @ sk_B @ sk_D) = (k1_funct_1 @ sk_C @ sk_D)))),
% 0.21/0.50      inference('simplify_reflect-', [status(thm)], ['51', '52'])).
% 0.21/0.50  thf('54', plain,
% 0.21/0.50      ((![X11 : $i]:
% 0.21/0.50          (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50           | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11)))) | 
% 0.21/0.50       ((r1_partfun1 @ sk_B @ sk_C))),
% 0.21/0.50      inference('split', [status(esa)], ['4'])).
% 0.21/0.50  thf('55', plain,
% 0.21/0.50      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A @ sk_A) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.50  thf('56', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.50         ((r2_hidden @ (sk_E @ X2 @ X3 @ X4 @ X5) @ 
% 0.21/0.50           (k1_relset_1 @ X2 @ X3 @ X4))
% 0.21/0.50          | (r1_partfun1 @ X4 @ X5)
% 0.21/0.50          | ~ (zip_tseitin_1 @ X5 @ X4 @ X3 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.50  thf('57', plain,
% 0.21/0.50      ((((sk_A) = (k1_xboole_0))
% 0.21/0.50        | (r1_partfun1 @ sk_B @ sk_C)
% 0.21/0.50        | (r2_hidden @ (sk_E @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 0.21/0.50           (k1_relset_1 @ sk_A @ sk_A @ sk_B)))),
% 0.21/0.50      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.50  thf('58', plain,
% 0.21/0.50      ((![X11 : $i]:
% 0.21/0.50          (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50           | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11))))
% 0.21/0.50         <= ((![X11 : $i]:
% 0.21/0.50                (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11)))))),
% 0.21/0.50      inference('split', [status(esa)], ['4'])).
% 0.21/0.50  thf('59', plain,
% 0.21/0.50      ((((r1_partfun1 @ sk_B @ sk_C)
% 0.21/0.50         | ((sk_A) = (k1_xboole_0))
% 0.21/0.50         | ((k1_funct_1 @ sk_B @ (sk_E @ sk_A @ sk_A @ sk_B @ sk_C))
% 0.21/0.50             = (k1_funct_1 @ sk_C @ (sk_E @ sk_A @ sk_A @ sk_B @ sk_C)))))
% 0.21/0.50         <= ((![X11 : $i]:
% 0.21/0.50                (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11)))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['57', '58'])).
% 0.21/0.50  thf('60', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.50         (((k1_funct_1 @ X4 @ (sk_E @ X2 @ X3 @ X4 @ X5))
% 0.21/0.50            != (k1_funct_1 @ X5 @ (sk_E @ X2 @ X3 @ X4 @ X5)))
% 0.21/0.50          | (r1_partfun1 @ X4 @ X5)
% 0.21/0.50          | ~ (zip_tseitin_1 @ X5 @ X4 @ X3 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.50  thf('61', plain,
% 0.21/0.50      (((((k1_funct_1 @ sk_C @ (sk_E @ sk_A @ sk_A @ sk_B @ sk_C))
% 0.21/0.50           != (k1_funct_1 @ sk_C @ (sk_E @ sk_A @ sk_A @ sk_B @ sk_C)))
% 0.21/0.50         | ((sk_A) = (k1_xboole_0))
% 0.21/0.50         | (r1_partfun1 @ sk_B @ sk_C)
% 0.21/0.50         | ~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A @ sk_A)
% 0.21/0.50         | (r1_partfun1 @ sk_B @ sk_C)))
% 0.21/0.50         <= ((![X11 : $i]:
% 0.21/0.50                (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11)))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['59', '60'])).
% 0.21/0.50  thf('62', plain,
% 0.21/0.50      (((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A @ sk_A)
% 0.21/0.50         | (r1_partfun1 @ sk_B @ sk_C)
% 0.21/0.50         | ((sk_A) = (k1_xboole_0))))
% 0.21/0.50         <= ((![X11 : $i]:
% 0.21/0.50                (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11)))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['61'])).
% 0.21/0.50  thf('63', plain,
% 0.21/0.50      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A @ sk_A) | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.50      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.50  thf('64', plain,
% 0.21/0.50      (((((sk_A) = (k1_xboole_0)) | (r1_partfun1 @ sk_B @ sk_C)))
% 0.21/0.50         <= ((![X11 : $i]:
% 0.21/0.50                (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11)))))),
% 0.21/0.50      inference('clc', [status(thm)], ['62', '63'])).
% 0.21/0.50  thf('65', plain,
% 0.21/0.50      ((~ (r1_partfun1 @ sk_B @ sk_C)) <= (~ ((r1_partfun1 @ sk_B @ sk_C)))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('66', plain,
% 0.21/0.50      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.50         <= (~ ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             (![X11 : $i]:
% 0.21/0.50                (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11)))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.50  thf('67', plain,
% 0.21/0.50      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('68', plain,
% 0.21/0.50      (((m1_subset_1 @ sk_B @ 
% 0.21/0.50         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0))))
% 0.21/0.50         <= (~ ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             (![X11 : $i]:
% 0.21/0.50                (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11)))))),
% 0.21/0.50      inference('sup+', [status(thm)], ['66', '67'])).
% 0.21/0.50  thf('69', plain,
% 0.21/0.50      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.50         <= (~ ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             (![X11 : $i]:
% 0.21/0.50                (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11)))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.50  thf('70', plain,
% 0.21/0.50      (((m1_subset_1 @ sk_B @ 
% 0.21/0.50         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0))))
% 0.21/0.50         <= (~ ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             (![X11 : $i]:
% 0.21/0.50                (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11)))))),
% 0.21/0.50      inference('demod', [status(thm)], ['68', '69'])).
% 0.21/0.50  thf('71', plain,
% 0.21/0.50      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.50         <= (~ ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             (![X11 : $i]:
% 0.21/0.50                (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11)))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.50  thf('72', plain,
% 0.21/0.50      (![X0 : $i]:
% 0.21/0.50         (~ (v1_funct_1 @ X0)
% 0.21/0.50          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.21/0.50          | ~ (zip_tseitin_0 @ sk_A @ sk_A)
% 0.21/0.50          | (zip_tseitin_1 @ sk_C @ X0 @ sk_A @ sk_A))),
% 0.21/0.50      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.21/0.50  thf('73', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          (~ (zip_tseitin_0 @ sk_A @ k1_xboole_0)
% 0.21/0.50           | (zip_tseitin_1 @ sk_C @ X0 @ sk_A @ sk_A)
% 0.21/0.50           | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.21/0.50           | ~ (v1_funct_1 @ X0)))
% 0.21/0.50         <= (~ ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             (![X11 : $i]:
% 0.21/0.50                (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11)))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['71', '72'])).
% 0.21/0.50  thf('74', plain,
% 0.21/0.50      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.50         <= (~ ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             (![X11 : $i]:
% 0.21/0.50                (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11)))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.50  thf('75', plain, (![X0 : $i]: (zip_tseitin_0 @ X0 @ k1_xboole_0)),
% 0.21/0.50      inference('simplify', [status(thm)], ['34'])).
% 0.21/0.50  thf('76', plain,
% 0.21/0.50      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.50         <= (~ ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             (![X11 : $i]:
% 0.21/0.50                (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11)))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.50  thf('77', plain,
% 0.21/0.50      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.50         <= (~ ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             (![X11 : $i]:
% 0.21/0.50                (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11)))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.50  thf('78', plain,
% 0.21/0.50      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.50         <= (~ ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             (![X11 : $i]:
% 0.21/0.50                (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11)))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.50  thf('79', plain,
% 0.21/0.50      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.50         <= (~ ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             (![X11 : $i]:
% 0.21/0.50                (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11)))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.50  thf('80', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          ((zip_tseitin_1 @ sk_C @ X0 @ k1_xboole_0 @ k1_xboole_0)
% 0.21/0.50           | ~ (m1_subset_1 @ X0 @ 
% 0.21/0.50                (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0)))
% 0.21/0.50           | ~ (v1_funct_1 @ X0)))
% 0.21/0.50         <= (~ ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             (![X11 : $i]:
% 0.21/0.50                (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11)))))),
% 0.21/0.50      inference('demod', [status(thm)],
% 0.21/0.50                ['73', '74', '75', '76', '77', '78', '79'])).
% 0.21/0.50  thf('81', plain,
% 0.21/0.50      (((~ (v1_funct_1 @ sk_B)
% 0.21/0.50         | (zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0 @ k1_xboole_0)))
% 0.21/0.50         <= (~ ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             (![X11 : $i]:
% 0.21/0.50                (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11)))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['70', '80'])).
% 0.21/0.50  thf('82', plain, ((v1_funct_1 @ sk_B)),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.50  thf('83', plain,
% 0.21/0.50      (((zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0 @ k1_xboole_0))
% 0.21/0.50         <= (~ ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             (![X11 : $i]:
% 0.21/0.50                (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11)))))),
% 0.21/0.50      inference('demod', [status(thm)], ['81', '82'])).
% 0.21/0.50  thf('84', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.50         ((r2_hidden @ (sk_E @ X2 @ X3 @ X4 @ X5) @ 
% 0.21/0.50           (k1_relset_1 @ X2 @ X3 @ X4))
% 0.21/0.50          | (r1_partfun1 @ X4 @ X5)
% 0.21/0.50          | ~ (zip_tseitin_1 @ X5 @ X4 @ X3 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.50  thf('85', plain,
% 0.21/0.50      ((((r1_partfun1 @ sk_B @ sk_C)
% 0.21/0.50         | (r2_hidden @ (sk_E @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_C) @ 
% 0.21/0.50            (k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B))))
% 0.21/0.50         <= (~ ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             (![X11 : $i]:
% 0.21/0.50                (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11)))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['83', '84'])).
% 0.21/0.50  thf('86', plain,
% 0.21/0.50      ((~ (r1_partfun1 @ sk_B @ sk_C)) <= (~ ((r1_partfun1 @ sk_B @ sk_C)))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('87', plain,
% 0.21/0.50      (((r2_hidden @ (sk_E @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_C) @ 
% 0.21/0.50         (k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B)))
% 0.21/0.50         <= (~ ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             (![X11 : $i]:
% 0.21/0.50                (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11)))))),
% 0.21/0.50      inference('clc', [status(thm)], ['85', '86'])).
% 0.21/0.50  thf('88', plain,
% 0.21/0.50      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.50         <= (~ ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             (![X11 : $i]:
% 0.21/0.50                (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11)))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.50  thf('89', plain,
% 0.21/0.50      ((![X11 : $i]:
% 0.21/0.50          (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50           | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11))))
% 0.21/0.50         <= ((![X11 : $i]:
% 0.21/0.50                (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11)))))),
% 0.21/0.50      inference('split', [status(esa)], ['4'])).
% 0.21/0.50  thf('90', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          (~ (r2_hidden @ X0 @ (k1_relset_1 @ sk_A @ k1_xboole_0 @ sk_B))
% 0.21/0.50           | ((k1_funct_1 @ sk_B @ X0) = (k1_funct_1 @ sk_C @ X0))))
% 0.21/0.50         <= (~ ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             (![X11 : $i]:
% 0.21/0.50                (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11)))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['88', '89'])).
% 0.21/0.50  thf('91', plain,
% 0.21/0.50      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.50         <= (~ ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             (![X11 : $i]:
% 0.21/0.50                (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11)))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['64', '65'])).
% 0.21/0.50  thf('92', plain,
% 0.21/0.50      ((![X0 : $i]:
% 0.21/0.50          (~ (r2_hidden @ X0 @ (k1_relset_1 @ k1_xboole_0 @ k1_xboole_0 @ sk_B))
% 0.21/0.50           | ((k1_funct_1 @ sk_B @ X0) = (k1_funct_1 @ sk_C @ X0))))
% 0.21/0.50         <= (~ ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             (![X11 : $i]:
% 0.21/0.50                (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11)))))),
% 0.21/0.50      inference('demod', [status(thm)], ['90', '91'])).
% 0.21/0.50  thf('93', plain,
% 0.21/0.50      ((((k1_funct_1 @ sk_B @ (sk_E @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_C))
% 0.21/0.50          = (k1_funct_1 @ sk_C @ 
% 0.21/0.50             (sk_E @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_C))))
% 0.21/0.50         <= (~ ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             (![X11 : $i]:
% 0.21/0.50                (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11)))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['87', '92'])).
% 0.21/0.50  thf('94', plain,
% 0.21/0.50      (![X2 : $i, X3 : $i, X4 : $i, X5 : $i]:
% 0.21/0.50         (((k1_funct_1 @ X4 @ (sk_E @ X2 @ X3 @ X4 @ X5))
% 0.21/0.50            != (k1_funct_1 @ X5 @ (sk_E @ X2 @ X3 @ X4 @ X5)))
% 0.21/0.50          | (r1_partfun1 @ X4 @ X5)
% 0.21/0.50          | ~ (zip_tseitin_1 @ X5 @ X4 @ X3 @ X2))),
% 0.21/0.50      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.50  thf('95', plain,
% 0.21/0.50      (((((k1_funct_1 @ sk_C @ (sk_E @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_C))
% 0.21/0.50           != (k1_funct_1 @ sk_C @ 
% 0.21/0.50               (sk_E @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_C)))
% 0.21/0.50         | ~ (zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0 @ k1_xboole_0)
% 0.21/0.50         | (r1_partfun1 @ sk_B @ sk_C)))
% 0.21/0.50         <= (~ ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             (![X11 : $i]:
% 0.21/0.50                (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11)))))),
% 0.21/0.50      inference('sup-', [status(thm)], ['93', '94'])).
% 0.21/0.50  thf('96', plain,
% 0.21/0.50      (((zip_tseitin_1 @ sk_C @ sk_B @ k1_xboole_0 @ k1_xboole_0))
% 0.21/0.50         <= (~ ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             (![X11 : $i]:
% 0.21/0.50                (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11)))))),
% 0.21/0.50      inference('demod', [status(thm)], ['81', '82'])).
% 0.21/0.50  thf('97', plain,
% 0.21/0.50      (((((k1_funct_1 @ sk_C @ (sk_E @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_C))
% 0.21/0.50           != (k1_funct_1 @ sk_C @ 
% 0.21/0.50               (sk_E @ k1_xboole_0 @ k1_xboole_0 @ sk_B @ sk_C)))
% 0.21/0.50         | (r1_partfun1 @ sk_B @ sk_C)))
% 0.21/0.50         <= (~ ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             (![X11 : $i]:
% 0.21/0.50                (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11)))))),
% 0.21/0.50      inference('demod', [status(thm)], ['95', '96'])).
% 0.21/0.50  thf('98', plain,
% 0.21/0.50      (((r1_partfun1 @ sk_B @ sk_C))
% 0.21/0.50         <= (~ ((r1_partfun1 @ sk_B @ sk_C)) & 
% 0.21/0.50             (![X11 : $i]:
% 0.21/0.50                (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50                 | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11)))))),
% 0.21/0.50      inference('simplify', [status(thm)], ['97'])).
% 0.21/0.50  thf('99', plain,
% 0.21/0.50      ((~ (r1_partfun1 @ sk_B @ sk_C)) <= (~ ((r1_partfun1 @ sk_B @ sk_C)))),
% 0.21/0.50      inference('split', [status(esa)], ['0'])).
% 0.21/0.50  thf('100', plain,
% 0.21/0.50      (~
% 0.21/0.50       (![X11 : $i]:
% 0.21/0.50          (~ (r2_hidden @ X11 @ (k1_relset_1 @ sk_A @ sk_A @ sk_B))
% 0.21/0.50           | ((k1_funct_1 @ sk_B @ X11) = (k1_funct_1 @ sk_C @ X11)))) | 
% 0.21/0.50       ((r1_partfun1 @ sk_B @ sk_C))),
% 0.21/0.50      inference('sup-', [status(thm)], ['98', '99'])).
% 0.21/0.50  thf('101', plain, ($false),
% 0.21/0.50      inference('sat_resolution*', [status(thm)], ['1', '3', '53', '54', '100'])).
% 0.21/0.50  
% 0.21/0.50  % SZS output end Refutation
% 0.21/0.50  
% 0.21/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
