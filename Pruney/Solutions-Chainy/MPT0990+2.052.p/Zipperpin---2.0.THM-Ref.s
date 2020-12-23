%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uD2OU05AWf

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:55:02 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 317 expanded)
%              Number of leaves         :   41 ( 111 expanded)
%              Depth                    :   14
%              Number of atoms          : 1494 (8382 expanded)
%              Number of equality atoms :  105 ( 596 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t36_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ A )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
         => ( ( ( ( k2_relset_1 @ A @ B @ C )
                = B )
              & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
              & ( v2_funct_1 @ C ) )
           => ( ( A = k1_xboole_0 )
              | ( B = k1_xboole_0 )
              | ( D
                = ( k2_funct_1 @ C ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ B @ A )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
           => ( ( ( ( k2_relset_1 @ A @ B @ C )
                  = B )
                & ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ ( k6_partfun1 @ A ) )
                & ( v2_funct_1 @ C ) )
             => ( ( A = k1_xboole_0 )
                | ( B = k1_xboole_0 )
                | ( D
                  = ( k2_funct_1 @ C ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_funct_2])).

thf('0',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('5',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 )
        = ( k5_relat_1 @ X29 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k5_relat_1 @ sk_C @ sk_D ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['2','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('15',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['13','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k5_relat_1 @ sk_C @ sk_D ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('22',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('23',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) )
      | ( X11 = X14 )
      | ~ ( r2_relset_1 @ X12 @ X13 @ X11 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['12','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t31_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v2_funct_1 @ C )
          & ( ( k2_relset_1 @ A @ B @ C )
            = B ) )
       => ( ( v1_funct_1 @ ( k2_funct_1 @ C ) )
          & ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A )
          & ( m1_subset_1 @ ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ) )).

thf('27',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v2_funct_1 @ X36 )
      | ( ( k2_relset_1 @ X38 @ X37 @ X36 )
       != X37 )
      | ( m1_subset_1 @ ( k2_funct_1 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('28',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,
    ( ( m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['28','29','30','31','32'])).

thf('34',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('36',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( v2_funct_1 @ X36 )
      | ( ( k2_relset_1 @ X38 @ X37 @ X36 )
       != X37 )
      | ( v1_funct_1 @ ( k2_funct_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t31_funct_2])).

thf('39',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['39','40','41','42','43'])).

thf('45',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,(
    m1_subset_1 @ ( k2_funct_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('48',plain,
    ( ~ ( v1_funct_1 @ ( k2_funct_1 @ sk_C ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_funct_1 @ ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['44'])).

thf('50',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t35_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( ( k2_relset_1 @ A @ B @ C )
            = B )
          & ( v2_funct_1 @ C ) )
       => ( ( B = k1_xboole_0 )
          | ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) )
              = ( k6_partfun1 @ A ) )
            & ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C )
              = ( k6_partfun1 @ B ) ) ) ) ) ) )).

thf('52',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( X39 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X39 ) ) )
      | ( ( k5_relat_1 @ X40 @ ( k2_funct_1 @ X40 ) )
        = ( k6_partfun1 @ X41 ) )
      | ~ ( v2_funct_1 @ X40 )
      | ( ( k2_relset_1 @ X41 @ X39 @ X40 )
       != X39 ) ) ),
    inference(cnf,[status(esa)],[t35_funct_2])).

thf('53',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('54',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( X39 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X39 ) ) )
      | ( ( k5_relat_1 @ X40 @ ( k2_funct_1 @ X40 ) )
        = ( k6_relat_1 @ X41 ) )
      | ~ ( v2_funct_1 @ X40 )
      | ( ( k2_relset_1 @ X41 @ X39 @ X40 )
       != X39 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
     != sk_B )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ( sk_B = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( sk_B != sk_B )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) )
    | ( sk_B = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('61',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,
    ( ( k5_relat_1 @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ ( k2_funct_1 @ sk_C ) )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['50','63'])).

thf('65',plain,(
    m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','45','64'])).

thf('66',plain,
    ( ( k5_relat_1 @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['25','65'])).

thf(t63_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ! [B: $i] :
          ( ( ( v1_relat_1 @ B )
            & ( v1_funct_1 @ B ) )
         => ( ( ( v2_funct_1 @ A )
              & ( ( k2_relat_1 @ A )
                = ( k1_relat_1 @ B ) )
              & ( ( k5_relat_1 @ A @ B )
                = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) )
           => ( B
              = ( k2_funct_1 @ A ) ) ) ) ) )).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( X0
        = ( k2_funct_1 @ X1 ) )
      | ( ( k5_relat_1 @ X1 @ X0 )
       != ( k6_relat_1 @ ( k1_relat_1 @ X1 ) ) )
      | ( ( k2_relat_1 @ X1 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v2_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t63_funct_1])).

thf('68',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ ( k1_relat_1 @ sk_C ) ) )
    | ~ ( v1_relat_1 @ sk_C )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v2_funct_1 @ sk_C )
    | ( ( k2_relat_1 @ sk_C )
     != ( k1_relat_1 @ sk_D ) )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
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

thf('70',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ( X17
        = ( k1_relset_1 @ X17 @ X18 @ X19 ) )
      | ~ ( zip_tseitin_1 @ X19 @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('71',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('72',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('73',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('74',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X20 @ X21 )
      | ( zip_tseitin_1 @ X22 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('75',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,
    ( ( sk_B = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['72','75'])).

thf('77',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    zip_tseitin_1 @ sk_C @ sk_B @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('80',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k1_relset_1 @ X6 @ X7 @ X5 )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('81',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_C ) ),
    inference(demod,[status(thm)],['71','78','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('84',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('85',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v2_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('89',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( ( k2_relset_1 @ X9 @ X10 @ X8 )
        = ( k2_relat_1 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('90',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_B ),
    inference('sup+',[status(thm)],['90','91'])).

thf('93',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( v1_funct_2 @ X19 @ X17 @ X18 )
      | ( X17
        = ( k1_relset_1 @ X17 @ X18 @ X19 ) )
      | ~ ( zip_tseitin_1 @ X19 @ X18 @ X17 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('95',plain,
    ( ~ ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ( sk_B
      = ( k1_relset_1 @ sk_B @ sk_A @ sk_D ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X15: $i,X16: $i] :
      ( ( zip_tseitin_0 @ X15 @ X16 )
      | ( X15 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('97',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( zip_tseitin_0 @ X20 @ X21 )
      | ( zip_tseitin_1 @ X22 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('99',plain,
    ( ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_D @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['96','99'])).

thf('101',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    zip_tseitin_1 @ sk_D @ sk_A @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['100','101'])).

thf('103',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( ( k1_relset_1 @ X6 @ X7 @ X5 )
        = ( k1_relat_1 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('105',plain,
    ( ( k1_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,
    ( sk_B
    = ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['95','102','105'])).

thf('107',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('110',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,
    ( ( ( k6_relat_1 @ sk_A )
     != ( k6_relat_1 @ sk_A ) )
    | ( sk_B != sk_B )
    | ( sk_D
      = ( k2_funct_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['68','82','85','86','87','92','106','107','110'])).

thf('112',plain,
    ( sk_D
    = ( k2_funct_1 @ sk_C ) ),
    inference(simplify,[status(thm)],['111'])).

thf('113',plain,(
    sk_D
 != ( k2_funct_1 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['112','113'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uD2OU05AWf
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:02:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.75/0.96  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.75/0.96  % Solved by: fo/fo7.sh
% 0.75/0.96  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.96  % done 329 iterations in 0.499s
% 0.75/0.96  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.75/0.96  % SZS output start Refutation
% 0.75/0.96  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.75/0.96  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.75/0.96  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.75/0.96  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.75/0.96  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.75/0.96  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.75/0.96  thf(sk_C_type, type, sk_C: $i).
% 0.75/0.96  thf(sk_B_type, type, sk_B: $i).
% 0.75/0.96  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.75/0.96  thf(sk_D_type, type, sk_D: $i).
% 0.75/0.96  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.75/0.96  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.75/0.96  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.75/0.96  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.96  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.75/0.96  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.96  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.75/0.96  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.75/0.96  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 0.75/0.96  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.75/0.96  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.75/0.96  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.75/0.96  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.75/0.96  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.75/0.96  thf(t36_funct_2, conjecture,
% 0.75/0.96    (![A:$i,B:$i,C:$i]:
% 0.75/0.96     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.75/0.96         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/0.96       ( ![D:$i]:
% 0.75/0.96         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.75/0.96             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.75/0.96           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.75/0.96               ( r2_relset_1 @
% 0.75/0.96                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.75/0.96                 ( k6_partfun1 @ A ) ) & 
% 0.75/0.96               ( v2_funct_1 @ C ) ) =>
% 0.75/0.96             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.75/0.96               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 0.75/0.96  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.96    (~( ![A:$i,B:$i,C:$i]:
% 0.75/0.96        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.75/0.96            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/0.96          ( ![D:$i]:
% 0.75/0.96            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.75/0.96                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.75/0.96              ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 0.75/0.96                  ( r2_relset_1 @
% 0.75/0.96                    A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.75/0.96                    ( k6_partfun1 @ A ) ) & 
% 0.75/0.96                  ( v2_funct_1 @ C ) ) =>
% 0.75/0.96                ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.75/0.96                  ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ) )),
% 0.75/0.96    inference('cnf.neg', [status(esa)], [t36_funct_2])).
% 0.75/0.96  thf('0', plain,
% 0.75/0.96      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.75/0.96        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.75/0.96        (k6_partfun1 @ sk_A))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf(redefinition_k6_partfun1, axiom,
% 0.75/0.96    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.75/0.96  thf('1', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 0.75/0.96      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.75/0.96  thf('2', plain,
% 0.75/0.96      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.75/0.96        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.75/0.96        (k6_relat_1 @ sk_A))),
% 0.75/0.96      inference('demod', [status(thm)], ['0', '1'])).
% 0.75/0.96  thf('3', plain,
% 0.75/0.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('4', plain,
% 0.75/0.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf(redefinition_k1_partfun1, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.75/0.96     ( ( ( v1_funct_1 @ E ) & 
% 0.75/0.96         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.75/0.96         ( v1_funct_1 @ F ) & 
% 0.75/0.96         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.75/0.96       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.75/0.96  thf('5', plain,
% 0.75/0.96      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.75/0.96         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.75/0.96          | ~ (v1_funct_1 @ X29)
% 0.75/0.96          | ~ (v1_funct_1 @ X32)
% 0.75/0.96          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.75/0.96          | ((k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32)
% 0.75/0.96              = (k5_relat_1 @ X29 @ X32)))),
% 0.75/0.96      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 0.75/0.96  thf('6', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.96         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.75/0.96            = (k5_relat_1 @ sk_C @ X0))
% 0.75/0.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.75/0.96          | ~ (v1_funct_1 @ X0)
% 0.75/0.96          | ~ (v1_funct_1 @ sk_C))),
% 0.75/0.96      inference('sup-', [status(thm)], ['4', '5'])).
% 0.75/0.96  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('8', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.96         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.75/0.96            = (k5_relat_1 @ sk_C @ X0))
% 0.75/0.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.75/0.96          | ~ (v1_funct_1 @ X0))),
% 0.75/0.96      inference('demod', [status(thm)], ['6', '7'])).
% 0.75/0.96  thf('9', plain,
% 0.75/0.96      ((~ (v1_funct_1 @ sk_D)
% 0.75/0.96        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.75/0.96            = (k5_relat_1 @ sk_C @ sk_D)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['3', '8'])).
% 0.75/0.96  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('11', plain,
% 0.75/0.96      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.75/0.96         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.75/0.96      inference('demod', [status(thm)], ['9', '10'])).
% 0.75/0.96  thf('12', plain,
% 0.75/0.96      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.75/0.96        (k6_relat_1 @ sk_A))),
% 0.75/0.96      inference('demod', [status(thm)], ['2', '11'])).
% 0.75/0.96  thf('13', plain,
% 0.75/0.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('14', plain,
% 0.75/0.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf(dt_k1_partfun1, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.75/0.96     ( ( ( v1_funct_1 @ E ) & 
% 0.75/0.96         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.75/0.96         ( v1_funct_1 @ F ) & 
% 0.75/0.96         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.75/0.96       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.75/0.96         ( m1_subset_1 @
% 0.75/0.96           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.75/0.96           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.75/0.96  thf('15', plain,
% 0.75/0.96      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.75/0.96         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.75/0.96          | ~ (v1_funct_1 @ X23)
% 0.75/0.96          | ~ (v1_funct_1 @ X26)
% 0.75/0.96          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.75/0.96          | (m1_subset_1 @ (k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26) @ 
% 0.75/0.96             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X28))))),
% 0.75/0.96      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.75/0.96  thf('16', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.96         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.75/0.96           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.75/0.96          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.75/0.96          | ~ (v1_funct_1 @ X1)
% 0.75/0.96          | ~ (v1_funct_1 @ sk_C))),
% 0.75/0.96      inference('sup-', [status(thm)], ['14', '15'])).
% 0.75/0.96  thf('17', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('18', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.96         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.75/0.96           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.75/0.96          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.75/0.96          | ~ (v1_funct_1 @ X1))),
% 0.75/0.96      inference('demod', [status(thm)], ['16', '17'])).
% 0.75/0.96  thf('19', plain,
% 0.75/0.96      ((~ (v1_funct_1 @ sk_D)
% 0.75/0.96        | (m1_subset_1 @ 
% 0.75/0.96           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.75/0.96           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.75/0.96      inference('sup-', [status(thm)], ['13', '18'])).
% 0.75/0.96  thf('20', plain, ((v1_funct_1 @ sk_D)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('21', plain,
% 0.75/0.96      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.75/0.96         = (k5_relat_1 @ sk_C @ sk_D))),
% 0.75/0.96      inference('demod', [status(thm)], ['9', '10'])).
% 0.75/0.96  thf('22', plain,
% 0.75/0.96      ((m1_subset_1 @ (k5_relat_1 @ sk_C @ sk_D) @ 
% 0.75/0.96        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.75/0.96      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.75/0.96  thf(redefinition_r2_relset_1, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.96     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.75/0.96         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/0.96       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.75/0.96  thf('23', plain,
% 0.75/0.96      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.75/0.96         (~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.75/0.96          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13)))
% 0.75/0.96          | ((X11) = (X14))
% 0.75/0.96          | ~ (r2_relset_1 @ X12 @ X13 @ X11 @ X14))),
% 0.75/0.96      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.75/0.96  thf('24', plain,
% 0.75/0.96      (![X0 : $i]:
% 0.75/0.96         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C @ sk_D) @ X0)
% 0.75/0.96          | ((k5_relat_1 @ sk_C @ sk_D) = (X0))
% 0.75/0.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.75/0.96      inference('sup-', [status(thm)], ['22', '23'])).
% 0.75/0.96  thf('25', plain,
% 0.75/0.96      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.75/0.96           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.75/0.96        | ((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['12', '24'])).
% 0.75/0.96  thf('26', plain,
% 0.75/0.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf(t31_funct_2, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i]:
% 0.75/0.96     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.75/0.96         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/0.96       ( ( ( v2_funct_1 @ C ) & ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) =>
% 0.75/0.96         ( ( v1_funct_1 @ ( k2_funct_1 @ C ) ) & 
% 0.75/0.96           ( v1_funct_2 @ ( k2_funct_1 @ C ) @ B @ A ) & 
% 0.75/0.96           ( m1_subset_1 @
% 0.75/0.96             ( k2_funct_1 @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) ) ))).
% 0.75/0.96  thf('27', plain,
% 0.75/0.96      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.75/0.96         (~ (v2_funct_1 @ X36)
% 0.75/0.96          | ((k2_relset_1 @ X38 @ X37 @ X36) != (X37))
% 0.75/0.96          | (m1_subset_1 @ (k2_funct_1 @ X36) @ 
% 0.75/0.96             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.75/0.96          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 0.75/0.96          | ~ (v1_funct_2 @ X36 @ X38 @ X37)
% 0.75/0.96          | ~ (v1_funct_1 @ X36))),
% 0.75/0.96      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.75/0.96  thf('28', plain,
% 0.75/0.96      ((~ (v1_funct_1 @ sk_C)
% 0.75/0.96        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.75/0.96        | (m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.75/0.96           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.75/0.96        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.75/0.96        | ~ (v2_funct_1 @ sk_C))),
% 0.75/0.96      inference('sup-', [status(thm)], ['26', '27'])).
% 0.75/0.96  thf('29', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('30', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('31', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('32', plain, ((v2_funct_1 @ sk_C)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('33', plain,
% 0.75/0.96      (((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.75/0.96         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.75/0.96        | ((sk_B) != (sk_B)))),
% 0.75/0.96      inference('demod', [status(thm)], ['28', '29', '30', '31', '32'])).
% 0.75/0.96  thf('34', plain,
% 0.75/0.96      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.75/0.96        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.75/0.96      inference('simplify', [status(thm)], ['33'])).
% 0.75/0.96  thf('35', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.96         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.75/0.96           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.75/0.96          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.75/0.96          | ~ (v1_funct_1 @ X1))),
% 0.75/0.96      inference('demod', [status(thm)], ['16', '17'])).
% 0.75/0.96  thf('36', plain,
% 0.75/0.96      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.96        | (m1_subset_1 @ 
% 0.75/0.96           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ 
% 0.75/0.96            (k2_funct_1 @ sk_C)) @ 
% 0.75/0.96           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.75/0.96      inference('sup-', [status(thm)], ['34', '35'])).
% 0.75/0.96  thf('37', plain,
% 0.75/0.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('38', plain,
% 0.75/0.96      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.75/0.96         (~ (v2_funct_1 @ X36)
% 0.75/0.96          | ((k2_relset_1 @ X38 @ X37 @ X36) != (X37))
% 0.75/0.96          | (v1_funct_1 @ (k2_funct_1 @ X36))
% 0.75/0.96          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 0.75/0.96          | ~ (v1_funct_2 @ X36 @ X38 @ X37)
% 0.75/0.96          | ~ (v1_funct_1 @ X36))),
% 0.75/0.96      inference('cnf', [status(esa)], [t31_funct_2])).
% 0.75/0.96  thf('39', plain,
% 0.75/0.96      ((~ (v1_funct_1 @ sk_C)
% 0.75/0.96        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.75/0.96        | (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.96        | ((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.75/0.96        | ~ (v2_funct_1 @ sk_C))),
% 0.75/0.96      inference('sup-', [status(thm)], ['37', '38'])).
% 0.75/0.96  thf('40', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('41', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('42', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('43', plain, ((v2_funct_1 @ sk_C)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('44', plain, (((v1_funct_1 @ (k2_funct_1 @ sk_C)) | ((sk_B) != (sk_B)))),
% 0.75/0.96      inference('demod', [status(thm)], ['39', '40', '41', '42', '43'])).
% 0.75/0.96  thf('45', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.75/0.96      inference('simplify', [status(thm)], ['44'])).
% 0.75/0.96  thf('46', plain,
% 0.75/0.96      ((m1_subset_1 @ (k2_funct_1 @ sk_C) @ 
% 0.75/0.96        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.75/0.96      inference('simplify', [status(thm)], ['33'])).
% 0.75/0.96  thf('47', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.96         (((k1_partfun1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.75/0.96            = (k5_relat_1 @ sk_C @ X0))
% 0.75/0.96          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 0.75/0.96          | ~ (v1_funct_1 @ X0))),
% 0.75/0.96      inference('demod', [status(thm)], ['6', '7'])).
% 0.75/0.96  thf('48', plain,
% 0.75/0.96      ((~ (v1_funct_1 @ (k2_funct_1 @ sk_C))
% 0.75/0.96        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ 
% 0.75/0.96            (k2_funct_1 @ sk_C)) = (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C))))),
% 0.75/0.96      inference('sup-', [status(thm)], ['46', '47'])).
% 0.75/0.96  thf('49', plain, ((v1_funct_1 @ (k2_funct_1 @ sk_C))),
% 0.75/0.96      inference('simplify', [status(thm)], ['44'])).
% 0.75/0.96  thf('50', plain,
% 0.75/0.96      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ (k2_funct_1 @ sk_C))
% 0.75/0.96         = (k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)))),
% 0.75/0.96      inference('demod', [status(thm)], ['48', '49'])).
% 0.75/0.96  thf('51', plain,
% 0.75/0.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf(t35_funct_2, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i]:
% 0.75/0.96     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.75/0.96         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/0.96       ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & ( v2_funct_1 @ C ) ) =>
% 0.75/0.96         ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.75/0.96           ( ( ( k5_relat_1 @ C @ ( k2_funct_1 @ C ) ) = ( k6_partfun1 @ A ) ) & 
% 0.75/0.96             ( ( k5_relat_1 @ ( k2_funct_1 @ C ) @ C ) = ( k6_partfun1 @ B ) ) ) ) ) ))).
% 0.75/0.96  thf('52', plain,
% 0.75/0.96      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.75/0.96         (((X39) = (k1_xboole_0))
% 0.75/0.96          | ~ (v1_funct_1 @ X40)
% 0.75/0.96          | ~ (v1_funct_2 @ X40 @ X41 @ X39)
% 0.75/0.96          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X39)))
% 0.75/0.96          | ((k5_relat_1 @ X40 @ (k2_funct_1 @ X40)) = (k6_partfun1 @ X41))
% 0.75/0.96          | ~ (v2_funct_1 @ X40)
% 0.75/0.96          | ((k2_relset_1 @ X41 @ X39 @ X40) != (X39)))),
% 0.75/0.96      inference('cnf', [status(esa)], [t35_funct_2])).
% 0.75/0.96  thf('53', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 0.75/0.96      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.75/0.96  thf('54', plain,
% 0.75/0.96      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.75/0.96         (((X39) = (k1_xboole_0))
% 0.75/0.96          | ~ (v1_funct_1 @ X40)
% 0.75/0.96          | ~ (v1_funct_2 @ X40 @ X41 @ X39)
% 0.75/0.96          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X39)))
% 0.75/0.96          | ((k5_relat_1 @ X40 @ (k2_funct_1 @ X40)) = (k6_relat_1 @ X41))
% 0.75/0.96          | ~ (v2_funct_1 @ X40)
% 0.75/0.96          | ((k2_relset_1 @ X41 @ X39 @ X40) != (X39)))),
% 0.75/0.96      inference('demod', [status(thm)], ['52', '53'])).
% 0.75/0.96  thf('55', plain,
% 0.75/0.96      ((((k2_relset_1 @ sk_A @ sk_B @ sk_C) != (sk_B))
% 0.75/0.96        | ~ (v2_funct_1 @ sk_C)
% 0.75/0.96        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 0.75/0.96        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.75/0.96        | ~ (v1_funct_1 @ sk_C)
% 0.75/0.96        | ((sk_B) = (k1_xboole_0)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['51', '54'])).
% 0.75/0.96  thf('56', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('57', plain, ((v2_funct_1 @ sk_C)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('58', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('59', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('60', plain,
% 0.75/0.96      ((((sk_B) != (sk_B))
% 0.75/0.96        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))
% 0.75/0.96        | ((sk_B) = (k1_xboole_0)))),
% 0.75/0.96      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 0.75/0.96  thf('61', plain,
% 0.75/0.96      ((((sk_B) = (k1_xboole_0))
% 0.75/0.96        | ((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A)))),
% 0.75/0.96      inference('simplify', [status(thm)], ['60'])).
% 0.75/0.96  thf('62', plain, (((sk_B) != (k1_xboole_0))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('63', plain,
% 0.75/0.96      (((k5_relat_1 @ sk_C @ (k2_funct_1 @ sk_C)) = (k6_relat_1 @ sk_A))),
% 0.75/0.96      inference('simplify_reflect-', [status(thm)], ['61', '62'])).
% 0.75/0.96  thf('64', plain,
% 0.75/0.96      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ (k2_funct_1 @ sk_C))
% 0.75/0.96         = (k6_relat_1 @ sk_A))),
% 0.75/0.96      inference('demod', [status(thm)], ['50', '63'])).
% 0.75/0.96  thf('65', plain,
% 0.75/0.96      ((m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 0.75/0.96        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.75/0.96      inference('demod', [status(thm)], ['36', '45', '64'])).
% 0.75/0.96  thf('66', plain, (((k5_relat_1 @ sk_C @ sk_D) = (k6_relat_1 @ sk_A))),
% 0.75/0.96      inference('demod', [status(thm)], ['25', '65'])).
% 0.75/0.96  thf(t63_funct_1, axiom,
% 0.75/0.96    (![A:$i]:
% 0.75/0.96     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.75/0.96       ( ![B:$i]:
% 0.75/0.96         ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.75/0.96           ( ( ( v2_funct_1 @ A ) & 
% 0.75/0.96               ( ( k2_relat_1 @ A ) = ( k1_relat_1 @ B ) ) & 
% 0.75/0.96               ( ( k5_relat_1 @ A @ B ) = ( k6_relat_1 @ ( k1_relat_1 @ A ) ) ) ) =>
% 0.75/0.96             ( ( B ) = ( k2_funct_1 @ A ) ) ) ) ) ))).
% 0.75/0.96  thf('67', plain,
% 0.75/0.96      (![X0 : $i, X1 : $i]:
% 0.75/0.96         (~ (v1_relat_1 @ X0)
% 0.75/0.96          | ~ (v1_funct_1 @ X0)
% 0.75/0.96          | ((X0) = (k2_funct_1 @ X1))
% 0.75/0.96          | ((k5_relat_1 @ X1 @ X0) != (k6_relat_1 @ (k1_relat_1 @ X1)))
% 0.75/0.96          | ((k2_relat_1 @ X1) != (k1_relat_1 @ X0))
% 0.75/0.96          | ~ (v2_funct_1 @ X1)
% 0.75/0.96          | ~ (v1_funct_1 @ X1)
% 0.75/0.96          | ~ (v1_relat_1 @ X1))),
% 0.75/0.96      inference('cnf', [status(esa)], [t63_funct_1])).
% 0.75/0.96  thf('68', plain,
% 0.75/0.96      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ (k1_relat_1 @ sk_C)))
% 0.75/0.96        | ~ (v1_relat_1 @ sk_C)
% 0.75/0.96        | ~ (v1_funct_1 @ sk_C)
% 0.75/0.96        | ~ (v2_funct_1 @ sk_C)
% 0.75/0.96        | ((k2_relat_1 @ sk_C) != (k1_relat_1 @ sk_D))
% 0.75/0.96        | ((sk_D) = (k2_funct_1 @ sk_C))
% 0.75/0.96        | ~ (v1_funct_1 @ sk_D)
% 0.75/0.96        | ~ (v1_relat_1 @ sk_D))),
% 0.75/0.96      inference('sup-', [status(thm)], ['66', '67'])).
% 0.75/0.96  thf('69', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf(d1_funct_2, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i]:
% 0.75/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.96       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.75/0.96           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.75/0.96             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.75/0.96         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.75/0.96           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.75/0.96             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.75/0.96  thf(zf_stmt_1, axiom,
% 0.75/0.96    (![C:$i,B:$i,A:$i]:
% 0.75/0.96     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.75/0.96       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.75/0.96  thf('70', plain,
% 0.75/0.96      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.75/0.96         (~ (v1_funct_2 @ X19 @ X17 @ X18)
% 0.75/0.96          | ((X17) = (k1_relset_1 @ X17 @ X18 @ X19))
% 0.75/0.96          | ~ (zip_tseitin_1 @ X19 @ X18 @ X17))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.96  thf('71', plain,
% 0.75/0.96      ((~ (zip_tseitin_1 @ sk_C @ sk_B @ sk_A)
% 0.75/0.96        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B @ sk_C)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['69', '70'])).
% 0.75/0.96  thf(zf_stmt_2, axiom,
% 0.75/0.96    (![B:$i,A:$i]:
% 0.75/0.96     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.75/0.96       ( zip_tseitin_0 @ B @ A ) ))).
% 0.75/0.96  thf('72', plain,
% 0.75/0.96      (![X15 : $i, X16 : $i]:
% 0.75/0.96         ((zip_tseitin_0 @ X15 @ X16) | ((X15) = (k1_xboole_0)))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.75/0.96  thf('73', plain,
% 0.75/0.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.75/0.96  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.75/0.96  thf(zf_stmt_5, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i]:
% 0.75/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.96       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.75/0.96         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.75/0.96           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.75/0.96             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.75/0.96  thf('74', plain,
% 0.75/0.96      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.75/0.96         (~ (zip_tseitin_0 @ X20 @ X21)
% 0.75/0.96          | (zip_tseitin_1 @ X22 @ X20 @ X21)
% 0.75/0.96          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20))))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.75/0.96  thf('75', plain,
% 0.75/0.96      (((zip_tseitin_1 @ sk_C @ sk_B @ sk_A) | ~ (zip_tseitin_0 @ sk_B @ sk_A))),
% 0.75/0.96      inference('sup-', [status(thm)], ['73', '74'])).
% 0.75/0.96  thf('76', plain,
% 0.75/0.96      ((((sk_B) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B @ sk_A))),
% 0.75/0.96      inference('sup-', [status(thm)], ['72', '75'])).
% 0.75/0.96  thf('77', plain, (((sk_B) != (k1_xboole_0))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('78', plain, ((zip_tseitin_1 @ sk_C @ sk_B @ sk_A)),
% 0.75/0.96      inference('simplify_reflect-', [status(thm)], ['76', '77'])).
% 0.75/0.96  thf('79', plain,
% 0.75/0.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf(redefinition_k1_relset_1, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i]:
% 0.75/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.96       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.75/0.96  thf('80', plain,
% 0.75/0.96      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.75/0.96         (((k1_relset_1 @ X6 @ X7 @ X5) = (k1_relat_1 @ X5))
% 0.75/0.96          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.75/0.96      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.75/0.96  thf('81', plain,
% 0.75/0.96      (((k1_relset_1 @ sk_A @ sk_B @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.75/0.96      inference('sup-', [status(thm)], ['79', '80'])).
% 0.75/0.96  thf('82', plain, (((sk_A) = (k1_relat_1 @ sk_C))),
% 0.75/0.96      inference('demod', [status(thm)], ['71', '78', '81'])).
% 0.75/0.96  thf('83', plain,
% 0.75/0.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf(cc1_relset_1, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i]:
% 0.75/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.96       ( v1_relat_1 @ C ) ))).
% 0.75/0.96  thf('84', plain,
% 0.75/0.96      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.75/0.96         ((v1_relat_1 @ X2)
% 0.75/0.96          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.75/0.96      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.75/0.96  thf('85', plain, ((v1_relat_1 @ sk_C)),
% 0.75/0.96      inference('sup-', [status(thm)], ['83', '84'])).
% 0.75/0.96  thf('86', plain, ((v1_funct_1 @ sk_C)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('87', plain, ((v2_funct_1 @ sk_C)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('88', plain,
% 0.75/0.96      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf(redefinition_k2_relset_1, axiom,
% 0.75/0.96    (![A:$i,B:$i,C:$i]:
% 0.75/0.96     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.96       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.75/0.96  thf('89', plain,
% 0.75/0.96      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.75/0.96         (((k2_relset_1 @ X9 @ X10 @ X8) = (k2_relat_1 @ X8))
% 0.75/0.96          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.75/0.96      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.75/0.96  thf('90', plain,
% 0.75/0.96      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.75/0.96      inference('sup-', [status(thm)], ['88', '89'])).
% 0.75/0.96  thf('91', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (sk_B))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('92', plain, (((k2_relat_1 @ sk_C) = (sk_B))),
% 0.75/0.96      inference('sup+', [status(thm)], ['90', '91'])).
% 0.75/0.96  thf('93', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('94', plain,
% 0.75/0.96      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.75/0.96         (~ (v1_funct_2 @ X19 @ X17 @ X18)
% 0.75/0.96          | ((X17) = (k1_relset_1 @ X17 @ X18 @ X19))
% 0.75/0.96          | ~ (zip_tseitin_1 @ X19 @ X18 @ X17))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.75/0.96  thf('95', plain,
% 0.75/0.96      ((~ (zip_tseitin_1 @ sk_D @ sk_A @ sk_B)
% 0.75/0.96        | ((sk_B) = (k1_relset_1 @ sk_B @ sk_A @ sk_D)))),
% 0.75/0.96      inference('sup-', [status(thm)], ['93', '94'])).
% 0.75/0.96  thf('96', plain,
% 0.75/0.96      (![X15 : $i, X16 : $i]:
% 0.75/0.96         ((zip_tseitin_0 @ X15 @ X16) | ((X15) = (k1_xboole_0)))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.75/0.96  thf('97', plain,
% 0.75/0.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('98', plain,
% 0.75/0.96      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.75/0.96         (~ (zip_tseitin_0 @ X20 @ X21)
% 0.75/0.96          | (zip_tseitin_1 @ X22 @ X20 @ X21)
% 0.75/0.96          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20))))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.75/0.96  thf('99', plain,
% 0.75/0.96      (((zip_tseitin_1 @ sk_D @ sk_A @ sk_B) | ~ (zip_tseitin_0 @ sk_A @ sk_B))),
% 0.75/0.96      inference('sup-', [status(thm)], ['97', '98'])).
% 0.75/0.96  thf('100', plain,
% 0.75/0.96      ((((sk_A) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_D @ sk_A @ sk_B))),
% 0.75/0.96      inference('sup-', [status(thm)], ['96', '99'])).
% 0.75/0.96  thf('101', plain, (((sk_A) != (k1_xboole_0))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('102', plain, ((zip_tseitin_1 @ sk_D @ sk_A @ sk_B)),
% 0.75/0.96      inference('simplify_reflect-', [status(thm)], ['100', '101'])).
% 0.75/0.96  thf('103', plain,
% 0.75/0.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('104', plain,
% 0.75/0.96      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.75/0.96         (((k1_relset_1 @ X6 @ X7 @ X5) = (k1_relat_1 @ X5))
% 0.75/0.96          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.75/0.96      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.75/0.96  thf('105', plain,
% 0.75/0.96      (((k1_relset_1 @ sk_B @ sk_A @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.75/0.96      inference('sup-', [status(thm)], ['103', '104'])).
% 0.75/0.96  thf('106', plain, (((sk_B) = (k1_relat_1 @ sk_D))),
% 0.75/0.96      inference('demod', [status(thm)], ['95', '102', '105'])).
% 0.75/0.96  thf('107', plain, ((v1_funct_1 @ sk_D)),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('108', plain,
% 0.75/0.96      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('109', plain,
% 0.75/0.96      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.75/0.96         ((v1_relat_1 @ X2)
% 0.75/0.96          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.75/0.96      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.75/0.96  thf('110', plain, ((v1_relat_1 @ sk_D)),
% 0.75/0.96      inference('sup-', [status(thm)], ['108', '109'])).
% 0.75/0.96  thf('111', plain,
% 0.75/0.96      ((((k6_relat_1 @ sk_A) != (k6_relat_1 @ sk_A))
% 0.75/0.96        | ((sk_B) != (sk_B))
% 0.75/0.96        | ((sk_D) = (k2_funct_1 @ sk_C)))),
% 0.75/0.96      inference('demod', [status(thm)],
% 0.75/0.96                ['68', '82', '85', '86', '87', '92', '106', '107', '110'])).
% 0.75/0.96  thf('112', plain, (((sk_D) = (k2_funct_1 @ sk_C))),
% 0.75/0.96      inference('simplify', [status(thm)], ['111'])).
% 0.75/0.96  thf('113', plain, (((sk_D) != (k2_funct_1 @ sk_C))),
% 0.75/0.96      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.96  thf('114', plain, ($false),
% 0.75/0.96      inference('simplify_reflect-', [status(thm)], ['112', '113'])).
% 0.75/0.96  
% 0.75/0.96  % SZS output end Refutation
% 0.75/0.96  
% 0.75/0.97  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
