%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3FxGf4LiWq

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:26 EST 2020

% Result     : Theorem 0.43s
% Output     : Refutation 0.43s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 314 expanded)
%              Number of leaves         :   42 ( 109 expanded)
%              Depth                    :   15
%              Number of atoms          : 1063 (6334 expanded)
%              Number of equality atoms :   41 (  73 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

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
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
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

thf('4',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( r2_relset_1 @ X34 @ X34 @ ( k1_partfun1 @ X34 @ X35 @ X35 @ X34 @ X33 @ X36 ) @ ( k6_partfun1 @ X34 ) )
      | ( ( k2_relset_1 @ X35 @ X34 @ X36 )
        = X34 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,
    ( ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('12',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['9','12','13','14','15'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('17',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k2_relat_1 @ X25 )
       != X24 )
      | ( v2_funct_2 @ X25 @ X24 )
      | ~ ( v5_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('18',plain,(
    ! [X25: $i] :
      ( ~ ( v1_relat_1 @ X25 )
      | ~ ( v5_relat_1 @ X25 @ ( k2_relat_1 @ X25 ) )
      | ( v2_funct_2 @ X25 @ ( k2_relat_1 @ X25 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v5_relat_1 @ X13 @ X15 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('22',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['9','12','13','14','15'])).

thf('24',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('25',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('26',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('27',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('28',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['19','22','23','28'])).

thf('30',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('31',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('33',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','33'])).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('35',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('36',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('37',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( v1_xboole_0 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
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

thf('42',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('46',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['40','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('49',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( X19 = X22 )
      | ~ ( r2_relset_1 @ X20 @ X21 @ X19 @ X22 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['39','50'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('52',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('53',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('54',plain,(
    ! [X23: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X23 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X23 ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['51','54'])).

thf('56',plain,(
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

thf('57',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X38 @ X39 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X40 @ X38 @ X38 @ X39 @ X41 @ X37 ) )
      | ( v2_funct_1 @ X41 )
      | ( X39 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X38 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X40 @ X38 )
      | ~ ( v1_funct_1 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['58','59','60'])).

thf('62',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['55','61'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('63',plain,(
    ! [X12: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('64',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('65',plain,(
    ! [X12: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X12 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['62','65','66','67','68'])).

thf('70',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','33'])).

thf('71',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['69','70'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('72',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k2_zfmisc_1 @ X2 @ X3 )
        = k1_xboole_0 )
      | ( X2 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('73',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X3 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['72'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('74',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('75',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C ) ),
    inference(demod,[status(thm)],['38','71','73','74'])).

thf('76',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['35','75'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('77',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf('78',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('79',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X12: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X12 ) ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('81',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    $false ),
    inference(demod,[status(thm)],['34','76','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3FxGf4LiWq
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:38:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.43/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.43/0.60  % Solved by: fo/fo7.sh
% 0.43/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.43/0.60  % done 249 iterations in 0.143s
% 0.43/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.43/0.60  % SZS output start Refutation
% 0.43/0.60  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.43/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.43/0.60  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.43/0.60  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.43/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.43/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.43/0.60  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.43/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.43/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.43/0.60  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.43/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.43/0.60  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.43/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.43/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.43/0.60  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.43/0.60  thf(sk_B_type, type, sk_B: $i > $i).
% 0.43/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.43/0.60  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.43/0.60  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.43/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.43/0.60  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.43/0.60  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.43/0.60  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.43/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.43/0.60  thf(t29_funct_2, conjecture,
% 0.43/0.60    (![A:$i,B:$i,C:$i]:
% 0.43/0.60     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.43/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.43/0.60       ( ![D:$i]:
% 0.43/0.60         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.43/0.60             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.43/0.60           ( ( r2_relset_1 @
% 0.43/0.60               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.43/0.60               ( k6_partfun1 @ A ) ) =>
% 0.43/0.60             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 0.43/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.43/0.60    (~( ![A:$i,B:$i,C:$i]:
% 0.43/0.60        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.43/0.60            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.43/0.60          ( ![D:$i]:
% 0.43/0.60            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.43/0.60                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.43/0.60              ( ( r2_relset_1 @
% 0.43/0.60                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.43/0.60                  ( k6_partfun1 @ A ) ) =>
% 0.43/0.60                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 0.43/0.60    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 0.43/0.60  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('1', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.43/0.60      inference('split', [status(esa)], ['0'])).
% 0.43/0.60  thf('2', plain,
% 0.43/0.60      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.43/0.60        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.43/0.60        (k6_partfun1 @ sk_A))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('3', plain,
% 0.43/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf(t24_funct_2, axiom,
% 0.43/0.60    (![A:$i,B:$i,C:$i]:
% 0.43/0.60     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.43/0.60         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.43/0.60       ( ![D:$i]:
% 0.43/0.60         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.43/0.60             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.43/0.60           ( ( r2_relset_1 @
% 0.43/0.60               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.43/0.60               ( k6_partfun1 @ B ) ) =>
% 0.43/0.60             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.43/0.60  thf('4', plain,
% 0.43/0.60      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.43/0.60         (~ (v1_funct_1 @ X33)
% 0.43/0.60          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 0.43/0.60          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.43/0.60          | ~ (r2_relset_1 @ X34 @ X34 @ 
% 0.43/0.60               (k1_partfun1 @ X34 @ X35 @ X35 @ X34 @ X33 @ X36) @ 
% 0.43/0.60               (k6_partfun1 @ X34))
% 0.43/0.60          | ((k2_relset_1 @ X35 @ X34 @ X36) = (X34))
% 0.43/0.60          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.43/0.60          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 0.43/0.60          | ~ (v1_funct_1 @ X36))),
% 0.43/0.60      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.43/0.60  thf('5', plain,
% 0.43/0.60      (![X0 : $i]:
% 0.43/0.60         (~ (v1_funct_1 @ X0)
% 0.43/0.60          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 0.43/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 0.43/0.60          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 0.43/0.60          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.43/0.60               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 0.43/0.60               (k6_partfun1 @ sk_A))
% 0.43/0.60          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 0.43/0.60          | ~ (v1_funct_1 @ sk_C))),
% 0.43/0.60      inference('sup-', [status(thm)], ['3', '4'])).
% 0.43/0.60  thf('6', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('8', plain,
% 0.43/0.60      (![X0 : $i]:
% 0.43/0.60         (~ (v1_funct_1 @ X0)
% 0.43/0.60          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 0.43/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 0.43/0.60          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 0.43/0.60          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.43/0.60               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 0.43/0.60               (k6_partfun1 @ sk_A)))),
% 0.43/0.60      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.43/0.60  thf('9', plain,
% 0.43/0.60      ((((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (sk_A))
% 0.43/0.60        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 0.43/0.60        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 0.43/0.60        | ~ (v1_funct_1 @ sk_D))),
% 0.43/0.60      inference('sup-', [status(thm)], ['2', '8'])).
% 0.43/0.60  thf('10', plain,
% 0.43/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf(redefinition_k2_relset_1, axiom,
% 0.43/0.60    (![A:$i,B:$i,C:$i]:
% 0.43/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.60       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.43/0.60  thf('11', plain,
% 0.43/0.60      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.43/0.60         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 0.43/0.60          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.43/0.60      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.43/0.60  thf('12', plain,
% 0.43/0.60      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.43/0.60      inference('sup-', [status(thm)], ['10', '11'])).
% 0.43/0.60  thf('13', plain,
% 0.43/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('14', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('15', plain, ((v1_funct_1 @ sk_D)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('16', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.43/0.60      inference('demod', [status(thm)], ['9', '12', '13', '14', '15'])).
% 0.43/0.60  thf(d3_funct_2, axiom,
% 0.43/0.60    (![A:$i,B:$i]:
% 0.43/0.60     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.43/0.60       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.43/0.60  thf('17', plain,
% 0.43/0.60      (![X24 : $i, X25 : $i]:
% 0.43/0.60         (((k2_relat_1 @ X25) != (X24))
% 0.43/0.60          | (v2_funct_2 @ X25 @ X24)
% 0.43/0.60          | ~ (v5_relat_1 @ X25 @ X24)
% 0.43/0.60          | ~ (v1_relat_1 @ X25))),
% 0.43/0.60      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.43/0.60  thf('18', plain,
% 0.43/0.60      (![X25 : $i]:
% 0.43/0.60         (~ (v1_relat_1 @ X25)
% 0.43/0.60          | ~ (v5_relat_1 @ X25 @ (k2_relat_1 @ X25))
% 0.43/0.60          | (v2_funct_2 @ X25 @ (k2_relat_1 @ X25)))),
% 0.43/0.60      inference('simplify', [status(thm)], ['17'])).
% 0.43/0.60  thf('19', plain,
% 0.43/0.60      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 0.43/0.60        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 0.43/0.60        | ~ (v1_relat_1 @ sk_D))),
% 0.43/0.60      inference('sup-', [status(thm)], ['16', '18'])).
% 0.43/0.60  thf('20', plain,
% 0.43/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf(cc2_relset_1, axiom,
% 0.43/0.60    (![A:$i,B:$i,C:$i]:
% 0.43/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.43/0.60       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.43/0.60  thf('21', plain,
% 0.43/0.60      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.43/0.60         ((v5_relat_1 @ X13 @ X15)
% 0.43/0.60          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.43/0.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.43/0.60  thf('22', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.43/0.60      inference('sup-', [status(thm)], ['20', '21'])).
% 0.43/0.60  thf('23', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.43/0.60      inference('demod', [status(thm)], ['9', '12', '13', '14', '15'])).
% 0.43/0.60  thf('24', plain,
% 0.43/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf(cc2_relat_1, axiom,
% 0.43/0.60    (![A:$i]:
% 0.43/0.60     ( ( v1_relat_1 @ A ) =>
% 0.43/0.60       ( ![B:$i]:
% 0.43/0.60         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.43/0.60  thf('25', plain,
% 0.43/0.60      (![X7 : $i, X8 : $i]:
% 0.43/0.60         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.43/0.60          | (v1_relat_1 @ X7)
% 0.43/0.60          | ~ (v1_relat_1 @ X8))),
% 0.43/0.60      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.43/0.60  thf('26', plain,
% 0.43/0.60      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)) | (v1_relat_1 @ sk_D))),
% 0.43/0.60      inference('sup-', [status(thm)], ['24', '25'])).
% 0.43/0.60  thf(fc6_relat_1, axiom,
% 0.43/0.60    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.43/0.60  thf('27', plain,
% 0.43/0.60      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.43/0.60      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.43/0.60  thf('28', plain, ((v1_relat_1 @ sk_D)),
% 0.43/0.60      inference('demod', [status(thm)], ['26', '27'])).
% 0.43/0.60  thf('29', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 0.43/0.60      inference('demod', [status(thm)], ['19', '22', '23', '28'])).
% 0.43/0.60  thf('30', plain,
% 0.43/0.60      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 0.43/0.60      inference('split', [status(esa)], ['0'])).
% 0.43/0.60  thf('31', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 0.43/0.60      inference('sup-', [status(thm)], ['29', '30'])).
% 0.43/0.60  thf('32', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 0.43/0.60      inference('split', [status(esa)], ['0'])).
% 0.43/0.60  thf('33', plain, (~ ((v2_funct_1 @ sk_C))),
% 0.43/0.60      inference('sat_resolution*', [status(thm)], ['31', '32'])).
% 0.43/0.60  thf('34', plain, (~ (v2_funct_1 @ sk_C)),
% 0.43/0.60      inference('simpl_trail', [status(thm)], ['1', '33'])).
% 0.43/0.60  thf(t7_xboole_0, axiom,
% 0.43/0.60    (![A:$i]:
% 0.43/0.60     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.43/0.60          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.43/0.60  thf('35', plain,
% 0.43/0.60      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.43/0.60      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.43/0.60  thf('36', plain,
% 0.43/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf(t5_subset, axiom,
% 0.43/0.60    (![A:$i,B:$i,C:$i]:
% 0.43/0.60     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.43/0.60          ( v1_xboole_0 @ C ) ) ))).
% 0.43/0.60  thf('37', plain,
% 0.43/0.60      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.43/0.60         (~ (r2_hidden @ X4 @ X5)
% 0.43/0.60          | ~ (v1_xboole_0 @ X6)
% 0.43/0.60          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.43/0.60      inference('cnf', [status(esa)], [t5_subset])).
% 0.43/0.60  thf('38', plain,
% 0.43/0.60      (![X0 : $i]:
% 0.43/0.60         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 0.43/0.60          | ~ (r2_hidden @ X0 @ sk_C))),
% 0.43/0.60      inference('sup-', [status(thm)], ['36', '37'])).
% 0.43/0.60  thf('39', plain,
% 0.43/0.60      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.43/0.60        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.43/0.60        (k6_partfun1 @ sk_A))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('40', plain,
% 0.43/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('41', plain,
% 0.43/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf(dt_k1_partfun1, axiom,
% 0.43/0.60    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.43/0.60     ( ( ( v1_funct_1 @ E ) & 
% 0.43/0.60         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.43/0.60         ( v1_funct_1 @ F ) & 
% 0.43/0.60         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.43/0.60       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.43/0.60         ( m1_subset_1 @
% 0.43/0.60           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.43/0.60           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.43/0.60  thf('42', plain,
% 0.43/0.60      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.43/0.60         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.43/0.60          | ~ (v1_funct_1 @ X26)
% 0.43/0.60          | ~ (v1_funct_1 @ X29)
% 0.43/0.60          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.43/0.60          | (m1_subset_1 @ (k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29) @ 
% 0.43/0.60             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X31))))),
% 0.43/0.60      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.43/0.60  thf('43', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.60         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 0.43/0.60           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.43/0.60          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.43/0.60          | ~ (v1_funct_1 @ X1)
% 0.43/0.60          | ~ (v1_funct_1 @ sk_C))),
% 0.43/0.60      inference('sup-', [status(thm)], ['41', '42'])).
% 0.43/0.60  thf('44', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('45', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.43/0.60         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 0.43/0.60           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.43/0.60          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.43/0.60          | ~ (v1_funct_1 @ X1))),
% 0.43/0.60      inference('demod', [status(thm)], ['43', '44'])).
% 0.43/0.60  thf('46', plain,
% 0.43/0.60      ((~ (v1_funct_1 @ sk_D)
% 0.43/0.60        | (m1_subset_1 @ 
% 0.43/0.60           (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.43/0.60           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.43/0.60      inference('sup-', [status(thm)], ['40', '45'])).
% 0.43/0.60  thf('47', plain, ((v1_funct_1 @ sk_D)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('48', plain,
% 0.43/0.60      ((m1_subset_1 @ 
% 0.43/0.60        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 0.43/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.43/0.60      inference('demod', [status(thm)], ['46', '47'])).
% 0.43/0.60  thf(redefinition_r2_relset_1, axiom,
% 0.43/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.60     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.43/0.60         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.43/0.60       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.43/0.60  thf('49', plain,
% 0.43/0.60      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.43/0.60         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.43/0.60          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.43/0.60          | ((X19) = (X22))
% 0.43/0.60          | ~ (r2_relset_1 @ X20 @ X21 @ X19 @ X22))),
% 0.43/0.60      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.43/0.60  thf('50', plain,
% 0.43/0.60      (![X0 : $i]:
% 0.43/0.60         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.43/0.60             (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ X0)
% 0.43/0.60          | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) = (X0))
% 0.43/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.43/0.60      inference('sup-', [status(thm)], ['48', '49'])).
% 0.43/0.60  thf('51', plain,
% 0.43/0.60      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.43/0.60           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.43/0.60        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 0.43/0.60            = (k6_partfun1 @ sk_A)))),
% 0.43/0.60      inference('sup-', [status(thm)], ['39', '50'])).
% 0.43/0.60  thf(t29_relset_1, axiom,
% 0.43/0.60    (![A:$i]:
% 0.43/0.60     ( m1_subset_1 @
% 0.43/0.60       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.43/0.60  thf('52', plain,
% 0.43/0.60      (![X23 : $i]:
% 0.43/0.60         (m1_subset_1 @ (k6_relat_1 @ X23) @ 
% 0.43/0.60          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 0.43/0.60      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.43/0.60  thf(redefinition_k6_partfun1, axiom,
% 0.43/0.60    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.43/0.60  thf('53', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.43/0.60      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.43/0.60  thf('54', plain,
% 0.43/0.60      (![X23 : $i]:
% 0.43/0.60         (m1_subset_1 @ (k6_partfun1 @ X23) @ 
% 0.43/0.60          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X23)))),
% 0.43/0.60      inference('demod', [status(thm)], ['52', '53'])).
% 0.43/0.60  thf('55', plain,
% 0.43/0.60      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 0.43/0.60         = (k6_partfun1 @ sk_A))),
% 0.43/0.60      inference('demod', [status(thm)], ['51', '54'])).
% 0.43/0.60  thf('56', plain,
% 0.43/0.60      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf(t26_funct_2, axiom,
% 0.43/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.43/0.60     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.43/0.60         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.43/0.60       ( ![E:$i]:
% 0.43/0.60         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.43/0.60             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.43/0.60           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 0.43/0.60             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 0.43/0.60               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 0.43/0.60  thf('57', plain,
% 0.43/0.60      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.43/0.60         (~ (v1_funct_1 @ X37)
% 0.43/0.60          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 0.43/0.60          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 0.43/0.60          | ~ (v2_funct_1 @ (k1_partfun1 @ X40 @ X38 @ X38 @ X39 @ X41 @ X37))
% 0.43/0.60          | (v2_funct_1 @ X41)
% 0.43/0.60          | ((X39) = (k1_xboole_0))
% 0.43/0.60          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X38)))
% 0.43/0.60          | ~ (v1_funct_2 @ X41 @ X40 @ X38)
% 0.43/0.60          | ~ (v1_funct_1 @ X41))),
% 0.43/0.60      inference('cnf', [status(esa)], [t26_funct_2])).
% 0.43/0.60  thf('58', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i]:
% 0.43/0.60         (~ (v1_funct_1 @ X0)
% 0.43/0.60          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 0.43/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 0.43/0.60          | ((sk_A) = (k1_xboole_0))
% 0.43/0.60          | (v2_funct_1 @ X0)
% 0.43/0.60          | ~ (v2_funct_1 @ 
% 0.43/0.60               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D))
% 0.43/0.60          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 0.43/0.60          | ~ (v1_funct_1 @ sk_D))),
% 0.43/0.60      inference('sup-', [status(thm)], ['56', '57'])).
% 0.43/0.60  thf('59', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('60', plain, ((v1_funct_1 @ sk_D)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('61', plain,
% 0.43/0.60      (![X0 : $i, X1 : $i]:
% 0.43/0.60         (~ (v1_funct_1 @ X0)
% 0.43/0.60          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 0.43/0.60          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 0.43/0.60          | ((sk_A) = (k1_xboole_0))
% 0.43/0.60          | (v2_funct_1 @ X0)
% 0.43/0.60          | ~ (v2_funct_1 @ 
% 0.43/0.60               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D)))),
% 0.43/0.60      inference('demod', [status(thm)], ['58', '59', '60'])).
% 0.43/0.60  thf('62', plain,
% 0.43/0.60      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.43/0.60        | (v2_funct_1 @ sk_C)
% 0.43/0.60        | ((sk_A) = (k1_xboole_0))
% 0.43/0.60        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.43/0.60        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 0.43/0.60        | ~ (v1_funct_1 @ sk_C))),
% 0.43/0.60      inference('sup-', [status(thm)], ['55', '61'])).
% 0.43/0.60  thf(fc4_funct_1, axiom,
% 0.43/0.60    (![A:$i]:
% 0.43/0.60     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.43/0.60       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.43/0.60  thf('63', plain, (![X12 : $i]: (v2_funct_1 @ (k6_relat_1 @ X12))),
% 0.43/0.60      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.43/0.60  thf('64', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.43/0.60      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.43/0.60  thf('65', plain, (![X12 : $i]: (v2_funct_1 @ (k6_partfun1 @ X12))),
% 0.43/0.60      inference('demod', [status(thm)], ['63', '64'])).
% 0.43/0.60  thf('66', plain,
% 0.43/0.60      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('67', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('68', plain, ((v1_funct_1 @ sk_C)),
% 0.43/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.43/0.60  thf('69', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.43/0.60      inference('demod', [status(thm)], ['62', '65', '66', '67', '68'])).
% 0.43/0.60  thf('70', plain, (~ (v2_funct_1 @ sk_C)),
% 0.43/0.60      inference('simpl_trail', [status(thm)], ['1', '33'])).
% 0.43/0.60  thf('71', plain, (((sk_A) = (k1_xboole_0))),
% 0.43/0.60      inference('clc', [status(thm)], ['69', '70'])).
% 0.43/0.60  thf(t113_zfmisc_1, axiom,
% 0.43/0.60    (![A:$i,B:$i]:
% 0.43/0.60     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.43/0.60       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.43/0.60  thf('72', plain,
% 0.43/0.60      (![X2 : $i, X3 : $i]:
% 0.43/0.60         (((k2_zfmisc_1 @ X2 @ X3) = (k1_xboole_0)) | ((X2) != (k1_xboole_0)))),
% 0.43/0.60      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.43/0.60  thf('73', plain,
% 0.43/0.60      (![X3 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X3) = (k1_xboole_0))),
% 0.43/0.60      inference('simplify', [status(thm)], ['72'])).
% 0.43/0.60  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.43/0.60  thf('74', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.43/0.60      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.43/0.60  thf('75', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C)),
% 0.43/0.60      inference('demod', [status(thm)], ['38', '71', '73', '74'])).
% 0.43/0.60  thf('76', plain, (((sk_C) = (k1_xboole_0))),
% 0.43/0.60      inference('sup-', [status(thm)], ['35', '75'])).
% 0.43/0.60  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 0.43/0.60  thf('77', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.60      inference('cnf', [status(esa)], [t81_relat_1])).
% 0.43/0.60  thf('78', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 0.43/0.60      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.43/0.60  thf('79', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.43/0.60      inference('demod', [status(thm)], ['77', '78'])).
% 0.43/0.60  thf('80', plain, (![X12 : $i]: (v2_funct_1 @ (k6_partfun1 @ X12))),
% 0.43/0.60      inference('demod', [status(thm)], ['63', '64'])).
% 0.43/0.60  thf('81', plain, ((v2_funct_1 @ k1_xboole_0)),
% 0.43/0.60      inference('sup+', [status(thm)], ['79', '80'])).
% 0.43/0.60  thf('82', plain, ($false),
% 0.43/0.60      inference('demod', [status(thm)], ['34', '76', '81'])).
% 0.43/0.60  
% 0.43/0.60  % SZS output end Refutation
% 0.43/0.60  
% 0.43/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
