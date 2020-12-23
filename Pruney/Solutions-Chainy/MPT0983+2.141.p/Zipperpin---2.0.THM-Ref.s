%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uyNCSXb0Jc

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:23 EST 2020

% Result     : Theorem 1.05s
% Output     : Refutation 1.05s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 336 expanded)
%              Number of leaves         :   39 ( 115 expanded)
%              Depth                    :   14
%              Number of atoms          : 1123 (6654 expanded)
%              Number of equality atoms :   33 (  82 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('0',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('3',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X12 ) ) )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('7',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['8'])).

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

thf('10',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['10'])).

thf('12',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['9','11'])).

thf('13',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('15',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
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

thf('17',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( r2_relset_1 @ X32 @ X32 @ ( k1_partfun1 @ X32 @ X33 @ X33 @ X32 @ X31 @ X34 ) @ ( k6_partfun1 @ X32 ) )
      | ( ( k2_relset_1 @ X33 @ X32 @ X34 )
        = X32 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('18',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('19',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( r2_relset_1 @ X32 @ X32 @ ( k1_partfun1 @ X32 @ X33 @ X33 @ X32 @ X31 @ X34 ) @ ( k6_relat_1 @ X32 ) )
      | ( ( k2_relset_1 @ X33 @ X32 @ X34 )
        = X32 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X33 @ X32 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','19'])).

thf('21',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['15','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('26',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('27',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['24','27','28','29','30'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('32',plain,(
    ! [X20: $i,X21: $i] :
      ( ( ( k2_relat_1 @ X21 )
       != X20 )
      | ( v2_funct_2 @ X21 @ X20 )
      | ~ ( v5_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('33',plain,(
    ! [X21: $i] :
      ( ~ ( v1_relat_1 @ X21 )
      | ~ ( v5_relat_1 @ X21 @ ( k2_relat_1 @ X21 ) )
      | ( v2_funct_2 @ X21 @ ( k2_relat_1 @ X21 ) ) ) ),
    inference(simplify,[status(thm)],['32'])).

thf('34',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['31','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('36',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v5_relat_1 @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('37',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['24','27','28','29','30'])).

thf('39',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('40',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('42',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('43',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['34','37','38','43'])).

thf('45',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('46',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['10'])).

thf('48',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['46','47'])).

thf('49',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['12','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X12 ) ) )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('52',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('54',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
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

thf('56',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','59'])).

thf('61',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('63',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( X16 = X19 )
      | ~ ( r2_relset_1 @ X17 @ X18 @ X16 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','64'])).

thf('66',plain,(
    ! [X29: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('67',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
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

thf('69',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X38 @ X36 @ X36 @ X37 @ X39 @ X35 ) )
      | ( v2_funct_1 @ X39 )
      | ( X37 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X36 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X36 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['67','73'])).

thf('75',plain,(
    ! [X6: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['74','75','76','77','78'])).

thf('80',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['10'])).

thf('81',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['46','47'])).

thf('82',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['80','81'])).

thf('83',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['79','82'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('84',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('85',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['52','83','84'])).

thf('86',plain,(
    $false ),
    inference(demod,[status(thm)],['49','85'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.uyNCSXb0Jc
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:22:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.36  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 1.05/1.29  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.05/1.29  % Solved by: fo/fo7.sh
% 1.05/1.29  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.05/1.29  % done 857 iterations in 0.779s
% 1.05/1.29  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.05/1.29  % SZS output start Refutation
% 1.05/1.29  thf(sk_A_type, type, sk_A: $i).
% 1.05/1.29  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.05/1.29  thf(sk_D_type, type, sk_D: $i).
% 1.05/1.29  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.05/1.29  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.05/1.29  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.05/1.29  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.05/1.29  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.05/1.29  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.05/1.29  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.05/1.29  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.05/1.29  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.05/1.29  thf(sk_B_type, type, sk_B: $i).
% 1.05/1.29  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.05/1.29  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.05/1.29  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.05/1.29  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.05/1.29  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.05/1.29  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 1.05/1.29  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.05/1.29  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.05/1.29  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.05/1.29  thf(sk_C_type, type, sk_C: $i).
% 1.05/1.29  thf(dt_k6_partfun1, axiom,
% 1.05/1.29    (![A:$i]:
% 1.05/1.29     ( ( m1_subset_1 @
% 1.05/1.29         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.05/1.29       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.05/1.29  thf('0', plain,
% 1.05/1.29      (![X29 : $i]:
% 1.05/1.29         (m1_subset_1 @ (k6_partfun1 @ X29) @ 
% 1.05/1.29          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 1.05/1.29      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.05/1.29  thf(redefinition_k6_partfun1, axiom,
% 1.05/1.29    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.05/1.29  thf('1', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 1.05/1.29      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.05/1.29  thf('2', plain,
% 1.05/1.29      (![X29 : $i]:
% 1.05/1.29         (m1_subset_1 @ (k6_relat_1 @ X29) @ 
% 1.05/1.29          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 1.05/1.29      inference('demod', [status(thm)], ['0', '1'])).
% 1.05/1.29  thf(cc3_relset_1, axiom,
% 1.05/1.29    (![A:$i,B:$i]:
% 1.05/1.29     ( ( v1_xboole_0 @ A ) =>
% 1.05/1.29       ( ![C:$i]:
% 1.05/1.29         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.29           ( v1_xboole_0 @ C ) ) ) ))).
% 1.05/1.29  thf('3', plain,
% 1.05/1.29      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.05/1.29         (~ (v1_xboole_0 @ X10)
% 1.05/1.29          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X12)))
% 1.05/1.29          | (v1_xboole_0 @ X11))),
% 1.05/1.29      inference('cnf', [status(esa)], [cc3_relset_1])).
% 1.05/1.29  thf('4', plain,
% 1.05/1.29      (![X0 : $i]: ((v1_xboole_0 @ (k6_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.05/1.29      inference('sup-', [status(thm)], ['2', '3'])).
% 1.05/1.29  thf(t8_boole, axiom,
% 1.05/1.29    (![A:$i,B:$i]:
% 1.05/1.29     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 1.05/1.29  thf('5', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i]:
% 1.05/1.29         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 1.05/1.29      inference('cnf', [status(esa)], [t8_boole])).
% 1.05/1.29  thf('6', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i]:
% 1.05/1.29         (~ (v1_xboole_0 @ X0)
% 1.05/1.29          | ((k6_relat_1 @ X0) = (X1))
% 1.05/1.29          | ~ (v1_xboole_0 @ X1))),
% 1.05/1.29      inference('sup-', [status(thm)], ['4', '5'])).
% 1.05/1.29  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 1.05/1.29  thf('7', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 1.05/1.29      inference('cnf', [status(esa)], [t52_funct_1])).
% 1.05/1.29  thf('8', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i]:
% 1.05/1.29         ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 1.05/1.29      inference('sup+', [status(thm)], ['6', '7'])).
% 1.05/1.29  thf('9', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 1.05/1.29      inference('condensation', [status(thm)], ['8'])).
% 1.05/1.29  thf(t29_funct_2, conjecture,
% 1.05/1.29    (![A:$i,B:$i,C:$i]:
% 1.05/1.29     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.05/1.29         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.05/1.29       ( ![D:$i]:
% 1.05/1.29         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.05/1.29             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.05/1.29           ( ( r2_relset_1 @
% 1.05/1.29               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.05/1.29               ( k6_partfun1 @ A ) ) =>
% 1.05/1.29             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 1.05/1.29  thf(zf_stmt_0, negated_conjecture,
% 1.05/1.29    (~( ![A:$i,B:$i,C:$i]:
% 1.05/1.29        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.05/1.29            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.05/1.29          ( ![D:$i]:
% 1.05/1.29            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.05/1.29                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.05/1.29              ( ( r2_relset_1 @
% 1.05/1.29                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.05/1.29                  ( k6_partfun1 @ A ) ) =>
% 1.05/1.29                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 1.05/1.29    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 1.05/1.29  thf('10', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('11', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 1.05/1.29      inference('split', [status(esa)], ['10'])).
% 1.05/1.29  thf('12', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 1.05/1.29      inference('sup-', [status(thm)], ['9', '11'])).
% 1.05/1.29  thf('13', plain,
% 1.05/1.29      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.05/1.29        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.05/1.29        (k6_partfun1 @ sk_A))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('14', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 1.05/1.29      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.05/1.29  thf('15', plain,
% 1.05/1.29      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.05/1.29        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.05/1.29        (k6_relat_1 @ sk_A))),
% 1.05/1.29      inference('demod', [status(thm)], ['13', '14'])).
% 1.05/1.29  thf('16', plain,
% 1.05/1.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf(t24_funct_2, axiom,
% 1.05/1.29    (![A:$i,B:$i,C:$i]:
% 1.05/1.29     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.05/1.29         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.05/1.29       ( ![D:$i]:
% 1.05/1.29         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.05/1.29             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.05/1.29           ( ( r2_relset_1 @
% 1.05/1.29               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.05/1.29               ( k6_partfun1 @ B ) ) =>
% 1.05/1.29             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.05/1.29  thf('17', plain,
% 1.05/1.29      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.05/1.29         (~ (v1_funct_1 @ X31)
% 1.05/1.29          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 1.05/1.29          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.05/1.29          | ~ (r2_relset_1 @ X32 @ X32 @ 
% 1.05/1.29               (k1_partfun1 @ X32 @ X33 @ X33 @ X32 @ X31 @ X34) @ 
% 1.05/1.29               (k6_partfun1 @ X32))
% 1.05/1.29          | ((k2_relset_1 @ X33 @ X32 @ X34) = (X32))
% 1.05/1.29          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 1.05/1.29          | ~ (v1_funct_2 @ X34 @ X33 @ X32)
% 1.05/1.29          | ~ (v1_funct_1 @ X34))),
% 1.05/1.29      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.05/1.29  thf('18', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 1.05/1.29      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.05/1.29  thf('19', plain,
% 1.05/1.29      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.05/1.29         (~ (v1_funct_1 @ X31)
% 1.05/1.29          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 1.05/1.29          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.05/1.29          | ~ (r2_relset_1 @ X32 @ X32 @ 
% 1.05/1.29               (k1_partfun1 @ X32 @ X33 @ X33 @ X32 @ X31 @ X34) @ 
% 1.05/1.29               (k6_relat_1 @ X32))
% 1.05/1.29          | ((k2_relset_1 @ X33 @ X32 @ X34) = (X32))
% 1.05/1.29          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 1.05/1.29          | ~ (v1_funct_2 @ X34 @ X33 @ X32)
% 1.05/1.29          | ~ (v1_funct_1 @ X34))),
% 1.05/1.29      inference('demod', [status(thm)], ['17', '18'])).
% 1.05/1.29  thf('20', plain,
% 1.05/1.29      (![X0 : $i]:
% 1.05/1.29         (~ (v1_funct_1 @ X0)
% 1.05/1.29          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.05/1.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.05/1.29          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.05/1.29          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.05/1.29               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.05/1.29               (k6_relat_1 @ sk_A))
% 1.05/1.29          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.05/1.29          | ~ (v1_funct_1 @ sk_C))),
% 1.05/1.29      inference('sup-', [status(thm)], ['16', '19'])).
% 1.05/1.29  thf('21', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('22', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('23', plain,
% 1.05/1.29      (![X0 : $i]:
% 1.05/1.29         (~ (v1_funct_1 @ X0)
% 1.05/1.29          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.05/1.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.05/1.29          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.05/1.29          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.05/1.29               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.05/1.29               (k6_relat_1 @ sk_A)))),
% 1.05/1.29      inference('demod', [status(thm)], ['20', '21', '22'])).
% 1.05/1.29  thf('24', plain,
% 1.05/1.29      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.05/1.29        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.05/1.29        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.05/1.29        | ~ (v1_funct_1 @ sk_D))),
% 1.05/1.29      inference('sup-', [status(thm)], ['15', '23'])).
% 1.05/1.29  thf('25', plain,
% 1.05/1.29      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf(redefinition_k2_relset_1, axiom,
% 1.05/1.29    (![A:$i,B:$i,C:$i]:
% 1.05/1.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.29       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.05/1.29  thf('26', plain,
% 1.05/1.29      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.05/1.29         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 1.05/1.29          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.05/1.29      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.05/1.29  thf('27', plain,
% 1.05/1.29      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.05/1.29      inference('sup-', [status(thm)], ['25', '26'])).
% 1.05/1.29  thf('28', plain,
% 1.05/1.29      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('29', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('30', plain, ((v1_funct_1 @ sk_D)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('31', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.05/1.29      inference('demod', [status(thm)], ['24', '27', '28', '29', '30'])).
% 1.05/1.29  thf(d3_funct_2, axiom,
% 1.05/1.29    (![A:$i,B:$i]:
% 1.05/1.29     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 1.05/1.29       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 1.05/1.29  thf('32', plain,
% 1.05/1.29      (![X20 : $i, X21 : $i]:
% 1.05/1.29         (((k2_relat_1 @ X21) != (X20))
% 1.05/1.29          | (v2_funct_2 @ X21 @ X20)
% 1.05/1.29          | ~ (v5_relat_1 @ X21 @ X20)
% 1.05/1.29          | ~ (v1_relat_1 @ X21))),
% 1.05/1.29      inference('cnf', [status(esa)], [d3_funct_2])).
% 1.05/1.29  thf('33', plain,
% 1.05/1.29      (![X21 : $i]:
% 1.05/1.29         (~ (v1_relat_1 @ X21)
% 1.05/1.29          | ~ (v5_relat_1 @ X21 @ (k2_relat_1 @ X21))
% 1.05/1.29          | (v2_funct_2 @ X21 @ (k2_relat_1 @ X21)))),
% 1.05/1.29      inference('simplify', [status(thm)], ['32'])).
% 1.05/1.29  thf('34', plain,
% 1.05/1.29      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 1.05/1.29        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 1.05/1.29        | ~ (v1_relat_1 @ sk_D))),
% 1.05/1.29      inference('sup-', [status(thm)], ['31', '33'])).
% 1.05/1.29  thf('35', plain,
% 1.05/1.29      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf(cc2_relset_1, axiom,
% 1.05/1.29    (![A:$i,B:$i,C:$i]:
% 1.05/1.29     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.05/1.29       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.05/1.29  thf('36', plain,
% 1.05/1.29      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.05/1.29         ((v5_relat_1 @ X7 @ X9)
% 1.05/1.29          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 1.05/1.29      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.05/1.29  thf('37', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 1.05/1.29      inference('sup-', [status(thm)], ['35', '36'])).
% 1.05/1.29  thf('38', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.05/1.29      inference('demod', [status(thm)], ['24', '27', '28', '29', '30'])).
% 1.05/1.29  thf('39', plain,
% 1.05/1.29      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf(cc2_relat_1, axiom,
% 1.05/1.29    (![A:$i]:
% 1.05/1.29     ( ( v1_relat_1 @ A ) =>
% 1.05/1.29       ( ![B:$i]:
% 1.05/1.29         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.05/1.29  thf('40', plain,
% 1.05/1.29      (![X2 : $i, X3 : $i]:
% 1.05/1.29         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 1.05/1.29          | (v1_relat_1 @ X2)
% 1.05/1.29          | ~ (v1_relat_1 @ X3))),
% 1.05/1.29      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.05/1.29  thf('41', plain,
% 1.05/1.29      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 1.05/1.29      inference('sup-', [status(thm)], ['39', '40'])).
% 1.05/1.29  thf(fc6_relat_1, axiom,
% 1.05/1.29    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.05/1.29  thf('42', plain,
% 1.05/1.29      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 1.05/1.29      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.05/1.29  thf('43', plain, ((v1_relat_1 @ sk_D)),
% 1.05/1.29      inference('demod', [status(thm)], ['41', '42'])).
% 1.05/1.29  thf('44', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 1.05/1.29      inference('demod', [status(thm)], ['34', '37', '38', '43'])).
% 1.05/1.29  thf('45', plain,
% 1.05/1.29      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 1.05/1.29      inference('split', [status(esa)], ['10'])).
% 1.05/1.29  thf('46', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 1.05/1.29      inference('sup-', [status(thm)], ['44', '45'])).
% 1.05/1.29  thf('47', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 1.05/1.29      inference('split', [status(esa)], ['10'])).
% 1.05/1.29  thf('48', plain, (~ ((v2_funct_1 @ sk_C))),
% 1.05/1.29      inference('sat_resolution*', [status(thm)], ['46', '47'])).
% 1.05/1.29  thf('49', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.05/1.29      inference('simpl_trail', [status(thm)], ['12', '48'])).
% 1.05/1.29  thf('50', plain,
% 1.05/1.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('51', plain,
% 1.05/1.29      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.05/1.29         (~ (v1_xboole_0 @ X10)
% 1.05/1.29          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X12)))
% 1.05/1.29          | (v1_xboole_0 @ X11))),
% 1.05/1.29      inference('cnf', [status(esa)], [cc3_relset_1])).
% 1.05/1.29  thf('52', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 1.05/1.29      inference('sup-', [status(thm)], ['50', '51'])).
% 1.05/1.29  thf('53', plain,
% 1.05/1.29      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.05/1.29        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.05/1.29        (k6_relat_1 @ sk_A))),
% 1.05/1.29      inference('demod', [status(thm)], ['13', '14'])).
% 1.05/1.29  thf('54', plain,
% 1.05/1.29      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('55', plain,
% 1.05/1.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf(dt_k1_partfun1, axiom,
% 1.05/1.29    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.05/1.29     ( ( ( v1_funct_1 @ E ) & 
% 1.05/1.29         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.05/1.29         ( v1_funct_1 @ F ) & 
% 1.05/1.29         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.05/1.29       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.05/1.29         ( m1_subset_1 @
% 1.05/1.29           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.05/1.29           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.05/1.29  thf('56', plain,
% 1.05/1.29      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 1.05/1.29         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 1.05/1.29          | ~ (v1_funct_1 @ X22)
% 1.05/1.29          | ~ (v1_funct_1 @ X25)
% 1.05/1.29          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 1.05/1.29          | (m1_subset_1 @ (k1_partfun1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25) @ 
% 1.05/1.29             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X27))))),
% 1.05/1.29      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.05/1.29  thf('57', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.29         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.05/1.29           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.05/1.29          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.05/1.29          | ~ (v1_funct_1 @ X1)
% 1.05/1.29          | ~ (v1_funct_1 @ sk_C))),
% 1.05/1.29      inference('sup-', [status(thm)], ['55', '56'])).
% 1.05/1.29  thf('58', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('59', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.05/1.29         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.05/1.29           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.05/1.29          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.05/1.29          | ~ (v1_funct_1 @ X1))),
% 1.05/1.29      inference('demod', [status(thm)], ['57', '58'])).
% 1.05/1.29  thf('60', plain,
% 1.05/1.29      ((~ (v1_funct_1 @ sk_D)
% 1.05/1.29        | (m1_subset_1 @ 
% 1.05/1.29           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.05/1.29           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.05/1.29      inference('sup-', [status(thm)], ['54', '59'])).
% 1.05/1.29  thf('61', plain, ((v1_funct_1 @ sk_D)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('62', plain,
% 1.05/1.29      ((m1_subset_1 @ 
% 1.05/1.29        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.05/1.29        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.05/1.29      inference('demod', [status(thm)], ['60', '61'])).
% 1.05/1.29  thf(redefinition_r2_relset_1, axiom,
% 1.05/1.29    (![A:$i,B:$i,C:$i,D:$i]:
% 1.05/1.29     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.05/1.29         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.05/1.29       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.05/1.29  thf('63', plain,
% 1.05/1.29      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 1.05/1.29         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 1.05/1.29          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 1.05/1.29          | ((X16) = (X19))
% 1.05/1.29          | ~ (r2_relset_1 @ X17 @ X18 @ X16 @ X19))),
% 1.05/1.29      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.05/1.29  thf('64', plain,
% 1.05/1.29      (![X0 : $i]:
% 1.05/1.29         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.05/1.29             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 1.05/1.29          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 1.05/1.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.05/1.29      inference('sup-', [status(thm)], ['62', '63'])).
% 1.05/1.29  thf('65', plain,
% 1.05/1.29      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 1.05/1.29           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.05/1.29        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.05/1.29            = (k6_relat_1 @ sk_A)))),
% 1.05/1.29      inference('sup-', [status(thm)], ['53', '64'])).
% 1.05/1.29  thf('66', plain,
% 1.05/1.29      (![X29 : $i]:
% 1.05/1.29         (m1_subset_1 @ (k6_relat_1 @ X29) @ 
% 1.05/1.29          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))),
% 1.05/1.29      inference('demod', [status(thm)], ['0', '1'])).
% 1.05/1.29  thf('67', plain,
% 1.05/1.29      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.05/1.29         = (k6_relat_1 @ sk_A))),
% 1.05/1.29      inference('demod', [status(thm)], ['65', '66'])).
% 1.05/1.29  thf('68', plain,
% 1.05/1.29      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf(t26_funct_2, axiom,
% 1.05/1.29    (![A:$i,B:$i,C:$i,D:$i]:
% 1.05/1.29     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.05/1.29         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.05/1.29       ( ![E:$i]:
% 1.05/1.29         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.05/1.29             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.05/1.29           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 1.05/1.29             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 1.05/1.29               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 1.05/1.29  thf('69', plain,
% 1.05/1.29      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 1.05/1.29         (~ (v1_funct_1 @ X35)
% 1.05/1.29          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 1.05/1.29          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 1.05/1.29          | ~ (v2_funct_1 @ (k1_partfun1 @ X38 @ X36 @ X36 @ X37 @ X39 @ X35))
% 1.05/1.29          | (v2_funct_1 @ X39)
% 1.05/1.29          | ((X37) = (k1_xboole_0))
% 1.05/1.29          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X36)))
% 1.05/1.29          | ~ (v1_funct_2 @ X39 @ X38 @ X36)
% 1.05/1.29          | ~ (v1_funct_1 @ X39))),
% 1.05/1.29      inference('cnf', [status(esa)], [t26_funct_2])).
% 1.05/1.29  thf('70', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i]:
% 1.05/1.29         (~ (v1_funct_1 @ X0)
% 1.05/1.29          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.05/1.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.05/1.29          | ((sk_A) = (k1_xboole_0))
% 1.05/1.29          | (v2_funct_1 @ X0)
% 1.05/1.29          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.05/1.29          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.05/1.29          | ~ (v1_funct_1 @ sk_D))),
% 1.05/1.29      inference('sup-', [status(thm)], ['68', '69'])).
% 1.05/1.29  thf('71', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('72', plain, ((v1_funct_1 @ sk_D)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('73', plain,
% 1.05/1.29      (![X0 : $i, X1 : $i]:
% 1.05/1.29         (~ (v1_funct_1 @ X0)
% 1.05/1.29          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.05/1.29          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.05/1.29          | ((sk_A) = (k1_xboole_0))
% 1.05/1.29          | (v2_funct_1 @ X0)
% 1.05/1.29          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 1.05/1.29      inference('demod', [status(thm)], ['70', '71', '72'])).
% 1.05/1.29  thf('74', plain,
% 1.05/1.29      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 1.05/1.29        | (v2_funct_1 @ sk_C)
% 1.05/1.29        | ((sk_A) = (k1_xboole_0))
% 1.05/1.29        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.05/1.29        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.05/1.29        | ~ (v1_funct_1 @ sk_C))),
% 1.05/1.29      inference('sup-', [status(thm)], ['67', '73'])).
% 1.05/1.29  thf('75', plain, (![X6 : $i]: (v2_funct_1 @ (k6_relat_1 @ X6))),
% 1.05/1.29      inference('cnf', [status(esa)], [t52_funct_1])).
% 1.05/1.29  thf('76', plain,
% 1.05/1.29      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('77', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('78', plain, ((v1_funct_1 @ sk_C)),
% 1.05/1.29      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.05/1.29  thf('79', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.05/1.29      inference('demod', [status(thm)], ['74', '75', '76', '77', '78'])).
% 1.05/1.29  thf('80', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 1.05/1.29      inference('split', [status(esa)], ['10'])).
% 1.05/1.29  thf('81', plain, (~ ((v2_funct_1 @ sk_C))),
% 1.05/1.29      inference('sat_resolution*', [status(thm)], ['46', '47'])).
% 1.05/1.29  thf('82', plain, (~ (v2_funct_1 @ sk_C)),
% 1.05/1.29      inference('simpl_trail', [status(thm)], ['80', '81'])).
% 1.05/1.29  thf('83', plain, (((sk_A) = (k1_xboole_0))),
% 1.05/1.29      inference('clc', [status(thm)], ['79', '82'])).
% 1.05/1.29  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.05/1.29  thf('84', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.05/1.29      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.05/1.29  thf('85', plain, ((v1_xboole_0 @ sk_C)),
% 1.05/1.29      inference('demod', [status(thm)], ['52', '83', '84'])).
% 1.05/1.29  thf('86', plain, ($false), inference('demod', [status(thm)], ['49', '85'])).
% 1.05/1.29  
% 1.05/1.29  % SZS output end Refutation
% 1.05/1.29  
% 1.05/1.30  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
