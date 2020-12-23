%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rHbrB8NBXx

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:07 EST 2020

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 330 expanded)
%              Number of leaves         :   38 ( 113 expanded)
%              Depth                    :   14
%              Number of atoms          : 1114 (6631 expanded)
%              Number of equality atoms :   33 (  82 expanded)
%              Maximal formula depth    :   19 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('0',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('3',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X11 ) ) )
      | ( v1_xboole_0 @ X10 ) ) ),
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

thf('7',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['7'])).

thf('9',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_funct_1 @ ( k6_relat_1 @ X0 ) )
        | ~ ( v1_xboole_0 @ sk_C )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['6','8'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('10',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('11',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ sk_C )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(condensation,[status(thm)],['11'])).

thf('13',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
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

thf('18',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('19',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( v1_funct_1 @ X33 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( r2_relset_1 @ X34 @ X34 @ ( k1_partfun1 @ X34 @ X35 @ X35 @ X34 @ X33 @ X36 ) @ ( k6_relat_1 @ X34 ) )
      | ( ( k2_relset_1 @ X35 @ X34 @ X36 )
        = X34 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X36 @ X35 @ X34 )
      | ~ ( v1_funct_1 @ X36 ) ) ),
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
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
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
    ! [X22: $i,X23: $i] :
      ( ( ( k2_relat_1 @ X23 )
       != X22 )
      | ( v2_funct_2 @ X23 @ X22 )
      | ~ ( v5_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('33',plain,(
    ! [X23: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v5_relat_1 @ X23 @ ( k2_relat_1 @ X23 ) )
      | ( v2_funct_2 @ X23 @ ( k2_relat_1 @ X23 ) ) ) ),
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
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v5_relat_1 @ X6 @ X8 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('40',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ( v1_relat_1 @ X3 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('41',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['34','37','38','41'])).

thf('43',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('44',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['7'])).

thf('46',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['12','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ~ ( v1_xboole_0 @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X11 ) ) )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('50',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('52',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
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

thf('54',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['52','57'])).

thf('59',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('61',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( X18 = X21 )
      | ~ ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','62'])).

thf('64',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('65',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
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

thf('67',plain,(
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

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['65','71'])).

thf('73',plain,(
    ! [X2: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['72','73','74','75','76'])).

thf('78',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['7'])).

thf('79',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['44','45'])).

thf('80',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['78','79'])).

thf('81',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['77','80'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('82',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('83',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['50','81','82'])).

thf('84',plain,(
    $false ),
    inference(demod,[status(thm)],['47','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rHbrB8NBXx
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:20:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.07/1.31  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.07/1.31  % Solved by: fo/fo7.sh
% 1.07/1.31  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.07/1.31  % done 856 iterations in 0.851s
% 1.07/1.31  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.07/1.31  % SZS output start Refutation
% 1.07/1.31  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.07/1.31  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.07/1.31  thf(sk_D_type, type, sk_D: $i).
% 1.07/1.31  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.07/1.31  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.07/1.31  thf(sk_A_type, type, sk_A: $i).
% 1.07/1.31  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.07/1.31  thf(sk_C_type, type, sk_C: $i).
% 1.07/1.31  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.07/1.31  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.07/1.31  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.07/1.31  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.07/1.31  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 1.07/1.31  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.07/1.31  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.07/1.31  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.07/1.31  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.07/1.31  thf(sk_B_type, type, sk_B: $i).
% 1.07/1.31  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.07/1.31  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.07/1.31  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 1.07/1.31  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.07/1.31  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.07/1.31  thf(dt_k6_partfun1, axiom,
% 1.07/1.31    (![A:$i]:
% 1.07/1.31     ( ( m1_subset_1 @
% 1.07/1.31         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 1.07/1.31       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 1.07/1.31  thf('0', plain,
% 1.07/1.31      (![X31 : $i]:
% 1.07/1.31         (m1_subset_1 @ (k6_partfun1 @ X31) @ 
% 1.07/1.31          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 1.07/1.31      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 1.07/1.31  thf(redefinition_k6_partfun1, axiom,
% 1.07/1.31    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.07/1.31  thf('1', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 1.07/1.31      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.07/1.31  thf('2', plain,
% 1.07/1.31      (![X31 : $i]:
% 1.07/1.31         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 1.07/1.31          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 1.07/1.31      inference('demod', [status(thm)], ['0', '1'])).
% 1.07/1.31  thf(cc3_relset_1, axiom,
% 1.07/1.31    (![A:$i,B:$i]:
% 1.07/1.31     ( ( v1_xboole_0 @ A ) =>
% 1.07/1.31       ( ![C:$i]:
% 1.07/1.31         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.31           ( v1_xboole_0 @ C ) ) ) ))).
% 1.07/1.31  thf('3', plain,
% 1.07/1.31      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.07/1.31         (~ (v1_xboole_0 @ X9)
% 1.07/1.31          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X11)))
% 1.07/1.31          | (v1_xboole_0 @ X10))),
% 1.07/1.31      inference('cnf', [status(esa)], [cc3_relset_1])).
% 1.07/1.31  thf('4', plain,
% 1.07/1.31      (![X0 : $i]: ((v1_xboole_0 @ (k6_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.07/1.31      inference('sup-', [status(thm)], ['2', '3'])).
% 1.07/1.31  thf(t8_boole, axiom,
% 1.07/1.31    (![A:$i,B:$i]:
% 1.07/1.31     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 1.07/1.31  thf('5', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i]:
% 1.07/1.31         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 1.07/1.31      inference('cnf', [status(esa)], [t8_boole])).
% 1.07/1.31  thf('6', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i]:
% 1.07/1.31         (~ (v1_xboole_0 @ X0)
% 1.07/1.31          | ((k6_relat_1 @ X0) = (X1))
% 1.07/1.31          | ~ (v1_xboole_0 @ X1))),
% 1.07/1.31      inference('sup-', [status(thm)], ['4', '5'])).
% 1.07/1.31  thf(t29_funct_2, conjecture,
% 1.07/1.31    (![A:$i,B:$i,C:$i]:
% 1.07/1.31     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.07/1.31         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.07/1.31       ( ![D:$i]:
% 1.07/1.31         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.07/1.31             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.07/1.31           ( ( r2_relset_1 @
% 1.07/1.31               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.07/1.31               ( k6_partfun1 @ A ) ) =>
% 1.07/1.31             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 1.07/1.31  thf(zf_stmt_0, negated_conjecture,
% 1.07/1.31    (~( ![A:$i,B:$i,C:$i]:
% 1.07/1.31        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.07/1.31            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.07/1.31          ( ![D:$i]:
% 1.07/1.31            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.07/1.31                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.07/1.31              ( ( r2_relset_1 @
% 1.07/1.31                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.07/1.31                  ( k6_partfun1 @ A ) ) =>
% 1.07/1.31                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 1.07/1.31    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 1.07/1.31  thf('7', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 1.07/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.31  thf('8', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 1.07/1.31      inference('split', [status(esa)], ['7'])).
% 1.07/1.31  thf('9', plain,
% 1.07/1.31      ((![X0 : $i]:
% 1.07/1.31          (~ (v2_funct_1 @ (k6_relat_1 @ X0))
% 1.07/1.31           | ~ (v1_xboole_0 @ sk_C)
% 1.07/1.31           | ~ (v1_xboole_0 @ X0)))
% 1.07/1.31         <= (~ ((v2_funct_1 @ sk_C)))),
% 1.07/1.31      inference('sup-', [status(thm)], ['6', '8'])).
% 1.07/1.31  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 1.07/1.31  thf('10', plain, (![X2 : $i]: (v2_funct_1 @ (k6_relat_1 @ X2))),
% 1.07/1.31      inference('cnf', [status(esa)], [t52_funct_1])).
% 1.07/1.31  thf('11', plain,
% 1.07/1.31      ((![X0 : $i]: (~ (v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ X0)))
% 1.07/1.31         <= (~ ((v2_funct_1 @ sk_C)))),
% 1.07/1.31      inference('demod', [status(thm)], ['9', '10'])).
% 1.07/1.31  thf('12', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 1.07/1.31      inference('condensation', [status(thm)], ['11'])).
% 1.07/1.31  thf('13', plain,
% 1.07/1.31      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.31        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.07/1.31        (k6_partfun1 @ sk_A))),
% 1.07/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.31  thf('14', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 1.07/1.31      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.07/1.31  thf('15', plain,
% 1.07/1.31      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.31        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.07/1.31        (k6_relat_1 @ sk_A))),
% 1.07/1.31      inference('demod', [status(thm)], ['13', '14'])).
% 1.07/1.31  thf('16', plain,
% 1.07/1.31      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.07/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.31  thf(t24_funct_2, axiom,
% 1.07/1.31    (![A:$i,B:$i,C:$i]:
% 1.07/1.31     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.07/1.31         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.07/1.31       ( ![D:$i]:
% 1.07/1.31         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.07/1.31             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.07/1.31           ( ( r2_relset_1 @
% 1.07/1.31               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.07/1.31               ( k6_partfun1 @ B ) ) =>
% 1.07/1.31             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.07/1.31  thf('17', plain,
% 1.07/1.31      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.07/1.31         (~ (v1_funct_1 @ X33)
% 1.07/1.31          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 1.07/1.31          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 1.07/1.31          | ~ (r2_relset_1 @ X34 @ X34 @ 
% 1.07/1.31               (k1_partfun1 @ X34 @ X35 @ X35 @ X34 @ X33 @ X36) @ 
% 1.07/1.31               (k6_partfun1 @ X34))
% 1.07/1.31          | ((k2_relset_1 @ X35 @ X34 @ X36) = (X34))
% 1.07/1.31          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 1.07/1.31          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 1.07/1.31          | ~ (v1_funct_1 @ X36))),
% 1.07/1.31      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.07/1.31  thf('18', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 1.07/1.31      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.07/1.31  thf('19', plain,
% 1.07/1.31      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.07/1.31         (~ (v1_funct_1 @ X33)
% 1.07/1.31          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 1.07/1.31          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 1.07/1.31          | ~ (r2_relset_1 @ X34 @ X34 @ 
% 1.07/1.31               (k1_partfun1 @ X34 @ X35 @ X35 @ X34 @ X33 @ X36) @ 
% 1.07/1.31               (k6_relat_1 @ X34))
% 1.07/1.31          | ((k2_relset_1 @ X35 @ X34 @ X36) = (X34))
% 1.07/1.31          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 1.07/1.31          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 1.07/1.31          | ~ (v1_funct_1 @ X36))),
% 1.07/1.31      inference('demod', [status(thm)], ['17', '18'])).
% 1.07/1.31  thf('20', plain,
% 1.07/1.31      (![X0 : $i]:
% 1.07/1.31         (~ (v1_funct_1 @ X0)
% 1.07/1.31          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.07/1.31          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.07/1.31          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.07/1.31          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.31               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.07/1.31               (k6_relat_1 @ sk_A))
% 1.07/1.31          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.07/1.31          | ~ (v1_funct_1 @ sk_C))),
% 1.07/1.31      inference('sup-', [status(thm)], ['16', '19'])).
% 1.07/1.31  thf('21', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.07/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.31  thf('22', plain, ((v1_funct_1 @ sk_C)),
% 1.07/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.31  thf('23', plain,
% 1.07/1.31      (![X0 : $i]:
% 1.07/1.31         (~ (v1_funct_1 @ X0)
% 1.07/1.31          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.07/1.31          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.07/1.31          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.07/1.31          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.31               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.07/1.31               (k6_relat_1 @ sk_A)))),
% 1.07/1.31      inference('demod', [status(thm)], ['20', '21', '22'])).
% 1.07/1.31  thf('24', plain,
% 1.07/1.31      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.07/1.31        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.07/1.31        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.07/1.31        | ~ (v1_funct_1 @ sk_D))),
% 1.07/1.31      inference('sup-', [status(thm)], ['15', '23'])).
% 1.07/1.31  thf('25', plain,
% 1.07/1.31      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.07/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.31  thf(redefinition_k2_relset_1, axiom,
% 1.07/1.31    (![A:$i,B:$i,C:$i]:
% 1.07/1.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.31       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.07/1.31  thf('26', plain,
% 1.07/1.31      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.07/1.31         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 1.07/1.31          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 1.07/1.31      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.07/1.31  thf('27', plain,
% 1.07/1.31      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.07/1.31      inference('sup-', [status(thm)], ['25', '26'])).
% 1.07/1.31  thf('28', plain,
% 1.07/1.31      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.07/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.31  thf('29', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.07/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.31  thf('30', plain, ((v1_funct_1 @ sk_D)),
% 1.07/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.31  thf('31', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.07/1.31      inference('demod', [status(thm)], ['24', '27', '28', '29', '30'])).
% 1.07/1.31  thf(d3_funct_2, axiom,
% 1.07/1.31    (![A:$i,B:$i]:
% 1.07/1.31     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 1.07/1.31       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 1.07/1.31  thf('32', plain,
% 1.07/1.31      (![X22 : $i, X23 : $i]:
% 1.07/1.31         (((k2_relat_1 @ X23) != (X22))
% 1.07/1.31          | (v2_funct_2 @ X23 @ X22)
% 1.07/1.31          | ~ (v5_relat_1 @ X23 @ X22)
% 1.07/1.31          | ~ (v1_relat_1 @ X23))),
% 1.07/1.31      inference('cnf', [status(esa)], [d3_funct_2])).
% 1.07/1.31  thf('33', plain,
% 1.07/1.31      (![X23 : $i]:
% 1.07/1.31         (~ (v1_relat_1 @ X23)
% 1.07/1.31          | ~ (v5_relat_1 @ X23 @ (k2_relat_1 @ X23))
% 1.07/1.31          | (v2_funct_2 @ X23 @ (k2_relat_1 @ X23)))),
% 1.07/1.31      inference('simplify', [status(thm)], ['32'])).
% 1.07/1.31  thf('34', plain,
% 1.07/1.31      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 1.07/1.31        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 1.07/1.31        | ~ (v1_relat_1 @ sk_D))),
% 1.07/1.31      inference('sup-', [status(thm)], ['31', '33'])).
% 1.07/1.31  thf('35', plain,
% 1.07/1.31      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.07/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.31  thf(cc2_relset_1, axiom,
% 1.07/1.31    (![A:$i,B:$i,C:$i]:
% 1.07/1.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.31       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.07/1.31  thf('36', plain,
% 1.07/1.31      (![X6 : $i, X7 : $i, X8 : $i]:
% 1.07/1.31         ((v5_relat_1 @ X6 @ X8)
% 1.07/1.31          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 1.07/1.31      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.07/1.31  thf('37', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 1.07/1.31      inference('sup-', [status(thm)], ['35', '36'])).
% 1.07/1.31  thf('38', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.07/1.31      inference('demod', [status(thm)], ['24', '27', '28', '29', '30'])).
% 1.07/1.31  thf('39', plain,
% 1.07/1.31      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.07/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.31  thf(cc1_relset_1, axiom,
% 1.07/1.31    (![A:$i,B:$i,C:$i]:
% 1.07/1.31     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.07/1.31       ( v1_relat_1 @ C ) ))).
% 1.07/1.31  thf('40', plain,
% 1.07/1.31      (![X3 : $i, X4 : $i, X5 : $i]:
% 1.07/1.31         ((v1_relat_1 @ X3)
% 1.07/1.31          | ~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X4 @ X5))))),
% 1.07/1.31      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.07/1.31  thf('41', plain, ((v1_relat_1 @ sk_D)),
% 1.07/1.31      inference('sup-', [status(thm)], ['39', '40'])).
% 1.07/1.31  thf('42', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 1.07/1.31      inference('demod', [status(thm)], ['34', '37', '38', '41'])).
% 1.07/1.31  thf('43', plain,
% 1.07/1.31      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 1.07/1.31      inference('split', [status(esa)], ['7'])).
% 1.07/1.31  thf('44', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 1.07/1.31      inference('sup-', [status(thm)], ['42', '43'])).
% 1.07/1.31  thf('45', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 1.07/1.31      inference('split', [status(esa)], ['7'])).
% 1.07/1.31  thf('46', plain, (~ ((v2_funct_1 @ sk_C))),
% 1.07/1.31      inference('sat_resolution*', [status(thm)], ['44', '45'])).
% 1.07/1.31  thf('47', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.07/1.31      inference('simpl_trail', [status(thm)], ['12', '46'])).
% 1.07/1.31  thf('48', plain,
% 1.07/1.31      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.07/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.31  thf('49', plain,
% 1.07/1.31      (![X9 : $i, X10 : $i, X11 : $i]:
% 1.07/1.31         (~ (v1_xboole_0 @ X9)
% 1.07/1.31          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X11)))
% 1.07/1.31          | (v1_xboole_0 @ X10))),
% 1.07/1.31      inference('cnf', [status(esa)], [cc3_relset_1])).
% 1.07/1.31  thf('50', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 1.07/1.31      inference('sup-', [status(thm)], ['48', '49'])).
% 1.07/1.31  thf('51', plain,
% 1.07/1.31      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.31        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.07/1.31        (k6_relat_1 @ sk_A))),
% 1.07/1.31      inference('demod', [status(thm)], ['13', '14'])).
% 1.07/1.31  thf('52', plain,
% 1.07/1.31      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.07/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.31  thf('53', plain,
% 1.07/1.31      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.07/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.31  thf(dt_k1_partfun1, axiom,
% 1.07/1.31    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.07/1.31     ( ( ( v1_funct_1 @ E ) & 
% 1.07/1.31         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.07/1.31         ( v1_funct_1 @ F ) & 
% 1.07/1.31         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.07/1.31       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.07/1.31         ( m1_subset_1 @
% 1.07/1.31           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.07/1.31           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.07/1.31  thf('54', plain,
% 1.07/1.31      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.07/1.31         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.07/1.31          | ~ (v1_funct_1 @ X24)
% 1.07/1.31          | ~ (v1_funct_1 @ X27)
% 1.07/1.31          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 1.07/1.31          | (m1_subset_1 @ (k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27) @ 
% 1.07/1.31             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X29))))),
% 1.07/1.31      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.07/1.31  thf('55', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.31         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.07/1.31           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.07/1.31          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.07/1.31          | ~ (v1_funct_1 @ X1)
% 1.07/1.31          | ~ (v1_funct_1 @ sk_C))),
% 1.07/1.31      inference('sup-', [status(thm)], ['53', '54'])).
% 1.07/1.31  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 1.07/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.31  thf('57', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.07/1.31         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.07/1.31           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.07/1.31          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.07/1.31          | ~ (v1_funct_1 @ X1))),
% 1.07/1.31      inference('demod', [status(thm)], ['55', '56'])).
% 1.07/1.31  thf('58', plain,
% 1.07/1.31      ((~ (v1_funct_1 @ sk_D)
% 1.07/1.31        | (m1_subset_1 @ 
% 1.07/1.31           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.07/1.31           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.07/1.31      inference('sup-', [status(thm)], ['52', '57'])).
% 1.07/1.31  thf('59', plain, ((v1_funct_1 @ sk_D)),
% 1.07/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.31  thf('60', plain,
% 1.07/1.31      ((m1_subset_1 @ 
% 1.07/1.31        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.07/1.31        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.07/1.31      inference('demod', [status(thm)], ['58', '59'])).
% 1.07/1.31  thf(redefinition_r2_relset_1, axiom,
% 1.07/1.31    (![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.31     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.07/1.31         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.07/1.31       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.07/1.31  thf('61', plain,
% 1.07/1.31      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 1.07/1.31         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 1.07/1.31          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 1.07/1.31          | ((X18) = (X21))
% 1.07/1.31          | ~ (r2_relset_1 @ X19 @ X20 @ X18 @ X21))),
% 1.07/1.31      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.07/1.31  thf('62', plain,
% 1.07/1.31      (![X0 : $i]:
% 1.07/1.31         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.07/1.31             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 1.07/1.31          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 1.07/1.31          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.07/1.31      inference('sup-', [status(thm)], ['60', '61'])).
% 1.07/1.31  thf('63', plain,
% 1.07/1.31      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 1.07/1.31           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.07/1.31        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.07/1.31            = (k6_relat_1 @ sk_A)))),
% 1.07/1.31      inference('sup-', [status(thm)], ['51', '62'])).
% 1.07/1.31  thf('64', plain,
% 1.07/1.31      (![X31 : $i]:
% 1.07/1.31         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 1.07/1.31          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 1.07/1.31      inference('demod', [status(thm)], ['0', '1'])).
% 1.07/1.31  thf('65', plain,
% 1.07/1.31      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.07/1.31         = (k6_relat_1 @ sk_A))),
% 1.07/1.31      inference('demod', [status(thm)], ['63', '64'])).
% 1.07/1.31  thf('66', plain,
% 1.07/1.31      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.07/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.31  thf(t26_funct_2, axiom,
% 1.07/1.31    (![A:$i,B:$i,C:$i,D:$i]:
% 1.07/1.31     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.07/1.31         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.07/1.31       ( ![E:$i]:
% 1.07/1.31         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.07/1.31             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.07/1.31           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 1.07/1.31             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 1.07/1.31               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 1.07/1.31  thf('67', plain,
% 1.07/1.31      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 1.07/1.31         (~ (v1_funct_1 @ X37)
% 1.07/1.31          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 1.07/1.31          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 1.07/1.31          | ~ (v2_funct_1 @ (k1_partfun1 @ X40 @ X38 @ X38 @ X39 @ X41 @ X37))
% 1.07/1.31          | (v2_funct_1 @ X41)
% 1.07/1.31          | ((X39) = (k1_xboole_0))
% 1.07/1.31          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X38)))
% 1.07/1.31          | ~ (v1_funct_2 @ X41 @ X40 @ X38)
% 1.07/1.31          | ~ (v1_funct_1 @ X41))),
% 1.07/1.31      inference('cnf', [status(esa)], [t26_funct_2])).
% 1.07/1.31  thf('68', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i]:
% 1.07/1.31         (~ (v1_funct_1 @ X0)
% 1.07/1.31          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.07/1.31          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.07/1.31          | ((sk_A) = (k1_xboole_0))
% 1.07/1.31          | (v2_funct_1 @ X0)
% 1.07/1.31          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.07/1.31          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.07/1.31          | ~ (v1_funct_1 @ sk_D))),
% 1.07/1.31      inference('sup-', [status(thm)], ['66', '67'])).
% 1.07/1.31  thf('69', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.07/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.31  thf('70', plain, ((v1_funct_1 @ sk_D)),
% 1.07/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.31  thf('71', plain,
% 1.07/1.31      (![X0 : $i, X1 : $i]:
% 1.07/1.31         (~ (v1_funct_1 @ X0)
% 1.07/1.31          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.07/1.31          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.07/1.31          | ((sk_A) = (k1_xboole_0))
% 1.07/1.31          | (v2_funct_1 @ X0)
% 1.07/1.31          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 1.07/1.31      inference('demod', [status(thm)], ['68', '69', '70'])).
% 1.07/1.31  thf('72', plain,
% 1.07/1.31      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 1.07/1.31        | (v2_funct_1 @ sk_C)
% 1.07/1.31        | ((sk_A) = (k1_xboole_0))
% 1.07/1.31        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.07/1.31        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.07/1.31        | ~ (v1_funct_1 @ sk_C))),
% 1.07/1.31      inference('sup-', [status(thm)], ['65', '71'])).
% 1.07/1.31  thf('73', plain, (![X2 : $i]: (v2_funct_1 @ (k6_relat_1 @ X2))),
% 1.07/1.31      inference('cnf', [status(esa)], [t52_funct_1])).
% 1.07/1.31  thf('74', plain,
% 1.07/1.31      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.07/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.31  thf('75', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.07/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.31  thf('76', plain, ((v1_funct_1 @ sk_C)),
% 1.07/1.31      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.07/1.31  thf('77', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.07/1.31      inference('demod', [status(thm)], ['72', '73', '74', '75', '76'])).
% 1.07/1.31  thf('78', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 1.07/1.31      inference('split', [status(esa)], ['7'])).
% 1.07/1.31  thf('79', plain, (~ ((v2_funct_1 @ sk_C))),
% 1.07/1.31      inference('sat_resolution*', [status(thm)], ['44', '45'])).
% 1.07/1.31  thf('80', plain, (~ (v2_funct_1 @ sk_C)),
% 1.07/1.31      inference('simpl_trail', [status(thm)], ['78', '79'])).
% 1.07/1.31  thf('81', plain, (((sk_A) = (k1_xboole_0))),
% 1.07/1.31      inference('clc', [status(thm)], ['77', '80'])).
% 1.07/1.31  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.07/1.31  thf('82', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.07/1.31      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.07/1.31  thf('83', plain, ((v1_xboole_0 @ sk_C)),
% 1.07/1.31      inference('demod', [status(thm)], ['50', '81', '82'])).
% 1.07/1.31  thf('84', plain, ($false), inference('demod', [status(thm)], ['47', '83'])).
% 1.07/1.31  
% 1.07/1.31  % SZS output end Refutation
% 1.07/1.31  
% 1.07/1.32  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
