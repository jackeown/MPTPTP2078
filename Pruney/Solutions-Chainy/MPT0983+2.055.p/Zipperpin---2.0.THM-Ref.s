%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y4i7505EdB

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:09 EST 2020

% Result     : Theorem 2.93s
% Output     : Refutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 365 expanded)
%              Number of leaves         :   39 ( 124 expanded)
%              Depth                    :   14
%              Number of atoms          : 1185 (6818 expanded)
%              Number of equality atoms :   46 ( 113 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('0',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('3',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X4 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('4',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('5',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('6',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('7',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ ( k6_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['4','7'])).

thf('9',plain,(
    ! [X3: $i] :
      ( ( k2_zfmisc_1 @ X3 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['3'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('10',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X12 ) ) )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('11',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('13',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,(
    v1_xboole_0 @ ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('16',plain,
    ( k1_xboole_0
    = ( k6_relat_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t52_funct_1,axiom,(
    ! [A: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ A ) ) )).

thf('17',plain,(
    ! [X5: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('18',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','18'])).

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

thf('20',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['20'])).

thf('22',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('25',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
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

thf('27',plain,(
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

thf('28',plain,(
    ! [X32: $i] :
      ( ( k6_partfun1 @ X32 )
      = ( k6_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('29',plain,(
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
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['25','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('36',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('37',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['34','37','38','39','40'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('42',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_relat_1 @ X23 )
       != X22 )
      | ( v2_funct_2 @ X23 @ X22 )
      | ~ ( v5_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('43',plain,(
    ! [X23: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v5_relat_1 @ X23 @ ( k2_relat_1 @ X23 ) )
      | ( v2_funct_2 @ X23 @ ( k2_relat_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('46',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v5_relat_1 @ X9 @ X11 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('47',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['34','37','38','39','40'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('50',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_relat_1 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('51',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['44','47','48','51'])).

thf('53',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['20'])).

thf('54',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['20'])).

thf('56',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['54','55'])).

thf('57',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['22','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('60',plain,(
    ! [X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('64',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
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

thf('66',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X29 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['64','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('73',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( X18 = X21 )
      | ~ ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['63','74'])).

thf('76',plain,(
    ! [X31: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X31 ) ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('77',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
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

thf('79',plain,(
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

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ~ ( v2_funct_1 @ ( k6_relat_1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['77','83'])).

thf('85',plain,(
    ! [X5: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t52_funct_1])).

thf('86',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['84','85','86','87','88'])).

thf('90',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['20'])).

thf('91',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['54','55'])).

thf('92',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['90','91'])).

thf('93',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['89','92'])).

thf('94',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k2_zfmisc_1 @ X3 @ X4 )
        = k1_xboole_0 )
      | ( X3 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('95',plain,(
    ! [X4: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X4 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('97',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['62','93','95','96'])).

thf('98',plain,(
    $false ),
    inference(demod,[status(thm)],['57','97'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.y4i7505EdB
% 0.14/0.35  % Computer   : n013.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:11:40 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 2.93/3.17  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.93/3.17  % Solved by: fo/fo7.sh
% 2.93/3.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.93/3.17  % done 3481 iterations in 2.709s
% 2.93/3.17  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.93/3.17  % SZS output start Refutation
% 2.93/3.17  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.93/3.17  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.93/3.17  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.93/3.17  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.93/3.17  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.93/3.17  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.93/3.17  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.93/3.17  thf(sk_C_type, type, sk_C: $i).
% 2.93/3.17  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.93/3.17  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.93/3.17  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.93/3.17  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 2.93/3.17  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 2.93/3.17  thf(sk_A_type, type, sk_A: $i).
% 2.93/3.17  thf(sk_B_type, type, sk_B: $i).
% 2.93/3.17  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.93/3.17  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.93/3.17  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 2.93/3.17  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.93/3.17  thf(sk_D_type, type, sk_D: $i).
% 2.93/3.17  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.93/3.17  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.93/3.17  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.93/3.17  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.93/3.17  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.93/3.17      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.93/3.17  thf(t8_boole, axiom,
% 2.93/3.17    (![A:$i,B:$i]:
% 2.93/3.17     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 2.93/3.17  thf('1', plain,
% 2.93/3.17      (![X0 : $i, X1 : $i]:
% 2.93/3.17         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 2.93/3.17      inference('cnf', [status(esa)], [t8_boole])).
% 2.93/3.17  thf('2', plain,
% 2.93/3.17      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.93/3.17      inference('sup-', [status(thm)], ['0', '1'])).
% 2.93/3.17  thf(t113_zfmisc_1, axiom,
% 2.93/3.17    (![A:$i,B:$i]:
% 2.93/3.17     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 2.93/3.17       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 2.93/3.17  thf('3', plain,
% 2.93/3.17      (![X3 : $i, X4 : $i]:
% 2.93/3.17         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X4) != (k1_xboole_0)))),
% 2.93/3.17      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.93/3.17  thf('4', plain,
% 2.93/3.17      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 2.93/3.17      inference('simplify', [status(thm)], ['3'])).
% 2.93/3.17  thf(dt_k6_partfun1, axiom,
% 2.93/3.17    (![A:$i]:
% 2.93/3.17     ( ( m1_subset_1 @
% 2.93/3.17         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 2.93/3.17       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 2.93/3.17  thf('5', plain,
% 2.93/3.17      (![X31 : $i]:
% 2.93/3.17         (m1_subset_1 @ (k6_partfun1 @ X31) @ 
% 2.93/3.17          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 2.93/3.17      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 2.93/3.17  thf(redefinition_k6_partfun1, axiom,
% 2.93/3.17    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.93/3.17  thf('6', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 2.93/3.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.93/3.17  thf('7', plain,
% 2.93/3.17      (![X31 : $i]:
% 2.93/3.17         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 2.93/3.17          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 2.93/3.17      inference('demod', [status(thm)], ['5', '6'])).
% 2.93/3.17  thf('8', plain,
% 2.93/3.17      ((m1_subset_1 @ (k6_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ k1_xboole_0))),
% 2.93/3.17      inference('sup+', [status(thm)], ['4', '7'])).
% 2.93/3.17  thf('9', plain,
% 2.93/3.17      (![X3 : $i]: ((k2_zfmisc_1 @ X3 @ k1_xboole_0) = (k1_xboole_0))),
% 2.93/3.17      inference('simplify', [status(thm)], ['3'])).
% 2.93/3.17  thf(cc4_relset_1, axiom,
% 2.93/3.17    (![A:$i,B:$i]:
% 2.93/3.17     ( ( v1_xboole_0 @ A ) =>
% 2.93/3.17       ( ![C:$i]:
% 2.93/3.17         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 2.93/3.17           ( v1_xboole_0 @ C ) ) ) ))).
% 2.93/3.17  thf('10', plain,
% 2.93/3.17      (![X12 : $i, X13 : $i, X14 : $i]:
% 2.93/3.17         (~ (v1_xboole_0 @ X12)
% 2.93/3.17          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X12)))
% 2.93/3.17          | (v1_xboole_0 @ X13))),
% 2.93/3.17      inference('cnf', [status(esa)], [cc4_relset_1])).
% 2.93/3.17  thf('11', plain,
% 2.93/3.17      (![X1 : $i]:
% 2.93/3.17         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.93/3.17          | (v1_xboole_0 @ X1)
% 2.93/3.17          | ~ (v1_xboole_0 @ k1_xboole_0))),
% 2.93/3.17      inference('sup-', [status(thm)], ['9', '10'])).
% 2.93/3.17  thf('12', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.93/3.17      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.93/3.17  thf('13', plain,
% 2.93/3.17      (![X1 : $i]:
% 2.93/3.17         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.93/3.17          | (v1_xboole_0 @ X1))),
% 2.93/3.17      inference('demod', [status(thm)], ['11', '12'])).
% 2.93/3.17  thf('14', plain, ((v1_xboole_0 @ (k6_relat_1 @ k1_xboole_0))),
% 2.93/3.17      inference('sup-', [status(thm)], ['8', '13'])).
% 2.93/3.17  thf('15', plain,
% 2.93/3.17      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.93/3.17      inference('sup-', [status(thm)], ['0', '1'])).
% 2.93/3.17  thf('16', plain, (((k1_xboole_0) = (k6_relat_1 @ k1_xboole_0))),
% 2.93/3.17      inference('sup-', [status(thm)], ['14', '15'])).
% 2.93/3.17  thf(t52_funct_1, axiom, (![A:$i]: ( v2_funct_1 @ ( k6_relat_1 @ A ) ))).
% 2.93/3.17  thf('17', plain, (![X5 : $i]: (v2_funct_1 @ (k6_relat_1 @ X5))),
% 2.93/3.17      inference('cnf', [status(esa)], [t52_funct_1])).
% 2.93/3.17  thf('18', plain, ((v2_funct_1 @ k1_xboole_0)),
% 2.93/3.17      inference('sup+', [status(thm)], ['16', '17'])).
% 2.93/3.17  thf('19', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 2.93/3.17      inference('sup+', [status(thm)], ['2', '18'])).
% 2.93/3.17  thf(t29_funct_2, conjecture,
% 2.93/3.17    (![A:$i,B:$i,C:$i]:
% 2.93/3.17     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.93/3.17         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.93/3.17       ( ![D:$i]:
% 2.93/3.17         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.93/3.17             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.93/3.17           ( ( r2_relset_1 @
% 2.93/3.17               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.93/3.17               ( k6_partfun1 @ A ) ) =>
% 2.93/3.17             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 2.93/3.17  thf(zf_stmt_0, negated_conjecture,
% 2.93/3.17    (~( ![A:$i,B:$i,C:$i]:
% 2.93/3.17        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.93/3.17            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.93/3.17          ( ![D:$i]:
% 2.93/3.17            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.93/3.17                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.93/3.17              ( ( r2_relset_1 @
% 2.93/3.17                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.93/3.17                  ( k6_partfun1 @ A ) ) =>
% 2.93/3.17                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 2.93/3.17    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 2.93/3.17  thf('20', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 2.93/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.17  thf('21', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.93/3.17      inference('split', [status(esa)], ['20'])).
% 2.93/3.17  thf('22', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.93/3.17      inference('sup-', [status(thm)], ['19', '21'])).
% 2.93/3.17  thf('23', plain,
% 2.93/3.17      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.93/3.17        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.93/3.17        (k6_partfun1 @ sk_A))),
% 2.93/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.17  thf('24', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 2.93/3.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.93/3.17  thf('25', plain,
% 2.93/3.17      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.93/3.17        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.93/3.17        (k6_relat_1 @ sk_A))),
% 2.93/3.17      inference('demod', [status(thm)], ['23', '24'])).
% 2.93/3.17  thf('26', plain,
% 2.93/3.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.93/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.17  thf(t24_funct_2, axiom,
% 2.93/3.17    (![A:$i,B:$i,C:$i]:
% 2.93/3.17     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.93/3.17         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.93/3.17       ( ![D:$i]:
% 2.93/3.17         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.93/3.17             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.93/3.17           ( ( r2_relset_1 @
% 2.93/3.17               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 2.93/3.17               ( k6_partfun1 @ B ) ) =>
% 2.93/3.17             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 2.93/3.17  thf('27', plain,
% 2.93/3.17      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 2.93/3.17         (~ (v1_funct_1 @ X33)
% 2.93/3.17          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 2.93/3.17          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 2.93/3.17          | ~ (r2_relset_1 @ X34 @ X34 @ 
% 2.93/3.17               (k1_partfun1 @ X34 @ X35 @ X35 @ X34 @ X33 @ X36) @ 
% 2.93/3.17               (k6_partfun1 @ X34))
% 2.93/3.17          | ((k2_relset_1 @ X35 @ X34 @ X36) = (X34))
% 2.93/3.17          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 2.93/3.17          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 2.93/3.17          | ~ (v1_funct_1 @ X36))),
% 2.93/3.17      inference('cnf', [status(esa)], [t24_funct_2])).
% 2.93/3.17  thf('28', plain, (![X32 : $i]: ((k6_partfun1 @ X32) = (k6_relat_1 @ X32))),
% 2.93/3.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.93/3.17  thf('29', plain,
% 2.93/3.17      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 2.93/3.17         (~ (v1_funct_1 @ X33)
% 2.93/3.17          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 2.93/3.17          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 2.93/3.17          | ~ (r2_relset_1 @ X34 @ X34 @ 
% 2.93/3.17               (k1_partfun1 @ X34 @ X35 @ X35 @ X34 @ X33 @ X36) @ 
% 2.93/3.17               (k6_relat_1 @ X34))
% 2.93/3.17          | ((k2_relset_1 @ X35 @ X34 @ X36) = (X34))
% 2.93/3.17          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 2.93/3.17          | ~ (v1_funct_2 @ X36 @ X35 @ X34)
% 2.93/3.17          | ~ (v1_funct_1 @ X36))),
% 2.93/3.17      inference('demod', [status(thm)], ['27', '28'])).
% 2.93/3.17  thf('30', plain,
% 2.93/3.17      (![X0 : $i]:
% 2.93/3.17         (~ (v1_funct_1 @ X0)
% 2.93/3.17          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.93/3.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.93/3.17          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.93/3.17          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.93/3.17               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.93/3.17               (k6_relat_1 @ sk_A))
% 2.93/3.17          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.93/3.17          | ~ (v1_funct_1 @ sk_C))),
% 2.93/3.17      inference('sup-', [status(thm)], ['26', '29'])).
% 2.93/3.17  thf('31', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.93/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.17  thf('32', plain, ((v1_funct_1 @ sk_C)),
% 2.93/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.17  thf('33', plain,
% 2.93/3.17      (![X0 : $i]:
% 2.93/3.17         (~ (v1_funct_1 @ X0)
% 2.93/3.17          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 2.93/3.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.93/3.17          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 2.93/3.17          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.93/3.17               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 2.93/3.17               (k6_relat_1 @ sk_A)))),
% 2.93/3.17      inference('demod', [status(thm)], ['30', '31', '32'])).
% 2.93/3.17  thf('34', plain,
% 2.93/3.17      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 2.93/3.17        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 2.93/3.17        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.93/3.17        | ~ (v1_funct_1 @ sk_D))),
% 2.93/3.17      inference('sup-', [status(thm)], ['25', '33'])).
% 2.93/3.17  thf('35', plain,
% 2.93/3.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.93/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.17  thf(redefinition_k2_relset_1, axiom,
% 2.93/3.17    (![A:$i,B:$i,C:$i]:
% 2.93/3.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.93/3.17       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 2.93/3.17  thf('36', plain,
% 2.93/3.17      (![X15 : $i, X16 : $i, X17 : $i]:
% 2.93/3.17         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 2.93/3.17          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 2.93/3.17      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 2.93/3.17  thf('37', plain,
% 2.93/3.17      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 2.93/3.17      inference('sup-', [status(thm)], ['35', '36'])).
% 2.93/3.17  thf('38', plain,
% 2.93/3.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.93/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.17  thf('39', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.93/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.17  thf('40', plain, ((v1_funct_1 @ sk_D)),
% 2.93/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.17  thf('41', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.93/3.17      inference('demod', [status(thm)], ['34', '37', '38', '39', '40'])).
% 2.93/3.17  thf(d3_funct_2, axiom,
% 2.93/3.17    (![A:$i,B:$i]:
% 2.93/3.17     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 2.93/3.17       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 2.93/3.17  thf('42', plain,
% 2.93/3.17      (![X22 : $i, X23 : $i]:
% 2.93/3.17         (((k2_relat_1 @ X23) != (X22))
% 2.93/3.17          | (v2_funct_2 @ X23 @ X22)
% 2.93/3.17          | ~ (v5_relat_1 @ X23 @ X22)
% 2.93/3.17          | ~ (v1_relat_1 @ X23))),
% 2.93/3.17      inference('cnf', [status(esa)], [d3_funct_2])).
% 2.93/3.17  thf('43', plain,
% 2.93/3.17      (![X23 : $i]:
% 2.93/3.17         (~ (v1_relat_1 @ X23)
% 2.93/3.17          | ~ (v5_relat_1 @ X23 @ (k2_relat_1 @ X23))
% 2.93/3.17          | (v2_funct_2 @ X23 @ (k2_relat_1 @ X23)))),
% 2.93/3.17      inference('simplify', [status(thm)], ['42'])).
% 2.93/3.17  thf('44', plain,
% 2.93/3.17      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 2.93/3.17        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 2.93/3.17        | ~ (v1_relat_1 @ sk_D))),
% 2.93/3.17      inference('sup-', [status(thm)], ['41', '43'])).
% 2.93/3.17  thf('45', plain,
% 2.93/3.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.93/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.17  thf(cc2_relset_1, axiom,
% 2.93/3.17    (![A:$i,B:$i,C:$i]:
% 2.93/3.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.93/3.17       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.93/3.17  thf('46', plain,
% 2.93/3.17      (![X9 : $i, X10 : $i, X11 : $i]:
% 2.93/3.17         ((v5_relat_1 @ X9 @ X11)
% 2.93/3.17          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 2.93/3.17      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.93/3.17  thf('47', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 2.93/3.17      inference('sup-', [status(thm)], ['45', '46'])).
% 2.93/3.17  thf('48', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.93/3.17      inference('demod', [status(thm)], ['34', '37', '38', '39', '40'])).
% 2.93/3.17  thf('49', plain,
% 2.93/3.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.93/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.17  thf(cc1_relset_1, axiom,
% 2.93/3.17    (![A:$i,B:$i,C:$i]:
% 2.93/3.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.93/3.17       ( v1_relat_1 @ C ) ))).
% 2.93/3.17  thf('50', plain,
% 2.93/3.17      (![X6 : $i, X7 : $i, X8 : $i]:
% 2.93/3.17         ((v1_relat_1 @ X6)
% 2.93/3.17          | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X7 @ X8))))),
% 2.93/3.17      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.93/3.17  thf('51', plain, ((v1_relat_1 @ sk_D)),
% 2.93/3.17      inference('sup-', [status(thm)], ['49', '50'])).
% 2.93/3.17  thf('52', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 2.93/3.17      inference('demod', [status(thm)], ['44', '47', '48', '51'])).
% 2.93/3.17  thf('53', plain,
% 2.93/3.17      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 2.93/3.17      inference('split', [status(esa)], ['20'])).
% 2.93/3.17  thf('54', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 2.93/3.17      inference('sup-', [status(thm)], ['52', '53'])).
% 2.93/3.17  thf('55', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 2.93/3.17      inference('split', [status(esa)], ['20'])).
% 2.93/3.17  thf('56', plain, (~ ((v2_funct_1 @ sk_C))),
% 2.93/3.17      inference('sat_resolution*', [status(thm)], ['54', '55'])).
% 2.93/3.17  thf('57', plain, (~ (v1_xboole_0 @ sk_C)),
% 2.93/3.17      inference('simpl_trail', [status(thm)], ['22', '56'])).
% 2.93/3.17  thf('58', plain,
% 2.93/3.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.93/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.17  thf('59', plain,
% 2.93/3.17      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.93/3.17      inference('sup-', [status(thm)], ['0', '1'])).
% 2.93/3.17  thf('60', plain,
% 2.93/3.17      (![X1 : $i]:
% 2.93/3.17         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 2.93/3.17          | (v1_xboole_0 @ X1))),
% 2.93/3.17      inference('demod', [status(thm)], ['11', '12'])).
% 2.93/3.17  thf('61', plain,
% 2.93/3.17      (![X0 : $i, X1 : $i]:
% 2.93/3.17         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X0))
% 2.93/3.17          | ~ (v1_xboole_0 @ X0)
% 2.93/3.17          | (v1_xboole_0 @ X1))),
% 2.93/3.17      inference('sup-', [status(thm)], ['59', '60'])).
% 2.93/3.17  thf('62', plain,
% 2.93/3.17      (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.93/3.17      inference('sup-', [status(thm)], ['58', '61'])).
% 2.93/3.17  thf('63', plain,
% 2.93/3.17      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.93/3.17        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.93/3.17        (k6_relat_1 @ sk_A))),
% 2.93/3.17      inference('demod', [status(thm)], ['23', '24'])).
% 2.93/3.17  thf('64', plain,
% 2.93/3.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.93/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.17  thf('65', plain,
% 2.93/3.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.93/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.17  thf(dt_k1_partfun1, axiom,
% 2.93/3.17    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.93/3.17     ( ( ( v1_funct_1 @ E ) & 
% 2.93/3.17         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.93/3.17         ( v1_funct_1 @ F ) & 
% 2.93/3.17         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.93/3.17       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.93/3.17         ( m1_subset_1 @
% 2.93/3.17           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.93/3.17           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.93/3.17  thf('66', plain,
% 2.93/3.17      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 2.93/3.17         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 2.93/3.17          | ~ (v1_funct_1 @ X24)
% 2.93/3.17          | ~ (v1_funct_1 @ X27)
% 2.93/3.17          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 2.93/3.17          | (m1_subset_1 @ (k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27) @ 
% 2.93/3.17             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X29))))),
% 2.93/3.17      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.93/3.17  thf('67', plain,
% 2.93/3.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.93/3.17         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.93/3.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.93/3.17          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.93/3.17          | ~ (v1_funct_1 @ X1)
% 2.93/3.17          | ~ (v1_funct_1 @ sk_C))),
% 2.93/3.17      inference('sup-', [status(thm)], ['65', '66'])).
% 2.93/3.17  thf('68', plain, ((v1_funct_1 @ sk_C)),
% 2.93/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.17  thf('69', plain,
% 2.93/3.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.93/3.17         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 2.93/3.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.93/3.17          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.93/3.17          | ~ (v1_funct_1 @ X1))),
% 2.93/3.17      inference('demod', [status(thm)], ['67', '68'])).
% 2.93/3.17  thf('70', plain,
% 2.93/3.17      ((~ (v1_funct_1 @ sk_D)
% 2.93/3.17        | (m1_subset_1 @ 
% 2.93/3.17           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.93/3.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.93/3.17      inference('sup-', [status(thm)], ['64', '69'])).
% 2.93/3.17  thf('71', plain, ((v1_funct_1 @ sk_D)),
% 2.93/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.17  thf('72', plain,
% 2.93/3.17      ((m1_subset_1 @ 
% 2.93/3.17        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 2.93/3.17        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.93/3.17      inference('demod', [status(thm)], ['70', '71'])).
% 2.93/3.17  thf(redefinition_r2_relset_1, axiom,
% 2.93/3.17    (![A:$i,B:$i,C:$i,D:$i]:
% 2.93/3.17     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.93/3.17         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.93/3.17       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.93/3.17  thf('73', plain,
% 2.93/3.17      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 2.93/3.17         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 2.93/3.17          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 2.93/3.17          | ((X18) = (X21))
% 2.93/3.17          | ~ (r2_relset_1 @ X19 @ X20 @ X18 @ X21))),
% 2.93/3.17      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.93/3.17  thf('74', plain,
% 2.93/3.17      (![X0 : $i]:
% 2.93/3.17         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 2.93/3.17             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 2.93/3.17          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 2.93/3.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.93/3.17      inference('sup-', [status(thm)], ['72', '73'])).
% 2.93/3.17  thf('75', plain,
% 2.93/3.17      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 2.93/3.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.93/3.17        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.93/3.17            = (k6_relat_1 @ sk_A)))),
% 2.93/3.17      inference('sup-', [status(thm)], ['63', '74'])).
% 2.93/3.17  thf('76', plain,
% 2.93/3.17      (![X31 : $i]:
% 2.93/3.17         (m1_subset_1 @ (k6_relat_1 @ X31) @ 
% 2.93/3.17          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X31)))),
% 2.93/3.17      inference('demod', [status(thm)], ['5', '6'])).
% 2.93/3.17  thf('77', plain,
% 2.93/3.17      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 2.93/3.17         = (k6_relat_1 @ sk_A))),
% 2.93/3.17      inference('demod', [status(thm)], ['75', '76'])).
% 2.93/3.17  thf('78', plain,
% 2.93/3.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 2.93/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.17  thf(t26_funct_2, axiom,
% 2.93/3.17    (![A:$i,B:$i,C:$i,D:$i]:
% 2.93/3.17     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.93/3.17         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.93/3.17       ( ![E:$i]:
% 2.93/3.17         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.93/3.17             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.93/3.17           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 2.93/3.17             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 2.93/3.17               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 2.93/3.17  thf('79', plain,
% 2.93/3.17      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 2.93/3.17         (~ (v1_funct_1 @ X37)
% 2.93/3.17          | ~ (v1_funct_2 @ X37 @ X38 @ X39)
% 2.93/3.17          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39)))
% 2.93/3.17          | ~ (v2_funct_1 @ (k1_partfun1 @ X40 @ X38 @ X38 @ X39 @ X41 @ X37))
% 2.93/3.17          | (v2_funct_1 @ X41)
% 2.93/3.17          | ((X39) = (k1_xboole_0))
% 2.93/3.17          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X38)))
% 2.93/3.17          | ~ (v1_funct_2 @ X41 @ X40 @ X38)
% 2.93/3.17          | ~ (v1_funct_1 @ X41))),
% 2.93/3.17      inference('cnf', [status(esa)], [t26_funct_2])).
% 2.93/3.17  thf('80', plain,
% 2.93/3.17      (![X0 : $i, X1 : $i]:
% 2.93/3.17         (~ (v1_funct_1 @ X0)
% 2.93/3.17          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.93/3.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.93/3.17          | ((sk_A) = (k1_xboole_0))
% 2.93/3.17          | (v2_funct_1 @ X0)
% 2.93/3.17          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 2.93/3.17          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 2.93/3.17          | ~ (v1_funct_1 @ sk_D))),
% 2.93/3.17      inference('sup-', [status(thm)], ['78', '79'])).
% 2.93/3.17  thf('81', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 2.93/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.17  thf('82', plain, ((v1_funct_1 @ sk_D)),
% 2.93/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.17  thf('83', plain,
% 2.93/3.17      (![X0 : $i, X1 : $i]:
% 2.93/3.17         (~ (v1_funct_1 @ X0)
% 2.93/3.17          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.93/3.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.93/3.17          | ((sk_A) = (k1_xboole_0))
% 2.93/3.17          | (v2_funct_1 @ X0)
% 2.93/3.17          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 2.93/3.17      inference('demod', [status(thm)], ['80', '81', '82'])).
% 2.93/3.17  thf('84', plain,
% 2.93/3.17      ((~ (v2_funct_1 @ (k6_relat_1 @ sk_A))
% 2.93/3.17        | (v2_funct_1 @ sk_C)
% 2.93/3.17        | ((sk_A) = (k1_xboole_0))
% 2.93/3.17        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 2.93/3.17        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 2.93/3.17        | ~ (v1_funct_1 @ sk_C))),
% 2.93/3.17      inference('sup-', [status(thm)], ['77', '83'])).
% 2.93/3.17  thf('85', plain, (![X5 : $i]: (v2_funct_1 @ (k6_relat_1 @ X5))),
% 2.93/3.17      inference('cnf', [status(esa)], [t52_funct_1])).
% 2.93/3.17  thf('86', plain,
% 2.93/3.17      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 2.93/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.17  thf('87', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 2.93/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.17  thf('88', plain, ((v1_funct_1 @ sk_C)),
% 2.93/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.93/3.17  thf('89', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 2.93/3.17      inference('demod', [status(thm)], ['84', '85', '86', '87', '88'])).
% 2.93/3.17  thf('90', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 2.93/3.17      inference('split', [status(esa)], ['20'])).
% 2.93/3.17  thf('91', plain, (~ ((v2_funct_1 @ sk_C))),
% 2.93/3.17      inference('sat_resolution*', [status(thm)], ['54', '55'])).
% 2.93/3.17  thf('92', plain, (~ (v2_funct_1 @ sk_C)),
% 2.93/3.17      inference('simpl_trail', [status(thm)], ['90', '91'])).
% 2.93/3.17  thf('93', plain, (((sk_A) = (k1_xboole_0))),
% 2.93/3.17      inference('clc', [status(thm)], ['89', '92'])).
% 2.93/3.17  thf('94', plain,
% 2.93/3.17      (![X3 : $i, X4 : $i]:
% 2.93/3.17         (((k2_zfmisc_1 @ X3 @ X4) = (k1_xboole_0)) | ((X3) != (k1_xboole_0)))),
% 2.93/3.17      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 2.93/3.17  thf('95', plain,
% 2.93/3.17      (![X4 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X4) = (k1_xboole_0))),
% 2.93/3.17      inference('simplify', [status(thm)], ['94'])).
% 2.93/3.17  thf('96', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.93/3.17      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.93/3.17  thf('97', plain, ((v1_xboole_0 @ sk_C)),
% 2.93/3.17      inference('demod', [status(thm)], ['62', '93', '95', '96'])).
% 2.93/3.17  thf('98', plain, ($false), inference('demod', [status(thm)], ['57', '97'])).
% 2.93/3.17  
% 2.93/3.17  % SZS output end Refutation
% 2.93/3.17  
% 2.93/3.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
