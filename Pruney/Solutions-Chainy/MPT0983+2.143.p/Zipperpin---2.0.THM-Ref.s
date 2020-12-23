%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WaNnWnWOhw

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:24 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 314 expanded)
%              Number of leaves         :   38 ( 107 expanded)
%              Depth                    :   14
%              Number of atoms          : 1066 (6360 expanded)
%              Number of equality atoms :   31 (  64 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('0',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

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
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('3',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X13 ) ) )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k6_partfun1 @ X0 ) )
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
      | ( ( k6_partfun1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('8',plain,(
    ! [X30: $i] :
      ( ( k6_partfun1 @ X30 )
      = ( k6_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('9',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X7 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['10'])).

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

thf('12',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['12'])).

thf('14',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['11','13'])).

thf('15',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,
    ( ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('24',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('25',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['22','25','26','27','28'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('30',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k2_relat_1 @ X23 )
       != X22 )
      | ( v2_funct_2 @ X23 @ X22 )
      | ~ ( v5_relat_1 @ X23 @ X22 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('31',plain,(
    ! [X23: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ~ ( v5_relat_1 @ X23 @ ( k2_relat_1 @ X23 ) )
      | ( v2_funct_2 @ X23 @ ( k2_relat_1 @ X23 ) ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['29','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('34',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v5_relat_1 @ X8 @ X10 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('35',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['22','25','26','27','28'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('38',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('39',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('40',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('41',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['39','40'])).

thf('42',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['32','35','36','41'])).

thf('43',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('44',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('46',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['44','45'])).

thf('47',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['14','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X13 ) ) )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('50',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X17 = X20 )
      | ~ ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','62'])).

thf('64',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X21 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('65',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
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
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['65','71'])).

thf('73',plain,(
    ! [X7: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X7 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

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
    inference(split,[status(esa)],['12'])).

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
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WaNnWnWOhw
% 0.13/0.31  % Computer   : n019.cluster.edu
% 0.13/0.31  % Model      : x86_64 x86_64
% 0.13/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.31  % Memory     : 8042.1875MB
% 0.13/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.31  % CPULimit   : 60
% 0.13/0.31  % DateTime   : Tue Dec  1 13:53:07 EST 2020
% 0.13/0.31  % CPUTime    : 
% 0.13/0.31  % Running portfolio for 600 s
% 0.13/0.31  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.31  % Number of cores: 8
% 0.17/0.32  % Python version: Python 3.6.8
% 0.17/0.32  % Running in FO mode
% 1.66/1.91  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.66/1.91  % Solved by: fo/fo7.sh
% 1.66/1.91  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.66/1.91  % done 1463 iterations in 1.484s
% 1.66/1.91  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.66/1.91  % SZS output start Refutation
% 1.66/1.91  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.66/1.91  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.66/1.91  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.66/1.91  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.66/1.91  thf(sk_C_type, type, sk_C: $i).
% 1.66/1.91  thf(sk_B_type, type, sk_B: $i).
% 1.66/1.91  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.66/1.91  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.66/1.91  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.66/1.91  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.66/1.91  thf(sk_D_type, type, sk_D: $i).
% 1.66/1.91  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.66/1.91  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.66/1.91  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 1.66/1.91  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.66/1.91  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.66/1.91  thf(sk_A_type, type, sk_A: $i).
% 1.66/1.91  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.66/1.91  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.66/1.91  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.66/1.91  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.66/1.91  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.66/1.91  thf(t29_relset_1, axiom,
% 1.66/1.91    (![A:$i]:
% 1.66/1.91     ( m1_subset_1 @
% 1.66/1.91       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.66/1.91  thf('0', plain,
% 1.66/1.91      (![X21 : $i]:
% 1.66/1.91         (m1_subset_1 @ (k6_relat_1 @ X21) @ 
% 1.66/1.91          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 1.66/1.91      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.66/1.91  thf(redefinition_k6_partfun1, axiom,
% 1.66/1.91    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.66/1.91  thf('1', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 1.66/1.91      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.66/1.91  thf('2', plain,
% 1.66/1.91      (![X21 : $i]:
% 1.66/1.91         (m1_subset_1 @ (k6_partfun1 @ X21) @ 
% 1.66/1.91          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 1.66/1.91      inference('demod', [status(thm)], ['0', '1'])).
% 1.66/1.91  thf(cc3_relset_1, axiom,
% 1.66/1.91    (![A:$i,B:$i]:
% 1.66/1.91     ( ( v1_xboole_0 @ A ) =>
% 1.66/1.91       ( ![C:$i]:
% 1.66/1.91         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.66/1.91           ( v1_xboole_0 @ C ) ) ) ))).
% 1.66/1.91  thf('3', plain,
% 1.66/1.91      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.66/1.91         (~ (v1_xboole_0 @ X11)
% 1.66/1.91          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X13)))
% 1.66/1.91          | (v1_xboole_0 @ X12))),
% 1.66/1.91      inference('cnf', [status(esa)], [cc3_relset_1])).
% 1.66/1.91  thf('4', plain,
% 1.66/1.91      (![X0 : $i]: ((v1_xboole_0 @ (k6_partfun1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.66/1.91      inference('sup-', [status(thm)], ['2', '3'])).
% 1.66/1.91  thf(t8_boole, axiom,
% 1.66/1.91    (![A:$i,B:$i]:
% 1.66/1.91     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 1.66/1.91  thf('5', plain,
% 1.66/1.91      (![X0 : $i, X1 : $i]:
% 1.66/1.91         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 1.66/1.91      inference('cnf', [status(esa)], [t8_boole])).
% 1.66/1.91  thf('6', plain,
% 1.66/1.91      (![X0 : $i, X1 : $i]:
% 1.66/1.91         (~ (v1_xboole_0 @ X0)
% 1.66/1.91          | ((k6_partfun1 @ X0) = (X1))
% 1.66/1.91          | ~ (v1_xboole_0 @ X1))),
% 1.66/1.91      inference('sup-', [status(thm)], ['4', '5'])).
% 1.66/1.91  thf(fc4_funct_1, axiom,
% 1.66/1.91    (![A:$i]:
% 1.66/1.91     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.66/1.91       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.66/1.91  thf('7', plain, (![X7 : $i]: (v2_funct_1 @ (k6_relat_1 @ X7))),
% 1.66/1.91      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.66/1.91  thf('8', plain, (![X30 : $i]: ((k6_partfun1 @ X30) = (k6_relat_1 @ X30))),
% 1.66/1.91      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.66/1.91  thf('9', plain, (![X7 : $i]: (v2_funct_1 @ (k6_partfun1 @ X7))),
% 1.66/1.91      inference('demod', [status(thm)], ['7', '8'])).
% 1.66/1.91  thf('10', plain,
% 1.66/1.91      (![X0 : $i, X1 : $i]:
% 1.66/1.91         ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 1.66/1.91      inference('sup+', [status(thm)], ['6', '9'])).
% 1.66/1.91  thf('11', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 1.66/1.91      inference('condensation', [status(thm)], ['10'])).
% 1.66/1.91  thf(t29_funct_2, conjecture,
% 1.66/1.91    (![A:$i,B:$i,C:$i]:
% 1.66/1.91     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.66/1.91         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.66/1.91       ( ![D:$i]:
% 1.66/1.91         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.66/1.91             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.66/1.91           ( ( r2_relset_1 @
% 1.66/1.91               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.66/1.91               ( k6_partfun1 @ A ) ) =>
% 1.66/1.91             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 1.66/1.91  thf(zf_stmt_0, negated_conjecture,
% 1.66/1.91    (~( ![A:$i,B:$i,C:$i]:
% 1.66/1.91        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.66/1.91            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.66/1.91          ( ![D:$i]:
% 1.66/1.91            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.66/1.91                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.66/1.91              ( ( r2_relset_1 @
% 1.66/1.91                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.66/1.91                  ( k6_partfun1 @ A ) ) =>
% 1.66/1.91                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 1.66/1.91    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 1.66/1.91  thf('12', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 1.66/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.91  thf('13', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 1.66/1.91      inference('split', [status(esa)], ['12'])).
% 1.66/1.91  thf('14', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 1.66/1.91      inference('sup-', [status(thm)], ['11', '13'])).
% 1.66/1.91  thf('15', plain,
% 1.66/1.91      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.66/1.91        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.66/1.91        (k6_partfun1 @ sk_A))),
% 1.66/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.91  thf('16', plain,
% 1.66/1.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.66/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.91  thf(t24_funct_2, axiom,
% 1.66/1.91    (![A:$i,B:$i,C:$i]:
% 1.66/1.91     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.66/1.91         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.66/1.91       ( ![D:$i]:
% 1.66/1.91         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.66/1.91             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.66/1.91           ( ( r2_relset_1 @
% 1.66/1.91               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.66/1.91               ( k6_partfun1 @ B ) ) =>
% 1.66/1.91             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.66/1.91  thf('17', plain,
% 1.66/1.91      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 1.66/1.91         (~ (v1_funct_1 @ X31)
% 1.66/1.91          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 1.66/1.91          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 1.66/1.91          | ~ (r2_relset_1 @ X32 @ X32 @ 
% 1.66/1.91               (k1_partfun1 @ X32 @ X33 @ X33 @ X32 @ X31 @ X34) @ 
% 1.66/1.91               (k6_partfun1 @ X32))
% 1.66/1.91          | ((k2_relset_1 @ X33 @ X32 @ X34) = (X32))
% 1.66/1.91          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 1.66/1.91          | ~ (v1_funct_2 @ X34 @ X33 @ X32)
% 1.66/1.91          | ~ (v1_funct_1 @ X34))),
% 1.66/1.91      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.66/1.91  thf('18', plain,
% 1.66/1.91      (![X0 : $i]:
% 1.66/1.91         (~ (v1_funct_1 @ X0)
% 1.66/1.91          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.66/1.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.66/1.91          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.66/1.91          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.66/1.91               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.66/1.91               (k6_partfun1 @ sk_A))
% 1.66/1.91          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.66/1.91          | ~ (v1_funct_1 @ sk_C))),
% 1.66/1.91      inference('sup-', [status(thm)], ['16', '17'])).
% 1.66/1.91  thf('19', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.66/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.91  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 1.66/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.91  thf('21', plain,
% 1.66/1.91      (![X0 : $i]:
% 1.66/1.91         (~ (v1_funct_1 @ X0)
% 1.66/1.91          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.66/1.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.66/1.91          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.66/1.91          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.66/1.91               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.66/1.91               (k6_partfun1 @ sk_A)))),
% 1.66/1.91      inference('demod', [status(thm)], ['18', '19', '20'])).
% 1.66/1.91  thf('22', plain,
% 1.66/1.91      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.66/1.91        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.66/1.91        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.66/1.91        | ~ (v1_funct_1 @ sk_D))),
% 1.66/1.91      inference('sup-', [status(thm)], ['15', '21'])).
% 1.66/1.91  thf('23', plain,
% 1.66/1.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.66/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.91  thf(redefinition_k2_relset_1, axiom,
% 1.66/1.91    (![A:$i,B:$i,C:$i]:
% 1.66/1.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.66/1.91       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.66/1.91  thf('24', plain,
% 1.66/1.91      (![X14 : $i, X15 : $i, X16 : $i]:
% 1.66/1.91         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 1.66/1.91          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 1.66/1.91      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.66/1.91  thf('25', plain,
% 1.66/1.91      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.66/1.91      inference('sup-', [status(thm)], ['23', '24'])).
% 1.66/1.91  thf('26', plain,
% 1.66/1.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.66/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.91  thf('27', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.66/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.91  thf('28', plain, ((v1_funct_1 @ sk_D)),
% 1.66/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.91  thf('29', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.66/1.91      inference('demod', [status(thm)], ['22', '25', '26', '27', '28'])).
% 1.66/1.91  thf(d3_funct_2, axiom,
% 1.66/1.91    (![A:$i,B:$i]:
% 1.66/1.91     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 1.66/1.91       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 1.66/1.91  thf('30', plain,
% 1.66/1.91      (![X22 : $i, X23 : $i]:
% 1.66/1.91         (((k2_relat_1 @ X23) != (X22))
% 1.66/1.91          | (v2_funct_2 @ X23 @ X22)
% 1.66/1.91          | ~ (v5_relat_1 @ X23 @ X22)
% 1.66/1.91          | ~ (v1_relat_1 @ X23))),
% 1.66/1.91      inference('cnf', [status(esa)], [d3_funct_2])).
% 1.66/1.91  thf('31', plain,
% 1.66/1.91      (![X23 : $i]:
% 1.66/1.91         (~ (v1_relat_1 @ X23)
% 1.66/1.91          | ~ (v5_relat_1 @ X23 @ (k2_relat_1 @ X23))
% 1.66/1.91          | (v2_funct_2 @ X23 @ (k2_relat_1 @ X23)))),
% 1.66/1.91      inference('simplify', [status(thm)], ['30'])).
% 1.66/1.91  thf('32', plain,
% 1.66/1.91      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 1.66/1.91        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 1.66/1.91        | ~ (v1_relat_1 @ sk_D))),
% 1.66/1.91      inference('sup-', [status(thm)], ['29', '31'])).
% 1.66/1.91  thf('33', plain,
% 1.66/1.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.66/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.91  thf(cc2_relset_1, axiom,
% 1.66/1.91    (![A:$i,B:$i,C:$i]:
% 1.66/1.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.66/1.91       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.66/1.91  thf('34', plain,
% 1.66/1.91      (![X8 : $i, X9 : $i, X10 : $i]:
% 1.66/1.91         ((v5_relat_1 @ X8 @ X10)
% 1.66/1.91          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 1.66/1.91      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.66/1.91  thf('35', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 1.66/1.91      inference('sup-', [status(thm)], ['33', '34'])).
% 1.66/1.91  thf('36', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.66/1.91      inference('demod', [status(thm)], ['22', '25', '26', '27', '28'])).
% 1.66/1.91  thf('37', plain,
% 1.66/1.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.66/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.91  thf(cc2_relat_1, axiom,
% 1.66/1.91    (![A:$i]:
% 1.66/1.91     ( ( v1_relat_1 @ A ) =>
% 1.66/1.91       ( ![B:$i]:
% 1.66/1.91         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 1.66/1.91  thf('38', plain,
% 1.66/1.91      (![X2 : $i, X3 : $i]:
% 1.66/1.91         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 1.66/1.91          | (v1_relat_1 @ X2)
% 1.66/1.91          | ~ (v1_relat_1 @ X3))),
% 1.66/1.91      inference('cnf', [status(esa)], [cc2_relat_1])).
% 1.66/1.91  thf('39', plain,
% 1.66/1.91      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)) | (v1_relat_1 @ sk_D))),
% 1.66/1.91      inference('sup-', [status(thm)], ['37', '38'])).
% 1.66/1.91  thf(fc6_relat_1, axiom,
% 1.66/1.91    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 1.66/1.91  thf('40', plain,
% 1.66/1.91      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 1.66/1.91      inference('cnf', [status(esa)], [fc6_relat_1])).
% 1.66/1.91  thf('41', plain, ((v1_relat_1 @ sk_D)),
% 1.66/1.91      inference('demod', [status(thm)], ['39', '40'])).
% 1.66/1.91  thf('42', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 1.66/1.91      inference('demod', [status(thm)], ['32', '35', '36', '41'])).
% 1.66/1.91  thf('43', plain,
% 1.66/1.91      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 1.66/1.91      inference('split', [status(esa)], ['12'])).
% 1.66/1.91  thf('44', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 1.66/1.91      inference('sup-', [status(thm)], ['42', '43'])).
% 1.66/1.91  thf('45', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 1.66/1.91      inference('split', [status(esa)], ['12'])).
% 1.66/1.91  thf('46', plain, (~ ((v2_funct_1 @ sk_C))),
% 1.66/1.91      inference('sat_resolution*', [status(thm)], ['44', '45'])).
% 1.66/1.91  thf('47', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.66/1.91      inference('simpl_trail', [status(thm)], ['14', '46'])).
% 1.66/1.91  thf('48', plain,
% 1.66/1.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.66/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.91  thf('49', plain,
% 1.66/1.91      (![X11 : $i, X12 : $i, X13 : $i]:
% 1.66/1.91         (~ (v1_xboole_0 @ X11)
% 1.66/1.91          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X13)))
% 1.66/1.91          | (v1_xboole_0 @ X12))),
% 1.66/1.91      inference('cnf', [status(esa)], [cc3_relset_1])).
% 1.66/1.91  thf('50', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 1.66/1.91      inference('sup-', [status(thm)], ['48', '49'])).
% 1.66/1.91  thf('51', plain,
% 1.66/1.91      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.66/1.91        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.66/1.91        (k6_partfun1 @ sk_A))),
% 1.66/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.91  thf('52', plain,
% 1.66/1.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.66/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.91  thf('53', plain,
% 1.66/1.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.66/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.91  thf(dt_k1_partfun1, axiom,
% 1.66/1.91    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.66/1.91     ( ( ( v1_funct_1 @ E ) & 
% 1.66/1.91         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.66/1.91         ( v1_funct_1 @ F ) & 
% 1.66/1.91         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.66/1.91       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.66/1.91         ( m1_subset_1 @
% 1.66/1.91           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.66/1.91           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.66/1.91  thf('54', plain,
% 1.66/1.91      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 1.66/1.91         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 1.66/1.91          | ~ (v1_funct_1 @ X24)
% 1.66/1.91          | ~ (v1_funct_1 @ X27)
% 1.66/1.91          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 1.66/1.91          | (m1_subset_1 @ (k1_partfun1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27) @ 
% 1.66/1.91             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X29))))),
% 1.66/1.91      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.66/1.91  thf('55', plain,
% 1.66/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.91         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.66/1.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.66/1.91          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.66/1.91          | ~ (v1_funct_1 @ X1)
% 1.66/1.91          | ~ (v1_funct_1 @ sk_C))),
% 1.66/1.91      inference('sup-', [status(thm)], ['53', '54'])).
% 1.66/1.91  thf('56', plain, ((v1_funct_1 @ sk_C)),
% 1.66/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.91  thf('57', plain,
% 1.66/1.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.66/1.91         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.66/1.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.66/1.91          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.66/1.91          | ~ (v1_funct_1 @ X1))),
% 1.66/1.91      inference('demod', [status(thm)], ['55', '56'])).
% 1.66/1.91  thf('58', plain,
% 1.66/1.91      ((~ (v1_funct_1 @ sk_D)
% 1.66/1.91        | (m1_subset_1 @ 
% 1.66/1.91           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.66/1.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.66/1.91      inference('sup-', [status(thm)], ['52', '57'])).
% 1.66/1.91  thf('59', plain, ((v1_funct_1 @ sk_D)),
% 1.66/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.91  thf('60', plain,
% 1.66/1.91      ((m1_subset_1 @ 
% 1.66/1.91        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.66/1.91        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.66/1.91      inference('demod', [status(thm)], ['58', '59'])).
% 1.66/1.91  thf(redefinition_r2_relset_1, axiom,
% 1.66/1.91    (![A:$i,B:$i,C:$i,D:$i]:
% 1.66/1.91     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.66/1.91         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.66/1.91       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.66/1.91  thf('61', plain,
% 1.66/1.91      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 1.66/1.91         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 1.66/1.91          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 1.66/1.91          | ((X17) = (X20))
% 1.66/1.91          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 1.66/1.91      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.66/1.91  thf('62', plain,
% 1.66/1.91      (![X0 : $i]:
% 1.66/1.91         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.66/1.91             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 1.66/1.91          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 1.66/1.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.66/1.91      inference('sup-', [status(thm)], ['60', '61'])).
% 1.66/1.91  thf('63', plain,
% 1.66/1.91      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.66/1.91           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.66/1.91        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.66/1.91            = (k6_partfun1 @ sk_A)))),
% 1.66/1.91      inference('sup-', [status(thm)], ['51', '62'])).
% 1.66/1.91  thf('64', plain,
% 1.66/1.91      (![X21 : $i]:
% 1.66/1.91         (m1_subset_1 @ (k6_partfun1 @ X21) @ 
% 1.66/1.91          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))),
% 1.66/1.91      inference('demod', [status(thm)], ['0', '1'])).
% 1.66/1.91  thf('65', plain,
% 1.66/1.91      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.66/1.91         = (k6_partfun1 @ sk_A))),
% 1.66/1.91      inference('demod', [status(thm)], ['63', '64'])).
% 1.66/1.91  thf('66', plain,
% 1.66/1.91      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.66/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.91  thf(t26_funct_2, axiom,
% 1.66/1.91    (![A:$i,B:$i,C:$i,D:$i]:
% 1.66/1.91     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.66/1.91         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.66/1.91       ( ![E:$i]:
% 1.66/1.91         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.66/1.91             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.66/1.91           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 1.66/1.91             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 1.66/1.91               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 1.66/1.91  thf('67', plain,
% 1.66/1.91      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 1.66/1.91         (~ (v1_funct_1 @ X35)
% 1.66/1.91          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 1.66/1.91          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 1.66/1.91          | ~ (v2_funct_1 @ (k1_partfun1 @ X38 @ X36 @ X36 @ X37 @ X39 @ X35))
% 1.66/1.91          | (v2_funct_1 @ X39)
% 1.66/1.91          | ((X37) = (k1_xboole_0))
% 1.66/1.91          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X36)))
% 1.66/1.91          | ~ (v1_funct_2 @ X39 @ X38 @ X36)
% 1.66/1.91          | ~ (v1_funct_1 @ X39))),
% 1.66/1.91      inference('cnf', [status(esa)], [t26_funct_2])).
% 1.66/1.91  thf('68', plain,
% 1.66/1.91      (![X0 : $i, X1 : $i]:
% 1.66/1.91         (~ (v1_funct_1 @ X0)
% 1.66/1.91          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.66/1.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.66/1.91          | ((sk_A) = (k1_xboole_0))
% 1.66/1.91          | (v2_funct_1 @ X0)
% 1.66/1.91          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.66/1.91          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.66/1.91          | ~ (v1_funct_1 @ sk_D))),
% 1.66/1.91      inference('sup-', [status(thm)], ['66', '67'])).
% 1.66/1.91  thf('69', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.66/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.91  thf('70', plain, ((v1_funct_1 @ sk_D)),
% 1.66/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.91  thf('71', plain,
% 1.66/1.91      (![X0 : $i, X1 : $i]:
% 1.66/1.91         (~ (v1_funct_1 @ X0)
% 1.66/1.91          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.66/1.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.66/1.91          | ((sk_A) = (k1_xboole_0))
% 1.66/1.91          | (v2_funct_1 @ X0)
% 1.66/1.91          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 1.66/1.91      inference('demod', [status(thm)], ['68', '69', '70'])).
% 1.66/1.91  thf('72', plain,
% 1.66/1.91      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 1.66/1.91        | (v2_funct_1 @ sk_C)
% 1.66/1.91        | ((sk_A) = (k1_xboole_0))
% 1.66/1.91        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.66/1.91        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.66/1.91        | ~ (v1_funct_1 @ sk_C))),
% 1.66/1.91      inference('sup-', [status(thm)], ['65', '71'])).
% 1.66/1.91  thf('73', plain, (![X7 : $i]: (v2_funct_1 @ (k6_partfun1 @ X7))),
% 1.66/1.91      inference('demod', [status(thm)], ['7', '8'])).
% 1.66/1.91  thf('74', plain,
% 1.66/1.91      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.66/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.91  thf('75', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.66/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.91  thf('76', plain, ((v1_funct_1 @ sk_C)),
% 1.66/1.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.66/1.91  thf('77', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.66/1.91      inference('demod', [status(thm)], ['72', '73', '74', '75', '76'])).
% 1.66/1.91  thf('78', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 1.66/1.91      inference('split', [status(esa)], ['12'])).
% 1.66/1.91  thf('79', plain, (~ ((v2_funct_1 @ sk_C))),
% 1.66/1.91      inference('sat_resolution*', [status(thm)], ['44', '45'])).
% 1.66/1.91  thf('80', plain, (~ (v2_funct_1 @ sk_C)),
% 1.66/1.91      inference('simpl_trail', [status(thm)], ['78', '79'])).
% 1.66/1.91  thf('81', plain, (((sk_A) = (k1_xboole_0))),
% 1.66/1.91      inference('clc', [status(thm)], ['77', '80'])).
% 1.66/1.91  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.66/1.91  thf('82', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.66/1.91      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.66/1.91  thf('83', plain, ((v1_xboole_0 @ sk_C)),
% 1.66/1.91      inference('demod', [status(thm)], ['50', '81', '82'])).
% 1.66/1.91  thf('84', plain, ($false), inference('demod', [status(thm)], ['47', '83'])).
% 1.66/1.91  
% 1.66/1.91  % SZS output end Refutation
% 1.66/1.91  
% 1.76/1.92  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
