%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AtBR9boSgV

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:08 EST 2020

% Result     : Theorem 1.77s
% Output     : Refutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 308 expanded)
%              Number of leaves         :   37 ( 105 expanded)
%              Depth                    :   14
%              Number of atoms          : 1052 (6332 expanded)
%              Number of equality atoms :   31 (  64 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('0',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('1',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('2',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) ) ),
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
    ! [X3: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('8',plain,(
    ! [X29: $i] :
      ( ( k6_partfun1 @ X29 )
      = ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('9',plain,(
    ! [X3: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X3 ) ) ),
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
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( r2_relset_1 @ X31 @ X31 @ ( k1_partfun1 @ X31 @ X32 @ X32 @ X31 @ X30 @ X33 ) @ ( k6_partfun1 @ X31 ) )
      | ( ( k2_relset_1 @ X32 @ X31 @ X33 )
        = X31 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X33 @ X32 @ X31 )
      | ~ ( v1_funct_1 @ X33 ) ) ),
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
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k2_relset_1 @ X14 @ X15 @ X13 )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ( ( k2_relat_1 @ X22 )
       != X21 )
      | ( v2_funct_2 @ X22 @ X21 )
      | ~ ( v5_relat_1 @ X22 @ X21 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('31',plain,(
    ! [X22: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ~ ( v5_relat_1 @ X22 @ ( k2_relat_1 @ X22 ) )
      | ( v2_funct_2 @ X22 @ ( k2_relat_1 @ X22 ) ) ) ),
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
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v5_relat_1 @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
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

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('38',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('39',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['32','35','36','39'])).

thf('41',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('42',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['12'])).

thf('44',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['14','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X12 ) ) )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('48',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
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

thf('52',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('59',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( X16 = X19 )
      | ~ ( r2_relset_1 @ X17 @ X18 @ X16 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','60'])).

thf('62',plain,(
    ! [X20: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X20 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X20 ) ) ) ),
    inference(demod,[status(thm)],['0','1'])).

thf('63',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
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

thf('65',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ X35 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X37 @ X35 @ X35 @ X36 @ X38 @ X34 ) )
      | ( v2_funct_1 @ X38 )
      | ( X36 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X37 @ X35 )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['63','69'])).

thf('71',plain,(
    ! [X3: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X3 ) ) ),
    inference(demod,[status(thm)],['7','8'])).

thf('72',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['70','71','72','73','74'])).

thf('76',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['12'])).

thf('77',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['42','43'])).

thf('78',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['76','77'])).

thf('79',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['75','78'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('80',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('81',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['48','79','80'])).

thf('82',plain,(
    $false ),
    inference(demod,[status(thm)],['45','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.AtBR9boSgV
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:11:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.77/1.95  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 1.77/1.95  % Solved by: fo/fo7.sh
% 1.77/1.95  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.77/1.95  % done 1463 iterations in 1.486s
% 1.77/1.95  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 1.77/1.95  % SZS output start Refutation
% 1.77/1.95  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 1.77/1.95  thf(sk_A_type, type, sk_A: $i).
% 1.77/1.95  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 1.77/1.95  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.77/1.95  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.77/1.95  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 1.77/1.95  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.77/1.95  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.77/1.95  thf(sk_B_type, type, sk_B: $i).
% 1.77/1.95  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.77/1.95  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 1.77/1.95  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 1.77/1.95  thf(sk_C_type, type, sk_C: $i).
% 1.77/1.95  thf(sk_D_type, type, sk_D: $i).
% 1.77/1.95  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 1.77/1.95  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 1.77/1.95  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.77/1.95  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 1.77/1.95  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.77/1.95  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.77/1.95  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 1.77/1.95  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 1.77/1.95  thf(t29_relset_1, axiom,
% 1.77/1.95    (![A:$i]:
% 1.77/1.95     ( m1_subset_1 @
% 1.77/1.95       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 1.77/1.95  thf('0', plain,
% 1.77/1.95      (![X20 : $i]:
% 1.77/1.95         (m1_subset_1 @ (k6_relat_1 @ X20) @ 
% 1.77/1.95          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))),
% 1.77/1.95      inference('cnf', [status(esa)], [t29_relset_1])).
% 1.77/1.95  thf(redefinition_k6_partfun1, axiom,
% 1.77/1.95    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 1.77/1.95  thf('1', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 1.77/1.95      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.77/1.95  thf('2', plain,
% 1.77/1.95      (![X20 : $i]:
% 1.77/1.95         (m1_subset_1 @ (k6_partfun1 @ X20) @ 
% 1.77/1.95          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))),
% 1.77/1.95      inference('demod', [status(thm)], ['0', '1'])).
% 1.77/1.95  thf(cc3_relset_1, axiom,
% 1.77/1.95    (![A:$i,B:$i]:
% 1.77/1.95     ( ( v1_xboole_0 @ A ) =>
% 1.77/1.95       ( ![C:$i]:
% 1.77/1.95         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.77/1.95           ( v1_xboole_0 @ C ) ) ) ))).
% 1.77/1.95  thf('3', plain,
% 1.77/1.95      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.77/1.95         (~ (v1_xboole_0 @ X10)
% 1.77/1.95          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X12)))
% 1.77/1.95          | (v1_xboole_0 @ X11))),
% 1.77/1.95      inference('cnf', [status(esa)], [cc3_relset_1])).
% 1.77/1.95  thf('4', plain,
% 1.77/1.95      (![X0 : $i]: ((v1_xboole_0 @ (k6_partfun1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 1.77/1.95      inference('sup-', [status(thm)], ['2', '3'])).
% 1.77/1.95  thf(t8_boole, axiom,
% 1.77/1.95    (![A:$i,B:$i]:
% 1.77/1.95     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 1.77/1.95  thf('5', plain,
% 1.77/1.95      (![X0 : $i, X1 : $i]:
% 1.77/1.95         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 1.77/1.95      inference('cnf', [status(esa)], [t8_boole])).
% 1.77/1.95  thf('6', plain,
% 1.77/1.95      (![X0 : $i, X1 : $i]:
% 1.77/1.95         (~ (v1_xboole_0 @ X0)
% 1.77/1.95          | ((k6_partfun1 @ X0) = (X1))
% 1.77/1.95          | ~ (v1_xboole_0 @ X1))),
% 1.77/1.95      inference('sup-', [status(thm)], ['4', '5'])).
% 1.77/1.95  thf(fc4_funct_1, axiom,
% 1.77/1.95    (![A:$i]:
% 1.77/1.95     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 1.77/1.95       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 1.77/1.95  thf('7', plain, (![X3 : $i]: (v2_funct_1 @ (k6_relat_1 @ X3))),
% 1.77/1.95      inference('cnf', [status(esa)], [fc4_funct_1])).
% 1.77/1.95  thf('8', plain, (![X29 : $i]: ((k6_partfun1 @ X29) = (k6_relat_1 @ X29))),
% 1.77/1.95      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 1.77/1.95  thf('9', plain, (![X3 : $i]: (v2_funct_1 @ (k6_partfun1 @ X3))),
% 1.77/1.95      inference('demod', [status(thm)], ['7', '8'])).
% 1.77/1.95  thf('10', plain,
% 1.77/1.95      (![X0 : $i, X1 : $i]:
% 1.77/1.95         ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 1.77/1.95      inference('sup+', [status(thm)], ['6', '9'])).
% 1.77/1.95  thf('11', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 1.77/1.95      inference('condensation', [status(thm)], ['10'])).
% 1.77/1.95  thf(t29_funct_2, conjecture,
% 1.77/1.95    (![A:$i,B:$i,C:$i]:
% 1.77/1.95     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.77/1.95         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.77/1.95       ( ![D:$i]:
% 1.77/1.95         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.77/1.95             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.77/1.95           ( ( r2_relset_1 @
% 1.77/1.95               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.77/1.95               ( k6_partfun1 @ A ) ) =>
% 1.77/1.95             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 1.77/1.95  thf(zf_stmt_0, negated_conjecture,
% 1.77/1.95    (~( ![A:$i,B:$i,C:$i]:
% 1.77/1.95        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.77/1.95            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.77/1.95          ( ![D:$i]:
% 1.77/1.95            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.77/1.95                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.77/1.95              ( ( r2_relset_1 @
% 1.77/1.95                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 1.77/1.95                  ( k6_partfun1 @ A ) ) =>
% 1.77/1.95                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 1.77/1.95    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 1.77/1.95  thf('12', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 1.77/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.77/1.95  thf('13', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 1.77/1.95      inference('split', [status(esa)], ['12'])).
% 1.77/1.95  thf('14', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 1.77/1.95      inference('sup-', [status(thm)], ['11', '13'])).
% 1.77/1.95  thf('15', plain,
% 1.77/1.95      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.77/1.95        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.77/1.95        (k6_partfun1 @ sk_A))),
% 1.77/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.77/1.95  thf('16', plain,
% 1.77/1.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.77/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.77/1.95  thf(t24_funct_2, axiom,
% 1.77/1.95    (![A:$i,B:$i,C:$i]:
% 1.77/1.95     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 1.77/1.95         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.77/1.95       ( ![D:$i]:
% 1.77/1.95         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 1.77/1.95             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 1.77/1.95           ( ( r2_relset_1 @
% 1.77/1.95               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 1.77/1.95               ( k6_partfun1 @ B ) ) =>
% 1.77/1.95             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 1.77/1.95  thf('17', plain,
% 1.77/1.95      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 1.77/1.95         (~ (v1_funct_1 @ X30)
% 1.77/1.95          | ~ (v1_funct_2 @ X30 @ X31 @ X32)
% 1.77/1.95          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 1.77/1.95          | ~ (r2_relset_1 @ X31 @ X31 @ 
% 1.77/1.95               (k1_partfun1 @ X31 @ X32 @ X32 @ X31 @ X30 @ X33) @ 
% 1.77/1.95               (k6_partfun1 @ X31))
% 1.77/1.95          | ((k2_relset_1 @ X32 @ X31 @ X33) = (X31))
% 1.77/1.95          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 1.77/1.95          | ~ (v1_funct_2 @ X33 @ X32 @ X31)
% 1.77/1.95          | ~ (v1_funct_1 @ X33))),
% 1.77/1.95      inference('cnf', [status(esa)], [t24_funct_2])).
% 1.77/1.95  thf('18', plain,
% 1.77/1.95      (![X0 : $i]:
% 1.77/1.95         (~ (v1_funct_1 @ X0)
% 1.77/1.95          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.77/1.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.77/1.95          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.77/1.95          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.77/1.95               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.77/1.95               (k6_partfun1 @ sk_A))
% 1.77/1.95          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.77/1.95          | ~ (v1_funct_1 @ sk_C))),
% 1.77/1.95      inference('sup-', [status(thm)], ['16', '17'])).
% 1.77/1.95  thf('19', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.77/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.77/1.95  thf('20', plain, ((v1_funct_1 @ sk_C)),
% 1.77/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.77/1.95  thf('21', plain,
% 1.77/1.95      (![X0 : $i]:
% 1.77/1.95         (~ (v1_funct_1 @ X0)
% 1.77/1.95          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 1.77/1.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.77/1.95          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 1.77/1.95          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.77/1.95               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 1.77/1.95               (k6_partfun1 @ sk_A)))),
% 1.77/1.95      inference('demod', [status(thm)], ['18', '19', '20'])).
% 1.77/1.95  thf('22', plain,
% 1.77/1.95      ((((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 1.77/1.95        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 1.77/1.95        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.77/1.95        | ~ (v1_funct_1 @ sk_D))),
% 1.77/1.95      inference('sup-', [status(thm)], ['15', '21'])).
% 1.77/1.95  thf('23', plain,
% 1.77/1.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.77/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.77/1.95  thf(redefinition_k2_relset_1, axiom,
% 1.77/1.95    (![A:$i,B:$i,C:$i]:
% 1.77/1.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.77/1.95       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 1.77/1.95  thf('24', plain,
% 1.77/1.95      (![X13 : $i, X14 : $i, X15 : $i]:
% 1.77/1.95         (((k2_relset_1 @ X14 @ X15 @ X13) = (k2_relat_1 @ X13))
% 1.77/1.95          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 1.77/1.95      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 1.77/1.95  thf('25', plain,
% 1.77/1.95      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 1.77/1.95      inference('sup-', [status(thm)], ['23', '24'])).
% 1.77/1.95  thf('26', plain,
% 1.77/1.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.77/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.77/1.95  thf('27', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.77/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.77/1.95  thf('28', plain, ((v1_funct_1 @ sk_D)),
% 1.77/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.77/1.95  thf('29', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.77/1.95      inference('demod', [status(thm)], ['22', '25', '26', '27', '28'])).
% 1.77/1.95  thf(d3_funct_2, axiom,
% 1.77/1.95    (![A:$i,B:$i]:
% 1.77/1.95     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 1.77/1.95       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 1.77/1.95  thf('30', plain,
% 1.77/1.95      (![X21 : $i, X22 : $i]:
% 1.77/1.95         (((k2_relat_1 @ X22) != (X21))
% 1.77/1.95          | (v2_funct_2 @ X22 @ X21)
% 1.77/1.95          | ~ (v5_relat_1 @ X22 @ X21)
% 1.77/1.95          | ~ (v1_relat_1 @ X22))),
% 1.77/1.95      inference('cnf', [status(esa)], [d3_funct_2])).
% 1.77/1.95  thf('31', plain,
% 1.77/1.95      (![X22 : $i]:
% 1.77/1.95         (~ (v1_relat_1 @ X22)
% 1.77/1.95          | ~ (v5_relat_1 @ X22 @ (k2_relat_1 @ X22))
% 1.77/1.95          | (v2_funct_2 @ X22 @ (k2_relat_1 @ X22)))),
% 1.77/1.95      inference('simplify', [status(thm)], ['30'])).
% 1.77/1.95  thf('32', plain,
% 1.77/1.95      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 1.77/1.95        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 1.77/1.95        | ~ (v1_relat_1 @ sk_D))),
% 1.77/1.95      inference('sup-', [status(thm)], ['29', '31'])).
% 1.77/1.95  thf('33', plain,
% 1.77/1.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.77/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.77/1.95  thf(cc2_relset_1, axiom,
% 1.77/1.95    (![A:$i,B:$i,C:$i]:
% 1.77/1.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.77/1.95       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 1.77/1.95  thf('34', plain,
% 1.77/1.95      (![X7 : $i, X8 : $i, X9 : $i]:
% 1.77/1.95         ((v5_relat_1 @ X7 @ X9)
% 1.77/1.95          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 1.77/1.95      inference('cnf', [status(esa)], [cc2_relset_1])).
% 1.77/1.95  thf('35', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 1.77/1.95      inference('sup-', [status(thm)], ['33', '34'])).
% 1.77/1.95  thf('36', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 1.77/1.95      inference('demod', [status(thm)], ['22', '25', '26', '27', '28'])).
% 1.77/1.95  thf('37', plain,
% 1.77/1.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.77/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.77/1.95  thf(cc1_relset_1, axiom,
% 1.77/1.95    (![A:$i,B:$i,C:$i]:
% 1.77/1.95     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.77/1.95       ( v1_relat_1 @ C ) ))).
% 1.77/1.95  thf('38', plain,
% 1.77/1.95      (![X4 : $i, X5 : $i, X6 : $i]:
% 1.77/1.95         ((v1_relat_1 @ X4)
% 1.77/1.95          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X5 @ X6))))),
% 1.77/1.95      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.77/1.95  thf('39', plain, ((v1_relat_1 @ sk_D)),
% 1.77/1.95      inference('sup-', [status(thm)], ['37', '38'])).
% 1.77/1.95  thf('40', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 1.77/1.95      inference('demod', [status(thm)], ['32', '35', '36', '39'])).
% 1.77/1.95  thf('41', plain,
% 1.77/1.95      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 1.77/1.95      inference('split', [status(esa)], ['12'])).
% 1.77/1.95  thf('42', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 1.77/1.95      inference('sup-', [status(thm)], ['40', '41'])).
% 1.77/1.95  thf('43', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 1.77/1.95      inference('split', [status(esa)], ['12'])).
% 1.77/1.95  thf('44', plain, (~ ((v2_funct_1 @ sk_C))),
% 1.77/1.95      inference('sat_resolution*', [status(thm)], ['42', '43'])).
% 1.77/1.95  thf('45', plain, (~ (v1_xboole_0 @ sk_C)),
% 1.77/1.95      inference('simpl_trail', [status(thm)], ['14', '44'])).
% 1.77/1.95  thf('46', plain,
% 1.77/1.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.77/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.77/1.95  thf('47', plain,
% 1.77/1.95      (![X10 : $i, X11 : $i, X12 : $i]:
% 1.77/1.95         (~ (v1_xboole_0 @ X10)
% 1.77/1.95          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X12)))
% 1.77/1.95          | (v1_xboole_0 @ X11))),
% 1.77/1.95      inference('cnf', [status(esa)], [cc3_relset_1])).
% 1.77/1.95  thf('48', plain, (((v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ sk_A))),
% 1.77/1.95      inference('sup-', [status(thm)], ['46', '47'])).
% 1.77/1.95  thf('49', plain,
% 1.77/1.95      ((r2_relset_1 @ sk_A @ sk_A @ 
% 1.77/1.95        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.77/1.95        (k6_partfun1 @ sk_A))),
% 1.77/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.77/1.95  thf('50', plain,
% 1.77/1.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.77/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.77/1.95  thf('51', plain,
% 1.77/1.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.77/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.77/1.95  thf(dt_k1_partfun1, axiom,
% 1.77/1.95    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.77/1.95     ( ( ( v1_funct_1 @ E ) & 
% 1.77/1.95         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.77/1.95         ( v1_funct_1 @ F ) & 
% 1.77/1.95         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 1.77/1.95       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.77/1.95         ( m1_subset_1 @
% 1.77/1.95           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.77/1.95           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 1.77/1.95  thf('52', plain,
% 1.77/1.95      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 1.77/1.95         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 1.77/1.95          | ~ (v1_funct_1 @ X23)
% 1.77/1.95          | ~ (v1_funct_1 @ X26)
% 1.77/1.95          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 1.77/1.95          | (m1_subset_1 @ (k1_partfun1 @ X24 @ X25 @ X27 @ X28 @ X23 @ X26) @ 
% 1.77/1.95             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X28))))),
% 1.77/1.95      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 1.77/1.95  thf('53', plain,
% 1.77/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.77/1.95         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.77/1.95           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.77/1.95          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.77/1.95          | ~ (v1_funct_1 @ X1)
% 1.77/1.95          | ~ (v1_funct_1 @ sk_C))),
% 1.77/1.95      inference('sup-', [status(thm)], ['51', '52'])).
% 1.77/1.95  thf('54', plain, ((v1_funct_1 @ sk_C)),
% 1.77/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.77/1.95  thf('55', plain,
% 1.77/1.95      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.77/1.95         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 1.77/1.95           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 1.77/1.95          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 1.77/1.95          | ~ (v1_funct_1 @ X1))),
% 1.77/1.95      inference('demod', [status(thm)], ['53', '54'])).
% 1.77/1.95  thf('56', plain,
% 1.77/1.95      ((~ (v1_funct_1 @ sk_D)
% 1.77/1.95        | (m1_subset_1 @ 
% 1.77/1.95           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.77/1.95           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.77/1.95      inference('sup-', [status(thm)], ['50', '55'])).
% 1.77/1.95  thf('57', plain, ((v1_funct_1 @ sk_D)),
% 1.77/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.77/1.95  thf('58', plain,
% 1.77/1.95      ((m1_subset_1 @ 
% 1.77/1.95        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 1.77/1.95        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 1.77/1.95      inference('demod', [status(thm)], ['56', '57'])).
% 1.77/1.95  thf(redefinition_r2_relset_1, axiom,
% 1.77/1.95    (![A:$i,B:$i,C:$i,D:$i]:
% 1.77/1.95     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 1.77/1.95         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.77/1.95       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 1.77/1.95  thf('59', plain,
% 1.77/1.95      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 1.77/1.95         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 1.77/1.95          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 1.77/1.95          | ((X16) = (X19))
% 1.77/1.95          | ~ (r2_relset_1 @ X17 @ X18 @ X16 @ X19))),
% 1.77/1.95      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 1.77/1.95  thf('60', plain,
% 1.77/1.95      (![X0 : $i]:
% 1.77/1.95         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 1.77/1.95             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 1.77/1.95          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 1.77/1.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 1.77/1.95      inference('sup-', [status(thm)], ['58', '59'])).
% 1.77/1.95  thf('61', plain,
% 1.77/1.95      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 1.77/1.95           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 1.77/1.95        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.77/1.95            = (k6_partfun1 @ sk_A)))),
% 1.77/1.95      inference('sup-', [status(thm)], ['49', '60'])).
% 1.77/1.95  thf('62', plain,
% 1.77/1.95      (![X20 : $i]:
% 1.77/1.95         (m1_subset_1 @ (k6_partfun1 @ X20) @ 
% 1.77/1.95          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X20)))),
% 1.77/1.95      inference('demod', [status(thm)], ['0', '1'])).
% 1.77/1.95  thf('63', plain,
% 1.77/1.95      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 1.77/1.95         = (k6_partfun1 @ sk_A))),
% 1.77/1.95      inference('demod', [status(thm)], ['61', '62'])).
% 1.77/1.95  thf('64', plain,
% 1.77/1.95      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 1.77/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.77/1.95  thf(t26_funct_2, axiom,
% 1.77/1.95    (![A:$i,B:$i,C:$i,D:$i]:
% 1.77/1.95     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 1.77/1.95         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.77/1.95       ( ![E:$i]:
% 1.77/1.95         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 1.77/1.95             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 1.77/1.95           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 1.77/1.95             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 1.77/1.95               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 1.77/1.95  thf('65', plain,
% 1.77/1.95      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 1.77/1.95         (~ (v1_funct_1 @ X34)
% 1.77/1.95          | ~ (v1_funct_2 @ X34 @ X35 @ X36)
% 1.77/1.95          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 1.77/1.95          | ~ (v2_funct_1 @ (k1_partfun1 @ X37 @ X35 @ X35 @ X36 @ X38 @ X34))
% 1.77/1.95          | (v2_funct_1 @ X38)
% 1.77/1.95          | ((X36) = (k1_xboole_0))
% 1.77/1.95          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X35)))
% 1.77/1.95          | ~ (v1_funct_2 @ X38 @ X37 @ X35)
% 1.77/1.95          | ~ (v1_funct_1 @ X38))),
% 1.77/1.95      inference('cnf', [status(esa)], [t26_funct_2])).
% 1.77/1.95  thf('66', plain,
% 1.77/1.95      (![X0 : $i, X1 : $i]:
% 1.77/1.95         (~ (v1_funct_1 @ X0)
% 1.77/1.95          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.77/1.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.77/1.95          | ((sk_A) = (k1_xboole_0))
% 1.77/1.95          | (v2_funct_1 @ X0)
% 1.77/1.95          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 1.77/1.95          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 1.77/1.95          | ~ (v1_funct_1 @ sk_D))),
% 1.77/1.95      inference('sup-', [status(thm)], ['64', '65'])).
% 1.77/1.95  thf('67', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 1.77/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.77/1.95  thf('68', plain, ((v1_funct_1 @ sk_D)),
% 1.77/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.77/1.95  thf('69', plain,
% 1.77/1.95      (![X0 : $i, X1 : $i]:
% 1.77/1.95         (~ (v1_funct_1 @ X0)
% 1.77/1.95          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.77/1.95          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.77/1.95          | ((sk_A) = (k1_xboole_0))
% 1.77/1.95          | (v2_funct_1 @ X0)
% 1.77/1.95          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 1.77/1.95      inference('demod', [status(thm)], ['66', '67', '68'])).
% 1.77/1.95  thf('70', plain,
% 1.77/1.95      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 1.77/1.95        | (v2_funct_1 @ sk_C)
% 1.77/1.95        | ((sk_A) = (k1_xboole_0))
% 1.77/1.95        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 1.77/1.95        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 1.77/1.95        | ~ (v1_funct_1 @ sk_C))),
% 1.77/1.95      inference('sup-', [status(thm)], ['63', '69'])).
% 1.77/1.95  thf('71', plain, (![X3 : $i]: (v2_funct_1 @ (k6_partfun1 @ X3))),
% 1.77/1.95      inference('demod', [status(thm)], ['7', '8'])).
% 1.77/1.95  thf('72', plain,
% 1.77/1.95      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 1.77/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.77/1.95  thf('73', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 1.77/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.77/1.95  thf('74', plain, ((v1_funct_1 @ sk_C)),
% 1.77/1.95      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.77/1.95  thf('75', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 1.77/1.95      inference('demod', [status(thm)], ['70', '71', '72', '73', '74'])).
% 1.77/1.95  thf('76', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 1.77/1.95      inference('split', [status(esa)], ['12'])).
% 1.77/1.95  thf('77', plain, (~ ((v2_funct_1 @ sk_C))),
% 1.77/1.95      inference('sat_resolution*', [status(thm)], ['42', '43'])).
% 1.77/1.95  thf('78', plain, (~ (v2_funct_1 @ sk_C)),
% 1.77/1.95      inference('simpl_trail', [status(thm)], ['76', '77'])).
% 1.77/1.95  thf('79', plain, (((sk_A) = (k1_xboole_0))),
% 1.77/1.95      inference('clc', [status(thm)], ['75', '78'])).
% 1.77/1.95  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 1.77/1.95  thf('80', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 1.77/1.95      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 1.77/1.95  thf('81', plain, ((v1_xboole_0 @ sk_C)),
% 1.77/1.95      inference('demod', [status(thm)], ['48', '79', '80'])).
% 1.77/1.95  thf('82', plain, ($false), inference('demod', [status(thm)], ['45', '81'])).
% 1.77/1.95  
% 1.77/1.95  % SZS output end Refutation
% 1.77/1.95  
% 1.77/1.96  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
