%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3XChP5f0Du

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:58:09 EST 2020

% Result     : Theorem 13.86s
% Output     : Refutation 13.86s
% Verified   : 
% Statistics : Number of formulae       :  222 ( 727 expanded)
%              Number of leaves         :   45 ( 240 expanded)
%              Depth                    :   17
%              Number of atoms          : 1862 (12588 expanded)
%              Number of equality atoms :   99 ( 261 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_funct_1_type,type,(
    k2_funct_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v3_funct_2_type,type,(
    v3_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_funct_2_type,type,(
    k2_funct_2: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('0',plain,(
    ! [X9: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(fc9_relat_1,axiom,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A ) )
     => ~ ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('1',plain,(
    ! [X7: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k6_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(dt_k6_relat_1,axiom,(
    ! [A: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X4: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[dt_k6_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

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

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('8',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('9',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('10',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('11',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 )
      | ( X17 != X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('12',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_relset_1 @ X1 @ X1 @ X0 @ ( k6_relat_1 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X1 @ X1 @ X2 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['6','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r2_relset_1 @ X1 @ X1 @ X2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf(t87_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ A @ A )
            & ( v3_funct_2 @ C @ A @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ ( k6_partfun1 @ A ) )
           => ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( v3_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ! [C: $i] :
            ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ A )
              & ( v3_funct_2 @ C @ A @ A )
              & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ( r2_relset_1 @ A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ ( k6_partfun1 @ A ) )
             => ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t87_funct_2])).

thf('17',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_2 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( v3_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k2_funct_2 @ A @ B )
        = ( k2_funct_1 @ B ) ) ) )).

thf('19',plain,(
    ! [X34: $i,X35: $i] :
      ( ( ( k2_funct_2 @ X35 @ X34 )
        = ( k2_funct_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) )
      | ~ ( v3_funct_2 @ X34 @ X35 @ X35 )
      | ~ ( v1_funct_2 @ X34 @ X35 @ X35 )
      | ~ ( v1_funct_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_funct_2])).

thf('20',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( ( k2_funct_2 @ sk_A @ sk_B )
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,
    ( ( k2_funct_2 @ sk_A @ sk_B )
    = ( k2_funct_1 @ sk_B ) ),
    inference(demod,[status(thm)],['20','21','22','23'])).

thf('25',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','24'])).

thf('26',plain,
    ( ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_B ) )
    | ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['16','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v3_funct_2 @ C @ A @ B ) )
       => ( ( v1_funct_1 @ C )
          & ( v2_funct_1 @ C )
          & ( v2_funct_2 @ C @ B ) ) ) ) )).

thf('28',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v3_funct_2 @ X21 @ X22 @ X23 )
      | ( v2_funct_2 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('29',plain,
    ( ( v2_funct_2 @ sk_C @ sk_A )
    | ~ ( v3_funct_2 @ sk_C @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    v3_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v2_funct_2 @ sk_C @ sk_A ),
    inference(demod,[status(thm)],['29','30','31'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('33',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v2_funct_2 @ X25 @ X24 )
      | ( ( k2_relat_1 @ X25 )
        = X24 )
      | ~ ( v5_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('34',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ~ ( v5_relat_1 @ sk_C @ sk_A )
    | ( ( k2_relat_1 @ sk_C )
      = sk_A ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('36',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('38',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('39',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('41',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('42',plain,(
    v5_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['34','39','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k6_relat_1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('46',plain,(
    ! [X9: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X9 ) )
      = X9 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_relat_1 @ X1 )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(condensation,[status(thm)],['51'])).

thf('53',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['43','52'])).

thf('54',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ ( k2_funct_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['26','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r2_relset_1 @ X1 @ X1 @ X2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('57',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X17 = X20 )
      | ~ ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ X0 )
      | ( sk_B = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_B @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B )
    | ( sk_B = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','66'])).

thf('68',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('69',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_B )
    | ( sk_B = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,
    ( ( sk_B = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v3_funct_2 @ X21 @ X22 @ X23 )
      | ( v2_funct_2 @ X21 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('73',plain,
    ( ( v2_funct_2 @ sk_B @ sk_A )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v2_funct_2 @ sk_B @ sk_A ),
    inference(demod,[status(thm)],['73','74','75'])).

thf('77',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v2_funct_2 @ X25 @ X24 )
      | ( ( k2_relat_1 @ X25 )
        = X24 )
      | ~ ( v5_relat_1 @ X25 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('78',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v5_relat_1 @ sk_B @ sk_A )
    | ( ( k2_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('81',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('83',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v5_relat_1 @ X11 @ X13 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('86',plain,(
    v5_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['78','83','86'])).

thf('88',plain,(
    ! [X7: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('89',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['81','82'])).

thf('91',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['70','91'])).

thf('93',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('95',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('98',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('99',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['99','100'])).

thf('102',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['96','101'])).

thf('103',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X17 = X20 )
      | ~ ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('106',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ~ ( m1_subset_1 @ ( k6_relat_1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
      = ( k6_relat_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['95','106'])).

thf('108',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('109',plain,
    ( ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C )
    = ( k6_relat_1 @ sk_A ) ),
    inference(demod,[status(thm)],['107','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t36_funct_2,axiom,(
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

thf('111',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( X41
        = ( k2_funct_1 @ X44 ) )
      | ~ ( r2_relset_1 @ X43 @ X43 @ ( k1_partfun1 @ X43 @ X42 @ X42 @ X43 @ X44 @ X41 ) @ ( k6_partfun1 @ X43 ) )
      | ( X42 = k1_xboole_0 )
      | ( X43 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X44 )
      | ( ( k2_relset_1 @ X43 @ X42 @ X44 )
       != X42 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X43 @ X42 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t36_funct_2])).

thf('112',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('113',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ( X41
        = ( k2_funct_1 @ X44 ) )
      | ~ ( r2_relset_1 @ X43 @ X43 @ ( k1_partfun1 @ X43 @ X42 @ X42 @ X43 @ X44 @ X41 ) @ ( k6_relat_1 @ X43 ) )
      | ( X42 = k1_xboole_0 )
      | ( X43 = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X44 )
      | ( ( k2_relset_1 @ X43 @ X42 @ X44 )
       != X42 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X43 @ X42 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['110','113'])).

thf('115',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( v2_funct_1 @ X0 )
      | ( sk_A = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_C
        = ( k2_funct_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( sk_C
        = ( k2_funct_1 @ X0 ) )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C ) @ ( k6_relat_1 @ sk_A ) )
      | ( sk_A = k1_xboole_0 )
      | ~ ( v2_funct_1 @ X0 )
      | ( ( k2_relset_1 @ sk_A @ sk_A @ X0 )
       != sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_relat_1 @ sk_A ) @ ( k6_relat_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
     != sk_A )
    | ~ ( v2_funct_1 @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['109','118'])).

thf('120',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('121',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('125',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k2_relset_1 @ X15 @ X16 @ X14 )
        = ( k2_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('126',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = ( k2_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['124','125'])).

thf('127',plain,
    ( ( k2_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['78','83','86'])).

thf('128',plain,
    ( ( k2_relset_1 @ sk_A @ sk_A @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['126','127'])).

thf('129',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v3_funct_2 @ X21 @ X22 @ X23 )
      | ( v2_funct_1 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_2])).

thf('131',plain,
    ( ( v2_funct_1 @ sk_B )
    | ~ ( v3_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v3_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v2_funct_1 @ sk_B ),
    inference(demod,[status(thm)],['131','132','133'])).

thf('135',plain,
    ( ( sk_A != sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_C
      = ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['119','120','121','122','123','128','134'])).

thf('136',plain,
    ( ( sk_C
      = ( k2_funct_1 @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ ( k2_funct_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['17','24'])).

thf('138',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_relset_1 @ X18 @ X19 @ X20 @ X20 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('141',plain,(
    r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['138','141'])).

thf('143',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('144',plain,(
    sk_B = k1_xboole_0 ),
    inference(demod,[status(thm)],['92','142','143'])).

thf('145',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('146',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( k1_xboole_0
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf(t67_funct_1,axiom,(
    ! [A: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ A ) )
      = ( k6_relat_1 @ A ) ) )).

thf('148',plain,(
    ! [X10: $i] :
      ( ( k2_funct_1 @ ( k6_relat_1 @ X10 ) )
      = ( k6_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_1])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ k1_xboole_0 )
        = ( k6_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( ( k2_funct_1 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['146','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_funct_1 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,
    ( ( k2_funct_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['145','151'])).

thf('153',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('154',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['54','144','152','153'])).

thf('155',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( r2_relset_1 @ X1 @ X1 @ X2 @ X0 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('156',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X0 ) ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('157',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( X17 = X20 )
      | ~ ( r2_relset_1 @ X18 @ X19 @ X17 @ X20 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ X0 )
      | ( sk_C = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( sk_C = k1_xboole_0 )
    | ~ ( r2_relset_1 @ sk_A @ sk_A @ sk_C @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['156','159'])).

thf('161',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C )
    | ( sk_C = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['155','160'])).

thf('162',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('163',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C )
    | ( sk_C = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['161','162'])).

thf('164',plain,
    ( ( sk_C = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_C )
    | ~ ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,
    ( ( k2_relat_1 @ sk_C )
    = sk_A ),
    inference(demod,[status(thm)],['34','39','42'])).

thf('166',plain,(
    ! [X7: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_relat_1 @ X7 ) )
      | ~ ( v1_relat_1 @ X7 )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc9_relat_1])).

thf('167',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('169',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['167','168'])).

thf('170',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( sk_C = k1_xboole_0 ) ),
    inference(clc,[status(thm)],['164','169'])).

thf('171',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['138','141'])).

thf('172',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('173',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('174',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('175',plain,(
    $false ),
    inference(demod,[status(thm)],['154','173','174'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3XChP5f0Du
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:11:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.35  % Python version: Python 3.6.8
% 0.15/0.35  % Running in FO mode
% 13.86/14.08  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 13.86/14.08  % Solved by: fo/fo7.sh
% 13.86/14.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 13.86/14.08  % done 7316 iterations in 13.613s
% 13.86/14.08  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 13.86/14.08  % SZS output start Refutation
% 13.86/14.08  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 13.86/14.08  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 13.86/14.08  thf(k2_funct_1_type, type, k2_funct_1: $i > $i).
% 13.86/14.08  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 13.86/14.08  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 13.86/14.08  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 13.86/14.08  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 13.86/14.08  thf(sk_A_type, type, sk_A: $i).
% 13.86/14.08  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 13.86/14.08  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 13.86/14.08  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 13.86/14.08  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 13.86/14.08  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 13.86/14.08  thf(v3_funct_2_type, type, v3_funct_2: $i > $i > $i > $o).
% 13.86/14.08  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 13.86/14.08  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 13.86/14.08  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 13.86/14.08  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 13.86/14.08  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 13.86/14.08  thf(sk_C_type, type, sk_C: $i).
% 13.86/14.08  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 13.86/14.08  thf(k2_funct_2_type, type, k2_funct_2: $i > $i > $i).
% 13.86/14.08  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 13.86/14.08  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 13.86/14.08  thf(sk_B_type, type, sk_B: $i).
% 13.86/14.08  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 13.86/14.08  thf(t71_relat_1, axiom,
% 13.86/14.08    (![A:$i]:
% 13.86/14.08     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 13.86/14.08       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 13.86/14.08  thf('0', plain, (![X9 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 13.86/14.08      inference('cnf', [status(esa)], [t71_relat_1])).
% 13.86/14.08  thf(fc9_relat_1, axiom,
% 13.86/14.08    (![A:$i]:
% 13.86/14.08     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ A ) ) =>
% 13.86/14.08       ( ~( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) ))).
% 13.86/14.08  thf('1', plain,
% 13.86/14.08      (![X7 : $i]:
% 13.86/14.08         (~ (v1_xboole_0 @ (k2_relat_1 @ X7))
% 13.86/14.08          | ~ (v1_relat_1 @ X7)
% 13.86/14.08          | (v1_xboole_0 @ X7))),
% 13.86/14.08      inference('cnf', [status(esa)], [fc9_relat_1])).
% 13.86/14.08  thf('2', plain,
% 13.86/14.08      (![X0 : $i]:
% 13.86/14.08         (~ (v1_xboole_0 @ X0)
% 13.86/14.08          | (v1_xboole_0 @ (k6_relat_1 @ X0))
% 13.86/14.08          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 13.86/14.08      inference('sup-', [status(thm)], ['0', '1'])).
% 13.86/14.08  thf(dt_k6_relat_1, axiom, (![A:$i]: ( v1_relat_1 @ ( k6_relat_1 @ A ) ))).
% 13.86/14.08  thf('3', plain, (![X4 : $i]: (v1_relat_1 @ (k6_relat_1 @ X4))),
% 13.86/14.08      inference('cnf', [status(esa)], [dt_k6_relat_1])).
% 13.86/14.08  thf('4', plain,
% 13.86/14.08      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k6_relat_1 @ X0)))),
% 13.86/14.08      inference('demod', [status(thm)], ['2', '3'])).
% 13.86/14.08  thf(t8_boole, axiom,
% 13.86/14.08    (![A:$i,B:$i]:
% 13.86/14.08     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 13.86/14.08  thf('5', plain,
% 13.86/14.08      (![X0 : $i, X1 : $i]:
% 13.86/14.08         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 13.86/14.08      inference('cnf', [status(esa)], [t8_boole])).
% 13.86/14.08  thf('6', plain,
% 13.86/14.08      (![X0 : $i, X1 : $i]:
% 13.86/14.08         (~ (v1_xboole_0 @ X0)
% 13.86/14.08          | ((k6_relat_1 @ X0) = (X1))
% 13.86/14.08          | ~ (v1_xboole_0 @ X1))),
% 13.86/14.08      inference('sup-', [status(thm)], ['4', '5'])).
% 13.86/14.08  thf('7', plain,
% 13.86/14.08      (![X0 : $i, X1 : $i]:
% 13.86/14.08         (~ (v1_xboole_0 @ X0)
% 13.86/14.08          | ((k6_relat_1 @ X0) = (X1))
% 13.86/14.08          | ~ (v1_xboole_0 @ X1))),
% 13.86/14.08      inference('sup-', [status(thm)], ['4', '5'])).
% 13.86/14.08  thf(dt_k6_partfun1, axiom,
% 13.86/14.08    (![A:$i]:
% 13.86/14.08     ( ( m1_subset_1 @
% 13.86/14.08         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 13.86/14.08       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 13.86/14.08  thf('8', plain,
% 13.86/14.08      (![X33 : $i]:
% 13.86/14.08         (m1_subset_1 @ (k6_partfun1 @ X33) @ 
% 13.86/14.08          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 13.86/14.08      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 13.86/14.08  thf(redefinition_k6_partfun1, axiom,
% 13.86/14.08    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 13.86/14.08  thf('9', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 13.86/14.08      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 13.86/14.08  thf('10', plain,
% 13.86/14.08      (![X33 : $i]:
% 13.86/14.08         (m1_subset_1 @ (k6_relat_1 @ X33) @ 
% 13.86/14.08          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 13.86/14.08      inference('demod', [status(thm)], ['8', '9'])).
% 13.86/14.08  thf(redefinition_r2_relset_1, axiom,
% 13.86/14.08    (![A:$i,B:$i,C:$i,D:$i]:
% 13.86/14.08     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 13.86/14.08         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 13.86/14.08       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 13.86/14.08  thf('11', plain,
% 13.86/14.08      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 13.86/14.08         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 13.86/14.08          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 13.86/14.08          | (r2_relset_1 @ X18 @ X19 @ X17 @ X20)
% 13.86/14.08          | ((X17) != (X20)))),
% 13.86/14.08      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 13.86/14.08  thf('12', plain,
% 13.86/14.08      (![X18 : $i, X19 : $i, X20 : $i]:
% 13.86/14.08         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 13.86/14.08          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 13.86/14.08      inference('simplify', [status(thm)], ['11'])).
% 13.86/14.08  thf('13', plain,
% 13.86/14.08      (![X0 : $i]:
% 13.86/14.08         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 13.86/14.08      inference('sup-', [status(thm)], ['10', '12'])).
% 13.86/14.08  thf('14', plain,
% 13.86/14.08      (![X0 : $i, X1 : $i]:
% 13.86/14.08         ((r2_relset_1 @ X1 @ X1 @ X0 @ (k6_relat_1 @ X1))
% 13.86/14.08          | ~ (v1_xboole_0 @ X0)
% 13.86/14.08          | ~ (v1_xboole_0 @ X1))),
% 13.86/14.08      inference('sup+', [status(thm)], ['7', '13'])).
% 13.86/14.08  thf('15', plain,
% 13.86/14.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.86/14.08         ((r2_relset_1 @ X1 @ X1 @ X2 @ X0)
% 13.86/14.08          | ~ (v1_xboole_0 @ X0)
% 13.86/14.08          | ~ (v1_xboole_0 @ X1)
% 13.86/14.08          | ~ (v1_xboole_0 @ X1)
% 13.86/14.08          | ~ (v1_xboole_0 @ X2))),
% 13.86/14.08      inference('sup+', [status(thm)], ['6', '14'])).
% 13.86/14.08  thf('16', plain,
% 13.86/14.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.86/14.08         (~ (v1_xboole_0 @ X2)
% 13.86/14.08          | ~ (v1_xboole_0 @ X1)
% 13.86/14.08          | ~ (v1_xboole_0 @ X0)
% 13.86/14.08          | (r2_relset_1 @ X1 @ X1 @ X2 @ X0))),
% 13.86/14.08      inference('simplify', [status(thm)], ['15'])).
% 13.86/14.08  thf(t87_funct_2, conjecture,
% 13.86/14.08    (![A:$i,B:$i]:
% 13.86/14.08     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 13.86/14.08         ( v3_funct_2 @ B @ A @ A ) & 
% 13.86/14.08         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 13.86/14.08       ( ![C:$i]:
% 13.86/14.08         ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 13.86/14.08             ( v3_funct_2 @ C @ A @ A ) & 
% 13.86/14.08             ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 13.86/14.08           ( ( r2_relset_1 @
% 13.86/14.08               A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 13.86/14.08               ( k6_partfun1 @ A ) ) =>
% 13.86/14.08             ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ))).
% 13.86/14.08  thf(zf_stmt_0, negated_conjecture,
% 13.86/14.08    (~( ![A:$i,B:$i]:
% 13.86/14.08        ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 13.86/14.08            ( v3_funct_2 @ B @ A @ A ) & 
% 13.86/14.08            ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 13.86/14.08          ( ![C:$i]:
% 13.86/14.08            ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ A ) & 
% 13.86/14.08                ( v3_funct_2 @ C @ A @ A ) & 
% 13.86/14.08                ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 13.86/14.08              ( ( r2_relset_1 @
% 13.86/14.08                  A @ A @ ( k1_partfun1 @ A @ A @ A @ A @ B @ C ) @ 
% 13.86/14.08                  ( k6_partfun1 @ A ) ) =>
% 13.86/14.08                ( r2_relset_1 @ A @ A @ C @ ( k2_funct_2 @ A @ B ) ) ) ) ) ) )),
% 13.86/14.08    inference('cnf.neg', [status(esa)], [t87_funct_2])).
% 13.86/14.08  thf('17', plain,
% 13.86/14.08      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_2 @ sk_A @ sk_B))),
% 13.86/14.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.86/14.08  thf('18', plain,
% 13.86/14.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.86/14.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.86/14.08  thf(redefinition_k2_funct_2, axiom,
% 13.86/14.08    (![A:$i,B:$i]:
% 13.86/14.08     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 13.86/14.08         ( v3_funct_2 @ B @ A @ A ) & 
% 13.86/14.08         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 13.86/14.08       ( ( k2_funct_2 @ A @ B ) = ( k2_funct_1 @ B ) ) ))).
% 13.86/14.08  thf('19', plain,
% 13.86/14.08      (![X34 : $i, X35 : $i]:
% 13.86/14.08         (((k2_funct_2 @ X35 @ X34) = (k2_funct_1 @ X34))
% 13.86/14.08          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))
% 13.86/14.08          | ~ (v3_funct_2 @ X34 @ X35 @ X35)
% 13.86/14.08          | ~ (v1_funct_2 @ X34 @ X35 @ X35)
% 13.86/14.08          | ~ (v1_funct_1 @ X34))),
% 13.86/14.08      inference('cnf', [status(esa)], [redefinition_k2_funct_2])).
% 13.86/14.08  thf('20', plain,
% 13.86/14.08      ((~ (v1_funct_1 @ sk_B)
% 13.86/14.08        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 13.86/14.08        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 13.86/14.08        | ((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B)))),
% 13.86/14.08      inference('sup-', [status(thm)], ['18', '19'])).
% 13.86/14.08  thf('21', plain, ((v1_funct_1 @ sk_B)),
% 13.86/14.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.86/14.08  thf('22', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 13.86/14.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.86/14.08  thf('23', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 13.86/14.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.86/14.08  thf('24', plain, (((k2_funct_2 @ sk_A @ sk_B) = (k2_funct_1 @ sk_B))),
% 13.86/14.08      inference('demod', [status(thm)], ['20', '21', '22', '23'])).
% 13.86/14.08  thf('25', plain,
% 13.86/14.08      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 13.86/14.08      inference('demod', [status(thm)], ['17', '24'])).
% 13.86/14.08  thf('26', plain,
% 13.86/14.08      ((~ (v1_xboole_0 @ (k2_funct_1 @ sk_B))
% 13.86/14.08        | ~ (v1_xboole_0 @ sk_A)
% 13.86/14.08        | ~ (v1_xboole_0 @ sk_C))),
% 13.86/14.08      inference('sup-', [status(thm)], ['16', '25'])).
% 13.86/14.08  thf('27', plain,
% 13.86/14.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.86/14.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.86/14.08  thf(cc2_funct_2, axiom,
% 13.86/14.08    (![A:$i,B:$i,C:$i]:
% 13.86/14.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 13.86/14.08       ( ( ( v1_funct_1 @ C ) & ( v3_funct_2 @ C @ A @ B ) ) =>
% 13.86/14.08         ( ( v1_funct_1 @ C ) & ( v2_funct_1 @ C ) & ( v2_funct_2 @ C @ B ) ) ) ))).
% 13.86/14.08  thf('28', plain,
% 13.86/14.08      (![X21 : $i, X22 : $i, X23 : $i]:
% 13.86/14.08         (~ (v1_funct_1 @ X21)
% 13.86/14.08          | ~ (v3_funct_2 @ X21 @ X22 @ X23)
% 13.86/14.08          | (v2_funct_2 @ X21 @ X23)
% 13.86/14.08          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 13.86/14.08      inference('cnf', [status(esa)], [cc2_funct_2])).
% 13.86/14.08  thf('29', plain,
% 13.86/14.08      (((v2_funct_2 @ sk_C @ sk_A)
% 13.86/14.08        | ~ (v3_funct_2 @ sk_C @ sk_A @ sk_A)
% 13.86/14.08        | ~ (v1_funct_1 @ sk_C))),
% 13.86/14.08      inference('sup-', [status(thm)], ['27', '28'])).
% 13.86/14.08  thf('30', plain, ((v3_funct_2 @ sk_C @ sk_A @ sk_A)),
% 13.86/14.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.86/14.08  thf('31', plain, ((v1_funct_1 @ sk_C)),
% 13.86/14.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.86/14.08  thf('32', plain, ((v2_funct_2 @ sk_C @ sk_A)),
% 13.86/14.08      inference('demod', [status(thm)], ['29', '30', '31'])).
% 13.86/14.08  thf(d3_funct_2, axiom,
% 13.86/14.08    (![A:$i,B:$i]:
% 13.86/14.08     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 13.86/14.08       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 13.86/14.08  thf('33', plain,
% 13.86/14.08      (![X24 : $i, X25 : $i]:
% 13.86/14.08         (~ (v2_funct_2 @ X25 @ X24)
% 13.86/14.08          | ((k2_relat_1 @ X25) = (X24))
% 13.86/14.08          | ~ (v5_relat_1 @ X25 @ X24)
% 13.86/14.08          | ~ (v1_relat_1 @ X25))),
% 13.86/14.08      inference('cnf', [status(esa)], [d3_funct_2])).
% 13.86/14.08  thf('34', plain,
% 13.86/14.08      ((~ (v1_relat_1 @ sk_C)
% 13.86/14.08        | ~ (v5_relat_1 @ sk_C @ sk_A)
% 13.86/14.08        | ((k2_relat_1 @ sk_C) = (sk_A)))),
% 13.86/14.08      inference('sup-', [status(thm)], ['32', '33'])).
% 13.86/14.08  thf('35', plain,
% 13.86/14.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.86/14.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.86/14.08  thf(cc2_relat_1, axiom,
% 13.86/14.08    (![A:$i]:
% 13.86/14.08     ( ( v1_relat_1 @ A ) =>
% 13.86/14.08       ( ![B:$i]:
% 13.86/14.08         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 13.86/14.08  thf('36', plain,
% 13.86/14.08      (![X2 : $i, X3 : $i]:
% 13.86/14.08         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 13.86/14.08          | (v1_relat_1 @ X2)
% 13.86/14.08          | ~ (v1_relat_1 @ X3))),
% 13.86/14.08      inference('cnf', [status(esa)], [cc2_relat_1])).
% 13.86/14.08  thf('37', plain,
% 13.86/14.08      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_C))),
% 13.86/14.08      inference('sup-', [status(thm)], ['35', '36'])).
% 13.86/14.08  thf(fc6_relat_1, axiom,
% 13.86/14.08    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 13.86/14.08  thf('38', plain,
% 13.86/14.08      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 13.86/14.08      inference('cnf', [status(esa)], [fc6_relat_1])).
% 13.86/14.08  thf('39', plain, ((v1_relat_1 @ sk_C)),
% 13.86/14.08      inference('demod', [status(thm)], ['37', '38'])).
% 13.86/14.08  thf('40', plain,
% 13.86/14.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.86/14.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.86/14.08  thf(cc2_relset_1, axiom,
% 13.86/14.08    (![A:$i,B:$i,C:$i]:
% 13.86/14.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 13.86/14.08       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 13.86/14.08  thf('41', plain,
% 13.86/14.08      (![X11 : $i, X12 : $i, X13 : $i]:
% 13.86/14.08         ((v5_relat_1 @ X11 @ X13)
% 13.86/14.08          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 13.86/14.08      inference('cnf', [status(esa)], [cc2_relset_1])).
% 13.86/14.08  thf('42', plain, ((v5_relat_1 @ sk_C @ sk_A)),
% 13.86/14.08      inference('sup-', [status(thm)], ['40', '41'])).
% 13.86/14.08  thf('43', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 13.86/14.08      inference('demod', [status(thm)], ['34', '39', '42'])).
% 13.86/14.08  thf('44', plain,
% 13.86/14.08      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k6_relat_1 @ X0)))),
% 13.86/14.08      inference('demod', [status(thm)], ['2', '3'])).
% 13.86/14.08  thf('45', plain,
% 13.86/14.08      (![X0 : $i, X1 : $i]:
% 13.86/14.08         (~ (v1_xboole_0 @ X0)
% 13.86/14.08          | ((k6_relat_1 @ X0) = (X1))
% 13.86/14.08          | ~ (v1_xboole_0 @ X1))),
% 13.86/14.08      inference('sup-', [status(thm)], ['4', '5'])).
% 13.86/14.08  thf('46', plain, (![X9 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X9)) = (X9))),
% 13.86/14.08      inference('cnf', [status(esa)], [t71_relat_1])).
% 13.86/14.08  thf('47', plain,
% 13.86/14.08      (![X0 : $i, X1 : $i]:
% 13.86/14.08         (((k2_relat_1 @ X0) = (X1))
% 13.86/14.08          | ~ (v1_xboole_0 @ X0)
% 13.86/14.08          | ~ (v1_xboole_0 @ X1))),
% 13.86/14.08      inference('sup+', [status(thm)], ['45', '46'])).
% 13.86/14.08  thf('48', plain,
% 13.86/14.08      (![X0 : $i, X1 : $i]:
% 13.86/14.08         (~ (v1_xboole_0 @ X0)
% 13.86/14.08          | ~ (v1_xboole_0 @ X1)
% 13.86/14.08          | ((k2_relat_1 @ X1) = (k6_relat_1 @ X0)))),
% 13.86/14.08      inference('sup-', [status(thm)], ['44', '47'])).
% 13.86/14.08  thf('49', plain,
% 13.86/14.08      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k6_relat_1 @ X0)))),
% 13.86/14.08      inference('demod', [status(thm)], ['2', '3'])).
% 13.86/14.08  thf('50', plain,
% 13.86/14.08      (![X0 : $i, X1 : $i]:
% 13.86/14.08         ((v1_xboole_0 @ (k2_relat_1 @ X0))
% 13.86/14.08          | ~ (v1_xboole_0 @ X0)
% 13.86/14.08          | ~ (v1_xboole_0 @ X1)
% 13.86/14.08          | ~ (v1_xboole_0 @ X1))),
% 13.86/14.08      inference('sup+', [status(thm)], ['48', '49'])).
% 13.86/14.08  thf('51', plain,
% 13.86/14.08      (![X0 : $i, X1 : $i]:
% 13.86/14.08         (~ (v1_xboole_0 @ X1)
% 13.86/14.08          | ~ (v1_xboole_0 @ X0)
% 13.86/14.08          | (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 13.86/14.08      inference('simplify', [status(thm)], ['50'])).
% 13.86/14.08  thf('52', plain,
% 13.86/14.08      (![X0 : $i]: ((v1_xboole_0 @ (k2_relat_1 @ X0)) | ~ (v1_xboole_0 @ X0))),
% 13.86/14.08      inference('condensation', [status(thm)], ['51'])).
% 13.86/14.08  thf('53', plain, (((v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ sk_C))),
% 13.86/14.08      inference('sup+', [status(thm)], ['43', '52'])).
% 13.86/14.08  thf('54', plain,
% 13.86/14.08      ((~ (v1_xboole_0 @ sk_C) | ~ (v1_xboole_0 @ (k2_funct_1 @ sk_B)))),
% 13.86/14.08      inference('clc', [status(thm)], ['26', '53'])).
% 13.86/14.08  thf('55', plain,
% 13.86/14.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.86/14.08         (~ (v1_xboole_0 @ X2)
% 13.86/14.08          | ~ (v1_xboole_0 @ X1)
% 13.86/14.08          | ~ (v1_xboole_0 @ X0)
% 13.86/14.08          | (r2_relset_1 @ X1 @ X1 @ X2 @ X0))),
% 13.86/14.08      inference('simplify', [status(thm)], ['15'])).
% 13.86/14.08  thf('56', plain,
% 13.86/14.08      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k6_relat_1 @ X0)))),
% 13.86/14.08      inference('demod', [status(thm)], ['2', '3'])).
% 13.86/14.08  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 13.86/14.08  thf('57', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 13.86/14.08      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 13.86/14.08  thf('58', plain,
% 13.86/14.08      (![X0 : $i, X1 : $i]:
% 13.86/14.08         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 13.86/14.08      inference('cnf', [status(esa)], [t8_boole])).
% 13.86/14.08  thf('59', plain,
% 13.86/14.08      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 13.86/14.08      inference('sup-', [status(thm)], ['57', '58'])).
% 13.86/14.08  thf('60', plain,
% 13.86/14.08      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (k6_relat_1 @ X0)))),
% 13.86/14.08      inference('sup-', [status(thm)], ['56', '59'])).
% 13.86/14.08  thf('61', plain,
% 13.86/14.08      (![X33 : $i]:
% 13.86/14.08         (m1_subset_1 @ (k6_relat_1 @ X33) @ 
% 13.86/14.08          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 13.86/14.08      inference('demod', [status(thm)], ['8', '9'])).
% 13.86/14.08  thf('62', plain,
% 13.86/14.08      (![X0 : $i]:
% 13.86/14.08         ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0)))
% 13.86/14.08          | ~ (v1_xboole_0 @ X0))),
% 13.86/14.08      inference('sup+', [status(thm)], ['60', '61'])).
% 13.86/14.08  thf('63', plain,
% 13.86/14.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.86/14.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.86/14.08  thf('64', plain,
% 13.86/14.08      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 13.86/14.08         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 13.86/14.08          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 13.86/14.08          | ((X17) = (X20))
% 13.86/14.08          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 13.86/14.08      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 13.86/14.08  thf('65', plain,
% 13.86/14.08      (![X0 : $i]:
% 13.86/14.08         (~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ X0)
% 13.86/14.08          | ((sk_B) = (X0))
% 13.86/14.08          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 13.86/14.08      inference('sup-', [status(thm)], ['63', '64'])).
% 13.86/14.08  thf('66', plain,
% 13.86/14.08      ((~ (v1_xboole_0 @ sk_A)
% 13.86/14.08        | ((sk_B) = (k1_xboole_0))
% 13.86/14.08        | ~ (r2_relset_1 @ sk_A @ sk_A @ sk_B @ k1_xboole_0))),
% 13.86/14.08      inference('sup-', [status(thm)], ['62', '65'])).
% 13.86/14.08  thf('67', plain,
% 13.86/14.08      ((~ (v1_xboole_0 @ k1_xboole_0)
% 13.86/14.08        | ~ (v1_xboole_0 @ sk_A)
% 13.86/14.08        | ~ (v1_xboole_0 @ sk_B)
% 13.86/14.08        | ((sk_B) = (k1_xboole_0))
% 13.86/14.08        | ~ (v1_xboole_0 @ sk_A))),
% 13.86/14.08      inference('sup-', [status(thm)], ['55', '66'])).
% 13.86/14.08  thf('68', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 13.86/14.08      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 13.86/14.08  thf('69', plain,
% 13.86/14.08      ((~ (v1_xboole_0 @ sk_A)
% 13.86/14.08        | ~ (v1_xboole_0 @ sk_B)
% 13.86/14.08        | ((sk_B) = (k1_xboole_0))
% 13.86/14.08        | ~ (v1_xboole_0 @ sk_A))),
% 13.86/14.08      inference('demod', [status(thm)], ['67', '68'])).
% 13.86/14.08  thf('70', plain,
% 13.86/14.08      ((((sk_B) = (k1_xboole_0))
% 13.86/14.08        | ~ (v1_xboole_0 @ sk_B)
% 13.86/14.08        | ~ (v1_xboole_0 @ sk_A))),
% 13.86/14.08      inference('simplify', [status(thm)], ['69'])).
% 13.86/14.08  thf('71', plain,
% 13.86/14.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.86/14.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.86/14.08  thf('72', plain,
% 13.86/14.08      (![X21 : $i, X22 : $i, X23 : $i]:
% 13.86/14.08         (~ (v1_funct_1 @ X21)
% 13.86/14.08          | ~ (v3_funct_2 @ X21 @ X22 @ X23)
% 13.86/14.08          | (v2_funct_2 @ X21 @ X23)
% 13.86/14.08          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 13.86/14.08      inference('cnf', [status(esa)], [cc2_funct_2])).
% 13.86/14.08  thf('73', plain,
% 13.86/14.08      (((v2_funct_2 @ sk_B @ sk_A)
% 13.86/14.08        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 13.86/14.08        | ~ (v1_funct_1 @ sk_B))),
% 13.86/14.08      inference('sup-', [status(thm)], ['71', '72'])).
% 13.86/14.08  thf('74', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 13.86/14.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.86/14.08  thf('75', plain, ((v1_funct_1 @ sk_B)),
% 13.86/14.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.86/14.08  thf('76', plain, ((v2_funct_2 @ sk_B @ sk_A)),
% 13.86/14.08      inference('demod', [status(thm)], ['73', '74', '75'])).
% 13.86/14.08  thf('77', plain,
% 13.86/14.08      (![X24 : $i, X25 : $i]:
% 13.86/14.08         (~ (v2_funct_2 @ X25 @ X24)
% 13.86/14.08          | ((k2_relat_1 @ X25) = (X24))
% 13.86/14.08          | ~ (v5_relat_1 @ X25 @ X24)
% 13.86/14.08          | ~ (v1_relat_1 @ X25))),
% 13.86/14.08      inference('cnf', [status(esa)], [d3_funct_2])).
% 13.86/14.08  thf('78', plain,
% 13.86/14.08      ((~ (v1_relat_1 @ sk_B)
% 13.86/14.08        | ~ (v5_relat_1 @ sk_B @ sk_A)
% 13.86/14.08        | ((k2_relat_1 @ sk_B) = (sk_A)))),
% 13.86/14.08      inference('sup-', [status(thm)], ['76', '77'])).
% 13.86/14.08  thf('79', plain,
% 13.86/14.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.86/14.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.86/14.08  thf('80', plain,
% 13.86/14.08      (![X2 : $i, X3 : $i]:
% 13.86/14.08         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 13.86/14.08          | (v1_relat_1 @ X2)
% 13.86/14.08          | ~ (v1_relat_1 @ X3))),
% 13.86/14.08      inference('cnf', [status(esa)], [cc2_relat_1])).
% 13.86/14.08  thf('81', plain,
% 13.86/14.08      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 13.86/14.08      inference('sup-', [status(thm)], ['79', '80'])).
% 13.86/14.08  thf('82', plain,
% 13.86/14.08      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 13.86/14.08      inference('cnf', [status(esa)], [fc6_relat_1])).
% 13.86/14.08  thf('83', plain, ((v1_relat_1 @ sk_B)),
% 13.86/14.08      inference('demod', [status(thm)], ['81', '82'])).
% 13.86/14.08  thf('84', plain,
% 13.86/14.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.86/14.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.86/14.08  thf('85', plain,
% 13.86/14.08      (![X11 : $i, X12 : $i, X13 : $i]:
% 13.86/14.08         ((v5_relat_1 @ X11 @ X13)
% 13.86/14.08          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 13.86/14.08      inference('cnf', [status(esa)], [cc2_relset_1])).
% 13.86/14.08  thf('86', plain, ((v5_relat_1 @ sk_B @ sk_A)),
% 13.86/14.08      inference('sup-', [status(thm)], ['84', '85'])).
% 13.86/14.08  thf('87', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 13.86/14.08      inference('demod', [status(thm)], ['78', '83', '86'])).
% 13.86/14.08  thf('88', plain,
% 13.86/14.08      (![X7 : $i]:
% 13.86/14.08         (~ (v1_xboole_0 @ (k2_relat_1 @ X7))
% 13.86/14.08          | ~ (v1_relat_1 @ X7)
% 13.86/14.08          | (v1_xboole_0 @ X7))),
% 13.86/14.08      inference('cnf', [status(esa)], [fc9_relat_1])).
% 13.86/14.08  thf('89', plain,
% 13.86/14.08      ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B) | ~ (v1_relat_1 @ sk_B))),
% 13.86/14.08      inference('sup-', [status(thm)], ['87', '88'])).
% 13.86/14.08  thf('90', plain, ((v1_relat_1 @ sk_B)),
% 13.86/14.08      inference('demod', [status(thm)], ['81', '82'])).
% 13.86/14.08  thf('91', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B))),
% 13.86/14.08      inference('demod', [status(thm)], ['89', '90'])).
% 13.86/14.08  thf('92', plain, ((~ (v1_xboole_0 @ sk_A) | ((sk_B) = (k1_xboole_0)))),
% 13.86/14.08      inference('clc', [status(thm)], ['70', '91'])).
% 13.86/14.08  thf('93', plain,
% 13.86/14.08      ((r2_relset_1 @ sk_A @ sk_A @ 
% 13.86/14.08        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 13.86/14.08        (k6_partfun1 @ sk_A))),
% 13.86/14.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.86/14.08  thf('94', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 13.86/14.08      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 13.86/14.08  thf('95', plain,
% 13.86/14.08      ((r2_relset_1 @ sk_A @ sk_A @ 
% 13.86/14.08        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 13.86/14.08        (k6_relat_1 @ sk_A))),
% 13.86/14.08      inference('demod', [status(thm)], ['93', '94'])).
% 13.86/14.08  thf('96', plain,
% 13.86/14.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.86/14.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.86/14.08  thf('97', plain,
% 13.86/14.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.86/14.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.86/14.08  thf(dt_k1_partfun1, axiom,
% 13.86/14.08    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 13.86/14.08     ( ( ( v1_funct_1 @ E ) & 
% 13.86/14.08         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 13.86/14.08         ( v1_funct_1 @ F ) & 
% 13.86/14.08         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 13.86/14.08       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 13.86/14.08         ( m1_subset_1 @
% 13.86/14.08           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 13.86/14.08           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 13.86/14.08  thf('98', plain,
% 13.86/14.08      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 13.86/14.08         (~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 13.86/14.08          | ~ (v1_funct_1 @ X26)
% 13.86/14.08          | ~ (v1_funct_1 @ X29)
% 13.86/14.08          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 13.86/14.08          | (m1_subset_1 @ (k1_partfun1 @ X27 @ X28 @ X30 @ X31 @ X26 @ X29) @ 
% 13.86/14.08             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X31))))),
% 13.86/14.08      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 13.86/14.08  thf('99', plain,
% 13.86/14.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.86/14.08         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 13.86/14.08           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 13.86/14.08          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 13.86/14.08          | ~ (v1_funct_1 @ X1)
% 13.86/14.08          | ~ (v1_funct_1 @ sk_B))),
% 13.86/14.08      inference('sup-', [status(thm)], ['97', '98'])).
% 13.86/14.08  thf('100', plain, ((v1_funct_1 @ sk_B)),
% 13.86/14.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.86/14.08  thf('101', plain,
% 13.86/14.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.86/14.08         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_A @ X2 @ X0 @ sk_B @ X1) @ 
% 13.86/14.08           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 13.86/14.08          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 13.86/14.08          | ~ (v1_funct_1 @ X1))),
% 13.86/14.08      inference('demod', [status(thm)], ['99', '100'])).
% 13.86/14.08  thf('102', plain,
% 13.86/14.08      ((~ (v1_funct_1 @ sk_C)
% 13.86/14.08        | (m1_subset_1 @ 
% 13.86/14.08           (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 13.86/14.08           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 13.86/14.08      inference('sup-', [status(thm)], ['96', '101'])).
% 13.86/14.08  thf('103', plain, ((v1_funct_1 @ sk_C)),
% 13.86/14.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.86/14.08  thf('104', plain,
% 13.86/14.08      ((m1_subset_1 @ 
% 13.86/14.08        (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ 
% 13.86/14.08        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.86/14.08      inference('demod', [status(thm)], ['102', '103'])).
% 13.86/14.08  thf('105', plain,
% 13.86/14.08      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 13.86/14.08         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 13.86/14.08          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 13.86/14.08          | ((X17) = (X20))
% 13.86/14.08          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 13.86/14.08      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 13.86/14.08  thf('106', plain,
% 13.86/14.08      (![X0 : $i]:
% 13.86/14.08         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 13.86/14.08             (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) @ X0)
% 13.86/14.08          | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C) = (X0))
% 13.86/14.08          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 13.86/14.08      inference('sup-', [status(thm)], ['104', '105'])).
% 13.86/14.08  thf('107', plain,
% 13.86/14.08      ((~ (m1_subset_1 @ (k6_relat_1 @ sk_A) @ 
% 13.86/14.08           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 13.86/14.08        | ((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 13.86/14.08            = (k6_relat_1 @ sk_A)))),
% 13.86/14.08      inference('sup-', [status(thm)], ['95', '106'])).
% 13.86/14.08  thf('108', plain,
% 13.86/14.08      (![X33 : $i]:
% 13.86/14.08         (m1_subset_1 @ (k6_relat_1 @ X33) @ 
% 13.86/14.08          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 13.86/14.08      inference('demod', [status(thm)], ['8', '9'])).
% 13.86/14.08  thf('109', plain,
% 13.86/14.08      (((k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ sk_B @ sk_C)
% 13.86/14.08         = (k6_relat_1 @ sk_A))),
% 13.86/14.08      inference('demod', [status(thm)], ['107', '108'])).
% 13.86/14.08  thf('110', plain,
% 13.86/14.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.86/14.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.86/14.08  thf(t36_funct_2, axiom,
% 13.86/14.08    (![A:$i,B:$i,C:$i]:
% 13.86/14.08     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 13.86/14.08         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 13.86/14.08       ( ![D:$i]:
% 13.86/14.08         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 13.86/14.08             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 13.86/14.08           ( ( ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) & 
% 13.86/14.08               ( r2_relset_1 @
% 13.86/14.08                 A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 13.86/14.08                 ( k6_partfun1 @ A ) ) & 
% 13.86/14.08               ( v2_funct_1 @ C ) ) =>
% 13.86/14.08             ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 13.86/14.08               ( ( D ) = ( k2_funct_1 @ C ) ) ) ) ) ) ))).
% 13.86/14.08  thf('111', plain,
% 13.86/14.08      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 13.86/14.08         (~ (v1_funct_1 @ X41)
% 13.86/14.08          | ~ (v1_funct_2 @ X41 @ X42 @ X43)
% 13.86/14.08          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 13.86/14.08          | ((X41) = (k2_funct_1 @ X44))
% 13.86/14.08          | ~ (r2_relset_1 @ X43 @ X43 @ 
% 13.86/14.08               (k1_partfun1 @ X43 @ X42 @ X42 @ X43 @ X44 @ X41) @ 
% 13.86/14.08               (k6_partfun1 @ X43))
% 13.86/14.08          | ((X42) = (k1_xboole_0))
% 13.86/14.08          | ((X43) = (k1_xboole_0))
% 13.86/14.08          | ~ (v2_funct_1 @ X44)
% 13.86/14.08          | ((k2_relset_1 @ X43 @ X42 @ X44) != (X42))
% 13.86/14.08          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))
% 13.86/14.08          | ~ (v1_funct_2 @ X44 @ X43 @ X42)
% 13.86/14.08          | ~ (v1_funct_1 @ X44))),
% 13.86/14.08      inference('cnf', [status(esa)], [t36_funct_2])).
% 13.86/14.08  thf('112', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 13.86/14.08      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 13.86/14.08  thf('113', plain,
% 13.86/14.08      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 13.86/14.08         (~ (v1_funct_1 @ X41)
% 13.86/14.08          | ~ (v1_funct_2 @ X41 @ X42 @ X43)
% 13.86/14.08          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 13.86/14.08          | ((X41) = (k2_funct_1 @ X44))
% 13.86/14.08          | ~ (r2_relset_1 @ X43 @ X43 @ 
% 13.86/14.08               (k1_partfun1 @ X43 @ X42 @ X42 @ X43 @ X44 @ X41) @ 
% 13.86/14.08               (k6_relat_1 @ X43))
% 13.86/14.08          | ((X42) = (k1_xboole_0))
% 13.86/14.08          | ((X43) = (k1_xboole_0))
% 13.86/14.08          | ~ (v2_funct_1 @ X44)
% 13.86/14.08          | ((k2_relset_1 @ X43 @ X42 @ X44) != (X42))
% 13.86/14.08          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))
% 13.86/14.08          | ~ (v1_funct_2 @ X44 @ X43 @ X42)
% 13.86/14.08          | ~ (v1_funct_1 @ X44))),
% 13.86/14.08      inference('demod', [status(thm)], ['111', '112'])).
% 13.86/14.08  thf('114', plain,
% 13.86/14.08      (![X0 : $i]:
% 13.86/14.08         (~ (v1_funct_1 @ X0)
% 13.86/14.08          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 13.86/14.08          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 13.86/14.08          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 13.86/14.08          | ~ (v2_funct_1 @ X0)
% 13.86/14.08          | ((sk_A) = (k1_xboole_0))
% 13.86/14.08          | ((sk_A) = (k1_xboole_0))
% 13.86/14.08          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 13.86/14.08               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 13.86/14.08               (k6_relat_1 @ sk_A))
% 13.86/14.08          | ((sk_C) = (k2_funct_1 @ X0))
% 13.86/14.08          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_A)
% 13.86/14.08          | ~ (v1_funct_1 @ sk_C))),
% 13.86/14.08      inference('sup-', [status(thm)], ['110', '113'])).
% 13.86/14.08  thf('115', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_A)),
% 13.86/14.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.86/14.08  thf('116', plain, ((v1_funct_1 @ sk_C)),
% 13.86/14.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.86/14.08  thf('117', plain,
% 13.86/14.08      (![X0 : $i]:
% 13.86/14.08         (~ (v1_funct_1 @ X0)
% 13.86/14.08          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 13.86/14.08          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 13.86/14.08          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 13.86/14.08          | ~ (v2_funct_1 @ X0)
% 13.86/14.08          | ((sk_A) = (k1_xboole_0))
% 13.86/14.08          | ((sk_A) = (k1_xboole_0))
% 13.86/14.08          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 13.86/14.08               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 13.86/14.08               (k6_relat_1 @ sk_A))
% 13.86/14.08          | ((sk_C) = (k2_funct_1 @ X0)))),
% 13.86/14.08      inference('demod', [status(thm)], ['114', '115', '116'])).
% 13.86/14.08  thf('118', plain,
% 13.86/14.08      (![X0 : $i]:
% 13.86/14.08         (((sk_C) = (k2_funct_1 @ X0))
% 13.86/14.08          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 13.86/14.08               (k1_partfun1 @ sk_A @ sk_A @ sk_A @ sk_A @ X0 @ sk_C) @ 
% 13.86/14.08               (k6_relat_1 @ sk_A))
% 13.86/14.08          | ((sk_A) = (k1_xboole_0))
% 13.86/14.08          | ~ (v2_funct_1 @ X0)
% 13.86/14.08          | ((k2_relset_1 @ sk_A @ sk_A @ X0) != (sk_A))
% 13.86/14.08          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 13.86/14.08          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 13.86/14.08          | ~ (v1_funct_1 @ X0))),
% 13.86/14.08      inference('simplify', [status(thm)], ['117'])).
% 13.86/14.08  thf('119', plain,
% 13.86/14.08      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_relat_1 @ sk_A) @ 
% 13.86/14.08           (k6_relat_1 @ sk_A))
% 13.86/14.08        | ~ (v1_funct_1 @ sk_B)
% 13.86/14.08        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 13.86/14.08        | ~ (m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 13.86/14.08        | ((k2_relset_1 @ sk_A @ sk_A @ sk_B) != (sk_A))
% 13.86/14.08        | ~ (v2_funct_1 @ sk_B)
% 13.86/14.08        | ((sk_A) = (k1_xboole_0))
% 13.86/14.08        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 13.86/14.08      inference('sup-', [status(thm)], ['109', '118'])).
% 13.86/14.08  thf('120', plain,
% 13.86/14.08      (![X0 : $i]:
% 13.86/14.08         (r2_relset_1 @ X0 @ X0 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X0))),
% 13.86/14.08      inference('sup-', [status(thm)], ['10', '12'])).
% 13.86/14.08  thf('121', plain, ((v1_funct_1 @ sk_B)),
% 13.86/14.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.86/14.08  thf('122', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 13.86/14.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.86/14.08  thf('123', plain,
% 13.86/14.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.86/14.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.86/14.08  thf('124', plain,
% 13.86/14.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.86/14.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.86/14.08  thf(redefinition_k2_relset_1, axiom,
% 13.86/14.08    (![A:$i,B:$i,C:$i]:
% 13.86/14.08     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 13.86/14.08       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 13.86/14.08  thf('125', plain,
% 13.86/14.08      (![X14 : $i, X15 : $i, X16 : $i]:
% 13.86/14.08         (((k2_relset_1 @ X15 @ X16 @ X14) = (k2_relat_1 @ X14))
% 13.86/14.08          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 13.86/14.08      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 13.86/14.08  thf('126', plain,
% 13.86/14.08      (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (k2_relat_1 @ sk_B))),
% 13.86/14.08      inference('sup-', [status(thm)], ['124', '125'])).
% 13.86/14.08  thf('127', plain, (((k2_relat_1 @ sk_B) = (sk_A))),
% 13.86/14.08      inference('demod', [status(thm)], ['78', '83', '86'])).
% 13.86/14.08  thf('128', plain, (((k2_relset_1 @ sk_A @ sk_A @ sk_B) = (sk_A))),
% 13.86/14.08      inference('demod', [status(thm)], ['126', '127'])).
% 13.86/14.08  thf('129', plain,
% 13.86/14.08      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.86/14.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.86/14.08  thf('130', plain,
% 13.86/14.08      (![X21 : $i, X22 : $i, X23 : $i]:
% 13.86/14.08         (~ (v1_funct_1 @ X21)
% 13.86/14.08          | ~ (v3_funct_2 @ X21 @ X22 @ X23)
% 13.86/14.08          | (v2_funct_1 @ X21)
% 13.86/14.08          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 13.86/14.08      inference('cnf', [status(esa)], [cc2_funct_2])).
% 13.86/14.08  thf('131', plain,
% 13.86/14.08      (((v2_funct_1 @ sk_B)
% 13.86/14.08        | ~ (v3_funct_2 @ sk_B @ sk_A @ sk_A)
% 13.86/14.08        | ~ (v1_funct_1 @ sk_B))),
% 13.86/14.08      inference('sup-', [status(thm)], ['129', '130'])).
% 13.86/14.08  thf('132', plain, ((v3_funct_2 @ sk_B @ sk_A @ sk_A)),
% 13.86/14.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.86/14.08  thf('133', plain, ((v1_funct_1 @ sk_B)),
% 13.86/14.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.86/14.08  thf('134', plain, ((v2_funct_1 @ sk_B)),
% 13.86/14.08      inference('demod', [status(thm)], ['131', '132', '133'])).
% 13.86/14.08  thf('135', plain,
% 13.86/14.08      ((((sk_A) != (sk_A))
% 13.86/14.08        | ((sk_A) = (k1_xboole_0))
% 13.86/14.08        | ((sk_C) = (k2_funct_1 @ sk_B)))),
% 13.86/14.08      inference('demod', [status(thm)],
% 13.86/14.08                ['119', '120', '121', '122', '123', '128', '134'])).
% 13.86/14.08  thf('136', plain,
% 13.86/14.08      ((((sk_C) = (k2_funct_1 @ sk_B)) | ((sk_A) = (k1_xboole_0)))),
% 13.86/14.08      inference('simplify', [status(thm)], ['135'])).
% 13.86/14.08  thf('137', plain,
% 13.86/14.08      (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ (k2_funct_1 @ sk_B))),
% 13.86/14.08      inference('demod', [status(thm)], ['17', '24'])).
% 13.86/14.08  thf('138', plain,
% 13.86/14.08      ((~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 13.86/14.08      inference('sup-', [status(thm)], ['136', '137'])).
% 13.86/14.08  thf('139', plain,
% 13.86/14.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.86/14.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.86/14.08  thf('140', plain,
% 13.86/14.08      (![X18 : $i, X19 : $i, X20 : $i]:
% 13.86/14.08         ((r2_relset_1 @ X18 @ X19 @ X20 @ X20)
% 13.86/14.08          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 13.86/14.08      inference('simplify', [status(thm)], ['11'])).
% 13.86/14.08  thf('141', plain, ((r2_relset_1 @ sk_A @ sk_A @ sk_C @ sk_C)),
% 13.86/14.08      inference('sup-', [status(thm)], ['139', '140'])).
% 13.86/14.08  thf('142', plain, (((sk_A) = (k1_xboole_0))),
% 13.86/14.08      inference('demod', [status(thm)], ['138', '141'])).
% 13.86/14.08  thf('143', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 13.86/14.08      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 13.86/14.08  thf('144', plain, (((sk_B) = (k1_xboole_0))),
% 13.86/14.08      inference('demod', [status(thm)], ['92', '142', '143'])).
% 13.86/14.08  thf('145', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 13.86/14.08      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 13.86/14.08  thf('146', plain,
% 13.86/14.08      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (k6_relat_1 @ X0)))),
% 13.86/14.08      inference('sup-', [status(thm)], ['56', '59'])).
% 13.86/14.08  thf('147', plain,
% 13.86/14.08      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k1_xboole_0) = (k6_relat_1 @ X0)))),
% 13.86/14.08      inference('sup-', [status(thm)], ['56', '59'])).
% 13.86/14.08  thf(t67_funct_1, axiom,
% 13.86/14.08    (![A:$i]: ( ( k2_funct_1 @ ( k6_relat_1 @ A ) ) = ( k6_relat_1 @ A ) ))).
% 13.86/14.08  thf('148', plain,
% 13.86/14.08      (![X10 : $i]: ((k2_funct_1 @ (k6_relat_1 @ X10)) = (k6_relat_1 @ X10))),
% 13.86/14.08      inference('cnf', [status(esa)], [t67_funct_1])).
% 13.86/14.08  thf('149', plain,
% 13.86/14.08      (![X0 : $i]:
% 13.86/14.08         (((k2_funct_1 @ k1_xboole_0) = (k6_relat_1 @ X0))
% 13.86/14.08          | ~ (v1_xboole_0 @ X0))),
% 13.86/14.08      inference('sup+', [status(thm)], ['147', '148'])).
% 13.86/14.08  thf('150', plain,
% 13.86/14.08      (![X0 : $i]:
% 13.86/14.08         (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))
% 13.86/14.08          | ~ (v1_xboole_0 @ X0)
% 13.86/14.08          | ~ (v1_xboole_0 @ X0))),
% 13.86/14.08      inference('sup+', [status(thm)], ['146', '149'])).
% 13.86/14.08  thf('151', plain,
% 13.86/14.08      (![X0 : $i]:
% 13.86/14.08         (~ (v1_xboole_0 @ X0) | ((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 13.86/14.08      inference('simplify', [status(thm)], ['150'])).
% 13.86/14.08  thf('152', plain, (((k2_funct_1 @ k1_xboole_0) = (k1_xboole_0))),
% 13.86/14.08      inference('sup-', [status(thm)], ['145', '151'])).
% 13.86/14.08  thf('153', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 13.86/14.08      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 13.86/14.08  thf('154', plain, (~ (v1_xboole_0 @ sk_C)),
% 13.86/14.08      inference('demod', [status(thm)], ['54', '144', '152', '153'])).
% 13.86/14.08  thf('155', plain,
% 13.86/14.08      (![X0 : $i, X1 : $i, X2 : $i]:
% 13.86/14.08         (~ (v1_xboole_0 @ X2)
% 13.86/14.08          | ~ (v1_xboole_0 @ X1)
% 13.86/14.08          | ~ (v1_xboole_0 @ X0)
% 13.86/14.08          | (r2_relset_1 @ X1 @ X1 @ X2 @ X0))),
% 13.86/14.08      inference('simplify', [status(thm)], ['15'])).
% 13.86/14.08  thf('156', plain,
% 13.86/14.08      (![X0 : $i]:
% 13.86/14.08         ((m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X0)))
% 13.86/14.08          | ~ (v1_xboole_0 @ X0))),
% 13.86/14.08      inference('sup+', [status(thm)], ['60', '61'])).
% 13.86/14.08  thf('157', plain,
% 13.86/14.08      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 13.86/14.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 13.86/14.08  thf('158', plain,
% 13.86/14.08      (![X17 : $i, X18 : $i, X19 : $i, X20 : $i]:
% 13.86/14.08         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 13.86/14.08          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 13.86/14.08          | ((X17) = (X20))
% 13.86/14.08          | ~ (r2_relset_1 @ X18 @ X19 @ X17 @ X20))),
% 13.86/14.08      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 13.86/14.08  thf('159', plain,
% 13.86/14.08      (![X0 : $i]:
% 13.86/14.08         (~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ X0)
% 13.86/14.08          | ((sk_C) = (X0))
% 13.86/14.08          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 13.86/14.08      inference('sup-', [status(thm)], ['157', '158'])).
% 13.86/14.08  thf('160', plain,
% 13.86/14.08      ((~ (v1_xboole_0 @ sk_A)
% 13.86/14.08        | ((sk_C) = (k1_xboole_0))
% 13.86/14.08        | ~ (r2_relset_1 @ sk_A @ sk_A @ sk_C @ k1_xboole_0))),
% 13.86/14.08      inference('sup-', [status(thm)], ['156', '159'])).
% 13.86/14.08  thf('161', plain,
% 13.86/14.08      ((~ (v1_xboole_0 @ k1_xboole_0)
% 13.86/14.08        | ~ (v1_xboole_0 @ sk_A)
% 13.86/14.08        | ~ (v1_xboole_0 @ sk_C)
% 13.86/14.08        | ((sk_C) = (k1_xboole_0))
% 13.86/14.08        | ~ (v1_xboole_0 @ sk_A))),
% 13.86/14.08      inference('sup-', [status(thm)], ['155', '160'])).
% 13.86/14.08  thf('162', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 13.86/14.08      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 13.86/14.08  thf('163', plain,
% 13.86/14.08      ((~ (v1_xboole_0 @ sk_A)
% 13.86/14.08        | ~ (v1_xboole_0 @ sk_C)
% 13.86/14.08        | ((sk_C) = (k1_xboole_0))
% 13.86/14.08        | ~ (v1_xboole_0 @ sk_A))),
% 13.86/14.08      inference('demod', [status(thm)], ['161', '162'])).
% 13.86/14.08  thf('164', plain,
% 13.86/14.08      ((((sk_C) = (k1_xboole_0))
% 13.86/14.08        | ~ (v1_xboole_0 @ sk_C)
% 13.86/14.08        | ~ (v1_xboole_0 @ sk_A))),
% 13.86/14.08      inference('simplify', [status(thm)], ['163'])).
% 13.86/14.08  thf('165', plain, (((k2_relat_1 @ sk_C) = (sk_A))),
% 13.86/14.08      inference('demod', [status(thm)], ['34', '39', '42'])).
% 13.86/14.08  thf('166', plain,
% 13.86/14.08      (![X7 : $i]:
% 13.86/14.08         (~ (v1_xboole_0 @ (k2_relat_1 @ X7))
% 13.86/14.08          | ~ (v1_relat_1 @ X7)
% 13.86/14.08          | (v1_xboole_0 @ X7))),
% 13.86/14.08      inference('cnf', [status(esa)], [fc9_relat_1])).
% 13.86/14.08  thf('167', plain,
% 13.86/14.08      ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C) | ~ (v1_relat_1 @ sk_C))),
% 13.86/14.08      inference('sup-', [status(thm)], ['165', '166'])).
% 13.86/14.08  thf('168', plain, ((v1_relat_1 @ sk_C)),
% 13.86/14.08      inference('demod', [status(thm)], ['37', '38'])).
% 13.86/14.08  thf('169', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C))),
% 13.86/14.08      inference('demod', [status(thm)], ['167', '168'])).
% 13.86/14.08  thf('170', plain, ((~ (v1_xboole_0 @ sk_A) | ((sk_C) = (k1_xboole_0)))),
% 13.86/14.08      inference('clc', [status(thm)], ['164', '169'])).
% 13.86/14.08  thf('171', plain, (((sk_A) = (k1_xboole_0))),
% 13.86/14.08      inference('demod', [status(thm)], ['138', '141'])).
% 13.86/14.08  thf('172', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 13.86/14.08      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 13.86/14.08  thf('173', plain, (((sk_C) = (k1_xboole_0))),
% 13.86/14.08      inference('demod', [status(thm)], ['170', '171', '172'])).
% 13.86/14.08  thf('174', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 13.86/14.08      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 13.86/14.08  thf('175', plain, ($false),
% 13.86/14.08      inference('demod', [status(thm)], ['154', '173', '174'])).
% 13.86/14.08  
% 13.86/14.08  % SZS output end Refutation
% 13.86/14.08  
% 13.86/14.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
