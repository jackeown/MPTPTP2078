%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mes88p9mnu

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:01 EST 2020

% Result     : Theorem 0.60s
% Output     : Refutation 0.60s
% Verified   : 
% Statistics : Number of formulae       :  126 ( 450 expanded)
%              Number of leaves         :   40 ( 147 expanded)
%              Depth                    :   20
%              Number of atoms          : 1105 (9072 expanded)
%              Number of equality atoms :   30 ( 101 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

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
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
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

thf('5',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['3','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('12',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( X18 = X21 )
      | ~ ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','13'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('15',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('16',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('17',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
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

thf('20',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( r2_relset_1 @ X33 @ X33 @ ( k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35 ) @ ( k6_partfun1 @ X33 ) )
      | ( ( k2_relset_1 @ X34 @ X33 @ X35 )
        = X33 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X34 @ X33 )
      | ~ ( v1_funct_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('21',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k6_partfun1 @ sk_A ) @ ( k6_partfun1 @ sk_A ) )
    | ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['18','24'])).

thf('26',plain,(
    ! [X22: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('27',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( r2_relset_1 @ X19 @ X20 @ X18 @ X21 )
      | ( X18 != X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('28',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_relset_1 @ X19 @ X20 @ X21 @ X21 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( r2_relset_1 @ X0 @ X0 @ ( k6_partfun1 @ X0 ) @ ( k6_partfun1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['26','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('31',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k2_relset_1 @ X16 @ X17 @ X15 )
        = ( k2_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('32',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['25','29','32','33','34','35'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('37',plain,(
    ! [X23: $i,X24: $i] :
      ( ( ( k2_relat_1 @ X24 )
       != X23 )
      | ( v2_funct_2 @ X24 @ X23 )
      | ~ ( v5_relat_1 @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('38',plain,(
    ! [X24: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ~ ( v5_relat_1 @ X24 @ ( k2_relat_1 @ X24 ) )
      | ( v2_funct_2 @ X24 @ ( k2_relat_1 @ X24 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['36','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('41',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ( v5_relat_1 @ X12 @ X14 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('42',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['25','29','32','33','34','35'])).

thf('44',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('45',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( v1_relat_1 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('46',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['39','42','43','46'])).

thf('48',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('49',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['0'])).

thf('51',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','51'])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('54',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('55',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_xboole_0 @ X2 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('56',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('59',plain,(
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

thf('60',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X39 @ X37 @ X37 @ X38 @ X40 @ X36 ) )
      | ( v2_funct_1 @ X40 )
      | ( X38 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X39 @ X37 )
      | ~ ( v1_funct_1 @ X40 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['61','62','63'])).

thf('65',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['58','64'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('66',plain,(
    ! [X8: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('67',plain,(
    ! [X31: $i] :
      ( ( k6_partfun1 @ X31 )
      = ( k6_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('68',plain,(
    ! [X8: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X8 ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['65','68','69','70','71'])).

thf('73',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['1','51'])).

thf('74',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['72','73'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('75',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('76',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['57','74','75'])).

thf(cc1_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_funct_1 @ A ) ) )).

thf('77',plain,(
    ! [X5: $i] :
      ( ( v1_funct_1 @ X5 )
      | ~ ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_1])).

thf(cc2_funct_1,axiom,(
    ! [A: $i] :
      ( ( ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A )
        & ( v2_funct_1 @ A ) ) ) )).

thf('78',plain,(
    ! [X6: $i] :
      ( ( v2_funct_1 @ X6 )
      | ~ ( v1_funct_1 @ X6 )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( v1_xboole_0 @ X6 ) ) ),
    inference(cnf,[status(esa)],[cc2_funct_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v2_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['79'])).

thf(cc1_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_relat_1 @ A ) ) )).

thf('81',plain,(
    ! [X4: $i] :
      ( ( v1_relat_1 @ X4 )
      | ~ ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc1_relat_1])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v2_funct_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['80','81'])).

thf('83',plain,(
    v2_funct_1 @ sk_C ),
    inference('sup-',[status(thm)],['76','82'])).

thf('84',plain,(
    $false ),
    inference(demod,[status(thm)],['52','83'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.mes88p9mnu
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:12:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.60/0.84  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.60/0.84  % Solved by: fo/fo7.sh
% 0.60/0.84  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.60/0.84  % done 438 iterations in 0.381s
% 0.60/0.84  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.60/0.84  % SZS output start Refutation
% 0.60/0.84  thf(sk_B_type, type, sk_B: $i).
% 0.60/0.84  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.60/0.84  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.60/0.84  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.60/0.84  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.60/0.84  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.60/0.84  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.60/0.84  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 0.60/0.84  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.60/0.84  thf(sk_A_type, type, sk_A: $i).
% 0.60/0.84  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.60/0.84  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.60/0.84  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.60/0.84  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 0.60/0.84  thf(sk_C_type, type, sk_C: $i).
% 0.60/0.84  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.60/0.84  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.60/0.84  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.60/0.84  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 0.60/0.84  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.60/0.84  thf(sk_D_type, type, sk_D: $i).
% 0.60/0.84  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.60/0.84  thf(t29_funct_2, conjecture,
% 0.60/0.84    (![A:$i,B:$i,C:$i]:
% 0.60/0.84     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.60/0.84         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.60/0.84       ( ![D:$i]:
% 0.60/0.84         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.60/0.84             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.60/0.84           ( ( r2_relset_1 @
% 0.60/0.84               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.60/0.84               ( k6_partfun1 @ A ) ) =>
% 0.60/0.84             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 0.60/0.84  thf(zf_stmt_0, negated_conjecture,
% 0.60/0.84    (~( ![A:$i,B:$i,C:$i]:
% 0.60/0.84        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.60/0.84            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.60/0.84          ( ![D:$i]:
% 0.60/0.84            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.60/0.84                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.60/0.84              ( ( r2_relset_1 @
% 0.60/0.84                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 0.60/0.84                  ( k6_partfun1 @ A ) ) =>
% 0.60/0.84                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 0.60/0.84    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 0.60/0.84  thf('0', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('1', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 0.60/0.84      inference('split', [status(esa)], ['0'])).
% 0.60/0.84  thf('2', plain,
% 0.60/0.84      ((r2_relset_1 @ sk_A @ sk_A @ 
% 0.60/0.84        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.60/0.84        (k6_partfun1 @ sk_A))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('3', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('4', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(dt_k1_partfun1, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.60/0.84     ( ( ( v1_funct_1 @ E ) & 
% 0.60/0.84         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.60/0.84         ( v1_funct_1 @ F ) & 
% 0.60/0.84         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.60/0.84       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.60/0.84         ( m1_subset_1 @
% 0.60/0.84           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.60/0.84           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 0.60/0.84  thf('5', plain,
% 0.60/0.84      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.60/0.84         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.60/0.84          | ~ (v1_funct_1 @ X25)
% 0.60/0.84          | ~ (v1_funct_1 @ X28)
% 0.60/0.84          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.60/0.84          | (m1_subset_1 @ (k1_partfun1 @ X26 @ X27 @ X29 @ X30 @ X25 @ X28) @ 
% 0.60/0.84             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X30))))),
% 0.60/0.84      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 0.60/0.84  thf('6', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.84         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.60/0.84           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.60/0.84          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.60/0.84          | ~ (v1_funct_1 @ X1)
% 0.60/0.84          | ~ (v1_funct_1 @ sk_C))),
% 0.60/0.84      inference('sup-', [status(thm)], ['4', '5'])).
% 0.60/0.84  thf('7', plain, ((v1_funct_1 @ sk_C)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('8', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.60/0.84         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B @ X2 @ X0 @ sk_C @ X1) @ 
% 0.60/0.84           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.60/0.84          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 0.60/0.84          | ~ (v1_funct_1 @ X1))),
% 0.60/0.84      inference('demod', [status(thm)], ['6', '7'])).
% 0.60/0.84  thf('9', plain,
% 0.60/0.84      ((~ (v1_funct_1 @ sk_D)
% 0.60/0.84        | (m1_subset_1 @ 
% 0.60/0.84           (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.60/0.84           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.60/0.84      inference('sup-', [status(thm)], ['3', '8'])).
% 0.60/0.84  thf('10', plain, ((v1_funct_1 @ sk_D)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('11', plain,
% 0.60/0.84      ((m1_subset_1 @ 
% 0.60/0.84        (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ 
% 0.60/0.84        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.60/0.84      inference('demod', [status(thm)], ['9', '10'])).
% 0.60/0.84  thf(redefinition_r2_relset_1, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.84     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.60/0.84         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.60/0.84       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.60/0.84  thf('12', plain,
% 0.60/0.84      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.60/0.84         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.60/0.84          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.60/0.84          | ((X18) = (X21))
% 0.60/0.84          | ~ (r2_relset_1 @ X19 @ X20 @ X18 @ X21))),
% 0.60/0.84      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.60/0.84  thf('13', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.60/0.84             (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) @ X0)
% 0.60/0.84          | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D) = (X0))
% 0.60/0.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.60/0.84      inference('sup-', [status(thm)], ['11', '12'])).
% 0.60/0.84  thf('14', plain,
% 0.60/0.84      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 0.60/0.84           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.60/0.84        | ((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.60/0.84            = (k6_partfun1 @ sk_A)))),
% 0.60/0.84      inference('sup-', [status(thm)], ['2', '13'])).
% 0.60/0.84  thf(t29_relset_1, axiom,
% 0.60/0.84    (![A:$i]:
% 0.60/0.84     ( m1_subset_1 @
% 0.60/0.84       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.60/0.84  thf('15', plain,
% 0.60/0.84      (![X22 : $i]:
% 0.60/0.84         (m1_subset_1 @ (k6_relat_1 @ X22) @ 
% 0.60/0.84          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 0.60/0.84      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.60/0.84  thf(redefinition_k6_partfun1, axiom,
% 0.60/0.84    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.60/0.84  thf('16', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.60/0.84      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.60/0.84  thf('17', plain,
% 0.60/0.84      (![X22 : $i]:
% 0.60/0.84         (m1_subset_1 @ (k6_partfun1 @ X22) @ 
% 0.60/0.84          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 0.60/0.84      inference('demod', [status(thm)], ['15', '16'])).
% 0.60/0.84  thf('18', plain,
% 0.60/0.84      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.60/0.84         = (k6_partfun1 @ sk_A))),
% 0.60/0.84      inference('demod', [status(thm)], ['14', '17'])).
% 0.60/0.84  thf('19', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(t24_funct_2, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i]:
% 0.60/0.84     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.60/0.84         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.60/0.84       ( ![D:$i]:
% 0.60/0.84         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.60/0.84             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.60/0.84           ( ( r2_relset_1 @
% 0.60/0.84               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 0.60/0.84               ( k6_partfun1 @ B ) ) =>
% 0.60/0.84             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 0.60/0.84  thf('20', plain,
% 0.60/0.84      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.60/0.84         (~ (v1_funct_1 @ X32)
% 0.60/0.84          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 0.60/0.84          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.60/0.84          | ~ (r2_relset_1 @ X33 @ X33 @ 
% 0.60/0.84               (k1_partfun1 @ X33 @ X34 @ X34 @ X33 @ X32 @ X35) @ 
% 0.60/0.84               (k6_partfun1 @ X33))
% 0.60/0.84          | ((k2_relset_1 @ X34 @ X33 @ X35) = (X33))
% 0.60/0.84          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.60/0.84          | ~ (v1_funct_2 @ X35 @ X34 @ X33)
% 0.60/0.84          | ~ (v1_funct_1 @ X35))),
% 0.60/0.84      inference('cnf', [status(esa)], [t24_funct_2])).
% 0.60/0.84  thf('21', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         (~ (v1_funct_1 @ X0)
% 0.60/0.84          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.60/0.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.60/0.84          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.60/0.84          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.60/0.84               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.60/0.84               (k6_partfun1 @ sk_A))
% 0.60/0.84          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.60/0.84          | ~ (v1_funct_1 @ sk_C))),
% 0.60/0.84      inference('sup-', [status(thm)], ['19', '20'])).
% 0.60/0.84  thf('22', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('23', plain, ((v1_funct_1 @ sk_C)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('24', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         (~ (v1_funct_1 @ X0)
% 0.60/0.84          | ~ (v1_funct_2 @ X0 @ sk_B @ sk_A)
% 0.60/0.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.60/0.84          | ((k2_relset_1 @ sk_B @ sk_A @ X0) = (sk_A))
% 0.60/0.84          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 0.60/0.84               (k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ X0) @ 
% 0.60/0.84               (k6_partfun1 @ sk_A)))),
% 0.60/0.84      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.60/0.84  thf('25', plain,
% 0.60/0.84      ((~ (r2_relset_1 @ sk_A @ sk_A @ (k6_partfun1 @ sk_A) @ 
% 0.60/0.84           (k6_partfun1 @ sk_A))
% 0.60/0.84        | ((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (sk_A))
% 0.60/0.84        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))
% 0.60/0.84        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.60/0.84        | ~ (v1_funct_1 @ sk_D))),
% 0.60/0.84      inference('sup-', [status(thm)], ['18', '24'])).
% 0.60/0.84  thf('26', plain,
% 0.60/0.84      (![X22 : $i]:
% 0.60/0.84         (m1_subset_1 @ (k6_partfun1 @ X22) @ 
% 0.60/0.84          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X22)))),
% 0.60/0.84      inference('demod', [status(thm)], ['15', '16'])).
% 0.60/0.84  thf('27', plain,
% 0.60/0.84      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.60/0.84         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.60/0.84          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.60/0.84          | (r2_relset_1 @ X19 @ X20 @ X18 @ X21)
% 0.60/0.84          | ((X18) != (X21)))),
% 0.60/0.84      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.60/0.84  thf('28', plain,
% 0.60/0.84      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.60/0.84         ((r2_relset_1 @ X19 @ X20 @ X21 @ X21)
% 0.60/0.84          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.60/0.84      inference('simplify', [status(thm)], ['27'])).
% 0.60/0.84  thf('29', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         (r2_relset_1 @ X0 @ X0 @ (k6_partfun1 @ X0) @ (k6_partfun1 @ X0))),
% 0.60/0.84      inference('sup-', [status(thm)], ['26', '28'])).
% 0.60/0.84  thf('30', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(redefinition_k2_relset_1, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i]:
% 0.60/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.84       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.60/0.84  thf('31', plain,
% 0.60/0.84      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.60/0.84         (((k2_relset_1 @ X16 @ X17 @ X15) = (k2_relat_1 @ X15))
% 0.60/0.84          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.60/0.84      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.60/0.84  thf('32', plain,
% 0.60/0.84      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.60/0.84      inference('sup-', [status(thm)], ['30', '31'])).
% 0.60/0.84  thf('33', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('34', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('35', plain, ((v1_funct_1 @ sk_D)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('36', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.60/0.84      inference('demod', [status(thm)], ['25', '29', '32', '33', '34', '35'])).
% 0.60/0.84  thf(d3_funct_2, axiom,
% 0.60/0.84    (![A:$i,B:$i]:
% 0.60/0.84     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 0.60/0.84       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 0.60/0.84  thf('37', plain,
% 0.60/0.84      (![X23 : $i, X24 : $i]:
% 0.60/0.84         (((k2_relat_1 @ X24) != (X23))
% 0.60/0.84          | (v2_funct_2 @ X24 @ X23)
% 0.60/0.84          | ~ (v5_relat_1 @ X24 @ X23)
% 0.60/0.84          | ~ (v1_relat_1 @ X24))),
% 0.60/0.84      inference('cnf', [status(esa)], [d3_funct_2])).
% 0.60/0.84  thf('38', plain,
% 0.60/0.84      (![X24 : $i]:
% 0.60/0.84         (~ (v1_relat_1 @ X24)
% 0.60/0.84          | ~ (v5_relat_1 @ X24 @ (k2_relat_1 @ X24))
% 0.60/0.84          | (v2_funct_2 @ X24 @ (k2_relat_1 @ X24)))),
% 0.60/0.84      inference('simplify', [status(thm)], ['37'])).
% 0.60/0.84  thf('39', plain,
% 0.60/0.84      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 0.60/0.84        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 0.60/0.84        | ~ (v1_relat_1 @ sk_D))),
% 0.60/0.84      inference('sup-', [status(thm)], ['36', '38'])).
% 0.60/0.84  thf('40', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(cc2_relset_1, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i]:
% 0.60/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.84       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.60/0.84  thf('41', plain,
% 0.60/0.84      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.60/0.84         ((v5_relat_1 @ X12 @ X14)
% 0.60/0.84          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X14))))),
% 0.60/0.84      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.60/0.84  thf('42', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.60/0.84      inference('sup-', [status(thm)], ['40', '41'])).
% 0.60/0.84  thf('43', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 0.60/0.84      inference('demod', [status(thm)], ['25', '29', '32', '33', '34', '35'])).
% 0.60/0.84  thf('44', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(cc1_relset_1, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i]:
% 0.60/0.84     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.60/0.84       ( v1_relat_1 @ C ) ))).
% 0.60/0.84  thf('45', plain,
% 0.60/0.84      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.60/0.84         ((v1_relat_1 @ X9)
% 0.60/0.84          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X10 @ X11))))),
% 0.60/0.84      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.60/0.84  thf('46', plain, ((v1_relat_1 @ sk_D)),
% 0.60/0.84      inference('sup-', [status(thm)], ['44', '45'])).
% 0.60/0.84  thf('47', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 0.60/0.84      inference('demod', [status(thm)], ['39', '42', '43', '46'])).
% 0.60/0.84  thf('48', plain,
% 0.60/0.84      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 0.60/0.84      inference('split', [status(esa)], ['0'])).
% 0.60/0.84  thf('49', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 0.60/0.84      inference('sup-', [status(thm)], ['47', '48'])).
% 0.60/0.84  thf('50', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 0.60/0.84      inference('split', [status(esa)], ['0'])).
% 0.60/0.84  thf('51', plain, (~ ((v2_funct_1 @ sk_C))),
% 0.60/0.84      inference('sat_resolution*', [status(thm)], ['49', '50'])).
% 0.60/0.84  thf('52', plain, (~ (v2_funct_1 @ sk_C)),
% 0.60/0.84      inference('simpl_trail', [status(thm)], ['1', '51'])).
% 0.60/0.84  thf(fc4_zfmisc_1, axiom,
% 0.60/0.84    (![A:$i,B:$i]:
% 0.60/0.84     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.60/0.84  thf('53', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)))),
% 0.60/0.84      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 0.60/0.84  thf('54', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(cc1_subset_1, axiom,
% 0.60/0.84    (![A:$i]:
% 0.60/0.84     ( ( v1_xboole_0 @ A ) =>
% 0.60/0.84       ( ![B:$i]:
% 0.60/0.84         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.60/0.84  thf('55', plain,
% 0.60/0.84      (![X2 : $i, X3 : $i]:
% 0.60/0.84         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.60/0.84          | (v1_xboole_0 @ X2)
% 0.60/0.84          | ~ (v1_xboole_0 @ X3))),
% 0.60/0.84      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.60/0.84  thf('56', plain,
% 0.60/0.84      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_xboole_0 @ sk_C))),
% 0.60/0.84      inference('sup-', [status(thm)], ['54', '55'])).
% 0.60/0.84  thf('57', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C))),
% 0.60/0.84      inference('sup-', [status(thm)], ['53', '56'])).
% 0.60/0.84  thf('58', plain,
% 0.60/0.84      (((k1_partfun1 @ sk_A @ sk_B @ sk_B @ sk_A @ sk_C @ sk_D)
% 0.60/0.84         = (k6_partfun1 @ sk_A))),
% 0.60/0.84      inference('demod', [status(thm)], ['14', '17'])).
% 0.60/0.84  thf('59', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf(t26_funct_2, axiom,
% 0.60/0.84    (![A:$i,B:$i,C:$i,D:$i]:
% 0.60/0.84     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.60/0.84         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.60/0.84       ( ![E:$i]:
% 0.60/0.84         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 0.60/0.84             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.60/0.84           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 0.60/0.84             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 0.60/0.84               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 0.60/0.84  thf('60', plain,
% 0.60/0.84      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.60/0.84         (~ (v1_funct_1 @ X36)
% 0.60/0.84          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 0.60/0.84          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.60/0.84          | ~ (v2_funct_1 @ (k1_partfun1 @ X39 @ X37 @ X37 @ X38 @ X40 @ X36))
% 0.60/0.84          | (v2_funct_1 @ X40)
% 0.60/0.84          | ((X38) = (k1_xboole_0))
% 0.60/0.84          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X37)))
% 0.60/0.84          | ~ (v1_funct_2 @ X40 @ X39 @ X37)
% 0.60/0.84          | ~ (v1_funct_1 @ X40))),
% 0.60/0.84      inference('cnf', [status(esa)], [t26_funct_2])).
% 0.60/0.84  thf('61', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (~ (v1_funct_1 @ X0)
% 0.60/0.84          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.60/0.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.60/0.84          | ((sk_A) = (k1_xboole_0))
% 0.60/0.84          | (v2_funct_1 @ X0)
% 0.60/0.84          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D))
% 0.60/0.84          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.60/0.84          | ~ (v1_funct_1 @ sk_D))),
% 0.60/0.84      inference('sup-', [status(thm)], ['59', '60'])).
% 0.60/0.84  thf('62', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('63', plain, ((v1_funct_1 @ sk_D)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('64', plain,
% 0.60/0.84      (![X0 : $i, X1 : $i]:
% 0.60/0.84         (~ (v1_funct_1 @ X0)
% 0.60/0.84          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.60/0.84          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.60/0.84          | ((sk_A) = (k1_xboole_0))
% 0.60/0.84          | (v2_funct_1 @ X0)
% 0.60/0.84          | ~ (v2_funct_1 @ (k1_partfun1 @ X1 @ sk_B @ sk_B @ sk_A @ X0 @ sk_D)))),
% 0.60/0.84      inference('demod', [status(thm)], ['61', '62', '63'])).
% 0.60/0.84  thf('65', plain,
% 0.60/0.84      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 0.60/0.84        | (v2_funct_1 @ sk_C)
% 0.60/0.84        | ((sk_A) = (k1_xboole_0))
% 0.60/0.84        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.60/0.84        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B)
% 0.60/0.84        | ~ (v1_funct_1 @ sk_C))),
% 0.60/0.84      inference('sup-', [status(thm)], ['58', '64'])).
% 0.60/0.84  thf(fc4_funct_1, axiom,
% 0.60/0.84    (![A:$i]:
% 0.60/0.84     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.60/0.84       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.60/0.84  thf('66', plain, (![X8 : $i]: (v2_funct_1 @ (k6_relat_1 @ X8))),
% 0.60/0.84      inference('cnf', [status(esa)], [fc4_funct_1])).
% 0.60/0.84  thf('67', plain, (![X31 : $i]: ((k6_partfun1 @ X31) = (k6_relat_1 @ X31))),
% 0.60/0.84      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.60/0.84  thf('68', plain, (![X8 : $i]: (v2_funct_1 @ (k6_partfun1 @ X8))),
% 0.60/0.84      inference('demod', [status(thm)], ['66', '67'])).
% 0.60/0.84  thf('69', plain,
% 0.60/0.84      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('70', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('71', plain, ((v1_funct_1 @ sk_C)),
% 0.60/0.84      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.60/0.84  thf('72', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 0.60/0.84      inference('demod', [status(thm)], ['65', '68', '69', '70', '71'])).
% 0.60/0.84  thf('73', plain, (~ (v2_funct_1 @ sk_C)),
% 0.60/0.84      inference('simpl_trail', [status(thm)], ['1', '51'])).
% 0.60/0.84  thf('74', plain, (((sk_A) = (k1_xboole_0))),
% 0.60/0.84      inference('clc', [status(thm)], ['72', '73'])).
% 0.60/0.84  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.60/0.84  thf('75', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.60/0.84      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.60/0.84  thf('76', plain, ((v1_xboole_0 @ sk_C)),
% 0.60/0.84      inference('demod', [status(thm)], ['57', '74', '75'])).
% 0.60/0.84  thf(cc1_funct_1, axiom,
% 0.60/0.84    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_funct_1 @ A ) ))).
% 0.60/0.84  thf('77', plain, (![X5 : $i]: ((v1_funct_1 @ X5) | ~ (v1_xboole_0 @ X5))),
% 0.60/0.84      inference('cnf', [status(esa)], [cc1_funct_1])).
% 0.60/0.84  thf(cc2_funct_1, axiom,
% 0.60/0.84    (![A:$i]:
% 0.60/0.84     ( ( ( v1_xboole_0 @ A ) & ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.60/0.84       ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) & ( v2_funct_1 @ A ) ) ))).
% 0.60/0.84  thf('78', plain,
% 0.60/0.84      (![X6 : $i]:
% 0.60/0.84         ((v2_funct_1 @ X6)
% 0.60/0.84          | ~ (v1_funct_1 @ X6)
% 0.60/0.84          | ~ (v1_relat_1 @ X6)
% 0.60/0.84          | ~ (v1_xboole_0 @ X6))),
% 0.60/0.84      inference('cnf', [status(esa)], [cc2_funct_1])).
% 0.60/0.84  thf('79', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         (~ (v1_xboole_0 @ X0)
% 0.60/0.84          | ~ (v1_xboole_0 @ X0)
% 0.60/0.84          | ~ (v1_relat_1 @ X0)
% 0.60/0.84          | (v2_funct_1 @ X0))),
% 0.60/0.84      inference('sup-', [status(thm)], ['77', '78'])).
% 0.60/0.84  thf('80', plain,
% 0.60/0.84      (![X0 : $i]:
% 0.60/0.84         ((v2_funct_1 @ X0) | ~ (v1_relat_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.60/0.84      inference('simplify', [status(thm)], ['79'])).
% 0.60/0.84  thf(cc1_relat_1, axiom,
% 0.60/0.84    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_relat_1 @ A ) ))).
% 0.60/0.84  thf('81', plain, (![X4 : $i]: ((v1_relat_1 @ X4) | ~ (v1_xboole_0 @ X4))),
% 0.60/0.84      inference('cnf', [status(esa)], [cc1_relat_1])).
% 0.60/0.84  thf('82', plain, (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v2_funct_1 @ X0))),
% 0.60/0.84      inference('clc', [status(thm)], ['80', '81'])).
% 0.60/0.84  thf('83', plain, ((v2_funct_1 @ sk_C)),
% 0.60/0.84      inference('sup-', [status(thm)], ['76', '82'])).
% 0.60/0.84  thf('84', plain, ($false), inference('demod', [status(thm)], ['52', '83'])).
% 0.60/0.84  
% 0.60/0.84  % SZS output end Refutation
% 0.60/0.84  
% 0.60/0.85  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
