%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dXmMINzIw2

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:15 EST 2020

% Result     : Theorem 3.21s
% Output     : Refutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :  131 ( 315 expanded)
%              Number of leaves         :   42 ( 109 expanded)
%              Depth                    :   15
%              Number of atoms          : 1081 (6334 expanded)
%              Number of equality atoms :   41 (  73 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

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
    ! [X3: $i,X4: $i] :
      ( ~ ( v1_xboole_0 @ X3 )
      | ~ ( v1_xboole_0 @ X4 )
      | ( X3 = X4 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf(t81_relat_1,axiom,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 )).

thf('3',plain,
    ( ( k6_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t81_relat_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('4',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('5',plain,
    ( ( k6_partfun1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['3','4'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('6',plain,(
    ! [X12: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('7',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('8',plain,(
    ! [X12: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X12 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('9',plain,(
    v2_funct_1 @ k1_xboole_0 ),
    inference('sup+',[status(thm)],['5','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v2_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['2','9'])).

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

thf('11',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,
    ( ~ ( v2_funct_1 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference(split,[status(esa)],['11'])).

thf('13',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
   <= ~ ( v2_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ~ ( r2_relset_1 @ X37 @ X37 @ ( k1_partfun1 @ X37 @ X38 @ X38 @ X37 @ X36 @ X39 ) @ ( k6_partfun1 @ X37 ) )
      | ( ( k2_relset_1 @ X38 @ X37 @ X39 )
        = X37 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[t24_funct_2])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) )
      | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ sk_B_1 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
      | ( ( k2_relset_1 @ sk_B_1 @ sk_A @ X0 )
        = sk_A )
      | ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0 ) @ ( k6_partfun1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
      = sk_A )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
    | ~ ( v1_funct_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('23',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('24',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['21','24','25','26','27'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('29',plain,(
    ! [X27: $i,X28: $i] :
      ( ( ( k2_relat_1 @ X28 )
       != X27 )
      | ( v2_funct_2 @ X28 @ X27 )
      | ~ ( v5_relat_1 @ X28 @ X27 )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('30',plain,(
    ! [X28: $i] :
      ( ~ ( v1_relat_1 @ X28 )
      | ~ ( v5_relat_1 @ X28 @ ( k2_relat_1 @ X28 ) )
      | ( v2_funct_2 @ X28 @ ( k2_relat_1 @ X28 ) ) ) ),
    inference(simplify,[status(thm)],['29'])).

thf('31',plain,
    ( ~ ( v5_relat_1 @ sk_D @ sk_A )
    | ( v2_funct_2 @ sk_D @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['28','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('33',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v5_relat_1 @ X16 @ X18 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('34',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['21','24','25','26','27'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('37',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('38',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['31','34','35','38'])).

thf('40',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf('41',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( v2_funct_1 @ sk_C )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['11'])).

thf('43',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['13','43'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('45',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('47',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
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

thf('52',plain,(
    ! [X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('59',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ( X22 = X25 )
      | ~ ( r2_relset_1 @ X23 @ X24 @ X22 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D ) @ X0 )
      | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['49','60'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('62',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('63',plain,(
    ! [X35: $i] :
      ( ( k6_partfun1 @ X35 )
      = ( k6_relat_1 @ X35 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('64',plain,(
    ! [X26: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X26 ) ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['61','64'])).

thf('66',plain,(
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

thf('67',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X41 @ X42 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X43 @ X41 @ X41 @ X42 @ X44 @ X40 ) )
      | ( v2_funct_1 @ X44 )
      | ( X42 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X41 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X43 @ X41 )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,
    ( ~ ( v2_funct_1 @ ( k6_partfun1 @ sk_A ) )
    | ( v2_funct_1 @ sk_C )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['65','71'])).

thf('73',plain,(
    ! [X12: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X12 ) ) ),
    inference(demod,[status(thm)],['6','7'])).

thf('74',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
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
    inference(split,[status(esa)],['11'])).

thf('79',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['41','42'])).

thf('80',plain,(
    ~ ( v2_funct_1 @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['78','79'])).

thf('81',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['77','80'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('82',plain,(
    ! [X6: $i,X7: $i] :
      ( ( ( k2_zfmisc_1 @ X6 @ X7 )
        = k1_xboole_0 )
      | ( X6 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('83',plain,(
    ! [X7: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X7 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['82'])).

thf('84',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('85',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C ) ),
    inference(demod,[status(thm)],['48','81','83','84'])).

thf('86',plain,(
    v1_xboole_0 @ sk_C ),
    inference('sup-',[status(thm)],['45','85'])).

thf('87',plain,(
    $false ),
    inference(demod,[status(thm)],['44','86'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.dXmMINzIw2
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:04:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 3.21/3.43  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.21/3.43  % Solved by: fo/fo7.sh
% 3.21/3.43  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.21/3.43  % done 3882 iterations in 2.987s
% 3.21/3.43  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.21/3.43  % SZS output start Refutation
% 3.21/3.43  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.21/3.43  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.21/3.43  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.21/3.43  thf(sk_B_type, type, sk_B: $i > $i).
% 3.21/3.43  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.21/3.43  thf(sk_A_type, type, sk_A: $i).
% 3.21/3.43  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 3.21/3.43  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 3.21/3.43  thf(sk_B_1_type, type, sk_B_1: $i).
% 3.21/3.43  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.21/3.43  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 3.21/3.43  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 3.21/3.43  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 3.21/3.43  thf(sk_D_type, type, sk_D: $i).
% 3.21/3.43  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.21/3.43  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.21/3.43  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.21/3.43  thf(sk_C_type, type, sk_C: $i).
% 3.21/3.43  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.21/3.43  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 3.21/3.43  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.21/3.43  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.21/3.43  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 3.21/3.43  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 3.21/3.43  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 3.21/3.43  thf('0', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.21/3.43      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.21/3.43  thf(t8_boole, axiom,
% 3.21/3.43    (![A:$i,B:$i]:
% 3.21/3.43     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 3.21/3.43  thf('1', plain,
% 3.21/3.43      (![X3 : $i, X4 : $i]:
% 3.21/3.43         (~ (v1_xboole_0 @ X3) | ~ (v1_xboole_0 @ X4) | ((X3) = (X4)))),
% 3.21/3.43      inference('cnf', [status(esa)], [t8_boole])).
% 3.21/3.43  thf('2', plain,
% 3.21/3.43      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 3.21/3.43      inference('sup-', [status(thm)], ['0', '1'])).
% 3.21/3.43  thf(t81_relat_1, axiom, (( k6_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ))).
% 3.21/3.43  thf('3', plain, (((k6_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.21/3.43      inference('cnf', [status(esa)], [t81_relat_1])).
% 3.21/3.43  thf(redefinition_k6_partfun1, axiom,
% 3.21/3.43    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 3.21/3.43  thf('4', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 3.21/3.43      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.21/3.43  thf('5', plain, (((k6_partfun1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.21/3.43      inference('demod', [status(thm)], ['3', '4'])).
% 3.21/3.43  thf(fc4_funct_1, axiom,
% 3.21/3.43    (![A:$i]:
% 3.21/3.43     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 3.21/3.43       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 3.21/3.43  thf('6', plain, (![X12 : $i]: (v2_funct_1 @ (k6_relat_1 @ X12))),
% 3.21/3.43      inference('cnf', [status(esa)], [fc4_funct_1])).
% 3.21/3.43  thf('7', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 3.21/3.43      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.21/3.43  thf('8', plain, (![X12 : $i]: (v2_funct_1 @ (k6_partfun1 @ X12))),
% 3.21/3.43      inference('demod', [status(thm)], ['6', '7'])).
% 3.21/3.43  thf('9', plain, ((v2_funct_1 @ k1_xboole_0)),
% 3.21/3.43      inference('sup+', [status(thm)], ['5', '8'])).
% 3.21/3.43  thf('10', plain, (![X0 : $i]: ((v2_funct_1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 3.21/3.43      inference('sup+', [status(thm)], ['2', '9'])).
% 3.21/3.43  thf(t29_funct_2, conjecture,
% 3.21/3.43    (![A:$i,B:$i,C:$i]:
% 3.21/3.43     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.21/3.43         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.21/3.43       ( ![D:$i]:
% 3.21/3.43         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.21/3.43             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.21/3.43           ( ( r2_relset_1 @
% 3.21/3.43               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.21/3.43               ( k6_partfun1 @ A ) ) =>
% 3.21/3.43             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 3.21/3.43  thf(zf_stmt_0, negated_conjecture,
% 3.21/3.43    (~( ![A:$i,B:$i,C:$i]:
% 3.21/3.43        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.21/3.43            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.21/3.43          ( ![D:$i]:
% 3.21/3.43            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.21/3.43                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.21/3.43              ( ( r2_relset_1 @
% 3.21/3.43                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 3.21/3.43                  ( k6_partfun1 @ A ) ) =>
% 3.21/3.43                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 3.21/3.43    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 3.21/3.43  thf('11', plain, ((~ (v2_funct_1 @ sk_C) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf('12', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.21/3.43      inference('split', [status(esa)], ['11'])).
% 3.21/3.43  thf('13', plain, ((~ (v1_xboole_0 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.21/3.43      inference('sup-', [status(thm)], ['10', '12'])).
% 3.21/3.43  thf('14', plain,
% 3.21/3.43      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.21/3.43        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 3.21/3.43        (k6_partfun1 @ sk_A))),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf('15', plain,
% 3.21/3.43      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf(t24_funct_2, axiom,
% 3.21/3.43    (![A:$i,B:$i,C:$i]:
% 3.21/3.43     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 3.21/3.43         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.21/3.43       ( ![D:$i]:
% 3.21/3.43         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 3.21/3.43             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 3.21/3.43           ( ( r2_relset_1 @
% 3.21/3.43               B @ B @ ( k1_partfun1 @ B @ A @ A @ B @ D @ C ) @ 
% 3.21/3.43               ( k6_partfun1 @ B ) ) =>
% 3.21/3.43             ( ( k2_relset_1 @ A @ B @ C ) = ( B ) ) ) ) ) ))).
% 3.21/3.43  thf('16', plain,
% 3.21/3.43      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 3.21/3.43         (~ (v1_funct_1 @ X36)
% 3.21/3.43          | ~ (v1_funct_2 @ X36 @ X37 @ X38)
% 3.21/3.43          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 3.21/3.43          | ~ (r2_relset_1 @ X37 @ X37 @ 
% 3.21/3.43               (k1_partfun1 @ X37 @ X38 @ X38 @ X37 @ X36 @ X39) @ 
% 3.21/3.43               (k6_partfun1 @ X37))
% 3.21/3.43          | ((k2_relset_1 @ X38 @ X37 @ X39) = (X37))
% 3.21/3.43          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 3.21/3.43          | ~ (v1_funct_2 @ X39 @ X38 @ X37)
% 3.21/3.43          | ~ (v1_funct_1 @ X39))),
% 3.21/3.43      inference('cnf', [status(esa)], [t24_funct_2])).
% 3.21/3.43  thf('17', plain,
% 3.21/3.43      (![X0 : $i]:
% 3.21/3.43         (~ (v1_funct_1 @ X0)
% 3.21/3.43          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 3.21/3.43          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 3.21/3.43          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 3.21/3.43          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.21/3.43               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 3.21/3.43               (k6_partfun1 @ sk_A))
% 3.21/3.43          | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 3.21/3.43          | ~ (v1_funct_1 @ sk_C))),
% 3.21/3.43      inference('sup-', [status(thm)], ['15', '16'])).
% 3.21/3.43  thf('18', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf('19', plain, ((v1_funct_1 @ sk_C)),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf('20', plain,
% 3.21/3.43      (![X0 : $i]:
% 3.21/3.43         (~ (v1_funct_1 @ X0)
% 3.21/3.43          | ~ (v1_funct_2 @ X0 @ sk_B_1 @ sk_A)
% 3.21/3.43          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 3.21/3.43          | ((k2_relset_1 @ sk_B_1 @ sk_A @ X0) = (sk_A))
% 3.21/3.43          | ~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.21/3.43               (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ X0) @ 
% 3.21/3.43               (k6_partfun1 @ sk_A)))),
% 3.21/3.43      inference('demod', [status(thm)], ['17', '18', '19'])).
% 3.21/3.43  thf('21', plain,
% 3.21/3.43      ((((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (sk_A))
% 3.21/3.43        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))
% 3.21/3.43        | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 3.21/3.43        | ~ (v1_funct_1 @ sk_D))),
% 3.21/3.43      inference('sup-', [status(thm)], ['14', '20'])).
% 3.21/3.43  thf('22', plain,
% 3.21/3.43      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf(redefinition_k2_relset_1, axiom,
% 3.21/3.43    (![A:$i,B:$i,C:$i]:
% 3.21/3.43     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.21/3.43       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 3.21/3.43  thf('23', plain,
% 3.21/3.43      (![X19 : $i, X20 : $i, X21 : $i]:
% 3.21/3.43         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 3.21/3.43          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 3.21/3.43      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 3.21/3.43  thf('24', plain,
% 3.21/3.43      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 3.21/3.43      inference('sup-', [status(thm)], ['22', '23'])).
% 3.21/3.43  thf('25', plain,
% 3.21/3.43      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf('26', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf('27', plain, ((v1_funct_1 @ sk_D)),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf('28', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.21/3.43      inference('demod', [status(thm)], ['21', '24', '25', '26', '27'])).
% 3.21/3.43  thf(d3_funct_2, axiom,
% 3.21/3.43    (![A:$i,B:$i]:
% 3.21/3.43     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 3.21/3.43       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 3.21/3.43  thf('29', plain,
% 3.21/3.43      (![X27 : $i, X28 : $i]:
% 3.21/3.43         (((k2_relat_1 @ X28) != (X27))
% 3.21/3.43          | (v2_funct_2 @ X28 @ X27)
% 3.21/3.43          | ~ (v5_relat_1 @ X28 @ X27)
% 3.21/3.43          | ~ (v1_relat_1 @ X28))),
% 3.21/3.43      inference('cnf', [status(esa)], [d3_funct_2])).
% 3.21/3.43  thf('30', plain,
% 3.21/3.43      (![X28 : $i]:
% 3.21/3.43         (~ (v1_relat_1 @ X28)
% 3.21/3.43          | ~ (v5_relat_1 @ X28 @ (k2_relat_1 @ X28))
% 3.21/3.43          | (v2_funct_2 @ X28 @ (k2_relat_1 @ X28)))),
% 3.21/3.43      inference('simplify', [status(thm)], ['29'])).
% 3.21/3.43  thf('31', plain,
% 3.21/3.43      ((~ (v5_relat_1 @ sk_D @ sk_A)
% 3.21/3.43        | (v2_funct_2 @ sk_D @ (k2_relat_1 @ sk_D))
% 3.21/3.43        | ~ (v1_relat_1 @ sk_D))),
% 3.21/3.43      inference('sup-', [status(thm)], ['28', '30'])).
% 3.21/3.43  thf('32', plain,
% 3.21/3.43      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf(cc2_relset_1, axiom,
% 3.21/3.43    (![A:$i,B:$i,C:$i]:
% 3.21/3.43     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.21/3.43       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.21/3.43  thf('33', plain,
% 3.21/3.43      (![X16 : $i, X17 : $i, X18 : $i]:
% 3.21/3.43         ((v5_relat_1 @ X16 @ X18)
% 3.21/3.43          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 3.21/3.43      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.21/3.43  thf('34', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 3.21/3.43      inference('sup-', [status(thm)], ['32', '33'])).
% 3.21/3.43  thf('35', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 3.21/3.43      inference('demod', [status(thm)], ['21', '24', '25', '26', '27'])).
% 3.21/3.43  thf('36', plain,
% 3.21/3.43      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf(cc1_relset_1, axiom,
% 3.21/3.43    (![A:$i,B:$i,C:$i]:
% 3.21/3.43     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.21/3.43       ( v1_relat_1 @ C ) ))).
% 3.21/3.43  thf('37', plain,
% 3.21/3.43      (![X13 : $i, X14 : $i, X15 : $i]:
% 3.21/3.43         ((v1_relat_1 @ X13)
% 3.21/3.43          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 3.21/3.43      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.21/3.43  thf('38', plain, ((v1_relat_1 @ sk_D)),
% 3.21/3.43      inference('sup-', [status(thm)], ['36', '37'])).
% 3.21/3.43  thf('39', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 3.21/3.43      inference('demod', [status(thm)], ['31', '34', '35', '38'])).
% 3.21/3.43  thf('40', plain,
% 3.21/3.43      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 3.21/3.43      inference('split', [status(esa)], ['11'])).
% 3.21/3.43  thf('41', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 3.21/3.43      inference('sup-', [status(thm)], ['39', '40'])).
% 3.21/3.43  thf('42', plain, (~ ((v2_funct_1 @ sk_C)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 3.21/3.43      inference('split', [status(esa)], ['11'])).
% 3.21/3.43  thf('43', plain, (~ ((v2_funct_1 @ sk_C))),
% 3.21/3.43      inference('sat_resolution*', [status(thm)], ['41', '42'])).
% 3.21/3.43  thf('44', plain, (~ (v1_xboole_0 @ sk_C)),
% 3.21/3.43      inference('simpl_trail', [status(thm)], ['13', '43'])).
% 3.21/3.43  thf(d1_xboole_0, axiom,
% 3.21/3.43    (![A:$i]:
% 3.21/3.43     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 3.21/3.43  thf('45', plain,
% 3.21/3.43      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 3.21/3.43      inference('cnf', [status(esa)], [d1_xboole_0])).
% 3.21/3.43  thf('46', plain,
% 3.21/3.43      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf(t5_subset, axiom,
% 3.21/3.43    (![A:$i,B:$i,C:$i]:
% 3.21/3.43     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 3.21/3.43          ( v1_xboole_0 @ C ) ) ))).
% 3.21/3.43  thf('47', plain,
% 3.21/3.43      (![X8 : $i, X9 : $i, X10 : $i]:
% 3.21/3.43         (~ (r2_hidden @ X8 @ X9)
% 3.21/3.43          | ~ (v1_xboole_0 @ X10)
% 3.21/3.43          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10)))),
% 3.21/3.43      inference('cnf', [status(esa)], [t5_subset])).
% 3.21/3.43  thf('48', plain,
% 3.21/3.43      (![X0 : $i]:
% 3.21/3.43         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 3.21/3.43          | ~ (r2_hidden @ X0 @ sk_C))),
% 3.21/3.43      inference('sup-', [status(thm)], ['46', '47'])).
% 3.21/3.43  thf('49', plain,
% 3.21/3.43      ((r2_relset_1 @ sk_A @ sk_A @ 
% 3.21/3.43        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 3.21/3.43        (k6_partfun1 @ sk_A))),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf('50', plain,
% 3.21/3.43      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf('51', plain,
% 3.21/3.43      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf(dt_k1_partfun1, axiom,
% 3.21/3.43    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 3.21/3.43     ( ( ( v1_funct_1 @ E ) & 
% 3.21/3.43         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.21/3.43         ( v1_funct_1 @ F ) & 
% 3.21/3.43         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 3.21/3.43       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 3.21/3.43         ( m1_subset_1 @
% 3.21/3.43           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 3.21/3.43           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 3.21/3.43  thf('52', plain,
% 3.21/3.43      (![X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 3.21/3.43         (~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 3.21/3.43          | ~ (v1_funct_1 @ X29)
% 3.21/3.43          | ~ (v1_funct_1 @ X32)
% 3.21/3.43          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 3.21/3.43          | (m1_subset_1 @ (k1_partfun1 @ X30 @ X31 @ X33 @ X34 @ X29 @ X32) @ 
% 3.21/3.43             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X34))))),
% 3.21/3.43      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 3.21/3.43  thf('53', plain,
% 3.21/3.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.21/3.43         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 3.21/3.43           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.21/3.43          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.21/3.43          | ~ (v1_funct_1 @ X1)
% 3.21/3.43          | ~ (v1_funct_1 @ sk_C))),
% 3.21/3.43      inference('sup-', [status(thm)], ['51', '52'])).
% 3.21/3.43  thf('54', plain, ((v1_funct_1 @ sk_C)),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf('55', plain,
% 3.21/3.43      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.21/3.43         ((m1_subset_1 @ (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C @ X1) @ 
% 3.21/3.43           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 3.21/3.43          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.21/3.43          | ~ (v1_funct_1 @ X1))),
% 3.21/3.43      inference('demod', [status(thm)], ['53', '54'])).
% 3.21/3.43  thf('56', plain,
% 3.21/3.43      ((~ (v1_funct_1 @ sk_D)
% 3.21/3.43        | (m1_subset_1 @ 
% 3.21/3.43           (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 3.21/3.43           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.21/3.43      inference('sup-', [status(thm)], ['50', '55'])).
% 3.21/3.43  thf('57', plain, ((v1_funct_1 @ sk_D)),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf('58', plain,
% 3.21/3.43      ((m1_subset_1 @ 
% 3.21/3.43        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ 
% 3.21/3.43        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 3.21/3.43      inference('demod', [status(thm)], ['56', '57'])).
% 3.21/3.43  thf(redefinition_r2_relset_1, axiom,
% 3.21/3.43    (![A:$i,B:$i,C:$i,D:$i]:
% 3.21/3.43     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 3.21/3.43         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.21/3.43       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 3.21/3.43  thf('59', plain,
% 3.21/3.43      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 3.21/3.43         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 3.21/3.43          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 3.21/3.43          | ((X22) = (X25))
% 3.21/3.43          | ~ (r2_relset_1 @ X23 @ X24 @ X22 @ X25))),
% 3.21/3.43      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 3.21/3.43  thf('60', plain,
% 3.21/3.43      (![X0 : $i]:
% 3.21/3.43         (~ (r2_relset_1 @ sk_A @ sk_A @ 
% 3.21/3.43             (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) @ X0)
% 3.21/3.43          | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D) = (X0))
% 3.21/3.43          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 3.21/3.43      inference('sup-', [status(thm)], ['58', '59'])).
% 3.21/3.43  thf('61', plain,
% 3.21/3.43      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 3.21/3.43           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 3.21/3.43        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 3.21/3.43            = (k6_partfun1 @ sk_A)))),
% 3.21/3.43      inference('sup-', [status(thm)], ['49', '60'])).
% 3.21/3.43  thf(t29_relset_1, axiom,
% 3.21/3.43    (![A:$i]:
% 3.21/3.43     ( m1_subset_1 @
% 3.21/3.43       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 3.21/3.43  thf('62', plain,
% 3.21/3.43      (![X26 : $i]:
% 3.21/3.43         (m1_subset_1 @ (k6_relat_1 @ X26) @ 
% 3.21/3.43          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))),
% 3.21/3.43      inference('cnf', [status(esa)], [t29_relset_1])).
% 3.21/3.43  thf('63', plain, (![X35 : $i]: ((k6_partfun1 @ X35) = (k6_relat_1 @ X35))),
% 3.21/3.43      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 3.21/3.43  thf('64', plain,
% 3.21/3.43      (![X26 : $i]:
% 3.21/3.43         (m1_subset_1 @ (k6_partfun1 @ X26) @ 
% 3.21/3.43          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X26)))),
% 3.21/3.43      inference('demod', [status(thm)], ['62', '63'])).
% 3.21/3.43  thf('65', plain,
% 3.21/3.43      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C @ sk_D)
% 3.21/3.43         = (k6_partfun1 @ sk_A))),
% 3.21/3.43      inference('demod', [status(thm)], ['61', '64'])).
% 3.21/3.43  thf('66', plain,
% 3.21/3.43      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf(t26_funct_2, axiom,
% 3.21/3.43    (![A:$i,B:$i,C:$i,D:$i]:
% 3.21/3.43     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 3.21/3.43         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 3.21/3.43       ( ![E:$i]:
% 3.21/3.43         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 3.21/3.43             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 3.21/3.43           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 3.21/3.43             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 3.21/3.43               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 3.21/3.43  thf('67', plain,
% 3.21/3.43      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 3.21/3.43         (~ (v1_funct_1 @ X40)
% 3.21/3.43          | ~ (v1_funct_2 @ X40 @ X41 @ X42)
% 3.21/3.43          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 3.21/3.43          | ~ (v2_funct_1 @ (k1_partfun1 @ X43 @ X41 @ X41 @ X42 @ X44 @ X40))
% 3.21/3.43          | (v2_funct_1 @ X44)
% 3.21/3.43          | ((X42) = (k1_xboole_0))
% 3.21/3.43          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X41)))
% 3.21/3.43          | ~ (v1_funct_2 @ X44 @ X43 @ X41)
% 3.21/3.43          | ~ (v1_funct_1 @ X44))),
% 3.21/3.43      inference('cnf', [status(esa)], [t26_funct_2])).
% 3.21/3.43  thf('68', plain,
% 3.21/3.43      (![X0 : $i, X1 : $i]:
% 3.21/3.43         (~ (v1_funct_1 @ X0)
% 3.21/3.43          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 3.21/3.43          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 3.21/3.43          | ((sk_A) = (k1_xboole_0))
% 3.21/3.43          | (v2_funct_1 @ X0)
% 3.21/3.43          | ~ (v2_funct_1 @ 
% 3.21/3.43               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D))
% 3.21/3.43          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 3.21/3.43          | ~ (v1_funct_1 @ sk_D))),
% 3.21/3.43      inference('sup-', [status(thm)], ['66', '67'])).
% 3.21/3.43  thf('69', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf('70', plain, ((v1_funct_1 @ sk_D)),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf('71', plain,
% 3.21/3.43      (![X0 : $i, X1 : $i]:
% 3.21/3.43         (~ (v1_funct_1 @ X0)
% 3.21/3.43          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 3.21/3.43          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 3.21/3.43          | ((sk_A) = (k1_xboole_0))
% 3.21/3.43          | (v2_funct_1 @ X0)
% 3.21/3.43          | ~ (v2_funct_1 @ 
% 3.21/3.43               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D)))),
% 3.21/3.43      inference('demod', [status(thm)], ['68', '69', '70'])).
% 3.21/3.43  thf('72', plain,
% 3.21/3.43      ((~ (v2_funct_1 @ (k6_partfun1 @ sk_A))
% 3.21/3.43        | (v2_funct_1 @ sk_C)
% 3.21/3.43        | ((sk_A) = (k1_xboole_0))
% 3.21/3.43        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 3.21/3.43        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_1)
% 3.21/3.43        | ~ (v1_funct_1 @ sk_C))),
% 3.21/3.43      inference('sup-', [status(thm)], ['65', '71'])).
% 3.21/3.43  thf('73', plain, (![X12 : $i]: (v2_funct_1 @ (k6_partfun1 @ X12))),
% 3.21/3.43      inference('demod', [status(thm)], ['6', '7'])).
% 3.21/3.43  thf('74', plain,
% 3.21/3.43      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf('75', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf('76', plain, ((v1_funct_1 @ sk_C)),
% 3.21/3.43      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.21/3.43  thf('77', plain, (((v2_funct_1 @ sk_C) | ((sk_A) = (k1_xboole_0)))),
% 3.21/3.43      inference('demod', [status(thm)], ['72', '73', '74', '75', '76'])).
% 3.21/3.43  thf('78', plain, ((~ (v2_funct_1 @ sk_C)) <= (~ ((v2_funct_1 @ sk_C)))),
% 3.21/3.43      inference('split', [status(esa)], ['11'])).
% 3.21/3.43  thf('79', plain, (~ ((v2_funct_1 @ sk_C))),
% 3.21/3.43      inference('sat_resolution*', [status(thm)], ['41', '42'])).
% 3.21/3.43  thf('80', plain, (~ (v2_funct_1 @ sk_C)),
% 3.21/3.43      inference('simpl_trail', [status(thm)], ['78', '79'])).
% 3.21/3.43  thf('81', plain, (((sk_A) = (k1_xboole_0))),
% 3.21/3.43      inference('clc', [status(thm)], ['77', '80'])).
% 3.21/3.43  thf(t113_zfmisc_1, axiom,
% 3.21/3.43    (![A:$i,B:$i]:
% 3.21/3.43     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.21/3.43       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.21/3.43  thf('82', plain,
% 3.21/3.43      (![X6 : $i, X7 : $i]:
% 3.21/3.43         (((k2_zfmisc_1 @ X6 @ X7) = (k1_xboole_0)) | ((X6) != (k1_xboole_0)))),
% 3.21/3.43      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.21/3.43  thf('83', plain,
% 3.21/3.43      (![X7 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X7) = (k1_xboole_0))),
% 3.21/3.43      inference('simplify', [status(thm)], ['82'])).
% 3.21/3.43  thf('84', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 3.21/3.43      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 3.21/3.43  thf('85', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C)),
% 3.21/3.43      inference('demod', [status(thm)], ['48', '81', '83', '84'])).
% 3.21/3.43  thf('86', plain, ((v1_xboole_0 @ sk_C)),
% 3.21/3.43      inference('sup-', [status(thm)], ['45', '85'])).
% 3.21/3.43  thf('87', plain, ($false), inference('demod', [status(thm)], ['44', '86'])).
% 3.21/3.43  
% 3.21/3.43  % SZS output end Refutation
% 3.21/3.43  
% 3.21/3.44  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
