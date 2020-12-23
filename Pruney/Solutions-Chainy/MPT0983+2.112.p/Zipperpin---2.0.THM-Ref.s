%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UIM2TcS5wf

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:54:19 EST 2020

% Result     : Theorem 2.98s
% Output     : Refutation 2.98s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 834 expanded)
%              Number of leaves         :   49 ( 259 expanded)
%              Depth                    :   23
%              Number of atoms          : 1360 (15864 expanded)
%              Number of equality atoms :   44 ( 187 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_partfun1_type,type,(
    k1_partfun1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v2_funct_1_type,type,(
    v2_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v2_funct_2_type,type,(
    v2_funct_2: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('0',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_xboole_0 @ X14 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('1',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X52: $i] :
      ( ( k6_partfun1 @ X52 )
      = ( k6_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('4',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( v1_xboole_0 @ X16 )
      | ~ ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X0 ) )
      | ( v1_xboole_0 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ ( k6_partfun1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['0','5'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X4: $i,X6: $i] :
      ( ( r1_tarski @ X4 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X4 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('11',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( r1_tarski @ X0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( ( k6_partfun1 @ X0 )
        = X1 ) ) ),
    inference('sup-',[status(thm)],['6','13'])).

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

thf('15',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,
    ( ! [X0: $i] :
        ( ~ ( v2_funct_1 @ ( k6_partfun1 @ X0 ) )
        | ~ ( v1_xboole_0 @ sk_C_1 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['14','16'])).

thf(fc4_funct_1,axiom,(
    ! [A: $i] :
      ( ( v2_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('18',plain,(
    ! [X29: $i] :
      ( v2_funct_1 @ ( k6_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc4_funct_1])).

thf('19',plain,(
    ! [X52: $i] :
      ( ( k6_partfun1 @ X52 )
      = ( k6_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('20',plain,(
    ! [X29: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X29 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ sk_C_1 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['17','20'])).

thf('22',plain,
    ( ~ ( v1_xboole_0 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(condensation,[status(thm)],['21'])).

thf('23',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) )
        & ( m1_subset_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ) )).

thf('25',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i,X44: $i,X45: $i] :
      ( ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ( m1_subset_1 @ ( k1_partfun1 @ X41 @ X42 @ X44 @ X45 @ X40 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X45 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_partfun1])).

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( m1_subset_1 @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['23','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('33',plain,(
    ! [X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X48 ) ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ( ( k1_partfun1 @ X47 @ X48 @ X50 @ X51 @ X46 @ X49 )
        = ( k5_relat_1 @ X46 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_partfun1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0 )
        = ( k5_relat_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0 )
        = ( k5_relat_1 @ sk_C_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,
    ( ~ ( v1_funct_1 @ sk_D )
    | ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
      = ( k5_relat_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k5_relat_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30','39'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('41',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('43',plain,(
    ! [X22: $i,X23: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('44',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['42','43'])).

thf(t45_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) )).

thf('45',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v1_relat_1 @ X24 )
      | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ X25 @ X24 ) ) @ ( k2_relat_1 @ X24 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t45_relat_1])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('46',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X21 )
      | ( v5_relat_1 @ X20 @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) )
      | ( v5_relat_1 @ ( k5_relat_1 @ X1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( v5_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('51',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X22: $i,X23: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('53',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    ! [X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ X19 ) )
      | ( v1_relat_1 @ X18 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('56',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X22: $i,X23: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('58',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    v5_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['48','53','58'])).

thf('60',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v5_relat_1 @ X20 @ X21 )
      | ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('61',plain,
    ( ~ ( v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    v1_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('63',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) ) @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X7: $i,X9: $i] :
      ( ( X7 = X9 )
      | ~ ( r1_tarski @ X9 @ X7 )
      | ~ ( r1_tarski @ X7 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('65',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k2_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) ) )
    | ( ( k2_relat_1 @ sk_D )
      = ( k2_relat_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k5_relat_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('68',plain,(
    r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_D ) @ ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['29','30','39'])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('70',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( X33 = X36 )
      | ~ ( r2_relset_1 @ X34 @ X35 @ X33 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( r2_relset_1 @ sk_A @ sk_A @ ( k5_relat_1 @ sk_C_1 @ sk_D ) @ X0 )
      | ( ( k5_relat_1 @ sk_C_1 @ sk_D )
        = X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ~ ( m1_subset_1 @ ( k6_partfun1 @ sk_A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
    | ( ( k5_relat_1 @ sk_C_1 @ sk_D )
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','71'])).

thf('73',plain,(
    ! [X37: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('74',plain,
    ( ( k5_relat_1 @ sk_C_1 @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('75',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X27 ) )
      = X27 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('76',plain,(
    ! [X52: $i] :
      ( ( k6_partfun1 @ X52 )
      = ( k6_relat_1 @ X52 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('77',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X27 ) )
      = X27 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('79',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v5_relat_1 @ X30 @ X32 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('80',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v5_relat_1 @ X20 @ X21 )
      | ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('82',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['51','52'])).

thf('84',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,
    ( ( k5_relat_1 @ sk_C_1 @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('86',plain,(
    ! [X27: $i] :
      ( ( k2_relat_1 @ ( k6_partfun1 @ X27 ) )
      = X27 ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('87',plain,
    ( ( k2_relat_1 @ sk_D )
    = sk_A ),
    inference(demod,[status(thm)],['65','74','77','84','85','86'])).

thf(d3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v5_relat_1 @ B @ A ) )
     => ( ( v2_funct_2 @ B @ A )
      <=> ( ( k2_relat_1 @ B )
          = A ) ) ) )).

thf('88',plain,(
    ! [X38: $i,X39: $i] :
      ( ( ( k2_relat_1 @ X39 )
       != X38 )
      | ( v2_funct_2 @ X39 @ X38 )
      | ~ ( v5_relat_1 @ X39 @ X38 )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d3_funct_2])).

thf('89',plain,(
    ! [X39: $i] :
      ( ~ ( v1_relat_1 @ X39 )
      | ~ ( v5_relat_1 @ X39 @ ( k2_relat_1 @ X39 ) )
      | ( v2_funct_2 @ X39 @ ( k2_relat_1 @ X39 ) ) ) ),
    inference(simplify,[status(thm)],['88'])).

thf('90',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('91',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['90'])).

thf('92',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X20 ) @ X21 )
      | ( v5_relat_1 @ X20 @ X21 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v5_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X39: $i] :
      ( ( v2_funct_2 @ X39 @ ( k2_relat_1 @ X39 ) )
      | ~ ( v1_relat_1 @ X39 ) ) ),
    inference(clc,[status(thm)],['89','93'])).

thf('95',plain,
    ( ( v2_funct_2 @ sk_D @ sk_A )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['87','94'])).

thf('96',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['51','52'])).

thf('97',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference(demod,[status(thm)],['95','96'])).

thf('98',plain,
    ( ~ ( v2_funct_2 @ sk_D @ sk_A )
   <= ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['15'])).

thf('99',plain,(
    v2_funct_2 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
    | ~ ( v2_funct_2 @ sk_D @ sk_A ) ),
    inference(split,[status(esa)],['15'])).

thf('101',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['22','101'])).

thf('103',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_xboole_0 @ X14 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf('104',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) )
      | ( v1_xboole_0 @ X16 )
      | ~ ( v1_xboole_0 @ X17 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('106',plain,
    ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,
    ( ~ ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['103','106'])).

thf('108',plain,
    ( ( k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D )
    = ( k5_relat_1 @ sk_C_1 @ sk_D ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('109',plain,(
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

thf('110',plain,(
    ! [X53: $i,X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ~ ( v1_funct_1 @ X53 )
      | ~ ( v1_funct_2 @ X53 @ X54 @ X55 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X54 @ X55 ) ) )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X56 @ X54 @ X54 @ X55 @ X57 @ X53 ) )
      | ( v2_funct_1 @ X57 )
      | ( X55 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X56 @ X54 ) ) )
      | ~ ( v1_funct_2 @ X57 @ X56 @ X54 )
      | ~ ( v1_funct_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t26_funct_2])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_B_1 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v1_funct_2 @ sk_D @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ( sk_A = k1_xboole_0 )
      | ( v2_funct_1 @ X0 )
      | ~ ( v2_funct_1 @ ( k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['108','114'])).

thf('116',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('119',plain,
    ( ~ ( v2_funct_1 @ ( k5_relat_1 @ sk_C_1 @ sk_D ) )
    | ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['115','116','117','118'])).

thf('120',plain,
    ( ( k5_relat_1 @ sk_C_1 @ sk_D )
    = ( k6_partfun1 @ sk_A ) ),
    inference(demod,[status(thm)],['72','73'])).

thf('121',plain,(
    ! [X29: $i] :
      ( v2_funct_1 @ ( k6_partfun1 @ X29 ) ) ),
    inference(demod,[status(thm)],['18','19'])).

thf('122',plain,
    ( ( v2_funct_1 @ sk_C_1 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['119','120','121'])).

thf('123',plain,
    ( ~ ( v2_funct_1 @ sk_C_1 )
   <= ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(split,[status(esa)],['15'])).

thf('124',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference('sat_resolution*',[status(thm)],['99','100'])).

thf('125',plain,(
    ~ ( v2_funct_1 @ sk_C_1 ) ),
    inference(simpl_trail,[status(thm)],['123','124'])).

thf('126',plain,(
    sk_A = k1_xboole_0 ),
    inference(clc,[status(thm)],['122','125'])).

thf('127',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['90'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('128',plain,(
    ! [X11: $i] :
      ( r1_xboole_0 @ X11 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('129',plain,(
    ! [X12: $i,X13: $i] :
      ( ~ ( r1_xboole_0 @ X12 @ X13 )
      | ~ ( r1_tarski @ X12 @ X13 )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r1_tarski @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['127','130'])).

thf('132',plain,(
    v1_xboole_0 @ sk_C_1 ),
    inference(demod,[status(thm)],['107','126','131'])).

thf('133',plain,(
    $false ),
    inference(demod,[status(thm)],['102','132'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.UIM2TcS5wf
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:01:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.36  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 2.98/3.17  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.98/3.17  % Solved by: fo/fo7.sh
% 2.98/3.17  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.98/3.17  % done 2440 iterations in 2.695s
% 2.98/3.17  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.98/3.17  % SZS output start Refutation
% 2.98/3.17  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.98/3.17  thf(k1_partfun1_type, type, k1_partfun1: $i > $i > $i > $i > $i > $i > $i).
% 2.98/3.17  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.98/3.17  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.98/3.17  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.98/3.17  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.98/3.17  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.98/3.17  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.98/3.17  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 2.98/3.17  thf(v2_funct_1_type, type, v2_funct_1: $i > $o).
% 2.98/3.17  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.98/3.17  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.98/3.17  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 2.98/3.17  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.98/3.17  thf(sk_D_type, type, sk_D: $i).
% 2.98/3.17  thf(v2_funct_2_type, type, v2_funct_2: $i > $i > $o).
% 2.98/3.17  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.98/3.17  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 2.98/3.17  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.98/3.17  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 2.98/3.17  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 2.98/3.17  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.98/3.17  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.98/3.17  thf(sk_A_type, type, sk_A: $i).
% 2.98/3.17  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 2.98/3.17  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.98/3.17  thf(sk_B_1_type, type, sk_B_1: $i).
% 2.98/3.17  thf(fc4_zfmisc_1, axiom,
% 2.98/3.17    (![A:$i,B:$i]:
% 2.98/3.17     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 2.98/3.17  thf('0', plain,
% 2.98/3.17      (![X14 : $i, X15 : $i]:
% 2.98/3.17         (~ (v1_xboole_0 @ X14) | (v1_xboole_0 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 2.98/3.17      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 2.98/3.17  thf(t29_relset_1, axiom,
% 2.98/3.17    (![A:$i]:
% 2.98/3.17     ( m1_subset_1 @
% 2.98/3.17       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 2.98/3.17  thf('1', plain,
% 2.98/3.17      (![X37 : $i]:
% 2.98/3.17         (m1_subset_1 @ (k6_relat_1 @ X37) @ 
% 2.98/3.17          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 2.98/3.17      inference('cnf', [status(esa)], [t29_relset_1])).
% 2.98/3.17  thf(redefinition_k6_partfun1, axiom,
% 2.98/3.17    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 2.98/3.17  thf('2', plain, (![X52 : $i]: ((k6_partfun1 @ X52) = (k6_relat_1 @ X52))),
% 2.98/3.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.98/3.17  thf('3', plain,
% 2.98/3.17      (![X37 : $i]:
% 2.98/3.17         (m1_subset_1 @ (k6_partfun1 @ X37) @ 
% 2.98/3.17          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 2.98/3.17      inference('demod', [status(thm)], ['1', '2'])).
% 2.98/3.17  thf(cc1_subset_1, axiom,
% 2.98/3.17    (![A:$i]:
% 2.98/3.17     ( ( v1_xboole_0 @ A ) =>
% 2.98/3.17       ( ![B:$i]:
% 2.98/3.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 2.98/3.17  thf('4', plain,
% 2.98/3.17      (![X16 : $i, X17 : $i]:
% 2.98/3.17         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 2.98/3.17          | (v1_xboole_0 @ X16)
% 2.98/3.17          | ~ (v1_xboole_0 @ X17))),
% 2.98/3.17      inference('cnf', [status(esa)], [cc1_subset_1])).
% 2.98/3.17  thf('5', plain,
% 2.98/3.17      (![X0 : $i]:
% 2.98/3.17         (~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X0))
% 2.98/3.17          | (v1_xboole_0 @ (k6_partfun1 @ X0)))),
% 2.98/3.17      inference('sup-', [status(thm)], ['3', '4'])).
% 2.98/3.17  thf('6', plain,
% 2.98/3.17      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | (v1_xboole_0 @ (k6_partfun1 @ X0)))),
% 2.98/3.17      inference('sup-', [status(thm)], ['0', '5'])).
% 2.98/3.17  thf(d3_tarski, axiom,
% 2.98/3.17    (![A:$i,B:$i]:
% 2.98/3.17     ( ( r1_tarski @ A @ B ) <=>
% 2.98/3.17       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 2.98/3.17  thf('7', plain,
% 2.98/3.17      (![X4 : $i, X6 : $i]:
% 2.98/3.17         ((r1_tarski @ X4 @ X6) | (r2_hidden @ (sk_C @ X6 @ X4) @ X4))),
% 2.98/3.17      inference('cnf', [status(esa)], [d3_tarski])).
% 2.98/3.17  thf(d1_xboole_0, axiom,
% 2.98/3.17    (![A:$i]:
% 2.98/3.17     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 2.98/3.17  thf('8', plain,
% 2.98/3.17      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 2.98/3.17      inference('cnf', [status(esa)], [d1_xboole_0])).
% 2.98/3.17  thf('9', plain,
% 2.98/3.17      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 2.98/3.17      inference('sup-', [status(thm)], ['7', '8'])).
% 2.98/3.17  thf('10', plain,
% 2.98/3.17      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 2.98/3.17      inference('sup-', [status(thm)], ['7', '8'])).
% 2.98/3.17  thf(d10_xboole_0, axiom,
% 2.98/3.17    (![A:$i,B:$i]:
% 2.98/3.17     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.98/3.17  thf('11', plain,
% 2.98/3.17      (![X7 : $i, X9 : $i]:
% 2.98/3.17         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 2.98/3.17      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.98/3.17  thf('12', plain,
% 2.98/3.17      (![X0 : $i, X1 : $i]:
% 2.98/3.17         (~ (v1_xboole_0 @ X1) | ~ (r1_tarski @ X0 @ X1) | ((X0) = (X1)))),
% 2.98/3.17      inference('sup-', [status(thm)], ['10', '11'])).
% 2.98/3.17  thf('13', plain,
% 2.98/3.17      (![X0 : $i, X1 : $i]:
% 2.98/3.17         (~ (v1_xboole_0 @ X1) | ((X1) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 2.98/3.17      inference('sup-', [status(thm)], ['9', '12'])).
% 2.98/3.17  thf('14', plain,
% 2.98/3.17      (![X0 : $i, X1 : $i]:
% 2.98/3.17         (~ (v1_xboole_0 @ X0)
% 2.98/3.17          | ~ (v1_xboole_0 @ X1)
% 2.98/3.17          | ((k6_partfun1 @ X0) = (X1)))),
% 2.98/3.17      inference('sup-', [status(thm)], ['6', '13'])).
% 2.98/3.17  thf(t29_funct_2, conjecture,
% 2.98/3.17    (![A:$i,B:$i,C:$i]:
% 2.98/3.17     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.98/3.17         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.98/3.17       ( ![D:$i]:
% 2.98/3.17         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.98/3.17             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.98/3.17           ( ( r2_relset_1 @
% 2.98/3.17               A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.98/3.17               ( k6_partfun1 @ A ) ) =>
% 2.98/3.17             ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ))).
% 2.98/3.17  thf(zf_stmt_0, negated_conjecture,
% 2.98/3.17    (~( ![A:$i,B:$i,C:$i]:
% 2.98/3.17        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 2.98/3.17            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.98/3.17          ( ![D:$i]:
% 2.98/3.17            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 2.98/3.17                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 2.98/3.17              ( ( r2_relset_1 @
% 2.98/3.17                  A @ A @ ( k1_partfun1 @ A @ B @ B @ A @ C @ D ) @ 
% 2.98/3.17                  ( k6_partfun1 @ A ) ) =>
% 2.98/3.17                ( ( v2_funct_1 @ C ) & ( v2_funct_2 @ D @ A ) ) ) ) ) ) )),
% 2.98/3.17    inference('cnf.neg', [status(esa)], [t29_funct_2])).
% 2.98/3.17  thf('15', plain, ((~ (v2_funct_1 @ sk_C_1) | ~ (v2_funct_2 @ sk_D @ sk_A))),
% 2.98/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.98/3.17  thf('16', plain, ((~ (v2_funct_1 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 2.98/3.17      inference('split', [status(esa)], ['15'])).
% 2.98/3.17  thf('17', plain,
% 2.98/3.17      ((![X0 : $i]:
% 2.98/3.17          (~ (v2_funct_1 @ (k6_partfun1 @ X0))
% 2.98/3.17           | ~ (v1_xboole_0 @ sk_C_1)
% 2.98/3.17           | ~ (v1_xboole_0 @ X0)))
% 2.98/3.17         <= (~ ((v2_funct_1 @ sk_C_1)))),
% 2.98/3.17      inference('sup-', [status(thm)], ['14', '16'])).
% 2.98/3.17  thf(fc4_funct_1, axiom,
% 2.98/3.17    (![A:$i]:
% 2.98/3.17     ( ( v2_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 2.98/3.17       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 2.98/3.17  thf('18', plain, (![X29 : $i]: (v2_funct_1 @ (k6_relat_1 @ X29))),
% 2.98/3.17      inference('cnf', [status(esa)], [fc4_funct_1])).
% 2.98/3.17  thf('19', plain, (![X52 : $i]: ((k6_partfun1 @ X52) = (k6_relat_1 @ X52))),
% 2.98/3.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.98/3.17  thf('20', plain, (![X29 : $i]: (v2_funct_1 @ (k6_partfun1 @ X29))),
% 2.98/3.17      inference('demod', [status(thm)], ['18', '19'])).
% 2.98/3.17  thf('21', plain,
% 2.98/3.17      ((![X0 : $i]: (~ (v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ X0)))
% 2.98/3.17         <= (~ ((v2_funct_1 @ sk_C_1)))),
% 2.98/3.17      inference('demod', [status(thm)], ['17', '20'])).
% 2.98/3.17  thf('22', plain, ((~ (v1_xboole_0 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 2.98/3.17      inference('condensation', [status(thm)], ['21'])).
% 2.98/3.17  thf('23', plain,
% 2.98/3.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 2.98/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.98/3.17  thf('24', plain,
% 2.98/3.17      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.98/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.98/3.17  thf(dt_k1_partfun1, axiom,
% 2.98/3.17    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.98/3.17     ( ( ( v1_funct_1 @ E ) & 
% 2.98/3.17         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.98/3.17         ( v1_funct_1 @ F ) & 
% 2.98/3.17         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.98/3.17       ( ( v1_funct_1 @ ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.98/3.17         ( m1_subset_1 @
% 2.98/3.17           ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.98/3.17           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) ))).
% 2.98/3.17  thf('25', plain,
% 2.98/3.17      (![X40 : $i, X41 : $i, X42 : $i, X43 : $i, X44 : $i, X45 : $i]:
% 2.98/3.17         (~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42)))
% 2.98/3.17          | ~ (v1_funct_1 @ X40)
% 2.98/3.17          | ~ (v1_funct_1 @ X43)
% 2.98/3.17          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 2.98/3.17          | (m1_subset_1 @ (k1_partfun1 @ X41 @ X42 @ X44 @ X45 @ X40 @ X43) @ 
% 2.98/3.17             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X45))))),
% 2.98/3.17      inference('cnf', [status(esa)], [dt_k1_partfun1])).
% 2.98/3.17  thf('26', plain,
% 2.98/3.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.98/3.17         ((m1_subset_1 @ 
% 2.98/3.17           (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 2.98/3.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.98/3.17          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.98/3.17          | ~ (v1_funct_1 @ X1)
% 2.98/3.17          | ~ (v1_funct_1 @ sk_C_1))),
% 2.98/3.17      inference('sup-', [status(thm)], ['24', '25'])).
% 2.98/3.17  thf('27', plain, ((v1_funct_1 @ sk_C_1)),
% 2.98/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.98/3.17  thf('28', plain,
% 2.98/3.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.98/3.17         ((m1_subset_1 @ 
% 2.98/3.17           (k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X0 @ sk_C_1 @ X1) @ 
% 2.98/3.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 2.98/3.17          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 2.98/3.17          | ~ (v1_funct_1 @ X1))),
% 2.98/3.17      inference('demod', [status(thm)], ['26', '27'])).
% 2.98/3.17  thf('29', plain,
% 2.98/3.17      ((~ (v1_funct_1 @ sk_D)
% 2.98/3.17        | (m1_subset_1 @ 
% 2.98/3.17           (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 2.98/3.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.98/3.17      inference('sup-', [status(thm)], ['23', '28'])).
% 2.98/3.17  thf('30', plain, ((v1_funct_1 @ sk_D)),
% 2.98/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.98/3.17  thf('31', plain,
% 2.98/3.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 2.98/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.98/3.17  thf('32', plain,
% 2.98/3.17      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.98/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.98/3.17  thf(redefinition_k1_partfun1, axiom,
% 2.98/3.17    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.98/3.17     ( ( ( v1_funct_1 @ E ) & 
% 2.98/3.17         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.98/3.17         ( v1_funct_1 @ F ) & 
% 2.98/3.17         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 2.98/3.17       ( ( k1_partfun1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 2.98/3.17  thf('33', plain,
% 2.98/3.17      (![X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 2.98/3.17         (~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X48)))
% 2.98/3.17          | ~ (v1_funct_1 @ X46)
% 2.98/3.17          | ~ (v1_funct_1 @ X49)
% 2.98/3.17          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 2.98/3.17          | ((k1_partfun1 @ X47 @ X48 @ X50 @ X51 @ X46 @ X49)
% 2.98/3.17              = (k5_relat_1 @ X46 @ X49)))),
% 2.98/3.17      inference('cnf', [status(esa)], [redefinition_k1_partfun1])).
% 2.98/3.17  thf('34', plain,
% 2.98/3.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.98/3.17         (((k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0)
% 2.98/3.17            = (k5_relat_1 @ sk_C_1 @ X0))
% 2.98/3.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.98/3.17          | ~ (v1_funct_1 @ X0)
% 2.98/3.17          | ~ (v1_funct_1 @ sk_C_1))),
% 2.98/3.17      inference('sup-', [status(thm)], ['32', '33'])).
% 2.98/3.17  thf('35', plain, ((v1_funct_1 @ sk_C_1)),
% 2.98/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.98/3.17  thf('36', plain,
% 2.98/3.17      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.98/3.17         (((k1_partfun1 @ sk_A @ sk_B_1 @ X2 @ X1 @ sk_C_1 @ X0)
% 2.98/3.17            = (k5_relat_1 @ sk_C_1 @ X0))
% 2.98/3.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1)))
% 2.98/3.17          | ~ (v1_funct_1 @ X0))),
% 2.98/3.17      inference('demod', [status(thm)], ['34', '35'])).
% 2.98/3.17  thf('37', plain,
% 2.98/3.17      ((~ (v1_funct_1 @ sk_D)
% 2.98/3.17        | ((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 2.98/3.17            = (k5_relat_1 @ sk_C_1 @ sk_D)))),
% 2.98/3.17      inference('sup-', [status(thm)], ['31', '36'])).
% 2.98/3.17  thf('38', plain, ((v1_funct_1 @ sk_D)),
% 2.98/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.98/3.17  thf('39', plain,
% 2.98/3.17      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 2.98/3.17         = (k5_relat_1 @ sk_C_1 @ sk_D))),
% 2.98/3.17      inference('demod', [status(thm)], ['37', '38'])).
% 2.98/3.17  thf('40', plain,
% 2.98/3.17      ((m1_subset_1 @ (k5_relat_1 @ sk_C_1 @ sk_D) @ 
% 2.98/3.17        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.98/3.17      inference('demod', [status(thm)], ['29', '30', '39'])).
% 2.98/3.17  thf(cc2_relat_1, axiom,
% 2.98/3.17    (![A:$i]:
% 2.98/3.17     ( ( v1_relat_1 @ A ) =>
% 2.98/3.17       ( ![B:$i]:
% 2.98/3.17         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 2.98/3.17  thf('41', plain,
% 2.98/3.17      (![X18 : $i, X19 : $i]:
% 2.98/3.17         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 2.98/3.17          | (v1_relat_1 @ X18)
% 2.98/3.17          | ~ (v1_relat_1 @ X19))),
% 2.98/3.17      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.98/3.17  thf('42', plain,
% 2.98/3.17      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))
% 2.98/3.17        | (v1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D)))),
% 2.98/3.17      inference('sup-', [status(thm)], ['40', '41'])).
% 2.98/3.17  thf(fc6_relat_1, axiom,
% 2.98/3.17    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 2.98/3.17  thf('43', plain,
% 2.98/3.17      (![X22 : $i, X23 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X22 @ X23))),
% 2.98/3.17      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.98/3.17  thf('44', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D))),
% 2.98/3.17      inference('demod', [status(thm)], ['42', '43'])).
% 2.98/3.17  thf(t45_relat_1, axiom,
% 2.98/3.17    (![A:$i]:
% 2.98/3.17     ( ( v1_relat_1 @ A ) =>
% 2.98/3.17       ( ![B:$i]:
% 2.98/3.17         ( ( v1_relat_1 @ B ) =>
% 2.98/3.17           ( r1_tarski @
% 2.98/3.17             ( k2_relat_1 @ ( k5_relat_1 @ A @ B ) ) @ ( k2_relat_1 @ B ) ) ) ) ))).
% 2.98/3.17  thf('45', plain,
% 2.98/3.17      (![X24 : $i, X25 : $i]:
% 2.98/3.17         (~ (v1_relat_1 @ X24)
% 2.98/3.17          | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ X25 @ X24)) @ 
% 2.98/3.17             (k2_relat_1 @ X24))
% 2.98/3.17          | ~ (v1_relat_1 @ X25))),
% 2.98/3.17      inference('cnf', [status(esa)], [t45_relat_1])).
% 2.98/3.17  thf(d19_relat_1, axiom,
% 2.98/3.17    (![A:$i,B:$i]:
% 2.98/3.17     ( ( v1_relat_1 @ B ) =>
% 2.98/3.17       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 2.98/3.17  thf('46', plain,
% 2.98/3.17      (![X20 : $i, X21 : $i]:
% 2.98/3.17         (~ (r1_tarski @ (k2_relat_1 @ X20) @ X21)
% 2.98/3.17          | (v5_relat_1 @ X20 @ X21)
% 2.98/3.17          | ~ (v1_relat_1 @ X20))),
% 2.98/3.17      inference('cnf', [status(esa)], [d19_relat_1])).
% 2.98/3.17  thf('47', plain,
% 2.98/3.17      (![X0 : $i, X1 : $i]:
% 2.98/3.17         (~ (v1_relat_1 @ X1)
% 2.98/3.17          | ~ (v1_relat_1 @ X0)
% 2.98/3.17          | ~ (v1_relat_1 @ (k5_relat_1 @ X1 @ X0))
% 2.98/3.17          | (v5_relat_1 @ (k5_relat_1 @ X1 @ X0) @ (k2_relat_1 @ X0)))),
% 2.98/3.17      inference('sup-', [status(thm)], ['45', '46'])).
% 2.98/3.17  thf('48', plain,
% 2.98/3.17      (((v5_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D) @ (k2_relat_1 @ sk_D))
% 2.98/3.17        | ~ (v1_relat_1 @ sk_D)
% 2.98/3.17        | ~ (v1_relat_1 @ sk_C_1))),
% 2.98/3.17      inference('sup-', [status(thm)], ['44', '47'])).
% 2.98/3.17  thf('49', plain,
% 2.98/3.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 2.98/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.98/3.17  thf('50', plain,
% 2.98/3.17      (![X18 : $i, X19 : $i]:
% 2.98/3.17         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 2.98/3.17          | (v1_relat_1 @ X18)
% 2.98/3.17          | ~ (v1_relat_1 @ X19))),
% 2.98/3.17      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.98/3.17  thf('51', plain,
% 2.98/3.17      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)) | (v1_relat_1 @ sk_D))),
% 2.98/3.17      inference('sup-', [status(thm)], ['49', '50'])).
% 2.98/3.17  thf('52', plain,
% 2.98/3.17      (![X22 : $i, X23 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X22 @ X23))),
% 2.98/3.17      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.98/3.17  thf('53', plain, ((v1_relat_1 @ sk_D)),
% 2.98/3.17      inference('demod', [status(thm)], ['51', '52'])).
% 2.98/3.17  thf('54', plain,
% 2.98/3.17      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.98/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.98/3.17  thf('55', plain,
% 2.98/3.17      (![X18 : $i, X19 : $i]:
% 2.98/3.17         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ X19))
% 2.98/3.17          | (v1_relat_1 @ X18)
% 2.98/3.17          | ~ (v1_relat_1 @ X19))),
% 2.98/3.17      inference('cnf', [status(esa)], [cc2_relat_1])).
% 2.98/3.17  thf('56', plain,
% 2.98/3.17      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C_1))),
% 2.98/3.17      inference('sup-', [status(thm)], ['54', '55'])).
% 2.98/3.17  thf('57', plain,
% 2.98/3.17      (![X22 : $i, X23 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X22 @ X23))),
% 2.98/3.17      inference('cnf', [status(esa)], [fc6_relat_1])).
% 2.98/3.17  thf('58', plain, ((v1_relat_1 @ sk_C_1)),
% 2.98/3.17      inference('demod', [status(thm)], ['56', '57'])).
% 2.98/3.17  thf('59', plain,
% 2.98/3.17      ((v5_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D) @ (k2_relat_1 @ sk_D))),
% 2.98/3.17      inference('demod', [status(thm)], ['48', '53', '58'])).
% 2.98/3.17  thf('60', plain,
% 2.98/3.17      (![X20 : $i, X21 : $i]:
% 2.98/3.17         (~ (v5_relat_1 @ X20 @ X21)
% 2.98/3.17          | (r1_tarski @ (k2_relat_1 @ X20) @ X21)
% 2.98/3.17          | ~ (v1_relat_1 @ X20))),
% 2.98/3.17      inference('cnf', [status(esa)], [d19_relat_1])).
% 2.98/3.17  thf('61', plain,
% 2.98/3.17      ((~ (v1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D))
% 2.98/3.17        | (r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D)) @ 
% 2.98/3.17           (k2_relat_1 @ sk_D)))),
% 2.98/3.17      inference('sup-', [status(thm)], ['59', '60'])).
% 2.98/3.17  thf('62', plain, ((v1_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D))),
% 2.98/3.17      inference('demod', [status(thm)], ['42', '43'])).
% 2.98/3.17  thf('63', plain,
% 2.98/3.17      ((r1_tarski @ (k2_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D)) @ 
% 2.98/3.17        (k2_relat_1 @ sk_D))),
% 2.98/3.17      inference('demod', [status(thm)], ['61', '62'])).
% 2.98/3.17  thf('64', plain,
% 2.98/3.17      (![X7 : $i, X9 : $i]:
% 2.98/3.17         (((X7) = (X9)) | ~ (r1_tarski @ X9 @ X7) | ~ (r1_tarski @ X7 @ X9))),
% 2.98/3.17      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.98/3.17  thf('65', plain,
% 2.98/3.17      ((~ (r1_tarski @ (k2_relat_1 @ sk_D) @ 
% 2.98/3.17           (k2_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D)))
% 2.98/3.17        | ((k2_relat_1 @ sk_D) = (k2_relat_1 @ (k5_relat_1 @ sk_C_1 @ sk_D))))),
% 2.98/3.17      inference('sup-', [status(thm)], ['63', '64'])).
% 2.98/3.17  thf('66', plain,
% 2.98/3.17      ((r2_relset_1 @ sk_A @ sk_A @ 
% 2.98/3.17        (k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D) @ 
% 2.98/3.17        (k6_partfun1 @ sk_A))),
% 2.98/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.98/3.17  thf('67', plain,
% 2.98/3.17      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 2.98/3.17         = (k5_relat_1 @ sk_C_1 @ sk_D))),
% 2.98/3.17      inference('demod', [status(thm)], ['37', '38'])).
% 2.98/3.17  thf('68', plain,
% 2.98/3.17      ((r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C_1 @ sk_D) @ 
% 2.98/3.17        (k6_partfun1 @ sk_A))),
% 2.98/3.17      inference('demod', [status(thm)], ['66', '67'])).
% 2.98/3.17  thf('69', plain,
% 2.98/3.17      ((m1_subset_1 @ (k5_relat_1 @ sk_C_1 @ sk_D) @ 
% 2.98/3.17        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 2.98/3.17      inference('demod', [status(thm)], ['29', '30', '39'])).
% 2.98/3.17  thf(redefinition_r2_relset_1, axiom,
% 2.98/3.17    (![A:$i,B:$i,C:$i,D:$i]:
% 2.98/3.17     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 2.98/3.17         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.98/3.17       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 2.98/3.17  thf('70', plain,
% 2.98/3.17      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 2.98/3.17         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 2.98/3.17          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 2.98/3.17          | ((X33) = (X36))
% 2.98/3.17          | ~ (r2_relset_1 @ X34 @ X35 @ X33 @ X36))),
% 2.98/3.17      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 2.98/3.17  thf('71', plain,
% 2.98/3.17      (![X0 : $i]:
% 2.98/3.17         (~ (r2_relset_1 @ sk_A @ sk_A @ (k5_relat_1 @ sk_C_1 @ sk_D) @ X0)
% 2.98/3.17          | ((k5_relat_1 @ sk_C_1 @ sk_D) = (X0))
% 2.98/3.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 2.98/3.17      inference('sup-', [status(thm)], ['69', '70'])).
% 2.98/3.17  thf('72', plain,
% 2.98/3.17      ((~ (m1_subset_1 @ (k6_partfun1 @ sk_A) @ 
% 2.98/3.17           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 2.98/3.17        | ((k5_relat_1 @ sk_C_1 @ sk_D) = (k6_partfun1 @ sk_A)))),
% 2.98/3.17      inference('sup-', [status(thm)], ['68', '71'])).
% 2.98/3.17  thf('73', plain,
% 2.98/3.17      (![X37 : $i]:
% 2.98/3.17         (m1_subset_1 @ (k6_partfun1 @ X37) @ 
% 2.98/3.17          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X37)))),
% 2.98/3.17      inference('demod', [status(thm)], ['1', '2'])).
% 2.98/3.17  thf('74', plain, (((k5_relat_1 @ sk_C_1 @ sk_D) = (k6_partfun1 @ sk_A))),
% 2.98/3.17      inference('demod', [status(thm)], ['72', '73'])).
% 2.98/3.17  thf(t71_relat_1, axiom,
% 2.98/3.17    (![A:$i]:
% 2.98/3.17     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 2.98/3.17       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 2.98/3.17  thf('75', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X27)) = (X27))),
% 2.98/3.17      inference('cnf', [status(esa)], [t71_relat_1])).
% 2.98/3.17  thf('76', plain, (![X52 : $i]: ((k6_partfun1 @ X52) = (k6_relat_1 @ X52))),
% 2.98/3.17      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 2.98/3.17  thf('77', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X27)) = (X27))),
% 2.98/3.17      inference('demod', [status(thm)], ['75', '76'])).
% 2.98/3.17  thf('78', plain,
% 2.98/3.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 2.98/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.98/3.17  thf(cc2_relset_1, axiom,
% 2.98/3.17    (![A:$i,B:$i,C:$i]:
% 2.98/3.17     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.98/3.17       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.98/3.17  thf('79', plain,
% 2.98/3.17      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.98/3.17         ((v5_relat_1 @ X30 @ X32)
% 2.98/3.17          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 2.98/3.17      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.98/3.17  thf('80', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 2.98/3.17      inference('sup-', [status(thm)], ['78', '79'])).
% 2.98/3.17  thf('81', plain,
% 2.98/3.17      (![X20 : $i, X21 : $i]:
% 2.98/3.17         (~ (v5_relat_1 @ X20 @ X21)
% 2.98/3.17          | (r1_tarski @ (k2_relat_1 @ X20) @ X21)
% 2.98/3.17          | ~ (v1_relat_1 @ X20))),
% 2.98/3.17      inference('cnf', [status(esa)], [d19_relat_1])).
% 2.98/3.17  thf('82', plain,
% 2.98/3.17      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 2.98/3.17      inference('sup-', [status(thm)], ['80', '81'])).
% 2.98/3.17  thf('83', plain, ((v1_relat_1 @ sk_D)),
% 2.98/3.17      inference('demod', [status(thm)], ['51', '52'])).
% 2.98/3.17  thf('84', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 2.98/3.17      inference('demod', [status(thm)], ['82', '83'])).
% 2.98/3.17  thf('85', plain, (((k5_relat_1 @ sk_C_1 @ sk_D) = (k6_partfun1 @ sk_A))),
% 2.98/3.17      inference('demod', [status(thm)], ['72', '73'])).
% 2.98/3.17  thf('86', plain, (![X27 : $i]: ((k2_relat_1 @ (k6_partfun1 @ X27)) = (X27))),
% 2.98/3.17      inference('demod', [status(thm)], ['75', '76'])).
% 2.98/3.17  thf('87', plain, (((k2_relat_1 @ sk_D) = (sk_A))),
% 2.98/3.17      inference('demod', [status(thm)], ['65', '74', '77', '84', '85', '86'])).
% 2.98/3.17  thf(d3_funct_2, axiom,
% 2.98/3.17    (![A:$i,B:$i]:
% 2.98/3.17     ( ( ( v1_relat_1 @ B ) & ( v5_relat_1 @ B @ A ) ) =>
% 2.98/3.17       ( ( v2_funct_2 @ B @ A ) <=> ( ( k2_relat_1 @ B ) = ( A ) ) ) ))).
% 2.98/3.17  thf('88', plain,
% 2.98/3.17      (![X38 : $i, X39 : $i]:
% 2.98/3.17         (((k2_relat_1 @ X39) != (X38))
% 2.98/3.17          | (v2_funct_2 @ X39 @ X38)
% 2.98/3.17          | ~ (v5_relat_1 @ X39 @ X38)
% 2.98/3.17          | ~ (v1_relat_1 @ X39))),
% 2.98/3.17      inference('cnf', [status(esa)], [d3_funct_2])).
% 2.98/3.17  thf('89', plain,
% 2.98/3.17      (![X39 : $i]:
% 2.98/3.17         (~ (v1_relat_1 @ X39)
% 2.98/3.17          | ~ (v5_relat_1 @ X39 @ (k2_relat_1 @ X39))
% 2.98/3.17          | (v2_funct_2 @ X39 @ (k2_relat_1 @ X39)))),
% 2.98/3.17      inference('simplify', [status(thm)], ['88'])).
% 2.98/3.17  thf('90', plain,
% 2.98/3.17      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 2.98/3.17      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.98/3.17  thf('91', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 2.98/3.17      inference('simplify', [status(thm)], ['90'])).
% 2.98/3.17  thf('92', plain,
% 2.98/3.17      (![X20 : $i, X21 : $i]:
% 2.98/3.17         (~ (r1_tarski @ (k2_relat_1 @ X20) @ X21)
% 2.98/3.17          | (v5_relat_1 @ X20 @ X21)
% 2.98/3.17          | ~ (v1_relat_1 @ X20))),
% 2.98/3.17      inference('cnf', [status(esa)], [d19_relat_1])).
% 2.98/3.17  thf('93', plain,
% 2.98/3.17      (![X0 : $i]:
% 2.98/3.17         (~ (v1_relat_1 @ X0) | (v5_relat_1 @ X0 @ (k2_relat_1 @ X0)))),
% 2.98/3.17      inference('sup-', [status(thm)], ['91', '92'])).
% 2.98/3.17  thf('94', plain,
% 2.98/3.17      (![X39 : $i]:
% 2.98/3.17         ((v2_funct_2 @ X39 @ (k2_relat_1 @ X39)) | ~ (v1_relat_1 @ X39))),
% 2.98/3.17      inference('clc', [status(thm)], ['89', '93'])).
% 2.98/3.17  thf('95', plain, (((v2_funct_2 @ sk_D @ sk_A) | ~ (v1_relat_1 @ sk_D))),
% 2.98/3.17      inference('sup+', [status(thm)], ['87', '94'])).
% 2.98/3.17  thf('96', plain, ((v1_relat_1 @ sk_D)),
% 2.98/3.17      inference('demod', [status(thm)], ['51', '52'])).
% 2.98/3.17  thf('97', plain, ((v2_funct_2 @ sk_D @ sk_A)),
% 2.98/3.17      inference('demod', [status(thm)], ['95', '96'])).
% 2.98/3.17  thf('98', plain,
% 2.98/3.17      ((~ (v2_funct_2 @ sk_D @ sk_A)) <= (~ ((v2_funct_2 @ sk_D @ sk_A)))),
% 2.98/3.17      inference('split', [status(esa)], ['15'])).
% 2.98/3.17  thf('99', plain, (((v2_funct_2 @ sk_D @ sk_A))),
% 2.98/3.17      inference('sup-', [status(thm)], ['97', '98'])).
% 2.98/3.17  thf('100', plain,
% 2.98/3.17      (~ ((v2_funct_1 @ sk_C_1)) | ~ ((v2_funct_2 @ sk_D @ sk_A))),
% 2.98/3.17      inference('split', [status(esa)], ['15'])).
% 2.98/3.17  thf('101', plain, (~ ((v2_funct_1 @ sk_C_1))),
% 2.98/3.17      inference('sat_resolution*', [status(thm)], ['99', '100'])).
% 2.98/3.17  thf('102', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 2.98/3.17      inference('simpl_trail', [status(thm)], ['22', '101'])).
% 2.98/3.17  thf('103', plain,
% 2.98/3.17      (![X14 : $i, X15 : $i]:
% 2.98/3.17         (~ (v1_xboole_0 @ X14) | (v1_xboole_0 @ (k2_zfmisc_1 @ X14 @ X15)))),
% 2.98/3.17      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 2.98/3.17  thf('104', plain,
% 2.98/3.17      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.98/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.98/3.17  thf('105', plain,
% 2.98/3.17      (![X16 : $i, X17 : $i]:
% 2.98/3.17         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17))
% 2.98/3.17          | (v1_xboole_0 @ X16)
% 2.98/3.17          | ~ (v1_xboole_0 @ X17))),
% 2.98/3.17      inference('cnf', [status(esa)], [cc1_subset_1])).
% 2.98/3.17  thf('106', plain,
% 2.98/3.17      ((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1))
% 2.98/3.17        | (v1_xboole_0 @ sk_C_1))),
% 2.98/3.17      inference('sup-', [status(thm)], ['104', '105'])).
% 2.98/3.17  thf('107', plain, ((~ (v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_C_1))),
% 2.98/3.17      inference('sup-', [status(thm)], ['103', '106'])).
% 2.98/3.17  thf('108', plain,
% 2.98/3.17      (((k1_partfun1 @ sk_A @ sk_B_1 @ sk_B_1 @ sk_A @ sk_C_1 @ sk_D)
% 2.98/3.17         = (k5_relat_1 @ sk_C_1 @ sk_D))),
% 2.98/3.17      inference('demod', [status(thm)], ['37', '38'])).
% 2.98/3.17  thf('109', plain,
% 2.98/3.17      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 2.98/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.98/3.17  thf(t26_funct_2, axiom,
% 2.98/3.17    (![A:$i,B:$i,C:$i,D:$i]:
% 2.98/3.17     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 2.98/3.17         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.98/3.17       ( ![E:$i]:
% 2.98/3.17         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ B @ C ) & 
% 2.98/3.17             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 2.98/3.17           ( ( v2_funct_1 @ ( k1_partfun1 @ A @ B @ B @ C @ D @ E ) ) =>
% 2.98/3.17             ( ( ( ( C ) = ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) ) | 
% 2.98/3.17               ( v2_funct_1 @ D ) ) ) ) ) ))).
% 2.98/3.17  thf('110', plain,
% 2.98/3.17      (![X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 2.98/3.17         (~ (v1_funct_1 @ X53)
% 2.98/3.17          | ~ (v1_funct_2 @ X53 @ X54 @ X55)
% 2.98/3.17          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X54 @ X55)))
% 2.98/3.17          | ~ (v2_funct_1 @ (k1_partfun1 @ X56 @ X54 @ X54 @ X55 @ X57 @ X53))
% 2.98/3.17          | (v2_funct_1 @ X57)
% 2.98/3.17          | ((X55) = (k1_xboole_0))
% 2.98/3.17          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X56 @ X54)))
% 2.98/3.17          | ~ (v1_funct_2 @ X57 @ X56 @ X54)
% 2.98/3.17          | ~ (v1_funct_1 @ X57))),
% 2.98/3.17      inference('cnf', [status(esa)], [t26_funct_2])).
% 2.98/3.17  thf('111', plain,
% 2.98/3.17      (![X0 : $i, X1 : $i]:
% 2.98/3.17         (~ (v1_funct_1 @ X0)
% 2.98/3.17          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 2.98/3.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 2.98/3.17          | ((sk_A) = (k1_xboole_0))
% 2.98/3.17          | (v2_funct_1 @ X0)
% 2.98/3.17          | ~ (v2_funct_1 @ 
% 2.98/3.17               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D))
% 2.98/3.17          | ~ (v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)
% 2.98/3.17          | ~ (v1_funct_1 @ sk_D))),
% 2.98/3.17      inference('sup-', [status(thm)], ['109', '110'])).
% 2.98/3.17  thf('112', plain, ((v1_funct_2 @ sk_D @ sk_B_1 @ sk_A)),
% 2.98/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.98/3.17  thf('113', plain, ((v1_funct_1 @ sk_D)),
% 2.98/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.98/3.17  thf('114', plain,
% 2.98/3.17      (![X0 : $i, X1 : $i]:
% 2.98/3.17         (~ (v1_funct_1 @ X0)
% 2.98/3.17          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 2.98/3.17          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 2.98/3.17          | ((sk_A) = (k1_xboole_0))
% 2.98/3.17          | (v2_funct_1 @ X0)
% 2.98/3.17          | ~ (v2_funct_1 @ 
% 2.98/3.17               (k1_partfun1 @ X1 @ sk_B_1 @ sk_B_1 @ sk_A @ X0 @ sk_D)))),
% 2.98/3.17      inference('demod', [status(thm)], ['111', '112', '113'])).
% 2.98/3.17  thf('115', plain,
% 2.98/3.17      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C_1 @ sk_D))
% 2.98/3.17        | (v2_funct_1 @ sk_C_1)
% 2.98/3.17        | ((sk_A) = (k1_xboole_0))
% 2.98/3.17        | ~ (m1_subset_1 @ sk_C_1 @ 
% 2.98/3.17             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 2.98/3.17        | ~ (v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)
% 2.98/3.17        | ~ (v1_funct_1 @ sk_C_1))),
% 2.98/3.17      inference('sup-', [status(thm)], ['108', '114'])).
% 2.98/3.17  thf('116', plain,
% 2.98/3.17      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 2.98/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.98/3.17  thf('117', plain, ((v1_funct_2 @ sk_C_1 @ sk_A @ sk_B_1)),
% 2.98/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.98/3.17  thf('118', plain, ((v1_funct_1 @ sk_C_1)),
% 2.98/3.17      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.98/3.17  thf('119', plain,
% 2.98/3.17      ((~ (v2_funct_1 @ (k5_relat_1 @ sk_C_1 @ sk_D))
% 2.98/3.17        | (v2_funct_1 @ sk_C_1)
% 2.98/3.17        | ((sk_A) = (k1_xboole_0)))),
% 2.98/3.17      inference('demod', [status(thm)], ['115', '116', '117', '118'])).
% 2.98/3.17  thf('120', plain, (((k5_relat_1 @ sk_C_1 @ sk_D) = (k6_partfun1 @ sk_A))),
% 2.98/3.17      inference('demod', [status(thm)], ['72', '73'])).
% 2.98/3.17  thf('121', plain, (![X29 : $i]: (v2_funct_1 @ (k6_partfun1 @ X29))),
% 2.98/3.17      inference('demod', [status(thm)], ['18', '19'])).
% 2.98/3.17  thf('122', plain, (((v2_funct_1 @ sk_C_1) | ((sk_A) = (k1_xboole_0)))),
% 2.98/3.17      inference('demod', [status(thm)], ['119', '120', '121'])).
% 2.98/3.17  thf('123', plain, ((~ (v2_funct_1 @ sk_C_1)) <= (~ ((v2_funct_1 @ sk_C_1)))),
% 2.98/3.17      inference('split', [status(esa)], ['15'])).
% 2.98/3.17  thf('124', plain, (~ ((v2_funct_1 @ sk_C_1))),
% 2.98/3.17      inference('sat_resolution*', [status(thm)], ['99', '100'])).
% 2.98/3.17  thf('125', plain, (~ (v2_funct_1 @ sk_C_1)),
% 2.98/3.17      inference('simpl_trail', [status(thm)], ['123', '124'])).
% 2.98/3.17  thf('126', plain, (((sk_A) = (k1_xboole_0))),
% 2.98/3.17      inference('clc', [status(thm)], ['122', '125'])).
% 2.98/3.17  thf('127', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 2.98/3.17      inference('simplify', [status(thm)], ['90'])).
% 2.98/3.17  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 2.98/3.17  thf('128', plain, (![X11 : $i]: (r1_xboole_0 @ X11 @ k1_xboole_0)),
% 2.98/3.17      inference('cnf', [status(esa)], [t65_xboole_1])).
% 2.98/3.17  thf(t69_xboole_1, axiom,
% 2.98/3.17    (![A:$i,B:$i]:
% 2.98/3.17     ( ( ~( v1_xboole_0 @ B ) ) =>
% 2.98/3.17       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 2.98/3.17  thf('129', plain,
% 2.98/3.17      (![X12 : $i, X13 : $i]:
% 2.98/3.17         (~ (r1_xboole_0 @ X12 @ X13)
% 2.98/3.17          | ~ (r1_tarski @ X12 @ X13)
% 2.98/3.17          | (v1_xboole_0 @ X12))),
% 2.98/3.17      inference('cnf', [status(esa)], [t69_xboole_1])).
% 2.98/3.17  thf('130', plain,
% 2.98/3.17      (![X0 : $i]: ((v1_xboole_0 @ X0) | ~ (r1_tarski @ X0 @ k1_xboole_0))),
% 2.98/3.17      inference('sup-', [status(thm)], ['128', '129'])).
% 2.98/3.17  thf('131', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.98/3.17      inference('sup-', [status(thm)], ['127', '130'])).
% 2.98/3.17  thf('132', plain, ((v1_xboole_0 @ sk_C_1)),
% 2.98/3.17      inference('demod', [status(thm)], ['107', '126', '131'])).
% 2.98/3.17  thf('133', plain, ($false), inference('demod', [status(thm)], ['102', '132'])).
% 2.98/3.17  
% 2.98/3.17  % SZS output end Refutation
% 2.98/3.17  
% 2.98/3.18  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
