%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RtWxsoqCXQ

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:49 EST 2020

% Result     : Theorem 0.36s
% Output     : Refutation 0.36s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 211 expanded)
%              Number of leaves         :   36 (  72 expanded)
%              Depth                    :   13
%              Number of atoms          :  733 (2297 expanded)
%              Number of equality atoms :   32 (  45 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_wellord2_type,type,(
    k1_wellord2: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(t4_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_relat_1 @ B )
          & ( v1_funct_1 @ B ) )
       => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
         => ( ( v1_funct_1 @ B )
            & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t4_funct_2])).

thf('0',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('3',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X18 ) @ X19 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X18 ) @ X20 )
      | ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['0','4'])).

thf('6',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('8',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k1_relset_1 @ X16 @ X17 @ X15 )
        = ( k1_relat_1 @ X15 ) )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('9',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_B ) @ sk_A @ sk_B )
    = ( k1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf('10',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( X29
       != ( k1_relset_1 @ X29 @ X30 @ X31 ) )
      | ( v1_funct_2 @ X31 @ X29 @ X30 )
      | ~ ( zip_tseitin_1 @ X31 @ X30 @ X29 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('11',plain,
    ( ( ( k1_relat_1 @ sk_B )
     != ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,
    ( ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
   <= ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(split,[status(esa)],['13'])).

thf('15',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( v1_funct_1 @ sk_B )
   <= ~ ( v1_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['13'])).

thf('17',plain,(
    v1_funct_1 @ sk_B ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('19',plain,
    ( ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
   <= ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ) ),
    inference(split,[status(esa)],['13'])).

thf('20',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference(split,[status(esa)],['13'])).

thf('22',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sat_resolution*',[status(thm)],['17','20','21'])).

thf('23',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['14','22'])).

thf('24',plain,(
    ~ ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['12','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_4,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('26',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( zip_tseitin_0 @ X32 @ X33 )
      | ( zip_tseitin_1 @ X34 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('27',plain,
    ( ( zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) )
    | ~ ( zip_tseitin_0 @ sk_A @ ( k1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X27: $i,X28: $i] :
      ( ( zip_tseitin_0 @ X27 @ X28 )
      | ( X27 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_4])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('29',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( zip_tseitin_0 @ X0 @ X2 ) ) ),
    inference('sup+',[status(thm)],['28','29'])).

thf('31',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_B ) @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('32',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r1_tarski @ X3 @ X4 )
      | ~ ( r1_tarski @ X4 @ X5 )
      | ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 )
      | ~ ( r1_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X1 )
      | ( r1_tarski @ ( k2_relat_1 @ sk_B ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['30','33'])).

thf('35',plain,(
    ! [X6: $i] :
      ( r1_tarski @ k1_xboole_0 @ X6 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('36',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( ( k2_relat_1 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('39',plain,(
    ! [X11: $i] :
      ( ( ( k2_relat_1 @ X11 )
       != k1_xboole_0 )
      | ( ( k1_relat_1 @ X11 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_A @ X0 )
      | ~ ( v1_relat_1 @ sk_B )
      | ( ( k1_relat_1 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_A @ X0 )
      | ( ( k1_relat_1 @ sk_B )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_B )
        = k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_A @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('47',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X26 ) ) )
      | ( v1_partfun1 @ X25 @ X24 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_partfun1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ( zip_tseitin_0 @ sk_A @ X0 )
      | ( v1_partfun1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
      | ~ ( v1_relat_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','48'])).

thf(fc1_wellord2,axiom,
    ( ( v1_xboole_0 @ ( k1_wellord2 @ k1_xboole_0 ) )
    & ( v1_relat_1 @ ( k1_wellord2 @ k1_xboole_0 ) ) )).

thf('50',plain,(
    v1_xboole_0 @ ( k1_wellord2 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[fc1_wellord2])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('51',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('52',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_xboole_0 @ X12 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X12 ) ) )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['50','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( zip_tseitin_0 @ sk_A @ X0 )
      | ( v1_partfun1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['49','54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_B ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['5','6'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('58',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_partfun1 @ X21 @ X22 )
      | ( v1_funct_2 @ X21 @ X22 @ X23 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('59',plain,
    ( ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( v1_partfun1 @ sk_B @ ( k1_relat_1 @ sk_B ) )
    | ~ ( v1_funct_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A )
    | ~ ( v1_partfun1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ~ ( v1_funct_2 @ sk_B @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference(simpl_trail,[status(thm)],['14','22'])).

thf('63',plain,(
    ~ ( v1_partfun1 @ sk_B @ ( k1_relat_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( zip_tseitin_0 @ sk_A @ X0 ) ),
    inference('sup-',[status(thm)],['56','63'])).

thf('65',plain,(
    zip_tseitin_1 @ sk_B @ sk_A @ ( k1_relat_1 @ sk_B ) ),
    inference(demod,[status(thm)],['27','64'])).

thf('66',plain,(
    $false ),
    inference(demod,[status(thm)],['24','65'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RtWxsoqCXQ
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:07:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.36/0.59  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.36/0.59  % Solved by: fo/fo7.sh
% 0.36/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.36/0.59  % done 164 iterations in 0.135s
% 0.36/0.59  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.36/0.59  % SZS output start Refutation
% 0.36/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.36/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.36/0.59  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.36/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.36/0.59  thf(k1_wellord2_type, type, k1_wellord2: $i > $i).
% 0.36/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.36/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.36/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.36/0.59  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.36/0.59  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.36/0.59  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.36/0.59  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.36/0.59  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.36/0.59  thf(sk_B_type, type, sk_B: $i).
% 0.36/0.59  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.36/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.36/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.36/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.36/0.59  thf(t4_funct_2, conjecture,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.36/0.59       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.36/0.59         ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.36/0.59           ( m1_subset_1 @
% 0.36/0.59             B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ))).
% 0.36/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.36/0.59    (~( ![A:$i,B:$i]:
% 0.36/0.59        ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.36/0.59          ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.36/0.59            ( ( v1_funct_1 @ B ) & 
% 0.36/0.59              ( v1_funct_2 @ B @ ( k1_relat_1 @ B ) @ A ) & 
% 0.36/0.59              ( m1_subset_1 @
% 0.36/0.59                B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ B ) @ A ) ) ) ) ) ) )),
% 0.36/0.59    inference('cnf.neg', [status(esa)], [t4_funct_2])).
% 0.36/0.59  thf('0', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(d10_xboole_0, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.36/0.59  thf('1', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.36/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.59  thf('2', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.36/0.59      inference('simplify', [status(thm)], ['1'])).
% 0.36/0.59  thf(t11_relset_1, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i]:
% 0.36/0.59     ( ( v1_relat_1 @ C ) =>
% 0.36/0.59       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.36/0.59           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.36/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.36/0.59  thf('3', plain,
% 0.36/0.59      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.36/0.59         (~ (r1_tarski @ (k1_relat_1 @ X18) @ X19)
% 0.36/0.59          | ~ (r1_tarski @ (k2_relat_1 @ X18) @ X20)
% 0.36/0.59          | (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.36/0.59          | ~ (v1_relat_1 @ X18))),
% 0.36/0.59      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.36/0.59  thf('4', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         (~ (v1_relat_1 @ X0)
% 0.36/0.59          | (m1_subset_1 @ X0 @ 
% 0.36/0.59             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.36/0.59          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.36/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.59  thf('5', plain,
% 0.36/0.59      (((m1_subset_1 @ sk_B @ 
% 0.36/0.59         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))
% 0.36/0.59        | ~ (v1_relat_1 @ sk_B))),
% 0.36/0.59      inference('sup-', [status(thm)], ['0', '4'])).
% 0.36/0.59  thf('6', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('7', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_B @ 
% 0.36/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.36/0.59      inference('demod', [status(thm)], ['5', '6'])).
% 0.36/0.59  thf(redefinition_k1_relset_1, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i]:
% 0.36/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.59       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.36/0.59  thf('8', plain,
% 0.36/0.59      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.36/0.59         (((k1_relset_1 @ X16 @ X17 @ X15) = (k1_relat_1 @ X15))
% 0.36/0.59          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.36/0.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.36/0.59  thf('9', plain,
% 0.36/0.59      (((k1_relset_1 @ (k1_relat_1 @ sk_B) @ sk_A @ sk_B) = (k1_relat_1 @ sk_B))),
% 0.36/0.59      inference('sup-', [status(thm)], ['7', '8'])).
% 0.36/0.59  thf(d1_funct_2, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i]:
% 0.36/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.59       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.36/0.59           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.36/0.59             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.36/0.59         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.59           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.36/0.59             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.36/0.59  thf(zf_stmt_1, axiom,
% 0.36/0.59    (![C:$i,B:$i,A:$i]:
% 0.36/0.59     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.36/0.59       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.36/0.59  thf('10', plain,
% 0.36/0.59      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.36/0.59         (((X29) != (k1_relset_1 @ X29 @ X30 @ X31))
% 0.36/0.59          | (v1_funct_2 @ X31 @ X29 @ X30)
% 0.36/0.59          | ~ (zip_tseitin_1 @ X31 @ X30 @ X29))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.36/0.59  thf('11', plain,
% 0.36/0.59      ((((k1_relat_1 @ sk_B) != (k1_relat_1 @ sk_B))
% 0.36/0.59        | ~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 0.36/0.59        | (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.36/0.59      inference('sup-', [status(thm)], ['9', '10'])).
% 0.36/0.59  thf('12', plain,
% 0.36/0.59      (((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.36/0.59        | ~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.36/0.59      inference('simplify', [status(thm)], ['11'])).
% 0.36/0.59  thf('13', plain,
% 0.36/0.59      ((~ (v1_funct_1 @ sk_B)
% 0.36/0.59        | ~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.36/0.59        | ~ (m1_subset_1 @ sk_B @ 
% 0.36/0.59             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('14', plain,
% 0.36/0.59      ((~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))
% 0.36/0.59         <= (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.36/0.59      inference('split', [status(esa)], ['13'])).
% 0.36/0.59  thf('15', plain, ((v1_funct_1 @ sk_B)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('16', plain, ((~ (v1_funct_1 @ sk_B)) <= (~ ((v1_funct_1 @ sk_B)))),
% 0.36/0.59      inference('split', [status(esa)], ['13'])).
% 0.36/0.59  thf('17', plain, (((v1_funct_1 @ sk_B))),
% 0.36/0.59      inference('sup-', [status(thm)], ['15', '16'])).
% 0.36/0.59  thf('18', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_B @ 
% 0.36/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.36/0.59      inference('demod', [status(thm)], ['5', '6'])).
% 0.36/0.59  thf('19', plain,
% 0.36/0.59      ((~ (m1_subset_1 @ sk_B @ 
% 0.36/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))
% 0.36/0.59         <= (~
% 0.36/0.59             ((m1_subset_1 @ sk_B @ 
% 0.36/0.59               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))))),
% 0.36/0.59      inference('split', [status(esa)], ['13'])).
% 0.36/0.59  thf('20', plain,
% 0.36/0.59      (((m1_subset_1 @ sk_B @ 
% 0.36/0.59         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A))))),
% 0.36/0.59      inference('sup-', [status(thm)], ['18', '19'])).
% 0.36/0.59  thf('21', plain,
% 0.36/0.59      (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)) | 
% 0.36/0.59       ~
% 0.36/0.59       ((m1_subset_1 @ sk_B @ 
% 0.36/0.59         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))) | 
% 0.36/0.59       ~ ((v1_funct_1 @ sk_B))),
% 0.36/0.59      inference('split', [status(esa)], ['13'])).
% 0.36/0.59  thf('22', plain, (~ ((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.36/0.59      inference('sat_resolution*', [status(thm)], ['17', '20', '21'])).
% 0.36/0.59  thf('23', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.36/0.59      inference('simpl_trail', [status(thm)], ['14', '22'])).
% 0.36/0.59  thf('24', plain, (~ (zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.36/0.59      inference('clc', [status(thm)], ['12', '23'])).
% 0.36/0.59  thf('25', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_B @ 
% 0.36/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.36/0.59      inference('demod', [status(thm)], ['5', '6'])).
% 0.36/0.59  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.36/0.59  thf(zf_stmt_3, type, zip_tseitin_0 : $i > $i > $o).
% 0.36/0.59  thf(zf_stmt_4, axiom,
% 0.36/0.59    (![B:$i,A:$i]:
% 0.36/0.59     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.36/0.59       ( zip_tseitin_0 @ B @ A ) ))).
% 0.36/0.59  thf(zf_stmt_5, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i]:
% 0.36/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.59       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.36/0.59         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.36/0.59           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.36/0.59             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.36/0.59  thf('26', plain,
% 0.36/0.59      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.36/0.59         (~ (zip_tseitin_0 @ X32 @ X33)
% 0.36/0.59          | (zip_tseitin_1 @ X34 @ X32 @ X33)
% 0.36/0.59          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32))))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.36/0.59  thf('27', plain,
% 0.36/0.59      (((zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))
% 0.36/0.59        | ~ (zip_tseitin_0 @ sk_A @ (k1_relat_1 @ sk_B)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['25', '26'])).
% 0.36/0.59  thf('28', plain,
% 0.36/0.59      (![X27 : $i, X28 : $i]:
% 0.36/0.59         ((zip_tseitin_0 @ X27 @ X28) | ((X27) = (k1_xboole_0)))),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_4])).
% 0.36/0.59  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.36/0.59  thf('29', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.36/0.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.59  thf('30', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.36/0.59         ((r1_tarski @ X0 @ X1) | (zip_tseitin_0 @ X0 @ X2))),
% 0.36/0.59      inference('sup+', [status(thm)], ['28', '29'])).
% 0.36/0.59  thf('31', plain, ((r1_tarski @ (k2_relat_1 @ sk_B) @ sk_A)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf(t1_xboole_1, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i]:
% 0.36/0.59     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.36/0.59       ( r1_tarski @ A @ C ) ))).
% 0.36/0.59  thf('32', plain,
% 0.36/0.59      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.36/0.59         (~ (r1_tarski @ X3 @ X4)
% 0.36/0.59          | ~ (r1_tarski @ X4 @ X5)
% 0.36/0.59          | (r1_tarski @ X3 @ X5))),
% 0.36/0.59      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.36/0.59  thf('33', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((r1_tarski @ (k2_relat_1 @ sk_B) @ X0) | ~ (r1_tarski @ sk_A @ X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['31', '32'])).
% 0.36/0.59  thf('34', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         ((zip_tseitin_0 @ sk_A @ X1) | (r1_tarski @ (k2_relat_1 @ sk_B) @ X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['30', '33'])).
% 0.36/0.59  thf('35', plain, (![X6 : $i]: (r1_tarski @ k1_xboole_0 @ X6)),
% 0.36/0.59      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.36/0.59  thf('36', plain,
% 0.36/0.59      (![X0 : $i, X2 : $i]:
% 0.36/0.59         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.36/0.59      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.36/0.59  thf('37', plain,
% 0.36/0.59      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['35', '36'])).
% 0.36/0.59  thf('38', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((zip_tseitin_0 @ sk_A @ X0) | ((k2_relat_1 @ sk_B) = (k1_xboole_0)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['34', '37'])).
% 0.36/0.59  thf(t65_relat_1, axiom,
% 0.36/0.59    (![A:$i]:
% 0.36/0.59     ( ( v1_relat_1 @ A ) =>
% 0.36/0.59       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.36/0.59         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.36/0.59  thf('39', plain,
% 0.36/0.59      (![X11 : $i]:
% 0.36/0.59         (((k2_relat_1 @ X11) != (k1_xboole_0))
% 0.36/0.59          | ((k1_relat_1 @ X11) = (k1_xboole_0))
% 0.36/0.59          | ~ (v1_relat_1 @ X11))),
% 0.36/0.59      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.36/0.59  thf('40', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (((k1_xboole_0) != (k1_xboole_0))
% 0.36/0.59          | (zip_tseitin_0 @ sk_A @ X0)
% 0.36/0.59          | ~ (v1_relat_1 @ sk_B)
% 0.36/0.59          | ((k1_relat_1 @ sk_B) = (k1_xboole_0)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['38', '39'])).
% 0.36/0.59  thf('41', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('42', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (((k1_xboole_0) != (k1_xboole_0))
% 0.36/0.59          | (zip_tseitin_0 @ sk_A @ X0)
% 0.36/0.59          | ((k1_relat_1 @ sk_B) = (k1_xboole_0)))),
% 0.36/0.59      inference('demod', [status(thm)], ['40', '41'])).
% 0.36/0.59  thf('43', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (((k1_relat_1 @ sk_B) = (k1_xboole_0)) | (zip_tseitin_0 @ sk_A @ X0))),
% 0.36/0.59      inference('simplify', [status(thm)], ['42'])).
% 0.36/0.59  thf('44', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.36/0.59      inference('simplify', [status(thm)], ['1'])).
% 0.36/0.59  thf('45', plain,
% 0.36/0.59      (![X0 : $i, X1 : $i]:
% 0.36/0.59         (~ (v1_relat_1 @ X0)
% 0.36/0.59          | (m1_subset_1 @ X0 @ 
% 0.36/0.59             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.36/0.59          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.36/0.59      inference('sup-', [status(thm)], ['2', '3'])).
% 0.36/0.59  thf('46', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((m1_subset_1 @ X0 @ 
% 0.36/0.59           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.36/0.59          | ~ (v1_relat_1 @ X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['44', '45'])).
% 0.36/0.59  thf(cc1_partfun1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( v1_xboole_0 @ A ) =>
% 0.36/0.59       ( ![C:$i]:
% 0.36/0.59         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.59           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.36/0.59  thf('47', plain,
% 0.36/0.59      (![X24 : $i, X25 : $i, X26 : $i]:
% 0.36/0.59         (~ (v1_xboole_0 @ X24)
% 0.36/0.59          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X26)))
% 0.36/0.59          | (v1_partfun1 @ X25 @ X24))),
% 0.36/0.59      inference('cnf', [status(esa)], [cc1_partfun1])).
% 0.36/0.59  thf('48', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (~ (v1_relat_1 @ X0)
% 0.36/0.59          | (v1_partfun1 @ X0 @ (k1_relat_1 @ X0))
% 0.36/0.59          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.36/0.59      inference('sup-', [status(thm)], ['46', '47'])).
% 0.36/0.59  thf('49', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.36/0.59          | (zip_tseitin_0 @ sk_A @ X0)
% 0.36/0.59          | (v1_partfun1 @ sk_B @ (k1_relat_1 @ sk_B))
% 0.36/0.59          | ~ (v1_relat_1 @ sk_B))),
% 0.36/0.59      inference('sup-', [status(thm)], ['43', '48'])).
% 0.36/0.59  thf(fc1_wellord2, axiom,
% 0.36/0.59    (( v1_xboole_0 @ ( k1_wellord2 @ k1_xboole_0 ) ) & 
% 0.36/0.59     ( v1_relat_1 @ ( k1_wellord2 @ k1_xboole_0 ) ))).
% 0.36/0.59  thf('50', plain, ((v1_xboole_0 @ (k1_wellord2 @ k1_xboole_0))),
% 0.36/0.59      inference('cnf', [status(esa)], [fc1_wellord2])).
% 0.36/0.59  thf(t4_subset_1, axiom,
% 0.36/0.59    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.36/0.59  thf('51', plain,
% 0.36/0.59      (![X7 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X7))),
% 0.36/0.59      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.36/0.59  thf(cc4_relset_1, axiom,
% 0.36/0.59    (![A:$i,B:$i]:
% 0.36/0.59     ( ( v1_xboole_0 @ A ) =>
% 0.36/0.59       ( ![C:$i]:
% 0.36/0.59         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.36/0.59           ( v1_xboole_0 @ C ) ) ) ))).
% 0.36/0.59  thf('52', plain,
% 0.36/0.59      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.36/0.59         (~ (v1_xboole_0 @ X12)
% 0.36/0.59          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X12)))
% 0.36/0.59          | (v1_xboole_0 @ X13))),
% 0.36/0.59      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.36/0.59  thf('53', plain,
% 0.36/0.59      (![X0 : $i]: ((v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 0.36/0.59      inference('sup-', [status(thm)], ['51', '52'])).
% 0.36/0.59  thf('54', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.36/0.59      inference('sup-', [status(thm)], ['50', '53'])).
% 0.36/0.59  thf('55', plain, ((v1_relat_1 @ sk_B)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('56', plain,
% 0.36/0.59      (![X0 : $i]:
% 0.36/0.59         ((zip_tseitin_0 @ sk_A @ X0)
% 0.36/0.59          | (v1_partfun1 @ sk_B @ (k1_relat_1 @ sk_B)))),
% 0.36/0.59      inference('demod', [status(thm)], ['49', '54', '55'])).
% 0.36/0.59  thf('57', plain,
% 0.36/0.59      ((m1_subset_1 @ sk_B @ 
% 0.36/0.59        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_B) @ sk_A)))),
% 0.36/0.59      inference('demod', [status(thm)], ['5', '6'])).
% 0.36/0.59  thf(cc1_funct_2, axiom,
% 0.36/0.59    (![A:$i,B:$i,C:$i]:
% 0.36/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.36/0.59       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.36/0.59         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.36/0.59  thf('58', plain,
% 0.36/0.59      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.36/0.59         (~ (v1_funct_1 @ X21)
% 0.36/0.59          | ~ (v1_partfun1 @ X21 @ X22)
% 0.36/0.59          | (v1_funct_2 @ X21 @ X22 @ X23)
% 0.36/0.59          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.36/0.59      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.36/0.59  thf('59', plain,
% 0.36/0.59      (((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.36/0.59        | ~ (v1_partfun1 @ sk_B @ (k1_relat_1 @ sk_B))
% 0.36/0.59        | ~ (v1_funct_1 @ sk_B))),
% 0.36/0.59      inference('sup-', [status(thm)], ['57', '58'])).
% 0.36/0.59  thf('60', plain, ((v1_funct_1 @ sk_B)),
% 0.36/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.36/0.59  thf('61', plain,
% 0.36/0.59      (((v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)
% 0.36/0.59        | ~ (v1_partfun1 @ sk_B @ (k1_relat_1 @ sk_B)))),
% 0.36/0.59      inference('demod', [status(thm)], ['59', '60'])).
% 0.36/0.59  thf('62', plain, (~ (v1_funct_2 @ sk_B @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.36/0.59      inference('simpl_trail', [status(thm)], ['14', '22'])).
% 0.36/0.59  thf('63', plain, (~ (v1_partfun1 @ sk_B @ (k1_relat_1 @ sk_B))),
% 0.36/0.59      inference('clc', [status(thm)], ['61', '62'])).
% 0.36/0.59  thf('64', plain, (![X0 : $i]: (zip_tseitin_0 @ sk_A @ X0)),
% 0.36/0.59      inference('sup-', [status(thm)], ['56', '63'])).
% 0.36/0.59  thf('65', plain, ((zip_tseitin_1 @ sk_B @ sk_A @ (k1_relat_1 @ sk_B))),
% 0.36/0.59      inference('demod', [status(thm)], ['27', '64'])).
% 0.36/0.59  thf('66', plain, ($false), inference('demod', [status(thm)], ['24', '65'])).
% 0.36/0.59  
% 0.36/0.59  % SZS output end Refutation
% 0.36/0.59  
% 0.36/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
