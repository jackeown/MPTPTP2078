%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R4X2cKj2v3

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:38 EST 2020

% Result     : Theorem 0.89s
% Output     : Refutation 0.89s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 193 expanded)
%              Number of leaves         :   31 (  65 expanded)
%              Depth                    :   14
%              Number of atoms          :  697 (1998 expanded)
%              Number of equality atoms :   25 (  51 expanded)
%              Maximal formula depth    :   12 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(fc10_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ) )).

thf('0',plain,(
    ! [X8: $i] :
      ( ( v1_xboole_0 @ ( k1_relat_1 @ X8 ) )
      | ~ ( v1_xboole_0 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc10_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ( X5 != X6 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['1'])).

thf('3',plain,(
    ! [X6: $i] :
      ( r1_tarski @ X6 @ X6 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X18 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X17 ) @ X19 )
      | ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('7',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X25 ) ) )
      | ( v1_partfun1 @ X24 @ X23 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_partfun1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_xboole_0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( v1_partfun1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['0','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('11',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( v1_funct_1 @ X20 )
      | ~ ( v1_partfun1 @ X20 @ X21 )
      | ( v1_funct_2 @ X20 @ X21 @ X22 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_partfun1 @ X0 @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf(t3_funct_2,conjecture,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ( v1_relat_1 @ A )
          & ( v1_funct_1 @ A ) )
       => ( ( v1_funct_1 @ A )
          & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
          & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_funct_2])).

thf('15',plain,
    ( ~ ( v1_funct_1 @ sk_A )
    | ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
   <= ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(split,[status(esa)],['15'])).

thf('17',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ~ ( v1_funct_1 @ sk_A )
   <= ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['15'])).

thf('19',plain,(
    v1_funct_1 @ sk_A ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf('21',plain,
    ( ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference(split,[status(esa)],['15'])).

thf('22',plain,
    ( ~ ( v1_relat_1 @ sk_A )
   <= ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['22','23'])).

thf('25',plain,
    ( ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) )
    | ~ ( m1_subset_1 @ sk_A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ) )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference(split,[status(esa)],['15'])).

thf('26',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference('sat_resolution*',[status(thm)],['19','24','25'])).

thf('27',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['16','26'])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ~ ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','27'])).

thf('29',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['28','29','30'])).

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
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('32',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('34',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('38',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( ( k1_relset_1 @ X15 @ X16 @ X14 )
        = ( k1_relat_1 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relset_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) @ X0 )
        = ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( X28
       != ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ~ ( zip_tseitin_1 @ X0 @ ( k2_relat_1 @ X0 ) @ ( k1_relat_1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ X0 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ~ ( v1_funct_2 @ sk_A @ ( k1_relat_1 @ sk_A ) @ ( k2_relat_1 @ sk_A ) ) ),
    inference(simpl_trail,[status(thm)],['16','26'])).

thf('46',plain,
    ( ~ ( v1_relat_1 @ sk_A )
    | ( ( k2_relat_1 @ sk_A )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,
    ( ( k2_relat_1 @ sk_A )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['2','5'])).

thf(cc4_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('50',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_xboole_0 @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X11 ) ) )
      | ( v1_xboole_0 @ X12 ) ) ),
    inference(cnf,[status(esa)],[cc4_relset_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ ( k2_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_relat_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','51'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('53',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('54',plain,(
    v1_relat_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['52','53','54'])).

thf('56',plain,(
    $false ),
    inference(demod,[status(thm)],['31','55'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.R4X2cKj2v3
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:30:03 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.89/1.10  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.89/1.10  % Solved by: fo/fo7.sh
% 0.89/1.10  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.89/1.10  % done 523 iterations in 0.642s
% 0.89/1.10  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.89/1.10  % SZS output start Refutation
% 0.89/1.10  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.89/1.10  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.89/1.10  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.89/1.10  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.89/1.10  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.89/1.10  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.89/1.10  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.89/1.10  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.89/1.10  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.89/1.10  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.89/1.10  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.89/1.10  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.89/1.10  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.89/1.10  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.89/1.10  thf(sk_A_type, type, sk_A: $i).
% 0.89/1.10  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.89/1.10  thf(fc10_relat_1, axiom,
% 0.89/1.10    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k1_relat_1 @ A ) ) ))).
% 0.89/1.10  thf('0', plain,
% 0.89/1.10      (![X8 : $i]: ((v1_xboole_0 @ (k1_relat_1 @ X8)) | ~ (v1_xboole_0 @ X8))),
% 0.89/1.10      inference('cnf', [status(esa)], [fc10_relat_1])).
% 0.89/1.10  thf(d10_xboole_0, axiom,
% 0.89/1.10    (![A:$i,B:$i]:
% 0.89/1.10     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.89/1.10  thf('1', plain,
% 0.89/1.10      (![X5 : $i, X6 : $i]: ((r1_tarski @ X5 @ X6) | ((X5) != (X6)))),
% 0.89/1.10      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.89/1.10  thf('2', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 0.89/1.10      inference('simplify', [status(thm)], ['1'])).
% 0.89/1.10  thf('3', plain, (![X6 : $i]: (r1_tarski @ X6 @ X6)),
% 0.89/1.10      inference('simplify', [status(thm)], ['1'])).
% 0.89/1.10  thf(t11_relset_1, axiom,
% 0.89/1.10    (![A:$i,B:$i,C:$i]:
% 0.89/1.10     ( ( v1_relat_1 @ C ) =>
% 0.89/1.10       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.89/1.10           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.89/1.10         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.89/1.10  thf('4', plain,
% 0.89/1.10      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.89/1.10         (~ (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 0.89/1.10          | ~ (r1_tarski @ (k2_relat_1 @ X17) @ X19)
% 0.89/1.10          | (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.89/1.10          | ~ (v1_relat_1 @ X17))),
% 0.89/1.10      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.89/1.10  thf('5', plain,
% 0.89/1.10      (![X0 : $i, X1 : $i]:
% 0.89/1.10         (~ (v1_relat_1 @ X0)
% 0.89/1.10          | (m1_subset_1 @ X0 @ 
% 0.89/1.10             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.89/1.10          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.89/1.10      inference('sup-', [status(thm)], ['3', '4'])).
% 0.89/1.10  thf('6', plain,
% 0.89/1.10      (![X0 : $i]:
% 0.89/1.10         ((m1_subset_1 @ X0 @ 
% 0.89/1.10           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.89/1.10          | ~ (v1_relat_1 @ X0))),
% 0.89/1.10      inference('sup-', [status(thm)], ['2', '5'])).
% 0.89/1.10  thf(cc1_partfun1, axiom,
% 0.89/1.10    (![A:$i,B:$i]:
% 0.89/1.10     ( ( v1_xboole_0 @ A ) =>
% 0.89/1.10       ( ![C:$i]:
% 0.89/1.10         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.10           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.89/1.10  thf('7', plain,
% 0.89/1.10      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.89/1.10         (~ (v1_xboole_0 @ X23)
% 0.89/1.10          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X25)))
% 0.89/1.10          | (v1_partfun1 @ X24 @ X23))),
% 0.89/1.10      inference('cnf', [status(esa)], [cc1_partfun1])).
% 0.89/1.10  thf('8', plain,
% 0.89/1.10      (![X0 : $i]:
% 0.89/1.10         (~ (v1_relat_1 @ X0)
% 0.89/1.10          | (v1_partfun1 @ X0 @ (k1_relat_1 @ X0))
% 0.89/1.10          | ~ (v1_xboole_0 @ (k1_relat_1 @ X0)))),
% 0.89/1.10      inference('sup-', [status(thm)], ['6', '7'])).
% 0.89/1.10  thf('9', plain,
% 0.89/1.10      (![X0 : $i]:
% 0.89/1.10         (~ (v1_xboole_0 @ X0)
% 0.89/1.10          | (v1_partfun1 @ X0 @ (k1_relat_1 @ X0))
% 0.89/1.10          | ~ (v1_relat_1 @ X0))),
% 0.89/1.10      inference('sup-', [status(thm)], ['0', '8'])).
% 0.89/1.10  thf('10', plain,
% 0.89/1.10      (![X0 : $i]:
% 0.89/1.10         ((m1_subset_1 @ X0 @ 
% 0.89/1.10           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.89/1.10          | ~ (v1_relat_1 @ X0))),
% 0.89/1.10      inference('sup-', [status(thm)], ['2', '5'])).
% 0.89/1.10  thf(cc1_funct_2, axiom,
% 0.89/1.10    (![A:$i,B:$i,C:$i]:
% 0.89/1.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.10       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.89/1.10         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.89/1.10  thf('11', plain,
% 0.89/1.10      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.89/1.10         (~ (v1_funct_1 @ X20)
% 0.89/1.10          | ~ (v1_partfun1 @ X20 @ X21)
% 0.89/1.10          | (v1_funct_2 @ X20 @ X21 @ X22)
% 0.89/1.10          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.89/1.10      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.89/1.10  thf('12', plain,
% 0.89/1.10      (![X0 : $i]:
% 0.89/1.10         (~ (v1_relat_1 @ X0)
% 0.89/1.10          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.89/1.10          | ~ (v1_partfun1 @ X0 @ (k1_relat_1 @ X0))
% 0.89/1.10          | ~ (v1_funct_1 @ X0))),
% 0.89/1.10      inference('sup-', [status(thm)], ['10', '11'])).
% 0.89/1.10  thf('13', plain,
% 0.89/1.10      (![X0 : $i]:
% 0.89/1.10         (~ (v1_relat_1 @ X0)
% 0.89/1.10          | ~ (v1_xboole_0 @ X0)
% 0.89/1.10          | ~ (v1_funct_1 @ X0)
% 0.89/1.10          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.89/1.10          | ~ (v1_relat_1 @ X0))),
% 0.89/1.10      inference('sup-', [status(thm)], ['9', '12'])).
% 0.89/1.10  thf('14', plain,
% 0.89/1.10      (![X0 : $i]:
% 0.89/1.10         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.89/1.10          | ~ (v1_funct_1 @ X0)
% 0.89/1.10          | ~ (v1_xboole_0 @ X0)
% 0.89/1.10          | ~ (v1_relat_1 @ X0))),
% 0.89/1.10      inference('simplify', [status(thm)], ['13'])).
% 0.89/1.10  thf(t3_funct_2, conjecture,
% 0.89/1.10    (![A:$i]:
% 0.89/1.10     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.89/1.10       ( ( v1_funct_1 @ A ) & 
% 0.89/1.10         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.89/1.10         ( m1_subset_1 @
% 0.89/1.10           A @ 
% 0.89/1.10           ( k1_zfmisc_1 @
% 0.89/1.10             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.89/1.10  thf(zf_stmt_0, negated_conjecture,
% 0.89/1.10    (~( ![A:$i]:
% 0.89/1.10        ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.89/1.10          ( ( v1_funct_1 @ A ) & 
% 0.89/1.10            ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.89/1.10            ( m1_subset_1 @
% 0.89/1.10              A @ 
% 0.89/1.10              ( k1_zfmisc_1 @
% 0.89/1.10                ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )),
% 0.89/1.10    inference('cnf.neg', [status(esa)], [t3_funct_2])).
% 0.89/1.10  thf('15', plain,
% 0.89/1.10      ((~ (v1_funct_1 @ sk_A)
% 0.89/1.10        | ~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))
% 0.89/1.10        | ~ (m1_subset_1 @ sk_A @ 
% 0.89/1.10             (k1_zfmisc_1 @ 
% 0.89/1.10              (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf('16', plain,
% 0.89/1.10      ((~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))
% 0.89/1.10         <= (~
% 0.89/1.10             ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))),
% 0.89/1.10      inference('split', [status(esa)], ['15'])).
% 0.89/1.10  thf('17', plain, ((v1_funct_1 @ sk_A)),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf('18', plain, ((~ (v1_funct_1 @ sk_A)) <= (~ ((v1_funct_1 @ sk_A)))),
% 0.89/1.10      inference('split', [status(esa)], ['15'])).
% 0.89/1.10  thf('19', plain, (((v1_funct_1 @ sk_A))),
% 0.89/1.10      inference('sup-', [status(thm)], ['17', '18'])).
% 0.89/1.10  thf('20', plain,
% 0.89/1.10      (![X0 : $i]:
% 0.89/1.10         ((m1_subset_1 @ X0 @ 
% 0.89/1.10           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.89/1.10          | ~ (v1_relat_1 @ X0))),
% 0.89/1.10      inference('sup-', [status(thm)], ['2', '5'])).
% 0.89/1.10  thf('21', plain,
% 0.89/1.10      ((~ (m1_subset_1 @ sk_A @ 
% 0.89/1.10           (k1_zfmisc_1 @ 
% 0.89/1.10            (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))
% 0.89/1.10         <= (~
% 0.89/1.10             ((m1_subset_1 @ sk_A @ 
% 0.89/1.10               (k1_zfmisc_1 @ 
% 0.89/1.10                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.89/1.10      inference('split', [status(esa)], ['15'])).
% 0.89/1.10  thf('22', plain,
% 0.89/1.10      ((~ (v1_relat_1 @ sk_A))
% 0.89/1.10         <= (~
% 0.89/1.10             ((m1_subset_1 @ sk_A @ 
% 0.89/1.10               (k1_zfmisc_1 @ 
% 0.89/1.10                (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))))),
% 0.89/1.10      inference('sup-', [status(thm)], ['20', '21'])).
% 0.89/1.10  thf('23', plain, ((v1_relat_1 @ sk_A)),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf('24', plain,
% 0.89/1.10      (((m1_subset_1 @ sk_A @ 
% 0.89/1.10         (k1_zfmisc_1 @ 
% 0.89/1.10          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))))),
% 0.89/1.10      inference('demod', [status(thm)], ['22', '23'])).
% 0.89/1.10  thf('25', plain,
% 0.89/1.10      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))) | 
% 0.89/1.10       ~
% 0.89/1.10       ((m1_subset_1 @ sk_A @ 
% 0.89/1.10         (k1_zfmisc_1 @ 
% 0.89/1.10          (k2_zfmisc_1 @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))))) | 
% 0.89/1.10       ~ ((v1_funct_1 @ sk_A))),
% 0.89/1.10      inference('split', [status(esa)], ['15'])).
% 0.89/1.10  thf('26', plain,
% 0.89/1.10      (~ ((v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A)))),
% 0.89/1.10      inference('sat_resolution*', [status(thm)], ['19', '24', '25'])).
% 0.89/1.10  thf('27', plain,
% 0.89/1.10      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.89/1.10      inference('simpl_trail', [status(thm)], ['16', '26'])).
% 0.89/1.10  thf('28', plain,
% 0.89/1.10      ((~ (v1_relat_1 @ sk_A) | ~ (v1_xboole_0 @ sk_A) | ~ (v1_funct_1 @ sk_A))),
% 0.89/1.10      inference('sup-', [status(thm)], ['14', '27'])).
% 0.89/1.10  thf('29', plain, ((v1_relat_1 @ sk_A)),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf('30', plain, ((v1_funct_1 @ sk_A)),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf('31', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.89/1.10      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.89/1.10  thf(d1_funct_2, axiom,
% 0.89/1.10    (![A:$i,B:$i,C:$i]:
% 0.89/1.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.10       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.89/1.10           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.89/1.10             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.89/1.10         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.89/1.10           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.89/1.10             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.89/1.10  thf(zf_stmt_1, axiom,
% 0.89/1.10    (![B:$i,A:$i]:
% 0.89/1.10     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.89/1.10       ( zip_tseitin_0 @ B @ A ) ))).
% 0.89/1.10  thf('32', plain,
% 0.89/1.10      (![X26 : $i, X27 : $i]:
% 0.89/1.10         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.89/1.10  thf('33', plain,
% 0.89/1.10      (![X0 : $i]:
% 0.89/1.10         ((m1_subset_1 @ X0 @ 
% 0.89/1.10           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.89/1.10          | ~ (v1_relat_1 @ X0))),
% 0.89/1.10      inference('sup-', [status(thm)], ['2', '5'])).
% 0.89/1.10  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.89/1.10  thf(zf_stmt_3, axiom,
% 0.89/1.10    (![C:$i,B:$i,A:$i]:
% 0.89/1.10     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.89/1.10       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.89/1.10  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.89/1.10  thf(zf_stmt_5, axiom,
% 0.89/1.10    (![A:$i,B:$i,C:$i]:
% 0.89/1.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.10       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.89/1.10         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.89/1.10           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.89/1.10             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.89/1.10  thf('34', plain,
% 0.89/1.10      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.89/1.10         (~ (zip_tseitin_0 @ X31 @ X32)
% 0.89/1.10          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 0.89/1.10          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.89/1.10  thf('35', plain,
% 0.89/1.10      (![X0 : $i]:
% 0.89/1.10         (~ (v1_relat_1 @ X0)
% 0.89/1.10          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.89/1.10          | ~ (zip_tseitin_0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0)))),
% 0.89/1.10      inference('sup-', [status(thm)], ['33', '34'])).
% 0.89/1.10  thf('36', plain,
% 0.89/1.10      (![X0 : $i]:
% 0.89/1.10         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.89/1.10          | (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.89/1.10          | ~ (v1_relat_1 @ X0))),
% 0.89/1.10      inference('sup-', [status(thm)], ['32', '35'])).
% 0.89/1.10  thf('37', plain,
% 0.89/1.10      (![X0 : $i]:
% 0.89/1.10         ((m1_subset_1 @ X0 @ 
% 0.89/1.10           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.89/1.10          | ~ (v1_relat_1 @ X0))),
% 0.89/1.10      inference('sup-', [status(thm)], ['2', '5'])).
% 0.89/1.10  thf(redefinition_k1_relset_1, axiom,
% 0.89/1.10    (![A:$i,B:$i,C:$i]:
% 0.89/1.10     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.89/1.10       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.89/1.10  thf('38', plain,
% 0.89/1.10      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.89/1.10         (((k1_relset_1 @ X15 @ X16 @ X14) = (k1_relat_1 @ X14))
% 0.89/1.10          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.89/1.10      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.89/1.10  thf('39', plain,
% 0.89/1.10      (![X0 : $i]:
% 0.89/1.10         (~ (v1_relat_1 @ X0)
% 0.89/1.10          | ((k1_relset_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0) @ X0)
% 0.89/1.10              = (k1_relat_1 @ X0)))),
% 0.89/1.10      inference('sup-', [status(thm)], ['37', '38'])).
% 0.89/1.10  thf('40', plain,
% 0.89/1.10      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.89/1.10         (((X28) != (k1_relset_1 @ X28 @ X29 @ X30))
% 0.89/1.10          | (v1_funct_2 @ X30 @ X28 @ X29)
% 0.89/1.10          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.89/1.10  thf('41', plain,
% 0.89/1.10      (![X0 : $i]:
% 0.89/1.10         (((k1_relat_1 @ X0) != (k1_relat_1 @ X0))
% 0.89/1.10          | ~ (v1_relat_1 @ X0)
% 0.89/1.10          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.89/1.10          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.89/1.10      inference('sup-', [status(thm)], ['39', '40'])).
% 0.89/1.10  thf('42', plain,
% 0.89/1.10      (![X0 : $i]:
% 0.89/1.10         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.89/1.10          | ~ (zip_tseitin_1 @ X0 @ (k2_relat_1 @ X0) @ (k1_relat_1 @ X0))
% 0.89/1.10          | ~ (v1_relat_1 @ X0))),
% 0.89/1.10      inference('simplify', [status(thm)], ['41'])).
% 0.89/1.10  thf('43', plain,
% 0.89/1.10      (![X0 : $i]:
% 0.89/1.10         (~ (v1_relat_1 @ X0)
% 0.89/1.10          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.89/1.10          | ~ (v1_relat_1 @ X0)
% 0.89/1.10          | (v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))),
% 0.89/1.10      inference('sup-', [status(thm)], ['36', '42'])).
% 0.89/1.10  thf('44', plain,
% 0.89/1.10      (![X0 : $i]:
% 0.89/1.10         ((v1_funct_2 @ X0 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))
% 0.89/1.10          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.89/1.10          | ~ (v1_relat_1 @ X0))),
% 0.89/1.10      inference('simplify', [status(thm)], ['43'])).
% 0.89/1.10  thf('45', plain,
% 0.89/1.10      (~ (v1_funct_2 @ sk_A @ (k1_relat_1 @ sk_A) @ (k2_relat_1 @ sk_A))),
% 0.89/1.10      inference('simpl_trail', [status(thm)], ['16', '26'])).
% 0.89/1.10  thf('46', plain,
% 0.89/1.10      ((~ (v1_relat_1 @ sk_A) | ((k2_relat_1 @ sk_A) = (k1_xboole_0)))),
% 0.89/1.10      inference('sup-', [status(thm)], ['44', '45'])).
% 0.89/1.10  thf('47', plain, ((v1_relat_1 @ sk_A)),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf('48', plain, (((k2_relat_1 @ sk_A) = (k1_xboole_0))),
% 0.89/1.10      inference('demod', [status(thm)], ['46', '47'])).
% 0.89/1.10  thf('49', plain,
% 0.89/1.10      (![X0 : $i]:
% 0.89/1.10         ((m1_subset_1 @ X0 @ 
% 0.89/1.10           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.89/1.10          | ~ (v1_relat_1 @ X0))),
% 0.89/1.10      inference('sup-', [status(thm)], ['2', '5'])).
% 0.89/1.10  thf(cc4_relset_1, axiom,
% 0.89/1.10    (![A:$i,B:$i]:
% 0.89/1.10     ( ( v1_xboole_0 @ A ) =>
% 0.89/1.10       ( ![C:$i]:
% 0.89/1.10         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.89/1.10           ( v1_xboole_0 @ C ) ) ) ))).
% 0.89/1.10  thf('50', plain,
% 0.89/1.10      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.89/1.10         (~ (v1_xboole_0 @ X11)
% 0.89/1.10          | ~ (m1_subset_1 @ X12 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X11)))
% 0.89/1.10          | (v1_xboole_0 @ X12))),
% 0.89/1.10      inference('cnf', [status(esa)], [cc4_relset_1])).
% 0.89/1.10  thf('51', plain,
% 0.89/1.10      (![X0 : $i]:
% 0.89/1.10         (~ (v1_relat_1 @ X0)
% 0.89/1.10          | (v1_xboole_0 @ X0)
% 0.89/1.10          | ~ (v1_xboole_0 @ (k2_relat_1 @ X0)))),
% 0.89/1.10      inference('sup-', [status(thm)], ['49', '50'])).
% 0.89/1.10  thf('52', plain,
% 0.89/1.10      ((~ (v1_xboole_0 @ k1_xboole_0)
% 0.89/1.10        | (v1_xboole_0 @ sk_A)
% 0.89/1.10        | ~ (v1_relat_1 @ sk_A))),
% 0.89/1.10      inference('sup-', [status(thm)], ['48', '51'])).
% 0.89/1.10  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.89/1.10  thf('53', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.89/1.10      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.89/1.10  thf('54', plain, ((v1_relat_1 @ sk_A)),
% 0.89/1.10      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.89/1.10  thf('55', plain, ((v1_xboole_0 @ sk_A)),
% 0.89/1.10      inference('demod', [status(thm)], ['52', '53', '54'])).
% 0.89/1.10  thf('56', plain, ($false), inference('demod', [status(thm)], ['31', '55'])).
% 0.89/1.10  
% 0.89/1.10  % SZS output end Refutation
% 0.89/1.10  
% 0.89/1.11  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
