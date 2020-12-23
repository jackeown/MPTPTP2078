%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vupC1xClWV

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:55 EST 2020

% Result     : Theorem 0.70s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  172 (2096 expanded)
%              Number of leaves         :   47 ( 635 expanded)
%              Depth                    :   23
%              Number of atoms          : 1386 (35509 expanded)
%              Number of equality atoms :   53 ( 462 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t178_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ~ ( v1_xboole_0 @ D )
     => ! [E: $i] :
          ( ( ( v1_funct_1 @ E )
            & ( v1_funct_2 @ E @ A @ D )
            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) )
         => ( ( ( r1_tarski @ B @ A )
              & ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) )
           => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) )
              & ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C )
              & ( m1_subset_1 @ ( k2_partfun1 @ A @ D @ E @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ~ ( v1_xboole_0 @ D )
       => ! [E: $i] :
            ( ( ( v1_funct_1 @ E )
              & ( v1_funct_2 @ E @ A @ D )
              & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) )
           => ( ( ( r1_tarski @ B @ A )
                & ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) )
             => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) )
                & ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C )
                & ( m1_subset_1 @ ( k2_partfun1 @ A @ D @ E @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t178_funct_2])).

thf('0',plain,
    ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) )
    | ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('3',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i] :
      ( ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( v1_funct_1 @ X43 )
      | ( ( k2_partfun1 @ X44 @ X45 @ X43 @ X46 )
        = ( k7_relat_1 @ X43 @ X46 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C )
   <= ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference(demod,[status(thm)],['1','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) )
        & ( m1_subset_1 @ ( k2_partfun1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('9',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X40 @ X41 @ X39 @ X42 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,
    ( ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) )
   <= ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('14',plain,(
    v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('15',plain,(
    ! [X17: $i,X18: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X17 @ X18 ) @ X17 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X4: $i,X6: $i] :
      ( ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r1_tarski @ X4 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('18',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('22',plain,(
    r1_tarski @ ( k7_relset_1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('24',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ( ( k7_relset_1 @ X25 @ X26 @ X24 @ X27 )
        = ( k9_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k9_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_E @ sk_B ) @ sk_C ),
    inference(demod,[status(thm)],['22','25'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('27',plain,(
    ! [X13: $i,X14: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) )
        = ( k9_relat_1 @ X13 @ X14 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('28',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ( v5_relat_1 @ X9 @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( v5_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( v5_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('34',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('35',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( v5_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference(demod,[status(thm)],['30','35'])).

thf('37',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( v5_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C ) ),
    inference('sup-',[status(thm)],['21','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['33','34'])).

thf('39',plain,(
    v5_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v5_relat_1 @ X9 @ X10 )
      | ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['20','41'])).

thf('43',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['33','34'])).

thf('44',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) @ sk_C ),
    inference(demod,[status(thm)],['42','43'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('45',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('46',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['45'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('47',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X28 ) @ X29 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X28 ) @ X30 )
      | ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,
    ( ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) @ sk_C ) ) )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['44','48'])).

thf('50',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_2 @ sk_E @ sk_A @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('52',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ( X33
        = ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('53',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf(zf_stmt_2,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('54',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('55',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(zf_stmt_3,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

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

thf('58',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('59',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['56','59'])).

thf('61',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    zip_tseitin_1 @ sk_E @ sk_D @ sk_A ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('64',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('65',plain,
    ( ( k1_relset_1 @ sk_A @ sk_D @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['53','62','65'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('67',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X20 @ X19 ) )
        = X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_E )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['33','34'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['68','69'])).

thf('71',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['50','70'])).

thf('72',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) )
      | ~ ( v1_funct_1 @ X39 )
      | ( m1_subset_1 @ ( k2_partfun1 @ X40 @ X41 @ X39 @ X42 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_partfun1])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X7: $i,X8: $i] :
      ( ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) )
      | ( v1_relat_1 @ X7 )
      | ~ ( v1_relat_1 @ X8 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) )
      | ( v1_relat_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X11: $i,X12: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('82',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['49','71','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('85',plain,
    ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('86',plain,
    ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('89',plain,(
    ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['14','87','88'])).

thf('90',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['7','89'])).

thf('91',plain,(
    ! [X31: $i,X32: $i] :
      ( ( zip_tseitin_0 @ X31 @ X32 )
      | ( X31 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('92',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['49','71','82'])).

thf('93',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( zip_tseitin_0 @ X36 @ X37 )
      | ( zip_tseitin_1 @ X38 @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('94',plain,
    ( ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['91','94'])).

thf('96',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['49','71','82'])).

thf('97',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k1_relset_1 @ X22 @ X23 @ X21 )
        = ( k1_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('98',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['50','70'])).

thf('100',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( X33
       != ( k1_relset_1 @ X33 @ X34 @ X35 ) )
      | ( v1_funct_2 @ X35 @ X33 @ X34 )
      | ~ ( zip_tseitin_1 @ X35 @ X34 @ X33 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('102',plain,
    ( ( sk_B != sk_B )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B ) ),
    inference(simplify,[status(thm)],['102'])).

thf('104',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['7','89'])).

thf('105',plain,(
    ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['103','104'])).

thf('106',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['95','105'])).

thf('107',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['90','106'])).

thf('108',plain,(
    r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) @ sk_C ),
    inference(demod,[status(thm)],['42','43'])).

thf('109',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('110',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) )
    | ( sk_C
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['95','105'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('112',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('113',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['95','105'])).

thf('114',plain,
    ( k1_xboole_0
    = ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference(demod,[status(thm)],['110','111','112','113'])).

thf(t3_funct_2,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_funct_1 @ A ) )
     => ( ( v1_funct_1 @ A )
        & ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) )
        & ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ) )).

thf('115',plain,(
    ! [X47: $i] :
      ( ( v1_funct_2 @ X47 @ ( k1_relat_1 @ X47 ) @ ( k2_relat_1 @ X47 ) )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_relat_1 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t3_funct_2])).

thf('116',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    | ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference('sup+',[status(thm)],['114','115'])).

thf('117',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['50','70'])).

thf('118',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('119',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('121',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['119','120'])).

thf('122',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ k1_xboole_0 ),
    inference(demod,[status(thm)],['116','117','118','121'])).

thf('123',plain,(
    $false ),
    inference(demod,[status(thm)],['107','122'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.vupC1xClWV
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:05:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.70/0.89  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.70/0.89  % Solved by: fo/fo7.sh
% 0.70/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.70/0.89  % done 423 iterations in 0.440s
% 0.70/0.89  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.70/0.89  % SZS output start Refutation
% 0.70/0.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.70/0.89  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.70/0.89  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.70/0.89  thf(sk_B_type, type, sk_B: $i).
% 0.70/0.89  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.70/0.89  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.70/0.89  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.70/0.89  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.70/0.89  thf(sk_E_type, type, sk_E: $i).
% 0.70/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.70/0.89  thf(sk_D_type, type, sk_D: $i).
% 0.70/0.89  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.70/0.89  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.70/0.89  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.70/0.89  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.70/0.89  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.70/0.89  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.70/0.89  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.70/0.89  thf(sk_C_type, type, sk_C: $i).
% 0.70/0.89  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.70/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.70/0.89  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.70/0.89  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.70/0.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.70/0.89  thf(t178_funct_2, conjecture,
% 0.70/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.70/0.89     ( ( ~( v1_xboole_0 @ D ) ) =>
% 0.70/0.89       ( ![E:$i]:
% 0.70/0.89         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ D ) & 
% 0.70/0.89             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) =>
% 0.70/0.89           ( ( ( r1_tarski @ B @ A ) & 
% 0.70/0.89               ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) ) =>
% 0.70/0.89             ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) ) & 
% 0.70/0.89               ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C ) & 
% 0.70/0.89               ( m1_subset_1 @
% 0.70/0.89                 ( k2_partfun1 @ A @ D @ E @ B ) @ 
% 0.70/0.89                 ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.70/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.70/0.89    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.70/0.89        ( ( ~( v1_xboole_0 @ D ) ) =>
% 0.70/0.89          ( ![E:$i]:
% 0.70/0.89            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ D ) & 
% 0.70/0.89                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) =>
% 0.70/0.89              ( ( ( r1_tarski @ B @ A ) & 
% 0.70/0.89                  ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) ) =>
% 0.70/0.89                ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) ) & 
% 0.70/0.89                  ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C ) & 
% 0.70/0.89                  ( m1_subset_1 @
% 0.70/0.89                    ( k2_partfun1 @ A @ D @ E @ B ) @ 
% 0.70/0.89                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ) )),
% 0.70/0.89    inference('cnf.neg', [status(esa)], [t178_funct_2])).
% 0.70/0.89  thf('0', plain,
% 0.70/0.89      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B))
% 0.70/0.89        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ 
% 0.70/0.89             sk_C)
% 0.70/0.89        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 0.70/0.89             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('1', plain,
% 0.70/0.89      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ sk_C))
% 0.70/0.89         <= (~
% 0.70/0.89             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ 
% 0.70/0.89               sk_C)))),
% 0.70/0.89      inference('split', [status(esa)], ['0'])).
% 0.70/0.89  thf('2', plain,
% 0.70/0.89      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf(redefinition_k2_partfun1, axiom,
% 0.70/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.70/0.89     ( ( ( v1_funct_1 @ C ) & 
% 0.70/0.89         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.70/0.89       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.70/0.89  thf('3', plain,
% 0.70/0.89      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i]:
% 0.70/0.89         (~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 0.70/0.89          | ~ (v1_funct_1 @ X43)
% 0.70/0.89          | ((k2_partfun1 @ X44 @ X45 @ X43 @ X46) = (k7_relat_1 @ X43 @ X46)))),
% 0.70/0.89      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.70/0.89  thf('4', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 0.70/0.89          | ~ (v1_funct_1 @ sk_E))),
% 0.70/0.89      inference('sup-', [status(thm)], ['2', '3'])).
% 0.70/0.89  thf('5', plain, ((v1_funct_1 @ sk_E)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('6', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.70/0.89      inference('demod', [status(thm)], ['4', '5'])).
% 0.70/0.89  thf('7', plain,
% 0.70/0.89      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C))
% 0.70/0.89         <= (~
% 0.70/0.89             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ 
% 0.70/0.89               sk_C)))),
% 0.70/0.89      inference('demod', [status(thm)], ['1', '6'])).
% 0.70/0.89  thf('8', plain,
% 0.70/0.89      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf(dt_k2_partfun1, axiom,
% 0.70/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.70/0.89     ( ( ( v1_funct_1 @ C ) & 
% 0.70/0.89         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.70/0.89       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 0.70/0.89         ( m1_subset_1 @
% 0.70/0.89           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 0.70/0.89           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.70/0.89  thf('9', plain,
% 0.70/0.89      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.70/0.89         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.70/0.89          | ~ (v1_funct_1 @ X39)
% 0.70/0.89          | (v1_funct_1 @ (k2_partfun1 @ X40 @ X41 @ X39 @ X42)))),
% 0.70/0.89      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 0.70/0.89  thf('10', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))
% 0.70/0.89          | ~ (v1_funct_1 @ sk_E))),
% 0.70/0.89      inference('sup-', [status(thm)], ['8', '9'])).
% 0.70/0.89  thf('11', plain, ((v1_funct_1 @ sk_E)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('12', plain,
% 0.70/0.89      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))),
% 0.70/0.89      inference('demod', [status(thm)], ['10', '11'])).
% 0.70/0.89  thf('13', plain,
% 0.70/0.89      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B)))
% 0.70/0.89         <= (~ ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B))))),
% 0.70/0.89      inference('split', [status(esa)], ['0'])).
% 0.70/0.89  thf('14', plain,
% 0.70/0.89      (((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['12', '13'])).
% 0.70/0.89  thf(t88_relat_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.70/0.89  thf('15', plain,
% 0.70/0.89      (![X17 : $i, X18 : $i]:
% 0.70/0.89         ((r1_tarski @ (k7_relat_1 @ X17 @ X18) @ X17) | ~ (v1_relat_1 @ X17))),
% 0.70/0.89      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.70/0.89  thf(t3_subset, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.70/0.89  thf('16', plain,
% 0.70/0.89      (![X4 : $i, X6 : $i]:
% 0.70/0.89         ((m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X6)) | ~ (r1_tarski @ X4 @ X6))),
% 0.70/0.89      inference('cnf', [status(esa)], [t3_subset])).
% 0.70/0.89  thf('17', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         (~ (v1_relat_1 @ X0)
% 0.70/0.89          | (m1_subset_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['15', '16'])).
% 0.70/0.89  thf(cc2_relat_1, axiom,
% 0.70/0.89    (![A:$i]:
% 0.70/0.89     ( ( v1_relat_1 @ A ) =>
% 0.70/0.89       ( ![B:$i]:
% 0.70/0.89         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.70/0.89  thf('18', plain,
% 0.70/0.89      (![X7 : $i, X8 : $i]:
% 0.70/0.89         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.70/0.89          | (v1_relat_1 @ X7)
% 0.70/0.89          | ~ (v1_relat_1 @ X8))),
% 0.70/0.89      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.70/0.89  thf('19', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         (~ (v1_relat_1 @ X0)
% 0.70/0.89          | ~ (v1_relat_1 @ X0)
% 0.70/0.89          | (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['17', '18'])).
% 0.70/0.89  thf('20', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((v1_relat_1 @ (k7_relat_1 @ X0 @ X1)) | ~ (v1_relat_1 @ X0))),
% 0.70/0.89      inference('simplify', [status(thm)], ['19'])).
% 0.70/0.89  thf('21', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         ((v1_relat_1 @ (k7_relat_1 @ X0 @ X1)) | ~ (v1_relat_1 @ X0))),
% 0.70/0.89      inference('simplify', [status(thm)], ['19'])).
% 0.70/0.89  thf('22', plain,
% 0.70/0.89      ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_C)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('23', plain,
% 0.70/0.89      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf(redefinition_k7_relset_1, axiom,
% 0.70/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.70/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.89       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.70/0.89  thf('24', plain,
% 0.70/0.89      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.70/0.89         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.70/0.89          | ((k7_relset_1 @ X25 @ X26 @ X24 @ X27) = (k9_relat_1 @ X24 @ X27)))),
% 0.70/0.89      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.70/0.89  thf('25', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((k7_relset_1 @ sk_A @ sk_D @ sk_E @ X0) = (k9_relat_1 @ sk_E @ X0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['23', '24'])).
% 0.70/0.89  thf('26', plain, ((r1_tarski @ (k9_relat_1 @ sk_E @ sk_B) @ sk_C)),
% 0.70/0.89      inference('demod', [status(thm)], ['22', '25'])).
% 0.70/0.89  thf(t148_relat_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( v1_relat_1 @ B ) =>
% 0.70/0.89       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.70/0.89  thf('27', plain,
% 0.70/0.89      (![X13 : $i, X14 : $i]:
% 0.70/0.89         (((k2_relat_1 @ (k7_relat_1 @ X13 @ X14)) = (k9_relat_1 @ X13 @ X14))
% 0.70/0.89          | ~ (v1_relat_1 @ X13))),
% 0.70/0.89      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.70/0.89  thf(d19_relat_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( v1_relat_1 @ B ) =>
% 0.70/0.89       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.70/0.89  thf('28', plain,
% 0.70/0.89      (![X9 : $i, X10 : $i]:
% 0.70/0.89         (~ (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 0.70/0.89          | (v5_relat_1 @ X9 @ X10)
% 0.70/0.89          | ~ (v1_relat_1 @ X9))),
% 0.70/0.89      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.70/0.89  thf('29', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.70/0.89         (~ (r1_tarski @ (k9_relat_1 @ X1 @ X0) @ X2)
% 0.70/0.89          | ~ (v1_relat_1 @ X1)
% 0.70/0.89          | ~ (v1_relat_1 @ (k7_relat_1 @ X1 @ X0))
% 0.70/0.89          | (v5_relat_1 @ (k7_relat_1 @ X1 @ X0) @ X2))),
% 0.70/0.89      inference('sup-', [status(thm)], ['27', '28'])).
% 0.70/0.89  thf('30', plain,
% 0.70/0.89      (((v5_relat_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C)
% 0.70/0.89        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B))
% 0.70/0.89        | ~ (v1_relat_1 @ sk_E))),
% 0.70/0.89      inference('sup-', [status(thm)], ['26', '29'])).
% 0.70/0.89  thf('31', plain,
% 0.70/0.89      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('32', plain,
% 0.70/0.89      (![X7 : $i, X8 : $i]:
% 0.70/0.89         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.70/0.89          | (v1_relat_1 @ X7)
% 0.70/0.89          | ~ (v1_relat_1 @ X8))),
% 0.70/0.89      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.70/0.89  thf('33', plain,
% 0.70/0.89      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)) | (v1_relat_1 @ sk_E))),
% 0.70/0.89      inference('sup-', [status(thm)], ['31', '32'])).
% 0.70/0.89  thf(fc6_relat_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.70/0.89  thf('34', plain,
% 0.70/0.89      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.70/0.89      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.70/0.89  thf('35', plain, ((v1_relat_1 @ sk_E)),
% 0.70/0.89      inference('demod', [status(thm)], ['33', '34'])).
% 0.70/0.89  thf('36', plain,
% 0.70/0.89      (((v5_relat_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C)
% 0.70/0.89        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)))),
% 0.70/0.89      inference('demod', [status(thm)], ['30', '35'])).
% 0.70/0.89  thf('37', plain,
% 0.70/0.89      ((~ (v1_relat_1 @ sk_E)
% 0.70/0.89        | (v5_relat_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C))),
% 0.70/0.89      inference('sup-', [status(thm)], ['21', '36'])).
% 0.70/0.89  thf('38', plain, ((v1_relat_1 @ sk_E)),
% 0.70/0.89      inference('demod', [status(thm)], ['33', '34'])).
% 0.70/0.89  thf('39', plain, ((v5_relat_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C)),
% 0.70/0.89      inference('demod', [status(thm)], ['37', '38'])).
% 0.70/0.89  thf('40', plain,
% 0.70/0.89      (![X9 : $i, X10 : $i]:
% 0.70/0.89         (~ (v5_relat_1 @ X9 @ X10)
% 0.70/0.89          | (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 0.70/0.89          | ~ (v1_relat_1 @ X9))),
% 0.70/0.89      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.70/0.89  thf('41', plain,
% 0.70/0.89      ((~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B))
% 0.70/0.89        | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) @ sk_C))),
% 0.70/0.89      inference('sup-', [status(thm)], ['39', '40'])).
% 0.70/0.89  thf('42', plain,
% 0.70/0.89      ((~ (v1_relat_1 @ sk_E)
% 0.70/0.89        | (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) @ sk_C))),
% 0.70/0.89      inference('sup-', [status(thm)], ['20', '41'])).
% 0.70/0.89  thf('43', plain, ((v1_relat_1 @ sk_E)),
% 0.70/0.89      inference('demod', [status(thm)], ['33', '34'])).
% 0.70/0.89  thf('44', plain,
% 0.70/0.89      ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) @ sk_C)),
% 0.70/0.89      inference('demod', [status(thm)], ['42', '43'])).
% 0.70/0.89  thf(d10_xboole_0, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.70/0.89  thf('45', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.70/0.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.70/0.89  thf('46', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.70/0.89      inference('simplify', [status(thm)], ['45'])).
% 0.70/0.89  thf(t11_relset_1, axiom,
% 0.70/0.89    (![A:$i,B:$i,C:$i]:
% 0.70/0.89     ( ( v1_relat_1 @ C ) =>
% 0.70/0.89       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.70/0.89           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.70/0.89         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.70/0.89  thf('47', plain,
% 0.70/0.89      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.70/0.89         (~ (r1_tarski @ (k1_relat_1 @ X28) @ X29)
% 0.70/0.89          | ~ (r1_tarski @ (k2_relat_1 @ X28) @ X30)
% 0.70/0.89          | (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.70/0.89          | ~ (v1_relat_1 @ X28))),
% 0.70/0.89      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.70/0.89  thf('48', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]:
% 0.70/0.89         (~ (v1_relat_1 @ X0)
% 0.70/0.89          | (m1_subset_1 @ X0 @ 
% 0.70/0.89             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ X1)))
% 0.70/0.89          | ~ (r1_tarski @ (k2_relat_1 @ X0) @ X1))),
% 0.70/0.89      inference('sup-', [status(thm)], ['46', '47'])).
% 0.70/0.89  thf('49', plain,
% 0.70/0.89      (((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 0.70/0.89         (k1_zfmisc_1 @ 
% 0.70/0.89          (k2_zfmisc_1 @ (k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) @ sk_C)))
% 0.70/0.89        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['44', '48'])).
% 0.70/0.89  thf('50', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('51', plain, ((v1_funct_2 @ sk_E @ sk_A @ sk_D)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf(d1_funct_2, axiom,
% 0.70/0.89    (![A:$i,B:$i,C:$i]:
% 0.70/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.89       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.70/0.89           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.70/0.89             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.70/0.89         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.70/0.89           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.70/0.89             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.70/0.89  thf(zf_stmt_1, axiom,
% 0.70/0.89    (![C:$i,B:$i,A:$i]:
% 0.70/0.89     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.70/0.89       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.70/0.89  thf('52', plain,
% 0.70/0.89      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.70/0.89         (~ (v1_funct_2 @ X35 @ X33 @ X34)
% 0.70/0.89          | ((X33) = (k1_relset_1 @ X33 @ X34 @ X35))
% 0.70/0.89          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.70/0.89  thf('53', plain,
% 0.70/0.89      ((~ (zip_tseitin_1 @ sk_E @ sk_D @ sk_A)
% 0.70/0.89        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_D @ sk_E)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['51', '52'])).
% 0.70/0.89  thf(zf_stmt_2, axiom,
% 0.70/0.89    (![B:$i,A:$i]:
% 0.70/0.89     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.70/0.89       ( zip_tseitin_0 @ B @ A ) ))).
% 0.70/0.89  thf('54', plain,
% 0.70/0.89      (![X31 : $i, X32 : $i]:
% 0.70/0.89         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.70/0.89  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.70/0.89  thf('55', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.70/0.89      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.70/0.89  thf('56', plain,
% 0.70/0.89      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.70/0.89      inference('sup+', [status(thm)], ['54', '55'])).
% 0.70/0.89  thf('57', plain,
% 0.70/0.89      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf(zf_stmt_3, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.70/0.89  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.70/0.89  thf(zf_stmt_5, axiom,
% 0.70/0.89    (![A:$i,B:$i,C:$i]:
% 0.70/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.89       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.70/0.89         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.70/0.89           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.70/0.89             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.70/0.89  thf('58', plain,
% 0.70/0.89      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.70/0.89         (~ (zip_tseitin_0 @ X36 @ X37)
% 0.70/0.89          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 0.70/0.89          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.70/0.89  thf('59', plain,
% 0.70/0.89      (((zip_tseitin_1 @ sk_E @ sk_D @ sk_A) | ~ (zip_tseitin_0 @ sk_D @ sk_A))),
% 0.70/0.89      inference('sup-', [status(thm)], ['57', '58'])).
% 0.70/0.89  thf('60', plain,
% 0.70/0.89      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_E @ sk_D @ sk_A))),
% 0.70/0.89      inference('sup-', [status(thm)], ['56', '59'])).
% 0.70/0.89  thf('61', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('62', plain, ((zip_tseitin_1 @ sk_E @ sk_D @ sk_A)),
% 0.70/0.89      inference('clc', [status(thm)], ['60', '61'])).
% 0.70/0.89  thf('63', plain,
% 0.70/0.89      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf(redefinition_k1_relset_1, axiom,
% 0.70/0.89    (![A:$i,B:$i,C:$i]:
% 0.70/0.89     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.70/0.89       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.70/0.89  thf('64', plain,
% 0.70/0.89      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.70/0.89         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 0.70/0.89          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.70/0.89      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.70/0.89  thf('65', plain,
% 0.70/0.89      (((k1_relset_1 @ sk_A @ sk_D @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.70/0.89      inference('sup-', [status(thm)], ['63', '64'])).
% 0.70/0.89  thf('66', plain, (((sk_A) = (k1_relat_1 @ sk_E))),
% 0.70/0.89      inference('demod', [status(thm)], ['53', '62', '65'])).
% 0.70/0.89  thf(t91_relat_1, axiom,
% 0.70/0.89    (![A:$i,B:$i]:
% 0.70/0.89     ( ( v1_relat_1 @ B ) =>
% 0.70/0.89       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.70/0.89         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.70/0.89  thf('67', plain,
% 0.70/0.89      (![X19 : $i, X20 : $i]:
% 0.70/0.89         (~ (r1_tarski @ X19 @ (k1_relat_1 @ X20))
% 0.70/0.89          | ((k1_relat_1 @ (k7_relat_1 @ X20 @ X19)) = (X19))
% 0.70/0.89          | ~ (v1_relat_1 @ X20))),
% 0.70/0.89      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.70/0.89  thf('68', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (~ (r1_tarski @ X0 @ sk_A)
% 0.70/0.89          | ~ (v1_relat_1 @ sk_E)
% 0.70/0.89          | ((k1_relat_1 @ (k7_relat_1 @ sk_E @ X0)) = (X0)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['66', '67'])).
% 0.70/0.89  thf('69', plain, ((v1_relat_1 @ sk_E)),
% 0.70/0.89      inference('demod', [status(thm)], ['33', '34'])).
% 0.70/0.89  thf('70', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (~ (r1_tarski @ X0 @ sk_A)
% 0.70/0.89          | ((k1_relat_1 @ (k7_relat_1 @ sk_E @ X0)) = (X0)))),
% 0.70/0.89      inference('demod', [status(thm)], ['68', '69'])).
% 0.70/0.89  thf('71', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 0.70/0.89      inference('sup-', [status(thm)], ['50', '70'])).
% 0.70/0.89  thf('72', plain,
% 0.70/0.89      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('73', plain,
% 0.70/0.89      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.70/0.89         (~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41)))
% 0.70/0.89          | ~ (v1_funct_1 @ X39)
% 0.70/0.89          | (m1_subset_1 @ (k2_partfun1 @ X40 @ X41 @ X39 @ X42) @ 
% 0.70/0.89             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 0.70/0.89      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 0.70/0.89  thf('74', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) @ 
% 0.70/0.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))
% 0.70/0.89          | ~ (v1_funct_1 @ sk_E))),
% 0.70/0.89      inference('sup-', [status(thm)], ['72', '73'])).
% 0.70/0.89  thf('75', plain, ((v1_funct_1 @ sk_E)),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.70/0.89  thf('76', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) @ 
% 0.70/0.89          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.70/0.89      inference('demod', [status(thm)], ['74', '75'])).
% 0.70/0.89  thf('77', plain,
% 0.70/0.89      (![X7 : $i, X8 : $i]:
% 0.70/0.89         (~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8))
% 0.70/0.89          | (v1_relat_1 @ X7)
% 0.70/0.89          | ~ (v1_relat_1 @ X8))),
% 0.70/0.89      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.70/0.89  thf('78', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         (~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_D))
% 0.70/0.89          | (v1_relat_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['76', '77'])).
% 0.70/0.89  thf('79', plain,
% 0.70/0.89      (![X11 : $i, X12 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12))),
% 0.70/0.89      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.70/0.89  thf('80', plain,
% 0.70/0.89      (![X0 : $i]: (v1_relat_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))),
% 0.70/0.89      inference('demod', [status(thm)], ['78', '79'])).
% 0.70/0.89  thf('81', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.70/0.89      inference('demod', [status(thm)], ['4', '5'])).
% 0.70/0.89  thf('82', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))),
% 0.70/0.89      inference('demod', [status(thm)], ['80', '81'])).
% 0.70/0.89  thf('83', plain,
% 0.70/0.89      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 0.70/0.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.70/0.89      inference('demod', [status(thm)], ['49', '71', '82'])).
% 0.70/0.89  thf('84', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.70/0.89      inference('demod', [status(thm)], ['4', '5'])).
% 0.70/0.89  thf('85', plain,
% 0.70/0.89      ((~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 0.70/0.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))
% 0.70/0.89         <= (~
% 0.70/0.89             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 0.70/0.89               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))))),
% 0.70/0.89      inference('split', [status(esa)], ['0'])).
% 0.70/0.89  thf('86', plain,
% 0.70/0.89      ((~ (m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 0.70/0.89           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))
% 0.70/0.89         <= (~
% 0.70/0.89             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 0.70/0.89               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))))),
% 0.70/0.89      inference('sup-', [status(thm)], ['84', '85'])).
% 0.70/0.89  thf('87', plain,
% 0.70/0.89      (((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 0.70/0.89         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 0.70/0.89      inference('sup-', [status(thm)], ['83', '86'])).
% 0.70/0.89  thf('88', plain,
% 0.70/0.89      (~
% 0.70/0.89       ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ sk_C)) | 
% 0.70/0.89       ~
% 0.70/0.89       ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 0.70/0.89         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))) | 
% 0.70/0.89       ~ ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B)))),
% 0.70/0.89      inference('split', [status(esa)], ['0'])).
% 0.70/0.89  thf('89', plain,
% 0.70/0.89      (~
% 0.70/0.89       ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ sk_C))),
% 0.70/0.89      inference('sat_resolution*', [status(thm)], ['14', '87', '88'])).
% 0.70/0.89  thf('90', plain, (~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)),
% 0.70/0.89      inference('simpl_trail', [status(thm)], ['7', '89'])).
% 0.70/0.89  thf('91', plain,
% 0.70/0.89      (![X31 : $i, X32 : $i]:
% 0.70/0.89         ((zip_tseitin_0 @ X31 @ X32) | ((X31) = (k1_xboole_0)))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.70/0.89  thf('92', plain,
% 0.70/0.89      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 0.70/0.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.70/0.89      inference('demod', [status(thm)], ['49', '71', '82'])).
% 0.70/0.89  thf('93', plain,
% 0.70/0.89      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.70/0.89         (~ (zip_tseitin_0 @ X36 @ X37)
% 0.70/0.89          | (zip_tseitin_1 @ X38 @ X36 @ X37)
% 0.70/0.89          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.70/0.89  thf('94', plain,
% 0.70/0.89      (((zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B)
% 0.70/0.89        | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 0.70/0.89      inference('sup-', [status(thm)], ['92', '93'])).
% 0.70/0.89  thf('95', plain,
% 0.70/0.89      ((((sk_C) = (k1_xboole_0))
% 0.70/0.89        | (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B))),
% 0.70/0.89      inference('sup-', [status(thm)], ['91', '94'])).
% 0.70/0.89  thf('96', plain,
% 0.70/0.89      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 0.70/0.89        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.70/0.89      inference('demod', [status(thm)], ['49', '71', '82'])).
% 0.70/0.89  thf('97', plain,
% 0.70/0.89      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.70/0.89         (((k1_relset_1 @ X22 @ X23 @ X21) = (k1_relat_1 @ X21))
% 0.70/0.89          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.70/0.89      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.70/0.89  thf('98', plain,
% 0.70/0.89      (((k1_relset_1 @ sk_B @ sk_C @ (k7_relat_1 @ sk_E @ sk_B))
% 0.70/0.89         = (k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)))),
% 0.70/0.89      inference('sup-', [status(thm)], ['96', '97'])).
% 0.70/0.89  thf('99', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 0.70/0.89      inference('sup-', [status(thm)], ['50', '70'])).
% 0.70/0.89  thf('100', plain,
% 0.70/0.89      (((k1_relset_1 @ sk_B @ sk_C @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 0.70/0.89      inference('demod', [status(thm)], ['98', '99'])).
% 0.70/0.89  thf('101', plain,
% 0.70/0.89      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.70/0.89         (((X33) != (k1_relset_1 @ X33 @ X34 @ X35))
% 0.70/0.89          | (v1_funct_2 @ X35 @ X33 @ X34)
% 0.70/0.89          | ~ (zip_tseitin_1 @ X35 @ X34 @ X33))),
% 0.70/0.89      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.70/0.89  thf('102', plain,
% 0.70/0.89      ((((sk_B) != (sk_B))
% 0.70/0.89        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B)
% 0.70/0.89        | (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C))),
% 0.70/0.89      inference('sup-', [status(thm)], ['100', '101'])).
% 0.70/0.89  thf('103', plain,
% 0.70/0.89      (((v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)
% 0.70/0.89        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B))),
% 0.70/0.89      inference('simplify', [status(thm)], ['102'])).
% 0.70/0.89  thf('104', plain,
% 0.70/0.89      (~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)),
% 0.70/0.89      inference('simpl_trail', [status(thm)], ['7', '89'])).
% 0.70/0.89  thf('105', plain,
% 0.70/0.89      (~ (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B)),
% 0.70/0.89      inference('clc', [status(thm)], ['103', '104'])).
% 0.70/0.89  thf('106', plain, (((sk_C) = (k1_xboole_0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['95', '105'])).
% 0.70/0.89  thf('107', plain,
% 0.70/0.89      (~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ k1_xboole_0)),
% 0.70/0.89      inference('demod', [status(thm)], ['90', '106'])).
% 0.70/0.89  thf('108', plain,
% 0.70/0.89      ((r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) @ sk_C)),
% 0.70/0.89      inference('demod', [status(thm)], ['42', '43'])).
% 0.70/0.89  thf('109', plain,
% 0.70/0.89      (![X0 : $i, X2 : $i]:
% 0.70/0.89         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.70/0.89      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.70/0.89  thf('110', plain,
% 0.70/0.89      ((~ (r1_tarski @ sk_C @ (k2_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)))
% 0.70/0.89        | ((sk_C) = (k2_relat_1 @ (k7_relat_1 @ sk_E @ sk_B))))),
% 0.70/0.89      inference('sup-', [status(thm)], ['108', '109'])).
% 0.70/0.89  thf('111', plain, (((sk_C) = (k1_xboole_0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['95', '105'])).
% 0.70/0.89  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.70/0.89  thf('112', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.70/0.89      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.70/0.89  thf('113', plain, (((sk_C) = (k1_xboole_0))),
% 0.70/0.89      inference('sup-', [status(thm)], ['95', '105'])).
% 0.70/0.89  thf('114', plain,
% 0.70/0.89      (((k1_xboole_0) = (k2_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)))),
% 0.70/0.89      inference('demod', [status(thm)], ['110', '111', '112', '113'])).
% 0.70/0.89  thf(t3_funct_2, axiom,
% 0.70/0.89    (![A:$i]:
% 0.70/0.89     ( ( ( v1_relat_1 @ A ) & ( v1_funct_1 @ A ) ) =>
% 0.70/0.89       ( ( v1_funct_1 @ A ) & 
% 0.70/0.89         ( v1_funct_2 @ A @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) & 
% 0.70/0.89         ( m1_subset_1 @
% 0.70/0.89           A @ 
% 0.70/0.89           ( k1_zfmisc_1 @
% 0.70/0.89             ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) ) ))).
% 0.70/0.89  thf('115', plain,
% 0.70/0.89      (![X47 : $i]:
% 0.70/0.89         ((v1_funct_2 @ X47 @ (k1_relat_1 @ X47) @ (k2_relat_1 @ X47))
% 0.70/0.89          | ~ (v1_funct_1 @ X47)
% 0.70/0.89          | ~ (v1_relat_1 @ X47))),
% 0.70/0.89      inference('cnf', [status(esa)], [t3_funct_2])).
% 0.70/0.89  thf('116', plain,
% 0.70/0.89      (((v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 0.70/0.89         (k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) @ k1_xboole_0)
% 0.70/0.89        | ~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B))
% 0.70/0.89        | ~ (v1_funct_1 @ (k7_relat_1 @ sk_E @ sk_B)))),
% 0.70/0.89      inference('sup+', [status(thm)], ['114', '115'])).
% 0.70/0.89  thf('117', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 0.70/0.89      inference('sup-', [status(thm)], ['50', '70'])).
% 0.70/0.89  thf('118', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))),
% 0.70/0.89      inference('demod', [status(thm)], ['80', '81'])).
% 0.70/0.89  thf('119', plain,
% 0.70/0.89      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))),
% 0.70/0.89      inference('demod', [status(thm)], ['10', '11'])).
% 0.70/0.89  thf('120', plain,
% 0.70/0.89      (![X0 : $i]:
% 0.70/0.89         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.70/0.89      inference('demod', [status(thm)], ['4', '5'])).
% 0.70/0.89  thf('121', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_E @ X0))),
% 0.74/0.89      inference('demod', [status(thm)], ['119', '120'])).
% 0.74/0.89  thf('122', plain,
% 0.74/0.89      ((v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ k1_xboole_0)),
% 0.74/0.89      inference('demod', [status(thm)], ['116', '117', '118', '121'])).
% 0.74/0.89  thf('123', plain, ($false), inference('demod', [status(thm)], ['107', '122'])).
% 0.74/0.89  
% 0.74/0.89  % SZS output end Refutation
% 0.74/0.89  
% 0.74/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
