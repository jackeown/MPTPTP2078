%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ixs5M5LPSY

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:55 EST 2020

% Result     : Theorem 0.71s
% Output     : Refutation 0.71s
% Verified   : 
% Statistics : Number of formulae       :  155 (1951 expanded)
%              Number of leaves         :   46 ( 592 expanded)
%              Depth                    :   22
%              Number of atoms          : 1289 (34000 expanded)
%              Number of equality atoms :   53 ( 285 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ( ( k2_partfun1 @ X39 @ X40 @ X38 @ X41 )
        = ( k7_relat_1 @ X38 @ X41 ) ) ) ),
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
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( v1_funct_1 @ X34 )
      | ( v1_funct_1 @ ( k2_partfun1 @ X35 @ X36 @ X34 @ X37 ) ) ) ),
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

thf('15',plain,(
    r1_tarski @ ( k7_relset_1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('17',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ( ( k7_relset_1 @ X20 @ X21 @ X19 @ X22 )
        = ( k9_relat_1 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k9_relat_1 @ sk_E @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k9_relat_1 @ sk_E @ sk_B ) @ sk_C ),
    inference(demod,[status(thm)],['15','18'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('20',plain,(
    ! [X9: $i,X10: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X9 @ X10 ) )
        = ( k9_relat_1 @ X9 @ X10 ) )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('21',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('22',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v4_relat_1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('23',plain,(
    v4_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['21','22'])).

thf(fc23_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v4_relat_1 @ C @ B ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) )
        & ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ A )
        & ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ) )).

thf('24',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v4_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) @ X5 )
      | ~ ( v4_relat_1 @ X4 @ X6 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc23_relat_1])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_E )
      | ( v4_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('28',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) )
    | ( v1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('29',plain,(
    ! [X7: $i,X8: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('30',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['25','30'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('32',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v4_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k1_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v4_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['21','22'])).

thf('35',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) )
      | ~ ( v4_relat_1 @ X4 @ X6 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc23_relat_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_E )
      | ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['28','29'])).

thf('38',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['33','38'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('40',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X23 ) @ X24 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X23 ) @ X25 )
      | ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_E @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ sk_E )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['20','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['28','29'])).

thf('46',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_E @ X0 ) @ X1 )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('49',plain,
    ( ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(split,[status(esa)],['0'])).

thf('50',plain,
    ( ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
   <= ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','50'])).

thf('52',plain,
    ( ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C )
    | ~ ( m1_subset_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) )
    | ~ ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) ) ),
    inference(split,[status(esa)],['0'])).

thf('53',plain,(
    ~ ( v1_funct_2 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['14','51','52'])).

thf('54',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['7','53'])).

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

thf('55',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('56',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','46'])).

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

thf('57',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('58',plain,
    ( ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B )
    | ~ ( zip_tseitin_0 @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B ) ),
    inference('sup-',[status(thm)],['55','58'])).

thf('60',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','46'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('61',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('62',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    r1_tarski @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_2 @ sk_E @ sk_A @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ( X28
        = ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('66',plain,
    ( ~ ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X26: $i,X27: $i] :
      ( ( zip_tseitin_0 @ X26 @ X27 )
      | ( X26 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('68',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( zip_tseitin_0 @ X0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( zip_tseitin_0 @ X31 @ X32 )
      | ( zip_tseitin_1 @ X33 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('72',plain,
    ( ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( zip_tseitin_1 @ sk_E @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['69','72'])).

thf('74',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    zip_tseitin_1 @ sk_E @ sk_D @ sk_A ),
    inference(clc,[status(thm)],['73','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('78',plain,
    ( ( k1_relset_1 @ sk_A @ sk_D @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,
    ( sk_A
    = ( k1_relat_1 @ sk_E ) ),
    inference(demod,[status(thm)],['66','75','78'])).

thf(t91_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
       => ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) )
          = A ) ) ) )).

thf('80',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ X11 @ ( k1_relat_1 @ X12 ) )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ X12 @ X11 ) )
        = X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t91_relat_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ~ ( v1_relat_1 @ sk_E )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_relat_1 @ sk_E ),
    inference(demod,[status(thm)],['28','29'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_A )
      | ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ X0 ) )
        = X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( ( k1_relat_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference('sup-',[status(thm)],['63','83'])).

thf('85',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['62','84'])).

thf('86',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( X28
       != ( k1_relset_1 @ X28 @ X29 @ X30 ) )
      | ( v1_funct_2 @ X30 @ X28 @ X29 )
      | ~ ( zip_tseitin_1 @ X30 @ X29 @ X28 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('87',plain,
    ( ( sk_B != sk_B )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C )
    | ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['7','53'])).

thf('90',plain,(
    ~ ( zip_tseitin_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_C @ sk_B ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['59','90'])).

thf('92',plain,(
    ~ ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','91'])).

thf('93',plain,(
    m1_subset_1 @ ( k7_relat_1 @ sk_E @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['19','46'])).

thf(t130_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( k1_relset_1 @ A @ B @ C )
          = A )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) )).

thf('94',plain,(
    ! [X42: $i,X43: $i,X44: $i] :
      ( ( ( k1_relset_1 @ X42 @ X43 @ X44 )
       != X42 )
      | ( v1_funct_2 @ X44 @ X42 @ X43 )
      | ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t130_funct_2])).

thf('95',plain,
    ( ~ ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    | ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C )
    | ( ( k1_relset_1 @ sk_B @ sk_C @ ( k7_relat_1 @ sk_E @ sk_B ) )
     != sk_B ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('98',plain,(
    ! [X0: $i] :
      ( v1_funct_1 @ ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['96','97'])).

thf('99',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ sk_C )
    | ( ( k1_relset_1 @ sk_B @ sk_C @ ( k7_relat_1 @ sk_E @ sk_B ) )
     != sk_B ) ),
    inference(demod,[status(thm)],['95','98'])).

thf('100',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['59','90'])).

thf('101',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['59','90'])).

thf('102',plain,
    ( ( k1_relset_1 @ sk_B @ sk_C @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['62','84'])).

thf('103',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['59','90'])).

thf('104',plain,
    ( ( k1_relset_1 @ sk_B @ k1_xboole_0 @ ( k7_relat_1 @ sk_E @ sk_B ) )
    = sk_B ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ k1_xboole_0 )
    | ( sk_B != sk_B ) ),
    inference(demod,[status(thm)],['99','100','101','104'])).

thf('106',plain,(
    v1_funct_2 @ ( k7_relat_1 @ sk_E @ sk_B ) @ sk_B @ k1_xboole_0 ),
    inference(simplify,[status(thm)],['105'])).

thf('107',plain,(
    $false ),
    inference(demod,[status(thm)],['92','106'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ixs5M5LPSY
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:37:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.71/0.92  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.71/0.92  % Solved by: fo/fo7.sh
% 0.71/0.92  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.71/0.92  % done 400 iterations in 0.458s
% 0.71/0.92  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.71/0.92  % SZS output start Refutation
% 0.71/0.92  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.71/0.92  thf(sk_C_type, type, sk_C: $i).
% 0.71/0.92  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.71/0.92  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.71/0.92  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.71/0.92  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.71/0.92  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.71/0.92  thf(sk_B_type, type, sk_B: $i).
% 0.71/0.92  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.71/0.92  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.71/0.92  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.71/0.92  thf(sk_E_type, type, sk_E: $i).
% 0.71/0.92  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.71/0.92  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.71/0.92  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.71/0.92  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.71/0.92  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.71/0.92  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.71/0.92  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.71/0.92  thf(sk_D_type, type, sk_D: $i).
% 0.71/0.92  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.71/0.92  thf(sk_A_type, type, sk_A: $i).
% 0.71/0.92  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.71/0.92  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.71/0.92  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.71/0.92  thf(t178_funct_2, conjecture,
% 0.71/0.92    (![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.92     ( ( ~( v1_xboole_0 @ D ) ) =>
% 0.71/0.92       ( ![E:$i]:
% 0.71/0.92         ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ D ) & 
% 0.71/0.92             ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) =>
% 0.71/0.92           ( ( ( r1_tarski @ B @ A ) & 
% 0.71/0.92               ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) ) =>
% 0.71/0.92             ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) ) & 
% 0.71/0.92               ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C ) & 
% 0.71/0.92               ( m1_subset_1 @
% 0.71/0.92                 ( k2_partfun1 @ A @ D @ E @ B ) @ 
% 0.71/0.92                 ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ))).
% 0.71/0.92  thf(zf_stmt_0, negated_conjecture,
% 0.71/0.92    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.92        ( ( ~( v1_xboole_0 @ D ) ) =>
% 0.71/0.92          ( ![E:$i]:
% 0.71/0.92            ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ D ) & 
% 0.71/0.92                ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ D ) ) ) ) =>
% 0.71/0.92              ( ( ( r1_tarski @ B @ A ) & 
% 0.71/0.92                  ( r1_tarski @ ( k7_relset_1 @ A @ D @ E @ B ) @ C ) ) =>
% 0.71/0.92                ( ( v1_funct_1 @ ( k2_partfun1 @ A @ D @ E @ B ) ) & 
% 0.71/0.92                  ( v1_funct_2 @ ( k2_partfun1 @ A @ D @ E @ B ) @ B @ C ) & 
% 0.71/0.92                  ( m1_subset_1 @
% 0.71/0.92                    ( k2_partfun1 @ A @ D @ E @ B ) @ 
% 0.71/0.92                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) ) ) ) )),
% 0.71/0.92    inference('cnf.neg', [status(esa)], [t178_funct_2])).
% 0.71/0.92  thf('0', plain,
% 0.71/0.92      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B))
% 0.71/0.92        | ~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ 
% 0.71/0.92             sk_C)
% 0.71/0.92        | ~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 0.71/0.92             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('1', plain,
% 0.71/0.92      ((~ (v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ sk_C))
% 0.71/0.92         <= (~
% 0.71/0.92             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ 
% 0.71/0.92               sk_C)))),
% 0.71/0.92      inference('split', [status(esa)], ['0'])).
% 0.71/0.92  thf('2', plain,
% 0.71/0.92      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf(redefinition_k2_partfun1, axiom,
% 0.71/0.92    (![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.92     ( ( ( v1_funct_1 @ C ) & 
% 0.71/0.92         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.71/0.92       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.71/0.92  thf('3', plain,
% 0.71/0.92      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.71/0.92         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.71/0.92          | ~ (v1_funct_1 @ X38)
% 0.71/0.92          | ((k2_partfun1 @ X39 @ X40 @ X38 @ X41) = (k7_relat_1 @ X38 @ X41)))),
% 0.71/0.92      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.71/0.92  thf('4', plain,
% 0.71/0.92      (![X0 : $i]:
% 0.71/0.92         (((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 0.71/0.92          | ~ (v1_funct_1 @ sk_E))),
% 0.71/0.92      inference('sup-', [status(thm)], ['2', '3'])).
% 0.71/0.92  thf('5', plain, ((v1_funct_1 @ sk_E)),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('6', plain,
% 0.71/0.92      (![X0 : $i]:
% 0.71/0.92         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.71/0.92      inference('demod', [status(thm)], ['4', '5'])).
% 0.71/0.92  thf('7', plain,
% 0.71/0.92      ((~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C))
% 0.71/0.92         <= (~
% 0.71/0.92             ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ 
% 0.71/0.92               sk_C)))),
% 0.71/0.92      inference('demod', [status(thm)], ['1', '6'])).
% 0.71/0.92  thf('8', plain,
% 0.71/0.92      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf(dt_k2_partfun1, axiom,
% 0.71/0.92    (![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.92     ( ( ( v1_funct_1 @ C ) & 
% 0.71/0.92         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.71/0.92       ( ( v1_funct_1 @ ( k2_partfun1 @ A @ B @ C @ D ) ) & 
% 0.71/0.92         ( m1_subset_1 @
% 0.71/0.92           ( k2_partfun1 @ A @ B @ C @ D ) @ 
% 0.71/0.92           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.71/0.92  thf('9', plain,
% 0.71/0.92      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.71/0.92         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.71/0.92          | ~ (v1_funct_1 @ X34)
% 0.71/0.92          | (v1_funct_1 @ (k2_partfun1 @ X35 @ X36 @ X34 @ X37)))),
% 0.71/0.92      inference('cnf', [status(esa)], [dt_k2_partfun1])).
% 0.71/0.92  thf('10', plain,
% 0.71/0.92      (![X0 : $i]:
% 0.71/0.92         ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))
% 0.71/0.92          | ~ (v1_funct_1 @ sk_E))),
% 0.71/0.92      inference('sup-', [status(thm)], ['8', '9'])).
% 0.71/0.92  thf('11', plain, ((v1_funct_1 @ sk_E)),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('12', plain,
% 0.71/0.92      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))),
% 0.71/0.92      inference('demod', [status(thm)], ['10', '11'])).
% 0.71/0.92  thf('13', plain,
% 0.71/0.92      ((~ (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B)))
% 0.71/0.92         <= (~ ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B))))),
% 0.71/0.92      inference('split', [status(esa)], ['0'])).
% 0.71/0.92  thf('14', plain,
% 0.71/0.92      (((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B)))),
% 0.71/0.92      inference('sup-', [status(thm)], ['12', '13'])).
% 0.71/0.92  thf('15', plain,
% 0.71/0.92      ((r1_tarski @ (k7_relset_1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_C)),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('16', plain,
% 0.71/0.92      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf(redefinition_k7_relset_1, axiom,
% 0.71/0.92    (![A:$i,B:$i,C:$i,D:$i]:
% 0.71/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.92       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.71/0.92  thf('17', plain,
% 0.71/0.92      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.71/0.92         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.71/0.92          | ((k7_relset_1 @ X20 @ X21 @ X19 @ X22) = (k9_relat_1 @ X19 @ X22)))),
% 0.71/0.92      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.71/0.92  thf('18', plain,
% 0.71/0.92      (![X0 : $i]:
% 0.71/0.92         ((k7_relset_1 @ sk_A @ sk_D @ sk_E @ X0) = (k9_relat_1 @ sk_E @ X0))),
% 0.71/0.92      inference('sup-', [status(thm)], ['16', '17'])).
% 0.71/0.92  thf('19', plain, ((r1_tarski @ (k9_relat_1 @ sk_E @ sk_B) @ sk_C)),
% 0.71/0.92      inference('demod', [status(thm)], ['15', '18'])).
% 0.71/0.92  thf(t148_relat_1, axiom,
% 0.71/0.92    (![A:$i,B:$i]:
% 0.71/0.92     ( ( v1_relat_1 @ B ) =>
% 0.71/0.92       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.71/0.92  thf('20', plain,
% 0.71/0.92      (![X9 : $i, X10 : $i]:
% 0.71/0.92         (((k2_relat_1 @ (k7_relat_1 @ X9 @ X10)) = (k9_relat_1 @ X9 @ X10))
% 0.71/0.92          | ~ (v1_relat_1 @ X9))),
% 0.71/0.92      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.71/0.92  thf('21', plain,
% 0.71/0.92      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf(cc2_relset_1, axiom,
% 0.71/0.92    (![A:$i,B:$i,C:$i]:
% 0.71/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.92       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.71/0.92  thf('22', plain,
% 0.71/0.92      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.71/0.92         ((v4_relat_1 @ X13 @ X14)
% 0.71/0.92          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.71/0.92      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.71/0.92  thf('23', plain, ((v4_relat_1 @ sk_E @ sk_A)),
% 0.71/0.92      inference('sup-', [status(thm)], ['21', '22'])).
% 0.71/0.92  thf(fc23_relat_1, axiom,
% 0.71/0.92    (![A:$i,B:$i,C:$i]:
% 0.71/0.92     ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ B ) ) =>
% 0.71/0.92       ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) ) & 
% 0.71/0.92         ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ A ) & 
% 0.71/0.92         ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ))).
% 0.71/0.92  thf('24', plain,
% 0.71/0.92      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.71/0.92         ((v4_relat_1 @ (k7_relat_1 @ X4 @ X5) @ X5)
% 0.71/0.92          | ~ (v4_relat_1 @ X4 @ X6)
% 0.71/0.92          | ~ (v1_relat_1 @ X4))),
% 0.71/0.92      inference('cnf', [status(esa)], [fc23_relat_1])).
% 0.71/0.92  thf('25', plain,
% 0.71/0.92      (![X0 : $i]:
% 0.71/0.92         (~ (v1_relat_1 @ sk_E) | (v4_relat_1 @ (k7_relat_1 @ sk_E @ X0) @ X0))),
% 0.71/0.92      inference('sup-', [status(thm)], ['23', '24'])).
% 0.71/0.92  thf('26', plain,
% 0.71/0.92      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf(cc2_relat_1, axiom,
% 0.71/0.92    (![A:$i]:
% 0.71/0.92     ( ( v1_relat_1 @ A ) =>
% 0.71/0.92       ( ![B:$i]:
% 0.71/0.92         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.71/0.92  thf('27', plain,
% 0.71/0.92      (![X0 : $i, X1 : $i]:
% 0.71/0.92         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.71/0.92          | (v1_relat_1 @ X0)
% 0.71/0.92          | ~ (v1_relat_1 @ X1))),
% 0.71/0.92      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.71/0.92  thf('28', plain,
% 0.71/0.92      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)) | (v1_relat_1 @ sk_E))),
% 0.71/0.92      inference('sup-', [status(thm)], ['26', '27'])).
% 0.71/0.92  thf(fc6_relat_1, axiom,
% 0.71/0.92    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.71/0.92  thf('29', plain,
% 0.71/0.92      (![X7 : $i, X8 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X7 @ X8))),
% 0.71/0.92      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.71/0.92  thf('30', plain, ((v1_relat_1 @ sk_E)),
% 0.71/0.92      inference('demod', [status(thm)], ['28', '29'])).
% 0.71/0.92  thf('31', plain, (![X0 : $i]: (v4_relat_1 @ (k7_relat_1 @ sk_E @ X0) @ X0)),
% 0.71/0.92      inference('demod', [status(thm)], ['25', '30'])).
% 0.71/0.92  thf(d18_relat_1, axiom,
% 0.71/0.92    (![A:$i,B:$i]:
% 0.71/0.92     ( ( v1_relat_1 @ B ) =>
% 0.71/0.92       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.71/0.92  thf('32', plain,
% 0.71/0.92      (![X2 : $i, X3 : $i]:
% 0.71/0.92         (~ (v4_relat_1 @ X2 @ X3)
% 0.71/0.92          | (r1_tarski @ (k1_relat_1 @ X2) @ X3)
% 0.71/0.92          | ~ (v1_relat_1 @ X2))),
% 0.71/0.92      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.71/0.92  thf('33', plain,
% 0.71/0.92      (![X0 : $i]:
% 0.71/0.92         (~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))
% 0.71/0.92          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_E @ X0)) @ X0))),
% 0.71/0.92      inference('sup-', [status(thm)], ['31', '32'])).
% 0.71/0.92  thf('34', plain, ((v4_relat_1 @ sk_E @ sk_A)),
% 0.71/0.92      inference('sup-', [status(thm)], ['21', '22'])).
% 0.71/0.92  thf('35', plain,
% 0.71/0.92      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.71/0.92         ((v1_relat_1 @ (k7_relat_1 @ X4 @ X5))
% 0.71/0.92          | ~ (v4_relat_1 @ X4 @ X6)
% 0.71/0.92          | ~ (v1_relat_1 @ X4))),
% 0.71/0.92      inference('cnf', [status(esa)], [fc23_relat_1])).
% 0.71/0.92  thf('36', plain,
% 0.71/0.92      (![X0 : $i]:
% 0.71/0.92         (~ (v1_relat_1 @ sk_E) | (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0)))),
% 0.71/0.92      inference('sup-', [status(thm)], ['34', '35'])).
% 0.71/0.92  thf('37', plain, ((v1_relat_1 @ sk_E)),
% 0.71/0.92      inference('demod', [status(thm)], ['28', '29'])).
% 0.71/0.92  thf('38', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))),
% 0.71/0.92      inference('demod', [status(thm)], ['36', '37'])).
% 0.71/0.92  thf('39', plain,
% 0.71/0.92      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_E @ X0)) @ X0)),
% 0.71/0.92      inference('demod', [status(thm)], ['33', '38'])).
% 0.71/0.92  thf(t11_relset_1, axiom,
% 0.71/0.92    (![A:$i,B:$i,C:$i]:
% 0.71/0.92     ( ( v1_relat_1 @ C ) =>
% 0.71/0.92       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.71/0.92           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.71/0.92         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.71/0.92  thf('40', plain,
% 0.71/0.92      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.71/0.92         (~ (r1_tarski @ (k1_relat_1 @ X23) @ X24)
% 0.71/0.92          | ~ (r1_tarski @ (k2_relat_1 @ X23) @ X25)
% 0.71/0.92          | (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.71/0.92          | ~ (v1_relat_1 @ X23))),
% 0.71/0.92      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.71/0.92  thf('41', plain,
% 0.71/0.92      (![X0 : $i, X1 : $i]:
% 0.71/0.92         (~ (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))
% 0.71/0.92          | (m1_subset_1 @ (k7_relat_1 @ sk_E @ X0) @ 
% 0.71/0.92             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.71/0.92          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_E @ X0)) @ X1))),
% 0.71/0.92      inference('sup-', [status(thm)], ['39', '40'])).
% 0.71/0.92  thf('42', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_E @ X0))),
% 0.71/0.92      inference('demod', [status(thm)], ['36', '37'])).
% 0.71/0.92  thf('43', plain,
% 0.71/0.92      (![X0 : $i, X1 : $i]:
% 0.71/0.92         ((m1_subset_1 @ (k7_relat_1 @ sk_E @ X0) @ 
% 0.71/0.92           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.71/0.92          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_E @ X0)) @ X1))),
% 0.71/0.92      inference('demod', [status(thm)], ['41', '42'])).
% 0.71/0.92  thf('44', plain,
% 0.71/0.92      (![X0 : $i, X1 : $i]:
% 0.71/0.92         (~ (r1_tarski @ (k9_relat_1 @ sk_E @ X0) @ X1)
% 0.71/0.92          | ~ (v1_relat_1 @ sk_E)
% 0.71/0.92          | (m1_subset_1 @ (k7_relat_1 @ sk_E @ X0) @ 
% 0.71/0.92             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 0.71/0.92      inference('sup-', [status(thm)], ['20', '43'])).
% 0.71/0.92  thf('45', plain, ((v1_relat_1 @ sk_E)),
% 0.71/0.92      inference('demod', [status(thm)], ['28', '29'])).
% 0.71/0.92  thf('46', plain,
% 0.71/0.92      (![X0 : $i, X1 : $i]:
% 0.71/0.92         (~ (r1_tarski @ (k9_relat_1 @ sk_E @ X0) @ X1)
% 0.71/0.92          | (m1_subset_1 @ (k7_relat_1 @ sk_E @ X0) @ 
% 0.71/0.92             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 0.71/0.92      inference('demod', [status(thm)], ['44', '45'])).
% 0.71/0.92  thf('47', plain,
% 0.71/0.92      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 0.71/0.92        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.71/0.92      inference('sup-', [status(thm)], ['19', '46'])).
% 0.71/0.92  thf('48', plain,
% 0.71/0.92      (![X0 : $i]:
% 0.71/0.92         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.71/0.92      inference('demod', [status(thm)], ['4', '5'])).
% 0.71/0.92  thf('49', plain,
% 0.71/0.92      ((~ (m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 0.71/0.92           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))
% 0.71/0.92         <= (~
% 0.71/0.92             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 0.71/0.92               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))))),
% 0.71/0.92      inference('split', [status(esa)], ['0'])).
% 0.71/0.92  thf('50', plain,
% 0.71/0.92      ((~ (m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 0.71/0.92           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))
% 0.71/0.92         <= (~
% 0.71/0.92             ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 0.71/0.92               (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))))),
% 0.71/0.92      inference('sup-', [status(thm)], ['48', '49'])).
% 0.71/0.92  thf('51', plain,
% 0.71/0.92      (((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 0.71/0.92         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 0.71/0.92      inference('sup-', [status(thm)], ['47', '50'])).
% 0.71/0.92  thf('52', plain,
% 0.71/0.92      (~
% 0.71/0.92       ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ sk_C)) | 
% 0.71/0.92       ~
% 0.71/0.92       ((m1_subset_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ 
% 0.71/0.92         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))) | 
% 0.71/0.92       ~ ((v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B)))),
% 0.71/0.92      inference('split', [status(esa)], ['0'])).
% 0.71/0.92  thf('53', plain,
% 0.71/0.92      (~
% 0.71/0.92       ((v1_funct_2 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ sk_B) @ sk_B @ sk_C))),
% 0.71/0.92      inference('sat_resolution*', [status(thm)], ['14', '51', '52'])).
% 0.71/0.92  thf('54', plain, (~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)),
% 0.71/0.92      inference('simpl_trail', [status(thm)], ['7', '53'])).
% 0.71/0.92  thf(d1_funct_2, axiom,
% 0.71/0.92    (![A:$i,B:$i,C:$i]:
% 0.71/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.92       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.71/0.92           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.71/0.92             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.71/0.92         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.71/0.92           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.71/0.92             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.71/0.92  thf(zf_stmt_1, axiom,
% 0.71/0.92    (![B:$i,A:$i]:
% 0.71/0.92     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.71/0.92       ( zip_tseitin_0 @ B @ A ) ))).
% 0.71/0.92  thf('55', plain,
% 0.71/0.92      (![X26 : $i, X27 : $i]:
% 0.71/0.92         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.71/0.92  thf('56', plain,
% 0.71/0.92      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 0.71/0.92        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.71/0.92      inference('sup-', [status(thm)], ['19', '46'])).
% 0.71/0.92  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.71/0.92  thf(zf_stmt_3, axiom,
% 0.71/0.92    (![C:$i,B:$i,A:$i]:
% 0.71/0.92     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.71/0.92       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.71/0.92  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.71/0.92  thf(zf_stmt_5, axiom,
% 0.71/0.92    (![A:$i,B:$i,C:$i]:
% 0.71/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.92       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.71/0.92         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.71/0.92           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.71/0.92             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.71/0.92  thf('57', plain,
% 0.71/0.92      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.71/0.92         (~ (zip_tseitin_0 @ X31 @ X32)
% 0.71/0.92          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 0.71/0.92          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.71/0.92  thf('58', plain,
% 0.71/0.92      (((zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B)
% 0.71/0.92        | ~ (zip_tseitin_0 @ sk_C @ sk_B))),
% 0.71/0.92      inference('sup-', [status(thm)], ['56', '57'])).
% 0.71/0.92  thf('59', plain,
% 0.71/0.92      ((((sk_C) = (k1_xboole_0))
% 0.71/0.92        | (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B))),
% 0.71/0.92      inference('sup-', [status(thm)], ['55', '58'])).
% 0.71/0.92  thf('60', plain,
% 0.71/0.92      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 0.71/0.92        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.71/0.92      inference('sup-', [status(thm)], ['19', '46'])).
% 0.71/0.92  thf(redefinition_k1_relset_1, axiom,
% 0.71/0.92    (![A:$i,B:$i,C:$i]:
% 0.71/0.92     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.71/0.92       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.71/0.92  thf('61', plain,
% 0.71/0.92      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.71/0.92         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.71/0.92          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.71/0.92      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.71/0.92  thf('62', plain,
% 0.71/0.92      (((k1_relset_1 @ sk_B @ sk_C @ (k7_relat_1 @ sk_E @ sk_B))
% 0.71/0.92         = (k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)))),
% 0.71/0.92      inference('sup-', [status(thm)], ['60', '61'])).
% 0.71/0.92  thf('63', plain, ((r1_tarski @ sk_B @ sk_A)),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('64', plain, ((v1_funct_2 @ sk_E @ sk_A @ sk_D)),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('65', plain,
% 0.71/0.92      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.71/0.92         (~ (v1_funct_2 @ X30 @ X28 @ X29)
% 0.71/0.92          | ((X28) = (k1_relset_1 @ X28 @ X29 @ X30))
% 0.71/0.92          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.71/0.92  thf('66', plain,
% 0.71/0.92      ((~ (zip_tseitin_1 @ sk_E @ sk_D @ sk_A)
% 0.71/0.92        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_D @ sk_E)))),
% 0.71/0.92      inference('sup-', [status(thm)], ['64', '65'])).
% 0.71/0.92  thf('67', plain,
% 0.71/0.92      (![X26 : $i, X27 : $i]:
% 0.71/0.92         ((zip_tseitin_0 @ X26 @ X27) | ((X26) = (k1_xboole_0)))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.71/0.92  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.71/0.92  thf('68', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.71/0.92      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.71/0.92  thf('69', plain,
% 0.71/0.92      (![X0 : $i, X1 : $i]: ((v1_xboole_0 @ X0) | (zip_tseitin_0 @ X0 @ X1))),
% 0.71/0.92      inference('sup+', [status(thm)], ['67', '68'])).
% 0.71/0.92  thf('70', plain,
% 0.71/0.92      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('71', plain,
% 0.71/0.92      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.71/0.92         (~ (zip_tseitin_0 @ X31 @ X32)
% 0.71/0.92          | (zip_tseitin_1 @ X33 @ X31 @ X32)
% 0.71/0.92          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31))))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.71/0.92  thf('72', plain,
% 0.71/0.92      (((zip_tseitin_1 @ sk_E @ sk_D @ sk_A) | ~ (zip_tseitin_0 @ sk_D @ sk_A))),
% 0.71/0.92      inference('sup-', [status(thm)], ['70', '71'])).
% 0.71/0.92  thf('73', plain,
% 0.71/0.92      (((v1_xboole_0 @ sk_D) | (zip_tseitin_1 @ sk_E @ sk_D @ sk_A))),
% 0.71/0.92      inference('sup-', [status(thm)], ['69', '72'])).
% 0.71/0.92  thf('74', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('75', plain, ((zip_tseitin_1 @ sk_E @ sk_D @ sk_A)),
% 0.71/0.92      inference('clc', [status(thm)], ['73', '74'])).
% 0.71/0.92  thf('76', plain,
% 0.71/0.92      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_D)))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.71/0.92  thf('77', plain,
% 0.71/0.92      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.71/0.92         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.71/0.92          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.71/0.92      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.71/0.92  thf('78', plain,
% 0.71/0.92      (((k1_relset_1 @ sk_A @ sk_D @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.71/0.92      inference('sup-', [status(thm)], ['76', '77'])).
% 0.71/0.92  thf('79', plain, (((sk_A) = (k1_relat_1 @ sk_E))),
% 0.71/0.92      inference('demod', [status(thm)], ['66', '75', '78'])).
% 0.71/0.92  thf(t91_relat_1, axiom,
% 0.71/0.92    (![A:$i,B:$i]:
% 0.71/0.92     ( ( v1_relat_1 @ B ) =>
% 0.71/0.92       ( ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) =>
% 0.71/0.92         ( ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( A ) ) ) ))).
% 0.71/0.92  thf('80', plain,
% 0.71/0.92      (![X11 : $i, X12 : $i]:
% 0.71/0.92         (~ (r1_tarski @ X11 @ (k1_relat_1 @ X12))
% 0.71/0.92          | ((k1_relat_1 @ (k7_relat_1 @ X12 @ X11)) = (X11))
% 0.71/0.92          | ~ (v1_relat_1 @ X12))),
% 0.71/0.92      inference('cnf', [status(esa)], [t91_relat_1])).
% 0.71/0.92  thf('81', plain,
% 0.71/0.92      (![X0 : $i]:
% 0.71/0.92         (~ (r1_tarski @ X0 @ sk_A)
% 0.71/0.92          | ~ (v1_relat_1 @ sk_E)
% 0.71/0.92          | ((k1_relat_1 @ (k7_relat_1 @ sk_E @ X0)) = (X0)))),
% 0.71/0.92      inference('sup-', [status(thm)], ['79', '80'])).
% 0.71/0.92  thf('82', plain, ((v1_relat_1 @ sk_E)),
% 0.71/0.92      inference('demod', [status(thm)], ['28', '29'])).
% 0.71/0.92  thf('83', plain,
% 0.71/0.92      (![X0 : $i]:
% 0.71/0.92         (~ (r1_tarski @ X0 @ sk_A)
% 0.71/0.92          | ((k1_relat_1 @ (k7_relat_1 @ sk_E @ X0)) = (X0)))),
% 0.71/0.92      inference('demod', [status(thm)], ['81', '82'])).
% 0.71/0.92  thf('84', plain, (((k1_relat_1 @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 0.71/0.92      inference('sup-', [status(thm)], ['63', '83'])).
% 0.71/0.92  thf('85', plain,
% 0.71/0.92      (((k1_relset_1 @ sk_B @ sk_C @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 0.71/0.92      inference('demod', [status(thm)], ['62', '84'])).
% 0.71/0.92  thf('86', plain,
% 0.71/0.92      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.71/0.92         (((X28) != (k1_relset_1 @ X28 @ X29 @ X30))
% 0.71/0.92          | (v1_funct_2 @ X30 @ X28 @ X29)
% 0.71/0.92          | ~ (zip_tseitin_1 @ X30 @ X29 @ X28))),
% 0.71/0.92      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.71/0.92  thf('87', plain,
% 0.71/0.92      ((((sk_B) != (sk_B))
% 0.71/0.92        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B)
% 0.71/0.92        | (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C))),
% 0.71/0.92      inference('sup-', [status(thm)], ['85', '86'])).
% 0.71/0.92  thf('88', plain,
% 0.71/0.92      (((v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)
% 0.71/0.92        | ~ (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B))),
% 0.71/0.92      inference('simplify', [status(thm)], ['87'])).
% 0.71/0.92  thf('89', plain, (~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)),
% 0.71/0.92      inference('simpl_trail', [status(thm)], ['7', '53'])).
% 0.71/0.92  thf('90', plain,
% 0.71/0.92      (~ (zip_tseitin_1 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_C @ sk_B)),
% 0.71/0.92      inference('clc', [status(thm)], ['88', '89'])).
% 0.71/0.92  thf('91', plain, (((sk_C) = (k1_xboole_0))),
% 0.71/0.92      inference('sup-', [status(thm)], ['59', '90'])).
% 0.71/0.92  thf('92', plain,
% 0.71/0.92      (~ (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ k1_xboole_0)),
% 0.71/0.92      inference('demod', [status(thm)], ['54', '91'])).
% 0.71/0.92  thf('93', plain,
% 0.71/0.92      ((m1_subset_1 @ (k7_relat_1 @ sk_E @ sk_B) @ 
% 0.71/0.92        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.71/0.92      inference('sup-', [status(thm)], ['19', '46'])).
% 0.71/0.92  thf(t130_funct_2, axiom,
% 0.71/0.92    (![A:$i,B:$i,C:$i]:
% 0.71/0.92     ( ( ( v1_funct_1 @ C ) & 
% 0.71/0.92         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.71/0.92       ( ( ( k1_relset_1 @ A @ B @ C ) = ( A ) ) =>
% 0.71/0.92         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.71/0.92           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ))).
% 0.71/0.92  thf('94', plain,
% 0.71/0.92      (![X42 : $i, X43 : $i, X44 : $i]:
% 0.71/0.92         (((k1_relset_1 @ X42 @ X43 @ X44) != (X42))
% 0.71/0.92          | (v1_funct_2 @ X44 @ X42 @ X43)
% 0.71/0.92          | ~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 0.71/0.92          | ~ (v1_funct_1 @ X44))),
% 0.71/0.92      inference('cnf', [status(esa)], [t130_funct_2])).
% 0.71/0.92  thf('95', plain,
% 0.71/0.92      ((~ (v1_funct_1 @ (k7_relat_1 @ sk_E @ sk_B))
% 0.71/0.92        | (v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)
% 0.71/0.92        | ((k1_relset_1 @ sk_B @ sk_C @ (k7_relat_1 @ sk_E @ sk_B)) != (sk_B)))),
% 0.71/0.92      inference('sup-', [status(thm)], ['93', '94'])).
% 0.71/0.92  thf('96', plain,
% 0.71/0.92      (![X0 : $i]: (v1_funct_1 @ (k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0))),
% 0.71/0.92      inference('demod', [status(thm)], ['10', '11'])).
% 0.71/0.92  thf('97', plain,
% 0.71/0.92      (![X0 : $i]:
% 0.71/0.92         ((k2_partfun1 @ sk_A @ sk_D @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.71/0.92      inference('demod', [status(thm)], ['4', '5'])).
% 0.71/0.92  thf('98', plain, (![X0 : $i]: (v1_funct_1 @ (k7_relat_1 @ sk_E @ X0))),
% 0.71/0.92      inference('demod', [status(thm)], ['96', '97'])).
% 0.71/0.92  thf('99', plain,
% 0.71/0.92      (((v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ sk_C)
% 0.71/0.92        | ((k1_relset_1 @ sk_B @ sk_C @ (k7_relat_1 @ sk_E @ sk_B)) != (sk_B)))),
% 0.71/0.92      inference('demod', [status(thm)], ['95', '98'])).
% 0.71/0.92  thf('100', plain, (((sk_C) = (k1_xboole_0))),
% 0.71/0.92      inference('sup-', [status(thm)], ['59', '90'])).
% 0.71/0.92  thf('101', plain, (((sk_C) = (k1_xboole_0))),
% 0.71/0.92      inference('sup-', [status(thm)], ['59', '90'])).
% 0.71/0.92  thf('102', plain,
% 0.71/0.92      (((k1_relset_1 @ sk_B @ sk_C @ (k7_relat_1 @ sk_E @ sk_B)) = (sk_B))),
% 0.71/0.92      inference('demod', [status(thm)], ['62', '84'])).
% 0.71/0.92  thf('103', plain, (((sk_C) = (k1_xboole_0))),
% 0.71/0.92      inference('sup-', [status(thm)], ['59', '90'])).
% 0.71/0.92  thf('104', plain,
% 0.71/0.92      (((k1_relset_1 @ sk_B @ k1_xboole_0 @ (k7_relat_1 @ sk_E @ sk_B))
% 0.71/0.92         = (sk_B))),
% 0.71/0.92      inference('demod', [status(thm)], ['102', '103'])).
% 0.71/0.92  thf('105', plain,
% 0.71/0.92      (((v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ k1_xboole_0)
% 0.71/0.92        | ((sk_B) != (sk_B)))),
% 0.71/0.92      inference('demod', [status(thm)], ['99', '100', '101', '104'])).
% 0.71/0.92  thf('106', plain,
% 0.71/0.92      ((v1_funct_2 @ (k7_relat_1 @ sk_E @ sk_B) @ sk_B @ k1_xboole_0)),
% 0.71/0.92      inference('simplify', [status(thm)], ['105'])).
% 0.71/0.92  thf('107', plain, ($false), inference('demod', [status(thm)], ['92', '106'])).
% 0.71/0.92  
% 0.71/0.92  % SZS output end Refutation
% 0.71/0.92  
% 0.75/0.93  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
