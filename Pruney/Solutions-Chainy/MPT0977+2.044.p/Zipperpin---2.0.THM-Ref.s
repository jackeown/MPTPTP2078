%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3trbn2wc2p

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:50 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 142 expanded)
%              Number of leaves         :   33 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :  821 (1779 expanded)
%              Number of equality atoms :   26 (  33 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(t94_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ) )).

thf('0',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k7_relat_1 @ X12 @ X11 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X11 ) @ X12 ) )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t94_relat_1])).

thf(t23_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( r2_relset_1 @ A @ B @ ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ C )
        & ( r2_relset_1 @ A @ B @ ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ C ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
       => ( ( r2_relset_1 @ A @ B @ ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ C )
          & ( r2_relset_1 @ A @ B @ ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ C ) ) ) ),
    inference('cnf.neg',[status(esa)],[t23_funct_2])).

thf('1',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C )
    | ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference(split,[status(esa)],['1'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('4',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_relat_1 @ sk_A ) @ sk_C ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('6',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) )
      | ( r2_relset_1 @ X29 @ X30 @ X28 @ X31 )
      | ( X28 != X31 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('7',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( r2_relset_1 @ X29 @ X30 @ X31 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['5','7'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('9',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('10',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('11',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('13',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k4_relset_1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 )
        = ( k5_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k4_relset_1 @ sk_A @ sk_B @ X0 @ X0 @ sk_C @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['11','14'])).

thf('16',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference(split,[status(esa)],['1'])).

thf('17',plain,(
    ! [X34: $i] :
      ( ( k6_partfun1 @ X34 )
      = ( k6_relat_1 @ X34 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('18',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_relat_1 @ sk_B ) ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['16','17'])).

thf('19',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['15','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('21',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X16 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('22',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('24',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('26',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k2_relset_1 @ X20 @ X21 @ X19 )
        = ( k2_relat_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('27',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['24','27'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('29',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X9 ) @ X10 )
      | ( ( k5_relat_1 @ X9 @ ( k6_relat_1 @ X10 ) )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('32',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('34',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('35',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['30','35'])).

thf('37',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['19','36'])).

thf('38',plain,(
    r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ),
    inference('sup-',[status(thm)],['8','37'])).

thf('39',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C )
    | ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference(split,[status(esa)],['1'])).

thf('40',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_relat_1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['4','40'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    ! [X33: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('44',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( ( k4_relset_1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25 )
        = ( k5_relat_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_relset_1 @ X0 @ X0 @ X3 @ X2 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( k4_relset_1 @ X0 @ X0 @ sk_A @ sk_B @ ( k6_relat_1 @ X0 ) @ sk_C )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['42','45'])).

thf('47',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['41','46'])).

thf('48',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k7_relat_1 @ sk_C @ sk_A ) @ sk_C )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['0','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('50',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v4_relat_1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('51',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['49','50'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('52',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7
        = ( k7_relat_1 @ X7 @ X8 ) )
      | ~ ( v4_relat_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('53',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['33','34'])).

thf('55',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['5','7'])).

thf('57',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['33','34'])).

thf('58',plain,(
    $false ),
    inference(demod,[status(thm)],['48','55','56','57'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.3trbn2wc2p
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:09:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.52  % Solved by: fo/fo7.sh
% 0.20/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.52  % done 96 iterations in 0.067s
% 0.20/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.52  % SZS output start Refutation
% 0.20/0.52  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.20/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.52  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.52  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.52  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.52  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.20/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.52  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.52  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.20/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.52  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.52  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.52  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.52  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.20/0.52  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 0.20/0.52  thf(t94_relat_1, axiom,
% 0.20/0.52    (![A:$i,B:$i]:
% 0.20/0.52     ( ( v1_relat_1 @ B ) =>
% 0.20/0.52       ( ( k7_relat_1 @ B @ A ) = ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) ) ))).
% 0.20/0.52  thf('0', plain,
% 0.20/0.52      (![X11 : $i, X12 : $i]:
% 0.20/0.52         (((k7_relat_1 @ X12 @ X11) = (k5_relat_1 @ (k6_relat_1 @ X11) @ X12))
% 0.20/0.52          | ~ (v1_relat_1 @ X12))),
% 0.20/0.52      inference('cnf', [status(esa)], [t94_relat_1])).
% 0.20/0.52  thf(t23_funct_2, conjecture,
% 0.20/0.52    (![A:$i,B:$i,C:$i]:
% 0.20/0.52     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.52       ( ( r2_relset_1 @
% 0.20/0.52           A @ B @ ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ 
% 0.20/0.52           C ) & 
% 0.20/0.52         ( r2_relset_1 @
% 0.20/0.52           A @ B @ ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ 
% 0.20/0.52           C ) ) ))).
% 0.20/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.52    (~( ![A:$i,B:$i,C:$i]:
% 0.20/0.53        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53          ( ( r2_relset_1 @
% 0.20/0.53              A @ B @ 
% 0.20/0.53              ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ C ) & 
% 0.20/0.53            ( r2_relset_1 @
% 0.20/0.53              A @ B @ 
% 0.20/0.53              ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ C ) ) ) )),
% 0.20/0.53    inference('cnf.neg', [status(esa)], [t23_funct_2])).
% 0.20/0.53  thf('1', plain,
% 0.20/0.53      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.53           (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A) @ 
% 0.20/0.53            sk_C) @ 
% 0.20/0.53           sk_C)
% 0.20/0.53        | ~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.53             (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.20/0.53              (k6_partfun1 @ sk_B)) @ 
% 0.20/0.53             sk_C))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('2', plain,
% 0.20/0.53      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.53           (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A) @ 
% 0.20/0.53            sk_C) @ 
% 0.20/0.53           sk_C))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.53               (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.20/0.53                (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.20/0.53               sk_C)))),
% 0.20/0.53      inference('split', [status(esa)], ['1'])).
% 0.20/0.53  thf(redefinition_k6_partfun1, axiom,
% 0.20/0.53    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.20/0.53  thf('3', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.53  thf('4', plain,
% 0.20/0.53      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.53           (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_relat_1 @ sk_A) @ 
% 0.20/0.53            sk_C) @ 
% 0.20/0.53           sk_C))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.53               (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.20/0.53                (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.20/0.53               sk_C)))),
% 0.20/0.53      inference('demod', [status(thm)], ['2', '3'])).
% 0.20/0.53  thf('5', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(redefinition_r2_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.53     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.53         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.53       ( ( r2_relset_1 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.20/0.53  thf('6', plain,
% 0.20/0.53      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.20/0.53          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30)))
% 0.20/0.53          | (r2_relset_1 @ X29 @ X30 @ X28 @ X31)
% 0.20/0.53          | ((X28) != (X31)))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_r2_relset_1])).
% 0.20/0.53  thf('7', plain,
% 0.20/0.53      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.20/0.53         ((r2_relset_1 @ X29 @ X30 @ X31 @ X31)
% 0.20/0.53          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.20/0.53      inference('simplify', [status(thm)], ['6'])).
% 0.20/0.53  thf('8', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C)),
% 0.20/0.53      inference('sup-', [status(thm)], ['5', '7'])).
% 0.20/0.53  thf(dt_k6_partfun1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( m1_subset_1 @
% 0.20/0.53         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.20/0.53       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.20/0.53  thf('9', plain,
% 0.20/0.53      (![X33 : $i]:
% 0.20/0.53         (m1_subset_1 @ (k6_partfun1 @ X33) @ 
% 0.20/0.53          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.20/0.53  thf('10', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.53  thf('11', plain,
% 0.20/0.53      (![X33 : $i]:
% 0.20/0.53         (m1_subset_1 @ (k6_relat_1 @ X33) @ 
% 0.20/0.53          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 0.20/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.53  thf('12', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(redefinition_k4_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.53     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.53         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.20/0.53       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.20/0.53  thf('13', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.20/0.53          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.20/0.53          | ((k4_relset_1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25)
% 0.20/0.53              = (k5_relat_1 @ X22 @ X25)))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 0.20/0.53  thf('14', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.53         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.20/0.53            = (k5_relat_1 @ sk_C @ X0))
% 0.20/0.53          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.53  thf('15', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k4_relset_1 @ sk_A @ sk_B @ X0 @ X0 @ sk_C @ (k6_relat_1 @ X0))
% 0.20/0.53           = (k5_relat_1 @ sk_C @ (k6_relat_1 @ X0)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['11', '14'])).
% 0.20/0.53  thf('16', plain,
% 0.20/0.53      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.53           (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.20/0.53            (k6_partfun1 @ sk_B)) @ 
% 0.20/0.53           sk_C))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.53               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.20/0.53                (k6_partfun1 @ sk_B)) @ 
% 0.20/0.53               sk_C)))),
% 0.20/0.53      inference('split', [status(esa)], ['1'])).
% 0.20/0.53  thf('17', plain, (![X34 : $i]: ((k6_partfun1 @ X34) = (k6_relat_1 @ X34))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.53  thf('18', plain,
% 0.20/0.53      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.53           (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.20/0.53            (k6_relat_1 @ sk_B)) @ 
% 0.20/0.53           sk_C))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.53               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.20/0.53                (k6_partfun1 @ sk_B)) @ 
% 0.20/0.53               sk_C)))),
% 0.20/0.53      inference('demod', [status(thm)], ['16', '17'])).
% 0.20/0.53  thf('19', plain,
% 0.20/0.53      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.53           (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) @ sk_C))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.53               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.20/0.53                (k6_partfun1 @ sk_B)) @ 
% 0.20/0.53               sk_C)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['15', '18'])).
% 0.20/0.53  thf('20', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(dt_k2_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.20/0.53  thf('21', plain,
% 0.20/0.53      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.53         ((m1_subset_1 @ (k2_relset_1 @ X16 @ X17 @ X18) @ (k1_zfmisc_1 @ X17))
% 0.20/0.53          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.20/0.53      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.20/0.53  thf('22', plain,
% 0.20/0.53      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 0.20/0.53      inference('sup-', [status(thm)], ['20', '21'])).
% 0.20/0.53  thf(t3_subset, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.53  thf('23', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i]:
% 0.20/0.53         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.20/0.53      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.53  thf('24', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_C) @ sk_B)),
% 0.20/0.53      inference('sup-', [status(thm)], ['22', '23'])).
% 0.20/0.53  thf('25', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.53  thf('26', plain,
% 0.20/0.53      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.53         (((k2_relset_1 @ X20 @ X21 @ X19) = (k2_relat_1 @ X19))
% 0.20/0.53          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.53  thf('27', plain,
% 0.20/0.53      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['25', '26'])).
% 0.20/0.53  thf('28', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.20/0.53      inference('demod', [status(thm)], ['24', '27'])).
% 0.20/0.53  thf(t79_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ B ) =>
% 0.20/0.53       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.20/0.53         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.20/0.53  thf('29', plain,
% 0.20/0.53      (![X9 : $i, X10 : $i]:
% 0.20/0.53         (~ (r1_tarski @ (k2_relat_1 @ X9) @ X10)
% 0.20/0.53          | ((k5_relat_1 @ X9 @ (k6_relat_1 @ X10)) = (X9))
% 0.20/0.53          | ~ (v1_relat_1 @ X9))),
% 0.20/0.53      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.20/0.53  thf('30', plain,
% 0.20/0.53      ((~ (v1_relat_1 @ sk_C)
% 0.20/0.53        | ((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['28', '29'])).
% 0.20/0.53  thf('31', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(cc2_relat_1, axiom,
% 0.20/0.53    (![A:$i]:
% 0.20/0.53     ( ( v1_relat_1 @ A ) =>
% 0.20/0.53       ( ![B:$i]:
% 0.20/0.53         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.20/0.53  thf('32', plain,
% 0.20/0.53      (![X3 : $i, X4 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.20/0.53          | (v1_relat_1 @ X3)
% 0.20/0.53          | ~ (v1_relat_1 @ X4))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.20/0.53  thf('33', plain,
% 0.20/0.53      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['31', '32'])).
% 0.20/0.53  thf(fc6_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.20/0.53  thf('34', plain,
% 0.20/0.53      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.20/0.53      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.20/0.53  thf('35', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.53  thf('36', plain, (((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C))),
% 0.20/0.53      inference('demod', [status(thm)], ['30', '35'])).
% 0.20/0.53  thf('37', plain,
% 0.20/0.53      ((~ (r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C))
% 0.20/0.53         <= (~
% 0.20/0.53             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.53               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.20/0.53                (k6_partfun1 @ sk_B)) @ 
% 0.20/0.53               sk_C)))),
% 0.20/0.53      inference('demod', [status(thm)], ['19', '36'])).
% 0.20/0.53  thf('38', plain,
% 0.20/0.53      (((r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.53         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ (k6_partfun1 @ sk_B)) @ 
% 0.20/0.53         sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['8', '37'])).
% 0.20/0.53  thf('39', plain,
% 0.20/0.53      (~
% 0.20/0.53       ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.53         (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.20/0.53         sk_C)) | 
% 0.20/0.53       ~
% 0.20/0.53       ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.53         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ (k6_partfun1 @ sk_B)) @ 
% 0.20/0.53         sk_C))),
% 0.20/0.53      inference('split', [status(esa)], ['1'])).
% 0.20/0.53  thf('40', plain,
% 0.20/0.53      (~
% 0.20/0.53       ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.53         (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.20/0.53         sk_C))),
% 0.20/0.53      inference('sat_resolution*', [status(thm)], ['38', '39'])).
% 0.20/0.53  thf('41', plain,
% 0.20/0.53      (~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.53          (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_relat_1 @ sk_A) @ sk_C) @ 
% 0.20/0.53          sk_C)),
% 0.20/0.53      inference('simpl_trail', [status(thm)], ['4', '40'])).
% 0.20/0.53  thf('42', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf('43', plain,
% 0.20/0.53      (![X33 : $i]:
% 0.20/0.53         (m1_subset_1 @ (k6_relat_1 @ X33) @ 
% 0.20/0.53          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))),
% 0.20/0.53      inference('demod', [status(thm)], ['9', '10'])).
% 0.20/0.53  thf('44', plain,
% 0.20/0.53      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.53         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.20/0.53          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.20/0.53          | ((k4_relset_1 @ X23 @ X24 @ X26 @ X27 @ X22 @ X25)
% 0.20/0.53              = (k5_relat_1 @ X22 @ X25)))),
% 0.20/0.53      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 0.20/0.53  thf('45', plain,
% 0.20/0.53      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.20/0.53         (((k4_relset_1 @ X0 @ X0 @ X3 @ X2 @ (k6_relat_1 @ X0) @ X1)
% 0.20/0.53            = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.20/0.53          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2))))),
% 0.20/0.53      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.53  thf('46', plain,
% 0.20/0.53      (![X0 : $i]:
% 0.20/0.53         ((k4_relset_1 @ X0 @ X0 @ sk_A @ sk_B @ (k6_relat_1 @ X0) @ sk_C)
% 0.20/0.53           = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['42', '45'])).
% 0.20/0.53  thf('47', plain,
% 0.20/0.53      (~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.20/0.53          (k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C) @ sk_C)),
% 0.20/0.53      inference('demod', [status(thm)], ['41', '46'])).
% 0.20/0.53  thf('48', plain,
% 0.20/0.53      ((~ (r2_relset_1 @ sk_A @ sk_B @ (k7_relat_1 @ sk_C @ sk_A) @ sk_C)
% 0.20/0.53        | ~ (v1_relat_1 @ sk_C))),
% 0.20/0.53      inference('sup-', [status(thm)], ['0', '47'])).
% 0.20/0.53  thf('49', plain,
% 0.20/0.53      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.20/0.53      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.53  thf(cc2_relset_1, axiom,
% 0.20/0.53    (![A:$i,B:$i,C:$i]:
% 0.20/0.53     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.53       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.53  thf('50', plain,
% 0.20/0.53      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.53         ((v4_relat_1 @ X13 @ X14)
% 0.20/0.53          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.20/0.53      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.53  thf('51', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.20/0.53      inference('sup-', [status(thm)], ['49', '50'])).
% 0.20/0.53  thf(t209_relat_1, axiom,
% 0.20/0.53    (![A:$i,B:$i]:
% 0.20/0.53     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.53       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.20/0.53  thf('52', plain,
% 0.20/0.53      (![X7 : $i, X8 : $i]:
% 0.20/0.53         (((X7) = (k7_relat_1 @ X7 @ X8))
% 0.20/0.53          | ~ (v4_relat_1 @ X7 @ X8)
% 0.20/0.53          | ~ (v1_relat_1 @ X7))),
% 0.20/0.53      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.20/0.53  thf('53', plain,
% 0.20/0.53      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.20/0.53      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.53  thf('54', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.53  thf('55', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.20/0.53      inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.53  thf('56', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C)),
% 0.20/0.53      inference('sup-', [status(thm)], ['5', '7'])).
% 0.20/0.53  thf('57', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.53      inference('demod', [status(thm)], ['33', '34'])).
% 0.20/0.53  thf('58', plain, ($false),
% 0.20/0.53      inference('demod', [status(thm)], ['48', '55', '56', '57'])).
% 0.20/0.53  
% 0.20/0.53  % SZS output end Refutation
% 0.20/0.53  
% 0.20/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
