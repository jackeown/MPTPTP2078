%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WS7RpVV3xh

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:53:51 EST 2020

% Result     : Theorem 0.38s
% Output     : Refutation 0.38s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 156 expanded)
%              Number of leaves         :   35 (  60 expanded)
%              Depth                    :   12
%              Number of atoms          :  844 (1892 expanded)
%              Number of equality atoms :   26 (  31 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k4_relset_1_type,type,(
    k4_relset_1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

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

thf('0',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C )
    | ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('2',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('3',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_relat_1 @ sk_A ) @ sk_C ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('4',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('5',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( r2_relset_1 @ X30 @ X31 @ X32 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['5'])).

thf('7',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['4','6'])).

thf(dt_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( m1_subset_1 @ ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
      & ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ) )).

thf('8',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_partfun1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_partfun1])).

thf('9',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('10',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) )
     => ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F )
        = ( k5_relat_1 @ E @ F ) ) ) )).

thf('12',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k4_relset_1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 )
        = ( k5_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0 )
        = ( k5_relat_1 @ sk_C @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ( k4_relset_1 @ sk_A @ sk_B @ X0 @ X0 @ sk_C @ ( k6_relat_1 @ X0 ) )
      = ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('16',plain,(
    ! [X36: $i] :
      ( ( k6_partfun1 @ X36 )
      = ( k6_relat_1 @ X36 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('17',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_relat_1 @ sk_B ) ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) ) @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('20',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X18 @ X19 @ X20 ) @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('21',plain,(
    m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('23',plain,(
    r1_tarski @ ( k2_relset_1 @ sk_A @ sk_B @ sk_C ) @ sk_B ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('25',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ( ( k2_relset_1 @ X22 @ X23 @ X21 )
        = ( k2_relat_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('26',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B ),
    inference(demod,[status(thm)],['23','26'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('28',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X11 ) @ X12 )
      | ( ( k5_relat_1 @ X11 @ ( k6_relat_1 @ X12 ) )
        = X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('29',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
      = sk_C ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('31',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) )
    | ( v1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('33',plain,(
    ! [X5: $i,X6: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('34',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k5_relat_1 @ sk_C @ ( k6_relat_1 @ sk_B ) )
    = sk_C ),
    inference(demod,[status(thm)],['29','34'])).

thf('36',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C )
   <= ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference(demod,[status(thm)],['18','35'])).

thf('37',plain,(
    r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ),
    inference('sup-',[status(thm)],['7','36'])).

thf('38',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C )
    | ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ ( k6_partfun1 @ sk_B ) ) @ sk_C ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference('sat_resolution*',[status(thm)],['37','38'])).

thf('40',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B @ ( k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ ( k6_relat_1 @ sk_A ) @ sk_C ) @ sk_C ) ),
    inference(simpl_trail,[status(thm)],['3','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X35: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X35 ) ) ) ),
    inference(demod,[status(thm)],['8','9'])).

thf('43',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ( ( k4_relset_1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27 )
        = ( k5_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_relset_1])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( ( k4_relset_1 @ X0 @ X0 @ X3 @ X2 @ ( k6_relat_1 @ X0 ) @ X1 )
        = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X2 ) ) ) ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k4_relset_1 @ X0 @ X0 @ sk_A @ sk_B @ ( k6_relat_1 @ X0 ) @ sk_C )
      = ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['41','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('47',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v4_relat_1 @ X15 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('48',plain,(
    v4_relat_1 @ sk_C @ sk_A ),
    inference('sup-',[status(thm)],['46','47'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('49',plain,(
    ! [X7: $i,X8: $i] :
      ( ( X7
        = ( k7_relat_1 @ X7 @ X8 ) )
      | ~ ( v4_relat_1 @ X7 @ X8 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('50',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_A ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('52',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf(t87_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ) )).

thf('53',plain,(
    ! [X13: $i,X14: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ X13 @ X14 ) ) @ X14 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t87_relat_1])).

thf('54',plain,
    ( ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_C ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf('55',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('56',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C ) @ sk_A ),
    inference(demod,[status(thm)],['54','55'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('57',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X9 ) @ X10 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X10 ) @ X9 )
        = X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('58',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C )
      = sk_C ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    v1_relat_1 @ sk_C ),
    inference(demod,[status(thm)],['32','33'])).

thf('60',plain,
    ( ( k5_relat_1 @ ( k6_relat_1 @ sk_A ) @ sk_C )
    = sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['4','6'])).

thf('62',plain,(
    $false ),
    inference(demod,[status(thm)],['40','45','60','61'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WS7RpVV3xh
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:38:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.38/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.38/0.57  % Solved by: fo/fo7.sh
% 0.38/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.38/0.57  % done 202 iterations in 0.109s
% 0.38/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.38/0.57  % SZS output start Refutation
% 0.38/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.38/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.38/0.57  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.38/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.38/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.38/0.57  thf(k4_relset_1_type, type, k4_relset_1: $i > $i > $i > $i > $i > $i > $i).
% 0.38/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.38/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.38/0.57  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.38/0.57  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.38/0.57  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.38/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.38/0.57  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.38/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.38/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.38/0.57  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.38/0.57  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.38/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.38/0.57  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.38/0.57  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.38/0.57  thf(t23_funct_2, conjecture,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.57       ( ( r2_relset_1 @
% 0.38/0.57           A @ B @ ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ 
% 0.38/0.57           C ) & 
% 0.38/0.57         ( r2_relset_1 @
% 0.38/0.57           A @ B @ ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ 
% 0.38/0.57           C ) ) ))).
% 0.38/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.38/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.38/0.57        ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.57          ( ( r2_relset_1 @
% 0.38/0.57              A @ B @ 
% 0.38/0.57              ( k4_relset_1 @ A @ A @ A @ B @ ( k6_partfun1 @ A ) @ C ) @ C ) & 
% 0.38/0.57            ( r2_relset_1 @
% 0.38/0.57              A @ B @ 
% 0.38/0.57              ( k4_relset_1 @ A @ B @ B @ B @ C @ ( k6_partfun1 @ B ) ) @ C ) ) ) )),
% 0.38/0.57    inference('cnf.neg', [status(esa)], [t23_funct_2])).
% 0.38/0.57  thf('0', plain,
% 0.38/0.57      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.38/0.57           (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A) @ 
% 0.38/0.57            sk_C) @ 
% 0.38/0.57           sk_C)
% 0.38/0.57        | ~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.38/0.57             (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.38/0.57              (k6_partfun1 @ sk_B)) @ 
% 0.38/0.57             sk_C))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('1', plain,
% 0.38/0.57      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.38/0.57           (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A) @ 
% 0.38/0.57            sk_C) @ 
% 0.38/0.57           sk_C))
% 0.38/0.57         <= (~
% 0.38/0.57             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.38/0.57               (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.38/0.57                (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.38/0.57               sk_C)))),
% 0.38/0.57      inference('split', [status(esa)], ['0'])).
% 0.38/0.57  thf(redefinition_k6_partfun1, axiom,
% 0.38/0.57    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.38/0.57  thf('2', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.38/0.57      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.38/0.57  thf('3', plain,
% 0.38/0.57      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.38/0.57           (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_relat_1 @ sk_A) @ 
% 0.38/0.57            sk_C) @ 
% 0.38/0.57           sk_C))
% 0.38/0.57         <= (~
% 0.38/0.57             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.38/0.57               (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ 
% 0.38/0.57                (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.38/0.57               sk_C)))),
% 0.38/0.57      inference('demod', [status(thm)], ['1', '2'])).
% 0.38/0.57  thf('4', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(reflexivity_r2_relset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.38/0.57     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.38/0.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.38/0.57       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.38/0.57  thf('5', plain,
% 0.38/0.57      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.38/0.57         ((r2_relset_1 @ X30 @ X31 @ X32 @ X32)
% 0.38/0.57          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31)))
% 0.38/0.57          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.38/0.57      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.38/0.57  thf('6', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.57         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.38/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.38/0.57      inference('condensation', [status(thm)], ['5'])).
% 0.38/0.57  thf('7', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C)),
% 0.38/0.57      inference('sup-', [status(thm)], ['4', '6'])).
% 0.38/0.57  thf(dt_k6_partfun1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( m1_subset_1 @
% 0.38/0.57         ( k6_partfun1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.38/0.57       ( v1_partfun1 @ ( k6_partfun1 @ A ) @ A ) ))).
% 0.38/0.57  thf('8', plain,
% 0.38/0.57      (![X35 : $i]:
% 0.38/0.57         (m1_subset_1 @ (k6_partfun1 @ X35) @ 
% 0.38/0.57          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_k6_partfun1])).
% 0.38/0.57  thf('9', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.38/0.57      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.38/0.57  thf('10', plain,
% 0.38/0.57      (![X35 : $i]:
% 0.38/0.57         (m1_subset_1 @ (k6_relat_1 @ X35) @ 
% 0.38/0.57          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 0.38/0.57      inference('demod', [status(thm)], ['8', '9'])).
% 0.38/0.57  thf('11', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(redefinition_k4_relset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.38/0.57     ( ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.38/0.57         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ D ) ) ) ) =>
% 0.38/0.57       ( ( k4_relset_1 @ A @ B @ C @ D @ E @ F ) = ( k5_relat_1 @ E @ F ) ) ))).
% 0.38/0.57  thf('12', plain,
% 0.38/0.57      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.38/0.57          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.38/0.57          | ((k4_relset_1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27)
% 0.38/0.57              = (k5_relat_1 @ X24 @ X27)))),
% 0.38/0.57      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 0.38/0.57  thf('13', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.38/0.57         (((k4_relset_1 @ sk_A @ sk_B @ X2 @ X1 @ sk_C @ X0)
% 0.38/0.57            = (k5_relat_1 @ sk_C @ X0))
% 0.38/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.38/0.57  thf('14', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((k4_relset_1 @ sk_A @ sk_B @ X0 @ X0 @ sk_C @ (k6_relat_1 @ X0))
% 0.38/0.57           = (k5_relat_1 @ sk_C @ (k6_relat_1 @ X0)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['10', '13'])).
% 0.38/0.57  thf('15', plain,
% 0.38/0.57      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.38/0.57           (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.38/0.57            (k6_partfun1 @ sk_B)) @ 
% 0.38/0.57           sk_C))
% 0.38/0.57         <= (~
% 0.38/0.57             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.38/0.57               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.38/0.57                (k6_partfun1 @ sk_B)) @ 
% 0.38/0.57               sk_C)))),
% 0.38/0.57      inference('split', [status(esa)], ['0'])).
% 0.38/0.57  thf('16', plain, (![X36 : $i]: ((k6_partfun1 @ X36) = (k6_relat_1 @ X36))),
% 0.38/0.57      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.38/0.57  thf('17', plain,
% 0.38/0.57      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.38/0.57           (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.38/0.57            (k6_relat_1 @ sk_B)) @ 
% 0.38/0.57           sk_C))
% 0.38/0.57         <= (~
% 0.38/0.57             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.38/0.57               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.38/0.57                (k6_partfun1 @ sk_B)) @ 
% 0.38/0.57               sk_C)))),
% 0.38/0.57      inference('demod', [status(thm)], ['15', '16'])).
% 0.38/0.57  thf('18', plain,
% 0.38/0.57      ((~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.38/0.57           (k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) @ sk_C))
% 0.38/0.57         <= (~
% 0.38/0.57             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.38/0.57               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.38/0.57                (k6_partfun1 @ sk_B)) @ 
% 0.38/0.57               sk_C)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['14', '17'])).
% 0.38/0.57  thf('19', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(dt_k2_relset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.57       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.38/0.57  thf('20', plain,
% 0.38/0.57      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.38/0.57         ((m1_subset_1 @ (k2_relset_1 @ X18 @ X19 @ X20) @ (k1_zfmisc_1 @ X19))
% 0.38/0.57          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.38/0.57      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.38/0.57  thf('21', plain,
% 0.38/0.57      ((m1_subset_1 @ (k2_relset_1 @ sk_A @ sk_B @ sk_C) @ (k1_zfmisc_1 @ sk_B))),
% 0.38/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.38/0.57  thf(t3_subset, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.38/0.57  thf('22', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i]:
% 0.38/0.57         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.38/0.57      inference('cnf', [status(esa)], [t3_subset])).
% 0.38/0.57  thf('23', plain, ((r1_tarski @ (k2_relset_1 @ sk_A @ sk_B @ sk_C) @ sk_B)),
% 0.38/0.57      inference('sup-', [status(thm)], ['21', '22'])).
% 0.38/0.57  thf('24', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(redefinition_k2_relset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.57       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.38/0.57  thf('25', plain,
% 0.38/0.57      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.38/0.57         (((k2_relset_1 @ X22 @ X23 @ X21) = (k2_relat_1 @ X21))
% 0.38/0.57          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.38/0.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.38/0.57  thf('26', plain,
% 0.38/0.57      (((k2_relset_1 @ sk_A @ sk_B @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.38/0.57      inference('sup-', [status(thm)], ['24', '25'])).
% 0.38/0.57  thf('27', plain, ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B)),
% 0.38/0.57      inference('demod', [status(thm)], ['23', '26'])).
% 0.38/0.57  thf(t79_relat_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( v1_relat_1 @ B ) =>
% 0.38/0.57       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.38/0.57         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.38/0.57  thf('28', plain,
% 0.38/0.57      (![X11 : $i, X12 : $i]:
% 0.38/0.57         (~ (r1_tarski @ (k2_relat_1 @ X11) @ X12)
% 0.38/0.57          | ((k5_relat_1 @ X11 @ (k6_relat_1 @ X12)) = (X11))
% 0.38/0.57          | ~ (v1_relat_1 @ X11))),
% 0.38/0.57      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.38/0.57  thf('29', plain,
% 0.38/0.57      ((~ (v1_relat_1 @ sk_C)
% 0.38/0.57        | ((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['27', '28'])).
% 0.38/0.57  thf('30', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(cc2_relat_1, axiom,
% 0.38/0.57    (![A:$i]:
% 0.38/0.57     ( ( v1_relat_1 @ A ) =>
% 0.38/0.57       ( ![B:$i]:
% 0.38/0.57         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.38/0.57  thf('31', plain,
% 0.38/0.57      (![X3 : $i, X4 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.38/0.57          | (v1_relat_1 @ X3)
% 0.38/0.57          | ~ (v1_relat_1 @ X4))),
% 0.38/0.57      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.38/0.57  thf('32', plain,
% 0.38/0.57      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)) | (v1_relat_1 @ sk_C))),
% 0.38/0.57      inference('sup-', [status(thm)], ['30', '31'])).
% 0.38/0.57  thf(fc6_relat_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.38/0.57  thf('33', plain,
% 0.38/0.57      (![X5 : $i, X6 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X5 @ X6))),
% 0.38/0.57      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.38/0.57  thf('34', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.57      inference('demod', [status(thm)], ['32', '33'])).
% 0.38/0.57  thf('35', plain, (((k5_relat_1 @ sk_C @ (k6_relat_1 @ sk_B)) = (sk_C))),
% 0.38/0.57      inference('demod', [status(thm)], ['29', '34'])).
% 0.38/0.57  thf('36', plain,
% 0.38/0.57      ((~ (r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C))
% 0.38/0.57         <= (~
% 0.38/0.57             ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.38/0.57               (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ 
% 0.38/0.57                (k6_partfun1 @ sk_B)) @ 
% 0.38/0.57               sk_C)))),
% 0.38/0.57      inference('demod', [status(thm)], ['18', '35'])).
% 0.38/0.57  thf('37', plain,
% 0.38/0.57      (((r2_relset_1 @ sk_A @ sk_B @ 
% 0.38/0.57         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ (k6_partfun1 @ sk_B)) @ 
% 0.38/0.57         sk_C))),
% 0.38/0.57      inference('sup-', [status(thm)], ['7', '36'])).
% 0.38/0.57  thf('38', plain,
% 0.38/0.57      (~
% 0.38/0.57       ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.38/0.57         (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.38/0.57         sk_C)) | 
% 0.38/0.57       ~
% 0.38/0.57       ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.38/0.57         (k4_relset_1 @ sk_A @ sk_B @ sk_B @ sk_B @ sk_C @ (k6_partfun1 @ sk_B)) @ 
% 0.38/0.57         sk_C))),
% 0.38/0.57      inference('split', [status(esa)], ['0'])).
% 0.38/0.57  thf('39', plain,
% 0.38/0.57      (~
% 0.38/0.57       ((r2_relset_1 @ sk_A @ sk_B @ 
% 0.38/0.57         (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A) @ sk_C) @ 
% 0.38/0.57         sk_C))),
% 0.38/0.57      inference('sat_resolution*', [status(thm)], ['37', '38'])).
% 0.38/0.57  thf('40', plain,
% 0.38/0.57      (~ (r2_relset_1 @ sk_A @ sk_B @ 
% 0.38/0.57          (k4_relset_1 @ sk_A @ sk_A @ sk_A @ sk_B @ (k6_relat_1 @ sk_A) @ sk_C) @ 
% 0.38/0.57          sk_C)),
% 0.38/0.57      inference('simpl_trail', [status(thm)], ['3', '39'])).
% 0.38/0.57  thf('41', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf('42', plain,
% 0.38/0.57      (![X35 : $i]:
% 0.38/0.57         (m1_subset_1 @ (k6_relat_1 @ X35) @ 
% 0.38/0.57          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X35)))),
% 0.38/0.57      inference('demod', [status(thm)], ['8', '9'])).
% 0.38/0.57  thf('43', plain,
% 0.38/0.57      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.38/0.57         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.38/0.57          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.38/0.57          | ((k4_relset_1 @ X25 @ X26 @ X28 @ X29 @ X24 @ X27)
% 0.38/0.57              = (k5_relat_1 @ X24 @ X27)))),
% 0.38/0.57      inference('cnf', [status(esa)], [redefinition_k4_relset_1])).
% 0.38/0.57  thf('44', plain,
% 0.38/0.57      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.38/0.57         (((k4_relset_1 @ X0 @ X0 @ X3 @ X2 @ (k6_relat_1 @ X0) @ X1)
% 0.38/0.57            = (k5_relat_1 @ (k6_relat_1 @ X0) @ X1))
% 0.38/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X2))))),
% 0.38/0.57      inference('sup-', [status(thm)], ['42', '43'])).
% 0.38/0.57  thf('45', plain,
% 0.38/0.57      (![X0 : $i]:
% 0.38/0.57         ((k4_relset_1 @ X0 @ X0 @ sk_A @ sk_B @ (k6_relat_1 @ X0) @ sk_C)
% 0.38/0.57           = (k5_relat_1 @ (k6_relat_1 @ X0) @ sk_C))),
% 0.38/0.57      inference('sup-', [status(thm)], ['41', '44'])).
% 0.38/0.57  thf('46', plain,
% 0.38/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.38/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.38/0.57  thf(cc2_relset_1, axiom,
% 0.38/0.57    (![A:$i,B:$i,C:$i]:
% 0.38/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.38/0.57       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.38/0.57  thf('47', plain,
% 0.38/0.57      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.38/0.57         ((v4_relat_1 @ X15 @ X16)
% 0.38/0.57          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.38/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.38/0.57  thf('48', plain, ((v4_relat_1 @ sk_C @ sk_A)),
% 0.38/0.57      inference('sup-', [status(thm)], ['46', '47'])).
% 0.38/0.57  thf(t209_relat_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.38/0.57       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.38/0.57  thf('49', plain,
% 0.38/0.57      (![X7 : $i, X8 : $i]:
% 0.38/0.57         (((X7) = (k7_relat_1 @ X7 @ X8))
% 0.38/0.57          | ~ (v4_relat_1 @ X7 @ X8)
% 0.38/0.57          | ~ (v1_relat_1 @ X7))),
% 0.38/0.57      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.38/0.57  thf('50', plain,
% 0.38/0.57      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_A)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['48', '49'])).
% 0.38/0.57  thf('51', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.57      inference('demod', [status(thm)], ['32', '33'])).
% 0.38/0.57  thf('52', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_A))),
% 0.38/0.57      inference('demod', [status(thm)], ['50', '51'])).
% 0.38/0.57  thf(t87_relat_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( v1_relat_1 @ B ) =>
% 0.38/0.57       ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ B @ A ) ) @ A ) ))).
% 0.38/0.57  thf('53', plain,
% 0.38/0.57      (![X13 : $i, X14 : $i]:
% 0.38/0.57         ((r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ X13 @ X14)) @ X14)
% 0.38/0.57          | ~ (v1_relat_1 @ X13))),
% 0.38/0.57      inference('cnf', [status(esa)], [t87_relat_1])).
% 0.38/0.57  thf('54', plain,
% 0.38/0.57      (((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A) | ~ (v1_relat_1 @ sk_C))),
% 0.38/0.57      inference('sup+', [status(thm)], ['52', '53'])).
% 0.38/0.57  thf('55', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.57      inference('demod', [status(thm)], ['32', '33'])).
% 0.38/0.57  thf('56', plain, ((r1_tarski @ (k1_relat_1 @ sk_C) @ sk_A)),
% 0.38/0.57      inference('demod', [status(thm)], ['54', '55'])).
% 0.38/0.57  thf(t77_relat_1, axiom,
% 0.38/0.57    (![A:$i,B:$i]:
% 0.38/0.57     ( ( v1_relat_1 @ B ) =>
% 0.38/0.57       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.38/0.57         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.38/0.57  thf('57', plain,
% 0.38/0.57      (![X9 : $i, X10 : $i]:
% 0.38/0.57         (~ (r1_tarski @ (k1_relat_1 @ X9) @ X10)
% 0.38/0.57          | ((k5_relat_1 @ (k6_relat_1 @ X10) @ X9) = (X9))
% 0.38/0.57          | ~ (v1_relat_1 @ X9))),
% 0.38/0.57      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.38/0.57  thf('58', plain,
% 0.38/0.57      ((~ (v1_relat_1 @ sk_C)
% 0.38/0.57        | ((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C) = (sk_C)))),
% 0.38/0.57      inference('sup-', [status(thm)], ['56', '57'])).
% 0.38/0.57  thf('59', plain, ((v1_relat_1 @ sk_C)),
% 0.38/0.57      inference('demod', [status(thm)], ['32', '33'])).
% 0.38/0.57  thf('60', plain, (((k5_relat_1 @ (k6_relat_1 @ sk_A) @ sk_C) = (sk_C))),
% 0.38/0.57      inference('demod', [status(thm)], ['58', '59'])).
% 0.38/0.57  thf('61', plain, ((r2_relset_1 @ sk_A @ sk_B @ sk_C @ sk_C)),
% 0.38/0.57      inference('sup-', [status(thm)], ['4', '6'])).
% 0.38/0.57  thf('62', plain, ($false),
% 0.38/0.57      inference('demod', [status(thm)], ['40', '45', '60', '61'])).
% 0.38/0.57  
% 0.38/0.57  % SZS output end Refutation
% 0.38/0.57  
% 0.38/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
