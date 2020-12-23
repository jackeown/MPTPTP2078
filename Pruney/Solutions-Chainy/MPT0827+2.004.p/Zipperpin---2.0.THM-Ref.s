%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.K99zyWbDAl

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:02 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 196 expanded)
%              Number of leaves         :   29 (  71 expanded)
%              Depth                    :   15
%              Number of atoms          :  626 (1829 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(t30_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D )
       => ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) )
          & ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
       => ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D )
         => ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) )
            & ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t30_relset_1])).

thf('0',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) )
    | ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) )
   <= ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('4',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_relat_1 @ sk_D ) )
   <= ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_C ) @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X5: $i,X7: $i] :
      ( ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    m1_subset_1 @ ( k6_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('10',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_D ) )
    | ( r2_hidden @ ( k6_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('11',plain,(
    ! [X2: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('12',plain,(
    r2_hidden @ ( k6_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_D ) ),
    inference(clc,[status(thm)],['10','11'])).

thf(t21_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( r1_tarski @ A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ) )).

thf('13',plain,(
    ! [X11: $i] :
      ( ( r1_tarski @ X11 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X11 ) @ ( k2_relat_1 @ X11 ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t21_relat_1])).

thf(t79_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_zfmisc_1 @ X0 ) @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( r1_tarski @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t79_zfmisc_1])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k1_zfmisc_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X5: $i,X7: $i] :
      ( ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r1_tarski @ X5 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k1_zfmisc_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X10 ) )
      | ( m1_subset_1 @ X8 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ X0 ) @ ( k2_relat_1 @ X0 ) ) ) )
      | ~ ( r2_hidden @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,
    ( ( m1_subset_1 @ ( k6_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['12','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('22',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v1_relat_1 @ X14 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('23',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ ( k6_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf(dt_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('25',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k1_relset_1 @ X17 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_relset_1])).

thf('26',plain,(
    m1_subset_1 @ ( k1_relset_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) @ ( k6_relat_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    m1_subset_1 @ ( k6_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('28',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('29',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) @ ( k6_relat_1 @ sk_C ) )
    = ( k1_relat_1 @ ( k6_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('30',plain,(
    ! [X12: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X12 ) )
      = X12 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('31',plain,
    ( ( k1_relset_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) @ ( k6_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k1_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['26','31'])).

thf('33',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    r1_tarski @ sk_C @ ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ( ( k1_relset_1 @ X24 @ X25 @ X23 )
        = ( k1_relat_1 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('37',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('39',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_D ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['34','39'])).

thf('41',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('42',plain,(
    ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sat_resolution*',[status(thm)],['40','41'])).

thf('43',plain,(
    ~ ( r1_tarski @ sk_C @ ( k2_relat_1 @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['5','42'])).

thf('44',plain,(
    m1_subset_1 @ ( k6_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('45',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X20 @ X21 @ X22 ) @ ( k1_zfmisc_1 @ X21 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('46',plain,(
    m1_subset_1 @ ( k2_relset_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) @ ( k6_relat_1 @ sk_C ) ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ ( k6_relat_1 @ sk_C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['20','23'])).

thf('48',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( ( k2_relset_1 @ X27 @ X28 @ X26 )
        = ( k2_relat_1 @ X26 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('49',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) @ ( k6_relat_1 @ sk_C ) )
    = ( k2_relat_1 @ ( k6_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X13: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X13 ) )
      = X13 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('51',plain,
    ( ( k2_relset_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) @ ( k6_relat_1 @ sk_C ) )
    = sk_C ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['46','51'])).

thf('53',plain,(
    ! [X5: $i,X6: $i] :
      ( ( r1_tarski @ X5 @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('54',plain,(
    r1_tarski @ sk_C @ ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    $false ),
    inference(demod,[status(thm)],['43','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.K99zyWbDAl
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:09:45 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.19/0.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.19/0.55  % Solved by: fo/fo7.sh
% 0.19/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.55  % done 409 iterations in 0.115s
% 0.19/0.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.19/0.55  % SZS output start Refutation
% 0.19/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.55  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.19/0.55  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.19/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.19/0.55  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.55  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.19/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.55  thf(t30_relset_1, conjecture,
% 0.19/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.55     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.55       ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D ) =>
% 0.19/0.55         ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) ) & 
% 0.19/0.55           ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.19/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.55    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.55        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.55          ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D ) =>
% 0.19/0.55            ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) ) & 
% 0.19/0.55              ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )),
% 0.19/0.55    inference('cnf.neg', [status(esa)], [t30_relset_1])).
% 0.19/0.55  thf('0', plain,
% 0.19/0.55      ((~ (r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D))
% 0.19/0.55        | ~ (r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf('1', plain,
% 0.19/0.55      ((~ (r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D)))
% 0.19/0.55         <= (~ ((r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D))))),
% 0.19/0.55      inference('split', [status(esa)], ['0'])).
% 0.19/0.55  thf('2', plain,
% 0.19/0.55      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(redefinition_k2_relset_1, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.55       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.19/0.55  thf('3', plain,
% 0.19/0.55      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.19/0.55         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 0.19/0.55          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.19/0.55      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.19/0.55  thf('4', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.19/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.19/0.55  thf('5', plain,
% 0.19/0.55      ((~ (r1_tarski @ sk_C @ (k2_relat_1 @ sk_D)))
% 0.19/0.55         <= (~ ((r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D))))),
% 0.19/0.55      inference('demod', [status(thm)], ['1', '4'])).
% 0.19/0.55  thf('6', plain, ((r1_tarski @ (k6_relat_1 @ sk_C) @ sk_D)),
% 0.19/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.55  thf(t3_subset, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.19/0.55  thf('7', plain,
% 0.19/0.55      (![X5 : $i, X7 : $i]:
% 0.19/0.55         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 0.19/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.55  thf('8', plain, ((m1_subset_1 @ (k6_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_D))),
% 0.19/0.55      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.55  thf(t2_subset, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( m1_subset_1 @ A @ B ) =>
% 0.19/0.55       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.19/0.55  thf('9', plain,
% 0.19/0.55      (![X3 : $i, X4 : $i]:
% 0.19/0.55         ((r2_hidden @ X3 @ X4)
% 0.19/0.55          | (v1_xboole_0 @ X4)
% 0.19/0.55          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.19/0.55      inference('cnf', [status(esa)], [t2_subset])).
% 0.19/0.55  thf('10', plain,
% 0.19/0.55      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_D))
% 0.19/0.55        | (r2_hidden @ (k6_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_D)))),
% 0.19/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.55  thf(fc1_subset_1, axiom,
% 0.19/0.55    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.55  thf('11', plain, (![X2 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X2))),
% 0.19/0.55      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.19/0.55  thf('12', plain, ((r2_hidden @ (k6_relat_1 @ sk_C) @ (k1_zfmisc_1 @ sk_D))),
% 0.19/0.55      inference('clc', [status(thm)], ['10', '11'])).
% 0.19/0.55  thf(t21_relat_1, axiom,
% 0.19/0.55    (![A:$i]:
% 0.19/0.55     ( ( v1_relat_1 @ A ) =>
% 0.19/0.55       ( r1_tarski @
% 0.19/0.55         A @ ( k2_zfmisc_1 @ ( k1_relat_1 @ A ) @ ( k2_relat_1 @ A ) ) ) ))).
% 0.19/0.55  thf('13', plain,
% 0.19/0.55      (![X11 : $i]:
% 0.19/0.55         ((r1_tarski @ X11 @ 
% 0.19/0.55           (k2_zfmisc_1 @ (k1_relat_1 @ X11) @ (k2_relat_1 @ X11)))
% 0.19/0.55          | ~ (v1_relat_1 @ X11))),
% 0.19/0.55      inference('cnf', [status(esa)], [t21_relat_1])).
% 0.19/0.55  thf(t79_zfmisc_1, axiom,
% 0.19/0.55    (![A:$i,B:$i]:
% 0.19/0.55     ( ( r1_tarski @ A @ B ) =>
% 0.19/0.55       ( r1_tarski @ ( k1_zfmisc_1 @ A ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.19/0.55  thf('14', plain,
% 0.19/0.55      (![X0 : $i, X1 : $i]:
% 0.19/0.55         ((r1_tarski @ (k1_zfmisc_1 @ X0) @ (k1_zfmisc_1 @ X1))
% 0.19/0.55          | ~ (r1_tarski @ X0 @ X1))),
% 0.19/0.55      inference('cnf', [status(esa)], [t79_zfmisc_1])).
% 0.19/0.55  thf('15', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (~ (v1_relat_1 @ X0)
% 0.19/0.55          | (r1_tarski @ (k1_zfmisc_1 @ X0) @ 
% 0.19/0.55             (k1_zfmisc_1 @ 
% 0.19/0.55              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0)))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.55  thf('16', plain,
% 0.19/0.55      (![X5 : $i, X7 : $i]:
% 0.19/0.55         ((m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X7)) | ~ (r1_tarski @ X5 @ X7))),
% 0.19/0.55      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.55  thf('17', plain,
% 0.19/0.55      (![X0 : $i]:
% 0.19/0.55         (~ (v1_relat_1 @ X0)
% 0.19/0.55          | (m1_subset_1 @ (k1_zfmisc_1 @ X0) @ 
% 0.19/0.55             (k1_zfmisc_1 @ 
% 0.19/0.55              (k1_zfmisc_1 @ 
% 0.19/0.55               (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))))),
% 0.19/0.55      inference('sup-', [status(thm)], ['15', '16'])).
% 0.19/0.55  thf(t4_subset, axiom,
% 0.19/0.55    (![A:$i,B:$i,C:$i]:
% 0.19/0.55     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.19/0.55       ( m1_subset_1 @ A @ C ) ))).
% 0.19/0.55  thf('18', plain,
% 0.19/0.55      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.55         (~ (r2_hidden @ X8 @ X9)
% 0.19/0.55          | ~ (m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X10))
% 0.19/0.56          | (m1_subset_1 @ X8 @ X10))),
% 0.19/0.56      inference('cnf', [status(esa)], [t4_subset])).
% 0.19/0.56  thf('19', plain,
% 0.19/0.56      (![X0 : $i, X1 : $i]:
% 0.19/0.56         (~ (v1_relat_1 @ X0)
% 0.19/0.56          | (m1_subset_1 @ X1 @ 
% 0.19/0.56             (k1_zfmisc_1 @ 
% 0.19/0.56              (k2_zfmisc_1 @ (k1_relat_1 @ X0) @ (k2_relat_1 @ X0))))
% 0.19/0.56          | ~ (r2_hidden @ X1 @ (k1_zfmisc_1 @ X0)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['17', '18'])).
% 0.19/0.56  thf('20', plain,
% 0.19/0.56      (((m1_subset_1 @ (k6_relat_1 @ sk_C) @ 
% 0.19/0.56         (k1_zfmisc_1 @ 
% 0.19/0.56          (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D))))
% 0.19/0.56        | ~ (v1_relat_1 @ sk_D))),
% 0.19/0.56      inference('sup-', [status(thm)], ['12', '19'])).
% 0.19/0.56  thf('21', plain,
% 0.19/0.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf(cc1_relset_1, axiom,
% 0.19/0.56    (![A:$i,B:$i,C:$i]:
% 0.19/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.56       ( v1_relat_1 @ C ) ))).
% 0.19/0.56  thf('22', plain,
% 0.19/0.56      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.56         ((v1_relat_1 @ X14)
% 0.19/0.56          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.19/0.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.19/0.56  thf('23', plain, ((v1_relat_1 @ sk_D)),
% 0.19/0.56      inference('sup-', [status(thm)], ['21', '22'])).
% 0.19/0.56  thf('24', plain,
% 0.19/0.56      ((m1_subset_1 @ (k6_relat_1 @ sk_C) @ 
% 0.19/0.56        (k1_zfmisc_1 @ 
% 0.19/0.56         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D))))),
% 0.19/0.56      inference('demod', [status(thm)], ['20', '23'])).
% 0.19/0.56  thf(dt_k1_relset_1, axiom,
% 0.19/0.56    (![A:$i,B:$i,C:$i]:
% 0.19/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.56       ( m1_subset_1 @ ( k1_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.19/0.56  thf('25', plain,
% 0.19/0.56      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.19/0.56         ((m1_subset_1 @ (k1_relset_1 @ X17 @ X18 @ X19) @ (k1_zfmisc_1 @ X17))
% 0.19/0.56          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.19/0.56      inference('cnf', [status(esa)], [dt_k1_relset_1])).
% 0.19/0.56  thf('26', plain,
% 0.19/0.56      ((m1_subset_1 @ 
% 0.19/0.56        (k1_relset_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D) @ 
% 0.19/0.56         (k6_relat_1 @ sk_C)) @ 
% 0.19/0.56        (k1_zfmisc_1 @ (k1_relat_1 @ sk_D)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['24', '25'])).
% 0.19/0.56  thf('27', plain,
% 0.19/0.56      ((m1_subset_1 @ (k6_relat_1 @ sk_C) @ 
% 0.19/0.56        (k1_zfmisc_1 @ 
% 0.19/0.56         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D))))),
% 0.19/0.56      inference('demod', [status(thm)], ['20', '23'])).
% 0.19/0.56  thf(redefinition_k1_relset_1, axiom,
% 0.19/0.56    (![A:$i,B:$i,C:$i]:
% 0.19/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.19/0.56  thf('28', plain,
% 0.19/0.56      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.19/0.56         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 0.19/0.56          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.19/0.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.19/0.56  thf('29', plain,
% 0.19/0.56      (((k1_relset_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D) @ 
% 0.19/0.56         (k6_relat_1 @ sk_C)) = (k1_relat_1 @ (k6_relat_1 @ sk_C)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['27', '28'])).
% 0.19/0.56  thf(t71_relat_1, axiom,
% 0.19/0.56    (![A:$i]:
% 0.19/0.56     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.19/0.56       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.19/0.56  thf('30', plain, (![X12 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X12)) = (X12))),
% 0.19/0.56      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.56  thf('31', plain,
% 0.19/0.56      (((k1_relset_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D) @ 
% 0.19/0.56         (k6_relat_1 @ sk_C)) = (sk_C))),
% 0.19/0.56      inference('demod', [status(thm)], ['29', '30'])).
% 0.19/0.56  thf('32', plain,
% 0.19/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k1_relat_1 @ sk_D)))),
% 0.19/0.56      inference('demod', [status(thm)], ['26', '31'])).
% 0.19/0.56  thf('33', plain,
% 0.19/0.56      (![X5 : $i, X6 : $i]:
% 0.19/0.56         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.19/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.56  thf('34', plain, ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_D))),
% 0.19/0.56      inference('sup-', [status(thm)], ['32', '33'])).
% 0.19/0.56  thf('35', plain,
% 0.19/0.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.19/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.56  thf('36', plain,
% 0.19/0.56      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.19/0.56         (((k1_relset_1 @ X24 @ X25 @ X23) = (k1_relat_1 @ X23))
% 0.19/0.56          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25))))),
% 0.19/0.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.19/0.56  thf('37', plain,
% 0.19/0.56      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.19/0.56      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.56  thf('38', plain,
% 0.19/0.56      ((~ (r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D)))
% 0.19/0.56         <= (~ ((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D))))),
% 0.19/0.56      inference('split', [status(esa)], ['0'])).
% 0.19/0.56  thf('39', plain,
% 0.19/0.56      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_D)))
% 0.19/0.56         <= (~ ((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D))))),
% 0.19/0.56      inference('sup-', [status(thm)], ['37', '38'])).
% 0.19/0.56  thf('40', plain, (((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['34', '39'])).
% 0.19/0.56  thf('41', plain,
% 0.19/0.56      (~ ((r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D))) | 
% 0.19/0.56       ~ ((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.19/0.56      inference('split', [status(esa)], ['0'])).
% 0.19/0.56  thf('42', plain,
% 0.19/0.56      (~ ((r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.19/0.56      inference('sat_resolution*', [status(thm)], ['40', '41'])).
% 0.19/0.56  thf('43', plain, (~ (r1_tarski @ sk_C @ (k2_relat_1 @ sk_D))),
% 0.19/0.56      inference('simpl_trail', [status(thm)], ['5', '42'])).
% 0.19/0.56  thf('44', plain,
% 0.19/0.56      ((m1_subset_1 @ (k6_relat_1 @ sk_C) @ 
% 0.19/0.56        (k1_zfmisc_1 @ 
% 0.19/0.56         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D))))),
% 0.19/0.56      inference('demod', [status(thm)], ['20', '23'])).
% 0.19/0.56  thf(dt_k2_relset_1, axiom,
% 0.19/0.56    (![A:$i,B:$i,C:$i]:
% 0.19/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.56       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.19/0.56  thf('45', plain,
% 0.19/0.56      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.19/0.56         ((m1_subset_1 @ (k2_relset_1 @ X20 @ X21 @ X22) @ (k1_zfmisc_1 @ X21))
% 0.19/0.56          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.19/0.56      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.19/0.56  thf('46', plain,
% 0.19/0.56      ((m1_subset_1 @ 
% 0.19/0.56        (k2_relset_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D) @ 
% 0.19/0.56         (k6_relat_1 @ sk_C)) @ 
% 0.19/0.56        (k1_zfmisc_1 @ (k2_relat_1 @ sk_D)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['44', '45'])).
% 0.19/0.56  thf('47', plain,
% 0.19/0.56      ((m1_subset_1 @ (k6_relat_1 @ sk_C) @ 
% 0.19/0.56        (k1_zfmisc_1 @ 
% 0.19/0.56         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D))))),
% 0.19/0.56      inference('demod', [status(thm)], ['20', '23'])).
% 0.19/0.56  thf('48', plain,
% 0.19/0.56      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.19/0.56         (((k2_relset_1 @ X27 @ X28 @ X26) = (k2_relat_1 @ X26))
% 0.19/0.56          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.19/0.56      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.19/0.56  thf('49', plain,
% 0.19/0.56      (((k2_relset_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D) @ 
% 0.19/0.56         (k6_relat_1 @ sk_C)) = (k2_relat_1 @ (k6_relat_1 @ sk_C)))),
% 0.19/0.56      inference('sup-', [status(thm)], ['47', '48'])).
% 0.19/0.56  thf('50', plain, (![X13 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X13)) = (X13))),
% 0.19/0.56      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.19/0.56  thf('51', plain,
% 0.19/0.56      (((k2_relset_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D) @ 
% 0.19/0.56         (k6_relat_1 @ sk_C)) = (sk_C))),
% 0.19/0.56      inference('demod', [status(thm)], ['49', '50'])).
% 0.19/0.56  thf('52', plain,
% 0.19/0.56      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_relat_1 @ sk_D)))),
% 0.19/0.56      inference('demod', [status(thm)], ['46', '51'])).
% 0.19/0.56  thf('53', plain,
% 0.19/0.56      (![X5 : $i, X6 : $i]:
% 0.19/0.56         ((r1_tarski @ X5 @ X6) | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.19/0.56      inference('cnf', [status(esa)], [t3_subset])).
% 0.19/0.56  thf('54', plain, ((r1_tarski @ sk_C @ (k2_relat_1 @ sk_D))),
% 0.19/0.56      inference('sup-', [status(thm)], ['52', '53'])).
% 0.19/0.56  thf('55', plain, ($false), inference('demod', [status(thm)], ['43', '54'])).
% 0.19/0.56  
% 0.19/0.56  % SZS output end Refutation
% 0.19/0.56  
% 0.19/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
