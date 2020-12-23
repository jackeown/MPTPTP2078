%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.99Ha3rYaWT

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:17 EST 2020

% Result     : Theorem 0.64s
% Output     : Refutation 0.64s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 147 expanded)
%              Number of leaves         :   29 (  56 expanded)
%              Depth                    :   12
%              Number of atoms          :  583 (1223 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   13 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k5_relset_1_type,type,(
    k5_relset_1: $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(t33_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( m1_subset_1 @ ( k5_relset_1 @ A @ C @ D @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
       => ( m1_subset_1 @ ( k5_relset_1 @ A @ C @ D @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_relset_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k5_relset_1 @ sk_A @ sk_C @ sk_D @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k5_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k5_relset_1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( ( k5_relset_1 @ X24 @ X25 @ X23 @ X26 )
        = ( k7_relat_1 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k5_relset_1 @ sk_A @ sk_C @ sk_D @ X0 )
      = ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t88_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ) )).

thf('5',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X12 @ X13 ) @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
     => ( ( r1_tarski @ A @ D )
       => ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('7',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( r1_tarski @ X30 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t4_relset_1])).

thf('8',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ sk_D )
      | ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ) ),
    inference('sup-',[status(thm)],['5','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('11',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
    | ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('13',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('14',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('16',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X17 @ X18 @ X19 ) @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_relset_1 @ sk_A @ sk_C @ ( k7_relat_1 @ sk_D @ X0 ) ) @ ( k1_zfmisc_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('19',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k2_relset_1 @ X21 @ X22 @ X20 )
        = ( k2_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_relset_1 @ sk_A @ sk_C @ ( k7_relat_1 @ sk_D @ X0 ) )
      = ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ ( k1_zfmisc_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['17','20'])).

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
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ sk_C ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    ! [X12: $i,X13: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ X12 @ X13 ) @ X12 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t88_relat_1])).

thf('25',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( k7_relat_1 @ X0 @ X1 ) @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_relat_1 @ ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('31',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('32',plain,(
    v4_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['30','31'])).

thf(fc23_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v4_relat_1 @ C @ B ) )
     => ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) )
        & ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ A )
        & ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ) )).

thf('33',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v4_relat_1 @ ( k7_relat_1 @ X7 @ X8 ) @ X8 )
      | ~ ( v4_relat_1 @ X7 @ X9 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[fc23_relat_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('36',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ X0 ) ),
    inference(demod,[status(thm)],['34','35'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('37',plain,(
    ! [X5: $i,X6: $i] :
      ( ~ ( v4_relat_1 @ X5 @ X6 )
      | ( r1_tarski @ ( k1_relat_1 @ X5 ) @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D )
      | ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['29','38'])).

thf('40',plain,(
    v1_relat_1 @ sk_D ),
    inference(demod,[status(thm)],['12','13'])).

thf('41',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['39','40'])).

thf(t11_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) )
       => ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('42',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X27 ) @ X28 )
      | ~ ( r1_tarski @ ( k2_relat_1 @ X27 ) @ X29 )
      | ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t11_relset_1])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) )
      | ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('45',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X4 ) )
      | ( v1_relat_1 @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) )
      | ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X10: $i,X11: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('48',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k7_relat_1 @ sk_D @ X0 ) ) @ X1 ) ) ),
    inference(demod,[status(thm)],['43','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['23','49'])).

thf('51',plain,(
    $false ),
    inference(demod,[status(thm)],['4','50'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.99Ha3rYaWT
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:43:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.64/0.83  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.64/0.83  % Solved by: fo/fo7.sh
% 0.64/0.83  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.64/0.83  % done 582 iterations in 0.375s
% 0.64/0.83  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.64/0.83  % SZS output start Refutation
% 0.64/0.83  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.64/0.83  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.64/0.83  thf(sk_C_type, type, sk_C: $i).
% 0.64/0.83  thf(sk_D_type, type, sk_D: $i).
% 0.64/0.83  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.64/0.83  thf(sk_A_type, type, sk_A: $i).
% 0.64/0.83  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.64/0.83  thf(k5_relset_1_type, type, k5_relset_1: $i > $i > $i > $i > $i).
% 0.64/0.83  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.64/0.83  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.64/0.83  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.64/0.83  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.64/0.83  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.64/0.83  thf(sk_B_type, type, sk_B: $i).
% 0.64/0.83  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.64/0.83  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.64/0.83  thf(t33_relset_1, conjecture,
% 0.64/0.83    (![A:$i,B:$i,C:$i,D:$i]:
% 0.64/0.83     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.64/0.83       ( m1_subset_1 @
% 0.64/0.83         ( k5_relset_1 @ A @ C @ D @ B ) @ 
% 0.64/0.83         ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ))).
% 0.64/0.83  thf(zf_stmt_0, negated_conjecture,
% 0.64/0.83    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.64/0.83        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.64/0.83          ( m1_subset_1 @
% 0.64/0.83            ( k5_relset_1 @ A @ C @ D @ B ) @ 
% 0.64/0.83            ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )),
% 0.64/0.83    inference('cnf.neg', [status(esa)], [t33_relset_1])).
% 0.64/0.83  thf('0', plain,
% 0.64/0.83      (~ (m1_subset_1 @ (k5_relset_1 @ sk_A @ sk_C @ sk_D @ sk_B) @ 
% 0.64/0.83          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.64/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.83  thf('1', plain,
% 0.64/0.83      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.64/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.83  thf(redefinition_k5_relset_1, axiom,
% 0.64/0.83    (![A:$i,B:$i,C:$i,D:$i]:
% 0.64/0.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.64/0.83       ( ( k5_relset_1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.64/0.83  thf('2', plain,
% 0.64/0.83      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.64/0.83         (~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X25)))
% 0.64/0.83          | ((k5_relset_1 @ X24 @ X25 @ X23 @ X26) = (k7_relat_1 @ X23 @ X26)))),
% 0.64/0.83      inference('cnf', [status(esa)], [redefinition_k5_relset_1])).
% 0.64/0.83  thf('3', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         ((k5_relset_1 @ sk_A @ sk_C @ sk_D @ X0) = (k7_relat_1 @ sk_D @ X0))),
% 0.64/0.83      inference('sup-', [status(thm)], ['1', '2'])).
% 0.64/0.83  thf('4', plain,
% 0.64/0.83      (~ (m1_subset_1 @ (k7_relat_1 @ sk_D @ sk_B) @ 
% 0.64/0.83          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.64/0.83      inference('demod', [status(thm)], ['0', '3'])).
% 0.64/0.83  thf(t88_relat_1, axiom,
% 0.64/0.83    (![A:$i,B:$i]:
% 0.64/0.83     ( ( v1_relat_1 @ B ) => ( r1_tarski @ ( k7_relat_1 @ B @ A ) @ B ) ))).
% 0.64/0.83  thf('5', plain,
% 0.64/0.83      (![X12 : $i, X13 : $i]:
% 0.64/0.83         ((r1_tarski @ (k7_relat_1 @ X12 @ X13) @ X12) | ~ (v1_relat_1 @ X12))),
% 0.64/0.83      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.64/0.83  thf('6', plain,
% 0.64/0.83      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.64/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.83  thf(t4_relset_1, axiom,
% 0.64/0.83    (![A:$i,B:$i,C:$i,D:$i]:
% 0.64/0.83     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.64/0.83       ( ( r1_tarski @ A @ D ) =>
% 0.64/0.83         ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.64/0.83  thf('7', plain,
% 0.64/0.83      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.64/0.83         ((m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.64/0.83          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.64/0.83          | ~ (r1_tarski @ X30 @ X33))),
% 0.64/0.83      inference('cnf', [status(esa)], [t4_relset_1])).
% 0.64/0.83  thf('8', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         (~ (r1_tarski @ X0 @ sk_D)
% 0.64/0.83          | (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.64/0.83      inference('sup-', [status(thm)], ['6', '7'])).
% 0.64/0.83  thf('9', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         (~ (v1_relat_1 @ sk_D)
% 0.64/0.83          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.64/0.83             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))))),
% 0.64/0.83      inference('sup-', [status(thm)], ['5', '8'])).
% 0.64/0.83  thf('10', plain,
% 0.64/0.83      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.64/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.83  thf(cc2_relat_1, axiom,
% 0.64/0.83    (![A:$i]:
% 0.64/0.83     ( ( v1_relat_1 @ A ) =>
% 0.64/0.83       ( ![B:$i]:
% 0.64/0.83         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.64/0.83  thf('11', plain,
% 0.64/0.83      (![X3 : $i, X4 : $i]:
% 0.64/0.83         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.64/0.83          | (v1_relat_1 @ X3)
% 0.64/0.83          | ~ (v1_relat_1 @ X4))),
% 0.64/0.83      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.64/0.83  thf('12', plain,
% 0.64/0.83      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)) | (v1_relat_1 @ sk_D))),
% 0.64/0.83      inference('sup-', [status(thm)], ['10', '11'])).
% 0.64/0.83  thf(fc6_relat_1, axiom,
% 0.64/0.83    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.64/0.83  thf('13', plain,
% 0.64/0.83      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.64/0.83      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.64/0.83  thf('14', plain, ((v1_relat_1 @ sk_D)),
% 0.64/0.83      inference('demod', [status(thm)], ['12', '13'])).
% 0.64/0.83  thf('15', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.64/0.83          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.64/0.83      inference('demod', [status(thm)], ['9', '14'])).
% 0.64/0.83  thf(dt_k2_relset_1, axiom,
% 0.64/0.83    (![A:$i,B:$i,C:$i]:
% 0.64/0.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.64/0.83       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.64/0.83  thf('16', plain,
% 0.64/0.83      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.64/0.83         ((m1_subset_1 @ (k2_relset_1 @ X17 @ X18 @ X19) @ (k1_zfmisc_1 @ X18))
% 0.64/0.83          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.64/0.83      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.64/0.83  thf('17', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         (m1_subset_1 @ 
% 0.64/0.83          (k2_relset_1 @ sk_A @ sk_C @ (k7_relat_1 @ sk_D @ X0)) @ 
% 0.64/0.83          (k1_zfmisc_1 @ sk_C))),
% 0.64/0.83      inference('sup-', [status(thm)], ['15', '16'])).
% 0.64/0.83  thf('18', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.64/0.83          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.64/0.83      inference('demod', [status(thm)], ['9', '14'])).
% 0.64/0.83  thf(redefinition_k2_relset_1, axiom,
% 0.64/0.83    (![A:$i,B:$i,C:$i]:
% 0.64/0.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.64/0.83       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.64/0.83  thf('19', plain,
% 0.64/0.83      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.64/0.83         (((k2_relset_1 @ X21 @ X22 @ X20) = (k2_relat_1 @ X20))
% 0.64/0.83          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.64/0.83      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.64/0.83  thf('20', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         ((k2_relset_1 @ sk_A @ sk_C @ (k7_relat_1 @ sk_D @ X0))
% 0.64/0.83           = (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 0.64/0.83      inference('sup-', [status(thm)], ['18', '19'])).
% 0.64/0.83  thf('21', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         (m1_subset_1 @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ 
% 0.64/0.83          (k1_zfmisc_1 @ sk_C))),
% 0.64/0.83      inference('demod', [status(thm)], ['17', '20'])).
% 0.64/0.83  thf(t3_subset, axiom,
% 0.64/0.83    (![A:$i,B:$i]:
% 0.64/0.83     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.64/0.83  thf('22', plain,
% 0.64/0.83      (![X0 : $i, X1 : $i]:
% 0.64/0.83         ((r1_tarski @ X0 @ X1) | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.64/0.83      inference('cnf', [status(esa)], [t3_subset])).
% 0.64/0.83  thf('23', plain,
% 0.64/0.83      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ sk_C)),
% 0.64/0.83      inference('sup-', [status(thm)], ['21', '22'])).
% 0.64/0.83  thf('24', plain,
% 0.64/0.83      (![X12 : $i, X13 : $i]:
% 0.64/0.83         ((r1_tarski @ (k7_relat_1 @ X12 @ X13) @ X12) | ~ (v1_relat_1 @ X12))),
% 0.64/0.83      inference('cnf', [status(esa)], [t88_relat_1])).
% 0.64/0.83  thf('25', plain,
% 0.64/0.83      (![X0 : $i, X2 : $i]:
% 0.64/0.83         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.64/0.83      inference('cnf', [status(esa)], [t3_subset])).
% 0.64/0.83  thf('26', plain,
% 0.64/0.83      (![X0 : $i, X1 : $i]:
% 0.64/0.83         (~ (v1_relat_1 @ X0)
% 0.64/0.83          | (m1_subset_1 @ (k7_relat_1 @ X0 @ X1) @ (k1_zfmisc_1 @ X0)))),
% 0.64/0.83      inference('sup-', [status(thm)], ['24', '25'])).
% 0.64/0.83  thf('27', plain,
% 0.64/0.83      (![X3 : $i, X4 : $i]:
% 0.64/0.83         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.64/0.83          | (v1_relat_1 @ X3)
% 0.64/0.83          | ~ (v1_relat_1 @ X4))),
% 0.64/0.83      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.64/0.83  thf('28', plain,
% 0.64/0.83      (![X0 : $i, X1 : $i]:
% 0.64/0.83         (~ (v1_relat_1 @ X0)
% 0.64/0.83          | ~ (v1_relat_1 @ X0)
% 0.64/0.83          | (v1_relat_1 @ (k7_relat_1 @ X0 @ X1)))),
% 0.64/0.83      inference('sup-', [status(thm)], ['26', '27'])).
% 0.64/0.83  thf('29', plain,
% 0.64/0.83      (![X0 : $i, X1 : $i]:
% 0.64/0.83         ((v1_relat_1 @ (k7_relat_1 @ X0 @ X1)) | ~ (v1_relat_1 @ X0))),
% 0.64/0.83      inference('simplify', [status(thm)], ['28'])).
% 0.64/0.83  thf('30', plain,
% 0.64/0.83      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.64/0.83      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.64/0.83  thf(cc2_relset_1, axiom,
% 0.64/0.83    (![A:$i,B:$i,C:$i]:
% 0.64/0.83     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.64/0.83       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.64/0.83  thf('31', plain,
% 0.64/0.83      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.64/0.83         ((v4_relat_1 @ X14 @ X15)
% 0.64/0.83          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.64/0.83      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.64/0.83  thf('32', plain, ((v4_relat_1 @ sk_D @ sk_A)),
% 0.64/0.83      inference('sup-', [status(thm)], ['30', '31'])).
% 0.64/0.83  thf(fc23_relat_1, axiom,
% 0.64/0.83    (![A:$i,B:$i,C:$i]:
% 0.64/0.83     ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ B ) ) =>
% 0.64/0.83       ( ( v1_relat_1 @ ( k7_relat_1 @ C @ A ) ) & 
% 0.64/0.83         ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ A ) & 
% 0.64/0.83         ( v4_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) ) ))).
% 0.64/0.83  thf('33', plain,
% 0.64/0.83      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.64/0.83         ((v4_relat_1 @ (k7_relat_1 @ X7 @ X8) @ X8)
% 0.64/0.83          | ~ (v4_relat_1 @ X7 @ X9)
% 0.64/0.83          | ~ (v1_relat_1 @ X7))),
% 0.64/0.83      inference('cnf', [status(esa)], [fc23_relat_1])).
% 0.64/0.83  thf('34', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         (~ (v1_relat_1 @ sk_D) | (v4_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X0))),
% 0.64/0.83      inference('sup-', [status(thm)], ['32', '33'])).
% 0.64/0.83  thf('35', plain, ((v1_relat_1 @ sk_D)),
% 0.64/0.83      inference('demod', [status(thm)], ['12', '13'])).
% 0.64/0.83  thf('36', plain, (![X0 : $i]: (v4_relat_1 @ (k7_relat_1 @ sk_D @ X0) @ X0)),
% 0.64/0.83      inference('demod', [status(thm)], ['34', '35'])).
% 0.64/0.83  thf(d18_relat_1, axiom,
% 0.64/0.83    (![A:$i,B:$i]:
% 0.64/0.83     ( ( v1_relat_1 @ B ) =>
% 0.64/0.83       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.64/0.83  thf('37', plain,
% 0.64/0.83      (![X5 : $i, X6 : $i]:
% 0.64/0.83         (~ (v4_relat_1 @ X5 @ X6)
% 0.64/0.83          | (r1_tarski @ (k1_relat_1 @ X5) @ X6)
% 0.64/0.83          | ~ (v1_relat_1 @ X5))),
% 0.64/0.83      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.64/0.83  thf('38', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 0.64/0.83          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X0))),
% 0.64/0.83      inference('sup-', [status(thm)], ['36', '37'])).
% 0.64/0.83  thf('39', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         (~ (v1_relat_1 @ sk_D)
% 0.64/0.83          | (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X0))),
% 0.64/0.83      inference('sup-', [status(thm)], ['29', '38'])).
% 0.64/0.83  thf('40', plain, ((v1_relat_1 @ sk_D)),
% 0.64/0.83      inference('demod', [status(thm)], ['12', '13'])).
% 0.64/0.83  thf('41', plain,
% 0.64/0.83      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X0)),
% 0.64/0.83      inference('demod', [status(thm)], ['39', '40'])).
% 0.64/0.83  thf(t11_relset_1, axiom,
% 0.64/0.83    (![A:$i,B:$i,C:$i]:
% 0.64/0.83     ( ( v1_relat_1 @ C ) =>
% 0.64/0.83       ( ( ( r1_tarski @ ( k1_relat_1 @ C ) @ A ) & 
% 0.64/0.83           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) =>
% 0.64/0.83         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.64/0.83  thf('42', plain,
% 0.64/0.83      (![X27 : $i, X28 : $i, X29 : $i]:
% 0.64/0.83         (~ (r1_tarski @ (k1_relat_1 @ X27) @ X28)
% 0.64/0.83          | ~ (r1_tarski @ (k2_relat_1 @ X27) @ X29)
% 0.64/0.83          | (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 0.64/0.83          | ~ (v1_relat_1 @ X27))),
% 0.64/0.83      inference('cnf', [status(esa)], [t11_relset_1])).
% 0.64/0.83  thf('43', plain,
% 0.64/0.83      (![X0 : $i, X1 : $i]:
% 0.64/0.83         (~ (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))
% 0.64/0.83          | (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.64/0.83             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.64/0.83          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X1))),
% 0.64/0.83      inference('sup-', [status(thm)], ['41', '42'])).
% 0.64/0.83  thf('44', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.64/0.83          (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.64/0.83      inference('demod', [status(thm)], ['9', '14'])).
% 0.64/0.83  thf('45', plain,
% 0.64/0.83      (![X3 : $i, X4 : $i]:
% 0.64/0.83         (~ (m1_subset_1 @ X3 @ (k1_zfmisc_1 @ X4))
% 0.64/0.83          | (v1_relat_1 @ X3)
% 0.64/0.83          | ~ (v1_relat_1 @ X4))),
% 0.64/0.83      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.64/0.83  thf('46', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         (~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_C))
% 0.64/0.83          | (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0)))),
% 0.64/0.83      inference('sup-', [status(thm)], ['44', '45'])).
% 0.64/0.83  thf('47', plain,
% 0.64/0.83      (![X10 : $i, X11 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X10 @ X11))),
% 0.64/0.83      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.64/0.83  thf('48', plain, (![X0 : $i]: (v1_relat_1 @ (k7_relat_1 @ sk_D @ X0))),
% 0.64/0.83      inference('demod', [status(thm)], ['46', '47'])).
% 0.64/0.83  thf('49', plain,
% 0.64/0.83      (![X0 : $i, X1 : $i]:
% 0.64/0.83         ((m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.64/0.83           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 0.64/0.83          | ~ (r1_tarski @ (k2_relat_1 @ (k7_relat_1 @ sk_D @ X0)) @ X1))),
% 0.64/0.83      inference('demod', [status(thm)], ['43', '48'])).
% 0.64/0.83  thf('50', plain,
% 0.64/0.83      (![X0 : $i]:
% 0.64/0.83         (m1_subset_1 @ (k7_relat_1 @ sk_D @ X0) @ 
% 0.64/0.83          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_C)))),
% 0.64/0.83      inference('sup-', [status(thm)], ['23', '49'])).
% 0.64/0.83  thf('51', plain, ($false), inference('demod', [status(thm)], ['4', '50'])).
% 0.64/0.83  
% 0.64/0.83  % SZS output end Refutation
% 0.64/0.83  
% 0.64/0.84  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
