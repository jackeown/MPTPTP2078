%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CBM3zEoYEH

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 141 expanded)
%              Number of leaves         :   38 (  60 expanded)
%              Depth                    :   13
%              Number of atoms          :  613 (1167 expanded)
%              Number of equality atoms :   26 (  36 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_xboole_0_type,type,(
    k2_xboole_0: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k6_subset_1_type,type,(
    k6_subset_1: $i > $i > $i )).

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
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k2_relset_1 @ X35 @ X36 @ X34 )
        = ( k2_relat_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
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

thf(t36_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ X5 @ X6 ) @ X5 ) ),
    inference(cnf,[status(esa)],[t36_xboole_1])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('8',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ~ ( r1_tarski @ X2 @ X3 )
      | ~ ( r1_tarski @ X3 @ X4 )
      | ( r1_tarski @ X2 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ X0 @ X1 ) @ X2 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k4_xboole_0 @ ( k6_relat_1 @ sk_C ) @ X0 ) @ sk_D ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf(t79_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ) )).

thf('11',plain,(
    ! [X12: $i,X13: $i] :
      ( r1_xboole_0 @ ( k4_xboole_0 @ X12 @ X13 ) @ X13 ) ),
    inference(cnf,[status(esa)],[t79_xboole_1])).

thf(t69_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( ( r1_tarski @ B @ A )
          & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r1_xboole_0 @ X10 @ X11 )
      | ~ ( r1_tarski @ X10 @ X11 )
      | ( v1_xboole_0 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_xboole_1])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k4_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_xboole_0 @ ( k4_xboole_0 @ ( k6_relat_1 @ sk_C ) @ sk_D ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('15',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('16',plain,
    ( ( k4_xboole_0 @ ( k6_relat_1 @ sk_C ) @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t15_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k6_subset_1 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) @ ( k1_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('17',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( r1_tarski @ ( k6_subset_1 @ ( k1_relat_1 @ X21 ) @ ( k1_relat_1 @ X20 ) ) @ ( k1_relat_1 @ ( k6_subset_1 @ X21 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t15_relat_1])).

thf(redefinition_k6_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k6_subset_1 @ A @ B )
      = ( k4_xboole_0 @ A @ B ) ) )).

thf('18',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('19',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('20',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_relat_1 @ X20 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ X21 ) @ ( k1_relat_1 @ X20 ) ) @ ( k1_relat_1 @ ( k4_xboole_0 @ X21 @ X20 ) ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ ( k1_relat_1 @ ( k6_relat_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_D ) ) @ ( k1_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['16','20'])).

thf(t71_relat_1,axiom,(
    ! [A: $i] :
      ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) )
        = A )
      & ( ( k1_relat_1 @ ( k6_relat_1 @ A ) )
        = A ) ) )).

thf('22',plain,(
    ! [X24: $i] :
      ( ( k1_relat_1 @ ( k6_relat_1 @ X24 ) )
      = X24 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('23',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(fc3_funct_1,axiom,(
    ! [A: $i] :
      ( ( v1_funct_1 @ ( k6_relat_1 @ A ) )
      & ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ) )).

thf('24',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('26',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('27',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_C @ ( k1_relat_1 @ sk_D ) ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['21','22','23','24','27'])).

thf(t44_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C )
     => ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ) )).

thf('29',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('30',plain,(
    r1_tarski @ sk_C @ ( k2_xboole_0 @ ( k1_relat_1 @ sk_D ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf(t1_boole,axiom,(
    ! [A: $i] :
      ( ( k2_xboole_0 @ A @ k1_xboole_0 )
      = A ) )).

thf('31',plain,(
    ! [X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('32',plain,(
    r1_tarski @ sk_C @ ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('34',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X33 @ X31 )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('35',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('37',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_D ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ),
    inference('sup-',[status(thm)],['32','37'])).

thf('39',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) )
    | ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('40',plain,(
    ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sat_resolution*',[status(thm)],['38','39'])).

thf('41',plain,(
    ~ ( r1_tarski @ sk_C @ ( k2_relat_1 @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['5','40'])).

thf('42',plain,
    ( ( k4_xboole_0 @ ( k6_relat_1 @ sk_C ) @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t28_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) )).

thf('43',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ( r1_tarski @ ( k6_subset_1 @ ( k2_relat_1 @ X23 ) @ ( k2_relat_1 @ X22 ) ) @ ( k2_relat_1 @ ( k6_subset_1 @ X23 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t28_relat_1])).

thf('44',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('45',plain,(
    ! [X18: $i,X19: $i] :
      ( ( k6_subset_1 @ X18 @ X19 )
      = ( k4_xboole_0 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_subset_1])).

thf('46',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( v1_relat_1 @ X22 )
      | ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ X23 ) @ ( k2_relat_1 @ X22 ) ) @ ( k2_relat_1 @ ( k4_xboole_0 @ X23 @ X22 ) ) )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( r1_tarski @ ( k4_xboole_0 @ ( k2_relat_1 @ ( k6_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_D ) ) @ ( k2_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['42','46'])).

thf('48',plain,(
    ! [X25: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X25 ) )
      = X25 ) ),
    inference(cnf,[status(esa)],[t71_relat_1])).

thf('49',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('50',plain,(
    ! [X26: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_1])).

thf('51',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['25','26'])).

thf('52',plain,(
    r1_tarski @ ( k4_xboole_0 @ sk_C @ ( k2_relat_1 @ sk_D ) ) @ k1_xboole_0 ),
    inference(demod,[status(thm)],['47','48','49','50','51'])).

thf('53',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( r1_tarski @ X7 @ ( k2_xboole_0 @ X8 @ X9 ) )
      | ~ ( r1_tarski @ ( k4_xboole_0 @ X7 @ X8 ) @ X9 ) ) ),
    inference(cnf,[status(esa)],[t44_xboole_1])).

thf('54',plain,(
    r1_tarski @ sk_C @ ( k2_xboole_0 @ ( k2_relat_1 @ sk_D ) @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X1: $i] :
      ( ( k2_xboole_0 @ X1 @ k1_xboole_0 )
      = X1 ) ),
    inference(cnf,[status(esa)],[t1_boole])).

thf('56',plain,(
    r1_tarski @ sk_C @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['41','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.CBM3zEoYEH
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:35:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.56  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.56  % Solved by: fo/fo7.sh
% 0.22/0.56  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.56  % done 160 iterations in 0.107s
% 0.22/0.56  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.56  % SZS output start Refutation
% 0.22/0.56  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.56  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.22/0.56  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.56  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.56  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.56  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.56  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.56  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.22/0.56  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.56  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 0.22/0.56  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.56  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.56  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.56  thf(k2_xboole_0_type, type, k2_xboole_0: $i > $i > $i).
% 0.22/0.56  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.56  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.56  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.56  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.56  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.56  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.56  thf(k6_subset_1_type, type, k6_subset_1: $i > $i > $i).
% 0.22/0.56  thf(t30_relset_1, conjecture,
% 0.22/0.56    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.56     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.56       ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D ) =>
% 0.22/0.56         ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) ) & 
% 0.22/0.56           ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.22/0.56  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.56    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.56        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.56          ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D ) =>
% 0.22/0.56            ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) ) & 
% 0.22/0.56              ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )),
% 0.22/0.56    inference('cnf.neg', [status(esa)], [t30_relset_1])).
% 0.22/0.56  thf('0', plain,
% 0.22/0.56      ((~ (r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D))
% 0.22/0.56        | ~ (r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf('1', plain,
% 0.22/0.56      ((~ (r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D)))
% 0.22/0.56         <= (~ ((r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D))))),
% 0.22/0.56      inference('split', [status(esa)], ['0'])).
% 0.22/0.56  thf('2', plain,
% 0.22/0.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf(redefinition_k2_relset_1, axiom,
% 0.22/0.56    (![A:$i,B:$i,C:$i]:
% 0.22/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.56       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.22/0.56  thf('3', plain,
% 0.22/0.56      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.22/0.56         (((k2_relset_1 @ X35 @ X36 @ X34) = (k2_relat_1 @ X34))
% 0.22/0.56          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.22/0.56      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.22/0.56  thf('4', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.22/0.56      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.56  thf('5', plain,
% 0.22/0.56      ((~ (r1_tarski @ sk_C @ (k2_relat_1 @ sk_D)))
% 0.22/0.56         <= (~ ((r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D))))),
% 0.22/0.56      inference('demod', [status(thm)], ['1', '4'])).
% 0.22/0.56  thf('6', plain, ((r1_tarski @ (k6_relat_1 @ sk_C) @ sk_D)),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf(t36_xboole_1, axiom,
% 0.22/0.56    (![A:$i,B:$i]: ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ A ))).
% 0.22/0.56  thf('7', plain,
% 0.22/0.56      (![X5 : $i, X6 : $i]: (r1_tarski @ (k4_xboole_0 @ X5 @ X6) @ X5)),
% 0.22/0.56      inference('cnf', [status(esa)], [t36_xboole_1])).
% 0.22/0.56  thf(t1_xboole_1, axiom,
% 0.22/0.56    (![A:$i,B:$i,C:$i]:
% 0.22/0.56     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.22/0.56       ( r1_tarski @ A @ C ) ))).
% 0.22/0.56  thf('8', plain,
% 0.22/0.56      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.56         (~ (r1_tarski @ X2 @ X3)
% 0.22/0.56          | ~ (r1_tarski @ X3 @ X4)
% 0.22/0.56          | (r1_tarski @ X2 @ X4))),
% 0.22/0.56      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.22/0.56  thf('9', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.56         ((r1_tarski @ (k4_xboole_0 @ X0 @ X1) @ X2) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.56      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.56  thf('10', plain,
% 0.22/0.56      (![X0 : $i]:
% 0.22/0.56         (r1_tarski @ (k4_xboole_0 @ (k6_relat_1 @ sk_C) @ X0) @ sk_D)),
% 0.22/0.56      inference('sup-', [status(thm)], ['6', '9'])).
% 0.22/0.56  thf(t79_xboole_1, axiom,
% 0.22/0.56    (![A:$i,B:$i]: ( r1_xboole_0 @ ( k4_xboole_0 @ A @ B ) @ B ))).
% 0.22/0.56  thf('11', plain,
% 0.22/0.56      (![X12 : $i, X13 : $i]: (r1_xboole_0 @ (k4_xboole_0 @ X12 @ X13) @ X13)),
% 0.22/0.56      inference('cnf', [status(esa)], [t79_xboole_1])).
% 0.22/0.56  thf(t69_xboole_1, axiom,
% 0.22/0.56    (![A:$i,B:$i]:
% 0.22/0.56     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.56       ( ~( ( r1_tarski @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ))).
% 0.22/0.56  thf('12', plain,
% 0.22/0.56      (![X10 : $i, X11 : $i]:
% 0.22/0.56         (~ (r1_xboole_0 @ X10 @ X11)
% 0.22/0.56          | ~ (r1_tarski @ X10 @ X11)
% 0.22/0.56          | (v1_xboole_0 @ X10))),
% 0.22/0.56      inference('cnf', [status(esa)], [t69_xboole_1])).
% 0.22/0.56  thf('13', plain,
% 0.22/0.56      (![X0 : $i, X1 : $i]:
% 0.22/0.56         ((v1_xboole_0 @ (k4_xboole_0 @ X1 @ X0))
% 0.22/0.56          | ~ (r1_tarski @ (k4_xboole_0 @ X1 @ X0) @ X0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.56  thf('14', plain,
% 0.22/0.56      ((v1_xboole_0 @ (k4_xboole_0 @ (k6_relat_1 @ sk_C) @ sk_D))),
% 0.22/0.56      inference('sup-', [status(thm)], ['10', '13'])).
% 0.22/0.56  thf(l13_xboole_0, axiom,
% 0.22/0.56    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.22/0.56  thf('15', plain,
% 0.22/0.56      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.22/0.56      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.22/0.56  thf('16', plain,
% 0.22/0.56      (((k4_xboole_0 @ (k6_relat_1 @ sk_C) @ sk_D) = (k1_xboole_0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.56  thf(t15_relat_1, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( v1_relat_1 @ A ) =>
% 0.22/0.56       ( ![B:$i]:
% 0.22/0.56         ( ( v1_relat_1 @ B ) =>
% 0.22/0.56           ( r1_tarski @
% 0.22/0.56             ( k6_subset_1 @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) @ 
% 0.22/0.56             ( k1_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.22/0.56  thf('17', plain,
% 0.22/0.56      (![X20 : $i, X21 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ X20)
% 0.22/0.56          | (r1_tarski @ 
% 0.22/0.56             (k6_subset_1 @ (k1_relat_1 @ X21) @ (k1_relat_1 @ X20)) @ 
% 0.22/0.56             (k1_relat_1 @ (k6_subset_1 @ X21 @ X20)))
% 0.22/0.56          | ~ (v1_relat_1 @ X21))),
% 0.22/0.56      inference('cnf', [status(esa)], [t15_relat_1])).
% 0.22/0.56  thf(redefinition_k6_subset_1, axiom,
% 0.22/0.56    (![A:$i,B:$i]: ( ( k6_subset_1 @ A @ B ) = ( k4_xboole_0 @ A @ B ) ))).
% 0.22/0.56  thf('18', plain,
% 0.22/0.56      (![X18 : $i, X19 : $i]:
% 0.22/0.56         ((k6_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))),
% 0.22/0.56      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.22/0.56  thf('19', plain,
% 0.22/0.56      (![X18 : $i, X19 : $i]:
% 0.22/0.56         ((k6_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))),
% 0.22/0.56      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.22/0.56  thf('20', plain,
% 0.22/0.56      (![X20 : $i, X21 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ X20)
% 0.22/0.56          | (r1_tarski @ 
% 0.22/0.56             (k4_xboole_0 @ (k1_relat_1 @ X21) @ (k1_relat_1 @ X20)) @ 
% 0.22/0.56             (k1_relat_1 @ (k4_xboole_0 @ X21 @ X20)))
% 0.22/0.56          | ~ (v1_relat_1 @ X21))),
% 0.22/0.56      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.22/0.56  thf('21', plain,
% 0.22/0.56      (((r1_tarski @ 
% 0.22/0.56         (k4_xboole_0 @ (k1_relat_1 @ (k6_relat_1 @ sk_C)) @ 
% 0.22/0.56          (k1_relat_1 @ sk_D)) @ 
% 0.22/0.56         (k1_relat_1 @ k1_xboole_0))
% 0.22/0.56        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_C))
% 0.22/0.56        | ~ (v1_relat_1 @ sk_D))),
% 0.22/0.56      inference('sup+', [status(thm)], ['16', '20'])).
% 0.22/0.56  thf(t71_relat_1, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( ( k2_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) & 
% 0.22/0.56       ( ( k1_relat_1 @ ( k6_relat_1 @ A ) ) = ( A ) ) ))).
% 0.22/0.56  thf('22', plain, (![X24 : $i]: ((k1_relat_1 @ (k6_relat_1 @ X24)) = (X24))),
% 0.22/0.56      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.56  thf(t60_relat_1, axiom,
% 0.22/0.56    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.22/0.56     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.56  thf('23', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.56      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.56  thf(fc3_funct_1, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( v1_funct_1 @ ( k6_relat_1 @ A ) ) & 
% 0.22/0.56       ( v1_relat_1 @ ( k6_relat_1 @ A ) ) ))).
% 0.22/0.56  thf('24', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.22/0.56      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.22/0.56  thf('25', plain,
% 0.22/0.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf(cc1_relset_1, axiom,
% 0.22/0.56    (![A:$i,B:$i,C:$i]:
% 0.22/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.56       ( v1_relat_1 @ C ) ))).
% 0.22/0.56  thf('26', plain,
% 0.22/0.56      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.22/0.56         ((v1_relat_1 @ X28)
% 0.22/0.56          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.22/0.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.56  thf('27', plain, ((v1_relat_1 @ sk_D)),
% 0.22/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.56  thf('28', plain,
% 0.22/0.56      ((r1_tarski @ (k4_xboole_0 @ sk_C @ (k1_relat_1 @ sk_D)) @ k1_xboole_0)),
% 0.22/0.56      inference('demod', [status(thm)], ['21', '22', '23', '24', '27'])).
% 0.22/0.56  thf(t44_xboole_1, axiom,
% 0.22/0.56    (![A:$i,B:$i,C:$i]:
% 0.22/0.56     ( ( r1_tarski @ ( k4_xboole_0 @ A @ B ) @ C ) =>
% 0.22/0.56       ( r1_tarski @ A @ ( k2_xboole_0 @ B @ C ) ) ))).
% 0.22/0.56  thf('29', plain,
% 0.22/0.56      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.56         ((r1_tarski @ X7 @ (k2_xboole_0 @ X8 @ X9))
% 0.22/0.56          | ~ (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X9))),
% 0.22/0.56      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.22/0.56  thf('30', plain,
% 0.22/0.56      ((r1_tarski @ sk_C @ (k2_xboole_0 @ (k1_relat_1 @ sk_D) @ k1_xboole_0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.56  thf(t1_boole, axiom,
% 0.22/0.56    (![A:$i]: ( ( k2_xboole_0 @ A @ k1_xboole_0 ) = ( A ) ))).
% 0.22/0.56  thf('31', plain, (![X1 : $i]: ((k2_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.22/0.56      inference('cnf', [status(esa)], [t1_boole])).
% 0.22/0.56  thf('32', plain, ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_D))),
% 0.22/0.56      inference('demod', [status(thm)], ['30', '31'])).
% 0.22/0.56  thf('33', plain,
% 0.22/0.56      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.22/0.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.56  thf(redefinition_k1_relset_1, axiom,
% 0.22/0.56    (![A:$i,B:$i,C:$i]:
% 0.22/0.56     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.56       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.22/0.56  thf('34', plain,
% 0.22/0.56      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.22/0.56         (((k1_relset_1 @ X32 @ X33 @ X31) = (k1_relat_1 @ X31))
% 0.22/0.56          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.22/0.56      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.22/0.56  thf('35', plain,
% 0.22/0.56      (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.22/0.56      inference('sup-', [status(thm)], ['33', '34'])).
% 0.22/0.56  thf('36', plain,
% 0.22/0.56      ((~ (r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D)))
% 0.22/0.56         <= (~ ((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D))))),
% 0.22/0.56      inference('split', [status(esa)], ['0'])).
% 0.22/0.56  thf('37', plain,
% 0.22/0.56      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_D)))
% 0.22/0.56         <= (~ ((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D))))),
% 0.22/0.56      inference('sup-', [status(thm)], ['35', '36'])).
% 0.22/0.56  thf('38', plain, (((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.22/0.56      inference('sup-', [status(thm)], ['32', '37'])).
% 0.22/0.56  thf('39', plain,
% 0.22/0.56      (~ ((r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D))) | 
% 0.22/0.56       ~ ((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.22/0.56      inference('split', [status(esa)], ['0'])).
% 0.22/0.56  thf('40', plain,
% 0.22/0.56      (~ ((r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.22/0.56      inference('sat_resolution*', [status(thm)], ['38', '39'])).
% 0.22/0.56  thf('41', plain, (~ (r1_tarski @ sk_C @ (k2_relat_1 @ sk_D))),
% 0.22/0.56      inference('simpl_trail', [status(thm)], ['5', '40'])).
% 0.22/0.56  thf('42', plain,
% 0.22/0.56      (((k4_xboole_0 @ (k6_relat_1 @ sk_C) @ sk_D) = (k1_xboole_0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.56  thf(t28_relat_1, axiom,
% 0.22/0.56    (![A:$i]:
% 0.22/0.56     ( ( v1_relat_1 @ A ) =>
% 0.22/0.56       ( ![B:$i]:
% 0.22/0.56         ( ( v1_relat_1 @ B ) =>
% 0.22/0.56           ( r1_tarski @
% 0.22/0.56             ( k6_subset_1 @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) @ 
% 0.22/0.56             ( k2_relat_1 @ ( k6_subset_1 @ A @ B ) ) ) ) ) ))).
% 0.22/0.56  thf('43', plain,
% 0.22/0.56      (![X22 : $i, X23 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ X22)
% 0.22/0.56          | (r1_tarski @ 
% 0.22/0.56             (k6_subset_1 @ (k2_relat_1 @ X23) @ (k2_relat_1 @ X22)) @ 
% 0.22/0.56             (k2_relat_1 @ (k6_subset_1 @ X23 @ X22)))
% 0.22/0.56          | ~ (v1_relat_1 @ X23))),
% 0.22/0.56      inference('cnf', [status(esa)], [t28_relat_1])).
% 0.22/0.56  thf('44', plain,
% 0.22/0.56      (![X18 : $i, X19 : $i]:
% 0.22/0.56         ((k6_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))),
% 0.22/0.56      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.22/0.56  thf('45', plain,
% 0.22/0.56      (![X18 : $i, X19 : $i]:
% 0.22/0.56         ((k6_subset_1 @ X18 @ X19) = (k4_xboole_0 @ X18 @ X19))),
% 0.22/0.56      inference('cnf', [status(esa)], [redefinition_k6_subset_1])).
% 0.22/0.56  thf('46', plain,
% 0.22/0.56      (![X22 : $i, X23 : $i]:
% 0.22/0.56         (~ (v1_relat_1 @ X22)
% 0.22/0.56          | (r1_tarski @ 
% 0.22/0.56             (k4_xboole_0 @ (k2_relat_1 @ X23) @ (k2_relat_1 @ X22)) @ 
% 0.22/0.56             (k2_relat_1 @ (k4_xboole_0 @ X23 @ X22)))
% 0.22/0.56          | ~ (v1_relat_1 @ X23))),
% 0.22/0.56      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.22/0.56  thf('47', plain,
% 0.22/0.56      (((r1_tarski @ 
% 0.22/0.56         (k4_xboole_0 @ (k2_relat_1 @ (k6_relat_1 @ sk_C)) @ 
% 0.22/0.56          (k2_relat_1 @ sk_D)) @ 
% 0.22/0.56         (k2_relat_1 @ k1_xboole_0))
% 0.22/0.56        | ~ (v1_relat_1 @ (k6_relat_1 @ sk_C))
% 0.22/0.56        | ~ (v1_relat_1 @ sk_D))),
% 0.22/0.56      inference('sup+', [status(thm)], ['42', '46'])).
% 0.22/0.56  thf('48', plain, (![X25 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X25)) = (X25))),
% 0.22/0.56      inference('cnf', [status(esa)], [t71_relat_1])).
% 0.22/0.56  thf('49', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.56      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.56  thf('50', plain, (![X26 : $i]: (v1_relat_1 @ (k6_relat_1 @ X26))),
% 0.22/0.56      inference('cnf', [status(esa)], [fc3_funct_1])).
% 0.22/0.56  thf('51', plain, ((v1_relat_1 @ sk_D)),
% 0.22/0.56      inference('sup-', [status(thm)], ['25', '26'])).
% 0.22/0.56  thf('52', plain,
% 0.22/0.56      ((r1_tarski @ (k4_xboole_0 @ sk_C @ (k2_relat_1 @ sk_D)) @ k1_xboole_0)),
% 0.22/0.56      inference('demod', [status(thm)], ['47', '48', '49', '50', '51'])).
% 0.22/0.56  thf('53', plain,
% 0.22/0.56      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.56         ((r1_tarski @ X7 @ (k2_xboole_0 @ X8 @ X9))
% 0.22/0.56          | ~ (r1_tarski @ (k4_xboole_0 @ X7 @ X8) @ X9))),
% 0.22/0.56      inference('cnf', [status(esa)], [t44_xboole_1])).
% 0.22/0.56  thf('54', plain,
% 0.22/0.56      ((r1_tarski @ sk_C @ (k2_xboole_0 @ (k2_relat_1 @ sk_D) @ k1_xboole_0))),
% 0.22/0.56      inference('sup-', [status(thm)], ['52', '53'])).
% 0.22/0.56  thf('55', plain, (![X1 : $i]: ((k2_xboole_0 @ X1 @ k1_xboole_0) = (X1))),
% 0.22/0.56      inference('cnf', [status(esa)], [t1_boole])).
% 0.22/0.56  thf('56', plain, ((r1_tarski @ sk_C @ (k2_relat_1 @ sk_D))),
% 0.22/0.56      inference('demod', [status(thm)], ['54', '55'])).
% 0.22/0.56  thf('57', plain, ($false), inference('demod', [status(thm)], ['41', '56'])).
% 0.22/0.56  
% 0.22/0.56  % SZS output end Refutation
% 0.22/0.56  
% 0.22/0.57  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
