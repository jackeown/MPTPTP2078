%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FQ0GlfhXAG

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:49:02 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 285 expanded)
%              Number of leaves         :   33 ( 103 expanded)
%              Depth                    :   17
%              Number of atoms          :  781 (2277 expanded)
%              Number of equality atoms :   27 (  54 expanded)
%              Maximal formula depth    :   13 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k5_relat_1_type,type,(
    k5_relat_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ( ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k1_relset_1 @ X38 @ X39 @ X37 )
        = ( k1_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('4',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_D ) )
   <= ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['1','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('7',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k2_relset_1 @ X41 @ X42 @ X40 )
        = ( k2_relat_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('8',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) )
   <= ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('10',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k2_relat_1 @ sk_D ) )
   <= ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_C ) @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( r1_tarski @ ( k2_relat_1 @ X24 ) @ ( k2_relat_1 @ X23 ) )
      | ~ ( r1_tarski @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ sk_C ) ) @ ( k2_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(t29_relset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )).

thf('14',plain,(
    ! [X43: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('15',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v1_relat_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('16',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X12: $i,X14: $i] :
      ( ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ X14 ) )
      | ~ ( r1_tarski @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t162_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B )
        = B ) ) )).

thf('21',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k9_relat_1 @ ( k6_relat_1 @ X30 ) @ X29 )
        = X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t162_funct_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('23',plain,(
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X21 @ X22 ) @ ( k2_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('26',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) @ X0 )
      | ( ( k2_relat_1 @ ( k6_relat_1 @ X0 ) )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X43: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('30',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v5_relat_1 @ X34 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( v5_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('32',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v5_relat_1 @ X19 @ X20 )
      | ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('35',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['28','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v1_relat_1 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('39',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    r1_tarski @ sk_C @ ( k2_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['13','16','36','39'])).

thf('41',plain,(
    r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['10','40'])).

thf('42',plain,
    ( ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) )
    | ~ ( r1_tarski @ sk_C @ ( k2_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(split,[status(esa)],['0'])).

thf('43',plain,(
    ~ ( r1_tarski @ sk_C @ ( k1_relset_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sat_resolution*',[status(thm)],['41','42'])).

thf('44',plain,(
    ~ ( r1_tarski @ sk_C @ ( k1_relat_1 @ sk_D ) ) ),
    inference(simpl_trail,[status(thm)],['5','43'])).

thf('45',plain,(
    r1_tarski @ ( k6_relat_1 @ sk_C ) @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X23: $i,X24: $i] :
      ( ~ ( v1_relat_1 @ X23 )
      | ( r1_tarski @ ( k1_relat_1 @ X24 ) @ ( k1_relat_1 @ X23 ) )
      | ~ ( r1_tarski @ X24 @ X23 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('47',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) )
    | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_D ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('49',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['37','38'])).

thf('50',plain,(
    r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['28','35'])).

thf('52',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ( v5_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('53',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( v5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( v5_relat_1 @ ( k6_relat_1 @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    v5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ sk_C ) ) ) @ ( k1_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['50','55'])).

thf('57',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(t77_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B )
          = B ) ) ) )).

thf('58',plain,(
    ! [X25: $i,X26: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X25 ) @ X26 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X26 ) @ X25 )
        = X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t77_relat_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ X0 ) ) @ X0 )
        = X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X43: $i] :
      ( m1_subset_1 @ ( k6_relat_1 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[t29_relset_1])).

thf('61',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v4_relat_1 @ X34 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k6_relat_1 @ X0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('63',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v4_relat_1 @ X17 @ X18 )
      | ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('66',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['28','35'])).

thf(t79_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A )
       => ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) )
          = B ) ) ) )).

thf('68',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X27 ) @ X28 )
      | ( ( k5_relat_1 @ X27 @ ( k6_relat_1 @ X28 ) )
        = X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t79_relat_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('71',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ( ( k5_relat_1 @ ( k6_relat_1 @ X0 ) @ ( k6_relat_1 @ X1 ) )
        = ( k6_relat_1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k5_relat_1 @ ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) @ ( k6_relat_1 @ X0 ) )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['66','71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k6_relat_1 @ X0 )
        = ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) )
      | ~ ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['59','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k6_relat_1 @ X0 )
      = ( k6_relat_1 @ ( k1_relat_1 @ ( k6_relat_1 @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    v5_relat_1 @ ( k6_relat_1 @ sk_C ) @ ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['56','75'])).

thf('77',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v5_relat_1 @ X19 @ X20 )
      | ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('78',plain,
    ( ~ ( v1_relat_1 @ ( k6_relat_1 @ sk_C ) )
    | ( r1_tarski @ ( k2_relat_1 @ ( k6_relat_1 @ sk_C ) ) @ ( k1_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k6_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k6_relat_1 @ X0 ) )
      = X0 ) ),
    inference(demod,[status(thm)],['28','35'])).

thf('81',plain,(
    r1_tarski @ sk_C @ ( k1_relat_1 @ sk_D ) ),
    inference(demod,[status(thm)],['78','79','80'])).

thf('82',plain,(
    $false ),
    inference(demod,[status(thm)],['44','81'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FQ0GlfhXAG
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:02:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.70  % Solved by: fo/fo7.sh
% 0.46/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.70  % done 514 iterations in 0.244s
% 0.46/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.70  % SZS output start Refutation
% 0.46/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.70  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.46/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.46/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.70  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.46/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.70  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.46/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.46/0.70  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.70  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.46/0.70  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.46/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.70  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.46/0.70  thf(k5_relat_1_type, type, k5_relat_1: $i > $i > $i).
% 0.46/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.70  thf(t30_relset_1, conjecture,
% 0.46/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70       ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D ) =>
% 0.46/0.70         ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) ) & 
% 0.46/0.70           ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ))).
% 0.46/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.70    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.70        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70          ( ( r1_tarski @ ( k6_relat_1 @ C ) @ D ) =>
% 0.46/0.70            ( ( r1_tarski @ C @ ( k1_relset_1 @ A @ B @ D ) ) & 
% 0.46/0.70              ( r1_tarski @ C @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) )),
% 0.46/0.70    inference('cnf.neg', [status(esa)], [t30_relset_1])).
% 0.46/0.70  thf('0', plain,
% 0.46/0.70      ((~ (r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D))
% 0.46/0.70        | ~ (r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('1', plain,
% 0.46/0.70      ((~ (r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D)))
% 0.46/0.70         <= (~ ((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D))))),
% 0.46/0.70      inference('split', [status(esa)], ['0'])).
% 0.46/0.70  thf('2', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(redefinition_k1_relset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.46/0.70  thf('3', plain,
% 0.46/0.70      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.46/0.70         (((k1_relset_1 @ X38 @ X39 @ X37) = (k1_relat_1 @ X37))
% 0.46/0.70          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.46/0.70  thf('4', plain, (((k1_relset_1 @ sk_A @ sk_B @ sk_D) = (k1_relat_1 @ sk_D))),
% 0.46/0.70      inference('sup-', [status(thm)], ['2', '3'])).
% 0.46/0.70  thf('5', plain,
% 0.46/0.70      ((~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_D)))
% 0.46/0.70         <= (~ ((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D))))),
% 0.46/0.70      inference('demod', [status(thm)], ['1', '4'])).
% 0.46/0.70  thf('6', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(redefinition_k2_relset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.46/0.70  thf('7', plain,
% 0.46/0.70      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.46/0.70         (((k2_relset_1 @ X41 @ X42 @ X40) = (k2_relat_1 @ X40))
% 0.46/0.70          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 0.46/0.70      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.46/0.70  thf('8', plain, (((k2_relset_1 @ sk_A @ sk_B @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.46/0.70      inference('sup-', [status(thm)], ['6', '7'])).
% 0.46/0.70  thf('9', plain,
% 0.46/0.70      ((~ (r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D)))
% 0.46/0.70         <= (~ ((r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D))))),
% 0.46/0.70      inference('split', [status(esa)], ['0'])).
% 0.46/0.70  thf('10', plain,
% 0.46/0.70      ((~ (r1_tarski @ sk_C @ (k2_relat_1 @ sk_D)))
% 0.46/0.70         <= (~ ((r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.70  thf('11', plain, ((r1_tarski @ (k6_relat_1 @ sk_C) @ sk_D)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf(t25_relat_1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( ( v1_relat_1 @ A ) =>
% 0.46/0.70       ( ![B:$i]:
% 0.46/0.70         ( ( v1_relat_1 @ B ) =>
% 0.46/0.70           ( ( r1_tarski @ A @ B ) =>
% 0.46/0.70             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.46/0.70               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.46/0.70  thf('12', plain,
% 0.46/0.70      (![X23 : $i, X24 : $i]:
% 0.46/0.70         (~ (v1_relat_1 @ X23)
% 0.46/0.70          | (r1_tarski @ (k2_relat_1 @ X24) @ (k2_relat_1 @ X23))
% 0.46/0.70          | ~ (r1_tarski @ X24 @ X23)
% 0.46/0.70          | ~ (v1_relat_1 @ X24))),
% 0.46/0.70      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.46/0.70  thf('13', plain,
% 0.46/0.70      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_C))
% 0.46/0.70        | (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ sk_C)) @ (k2_relat_1 @ sk_D))
% 0.46/0.70        | ~ (v1_relat_1 @ sk_D))),
% 0.46/0.70      inference('sup-', [status(thm)], ['11', '12'])).
% 0.46/0.70  thf(t29_relset_1, axiom,
% 0.46/0.70    (![A:$i]:
% 0.46/0.70     ( m1_subset_1 @
% 0.46/0.70       ( k6_relat_1 @ A ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ))).
% 0.46/0.70  thf('14', plain,
% 0.46/0.70      (![X43 : $i]:
% 0.46/0.70         (m1_subset_1 @ (k6_relat_1 @ X43) @ 
% 0.46/0.70          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X43)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.46/0.70  thf(cc1_relset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70       ( v1_relat_1 @ C ) ))).
% 0.46/0.70  thf('15', plain,
% 0.46/0.70      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.46/0.70         ((v1_relat_1 @ X31)
% 0.46/0.70          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.70  thf('16', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.70  thf(d10_xboole_0, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.46/0.70  thf('17', plain,
% 0.46/0.70      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.46/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.70  thf('18', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.46/0.70      inference('simplify', [status(thm)], ['17'])).
% 0.46/0.70  thf(t3_subset, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.46/0.70  thf('19', plain,
% 0.46/0.70      (![X12 : $i, X14 : $i]:
% 0.46/0.70         ((m1_subset_1 @ X12 @ (k1_zfmisc_1 @ X14)) | ~ (r1_tarski @ X12 @ X14))),
% 0.46/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.46/0.70  thf('20', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['18', '19'])).
% 0.46/0.70  thf(t162_funct_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.70       ( ( k9_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ))).
% 0.46/0.70  thf('21', plain,
% 0.46/0.70      (![X29 : $i, X30 : $i]:
% 0.46/0.70         (((k9_relat_1 @ (k6_relat_1 @ X30) @ X29) = (X29))
% 0.46/0.70          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t162_funct_1])).
% 0.46/0.70  thf('22', plain,
% 0.46/0.70      (![X0 : $i]: ((k9_relat_1 @ (k6_relat_1 @ X0) @ X0) = (X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['20', '21'])).
% 0.46/0.70  thf(t144_relat_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( v1_relat_1 @ B ) =>
% 0.46/0.70       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.46/0.70  thf('23', plain,
% 0.46/0.70      (![X21 : $i, X22 : $i]:
% 0.46/0.70         ((r1_tarski @ (k9_relat_1 @ X21 @ X22) @ (k2_relat_1 @ X21))
% 0.46/0.70          | ~ (v1_relat_1 @ X21))),
% 0.46/0.70      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.46/0.70  thf('24', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((r1_tarski @ X0 @ (k2_relat_1 @ (k6_relat_1 @ X0)))
% 0.46/0.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.46/0.70      inference('sup+', [status(thm)], ['22', '23'])).
% 0.46/0.70  thf('25', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.70  thf('26', plain,
% 0.46/0.70      (![X0 : $i]: (r1_tarski @ X0 @ (k2_relat_1 @ (k6_relat_1 @ X0)))),
% 0.46/0.70      inference('demod', [status(thm)], ['24', '25'])).
% 0.46/0.70  thf('27', plain,
% 0.46/0.70      (![X3 : $i, X5 : $i]:
% 0.46/0.70         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 0.46/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.46/0.70  thf('28', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ X0)) @ X0)
% 0.46/0.70          | ((k2_relat_1 @ (k6_relat_1 @ X0)) = (X0)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['26', '27'])).
% 0.46/0.70  thf('29', plain,
% 0.46/0.70      (![X43 : $i]:
% 0.46/0.70         (m1_subset_1 @ (k6_relat_1 @ X43) @ 
% 0.46/0.70          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X43)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.46/0.70  thf(cc2_relset_1, axiom,
% 0.46/0.70    (![A:$i,B:$i,C:$i]:
% 0.46/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.70       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.46/0.70  thf('30', plain,
% 0.46/0.70      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.46/0.70         ((v5_relat_1 @ X34 @ X36)
% 0.46/0.70          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.70  thf('31', plain, (![X0 : $i]: (v5_relat_1 @ (k6_relat_1 @ X0) @ X0)),
% 0.46/0.70      inference('sup-', [status(thm)], ['29', '30'])).
% 0.46/0.70  thf(d19_relat_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( v1_relat_1 @ B ) =>
% 0.46/0.70       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.46/0.70  thf('32', plain,
% 0.46/0.70      (![X19 : $i, X20 : $i]:
% 0.46/0.70         (~ (v5_relat_1 @ X19 @ X20)
% 0.46/0.70          | (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 0.46/0.70          | ~ (v1_relat_1 @ X19))),
% 0.46/0.70      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.46/0.70  thf('33', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.46/0.70          | (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ X0)) @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['31', '32'])).
% 0.46/0.70  thf('34', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.70  thf('35', plain,
% 0.46/0.70      (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ X0)) @ X0)),
% 0.46/0.70      inference('demod', [status(thm)], ['33', '34'])).
% 0.46/0.70  thf('36', plain, (![X0 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 0.46/0.70      inference('demod', [status(thm)], ['28', '35'])).
% 0.46/0.70  thf('37', plain,
% 0.46/0.70      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('38', plain,
% 0.46/0.70      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.46/0.70         ((v1_relat_1 @ X31)
% 0.46/0.70          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.70  thf('39', plain, ((v1_relat_1 @ sk_D)),
% 0.46/0.70      inference('sup-', [status(thm)], ['37', '38'])).
% 0.46/0.70  thf('40', plain, ((r1_tarski @ sk_C @ (k2_relat_1 @ sk_D))),
% 0.46/0.70      inference('demod', [status(thm)], ['13', '16', '36', '39'])).
% 0.46/0.70  thf('41', plain, (((r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.46/0.70      inference('demod', [status(thm)], ['10', '40'])).
% 0.46/0.70  thf('42', plain,
% 0.46/0.70      (~ ((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D))) | 
% 0.46/0.70       ~ ((r1_tarski @ sk_C @ (k2_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.46/0.70      inference('split', [status(esa)], ['0'])).
% 0.46/0.70  thf('43', plain,
% 0.46/0.70      (~ ((r1_tarski @ sk_C @ (k1_relset_1 @ sk_A @ sk_B @ sk_D)))),
% 0.46/0.70      inference('sat_resolution*', [status(thm)], ['41', '42'])).
% 0.46/0.70  thf('44', plain, (~ (r1_tarski @ sk_C @ (k1_relat_1 @ sk_D))),
% 0.46/0.70      inference('simpl_trail', [status(thm)], ['5', '43'])).
% 0.46/0.70  thf('45', plain, ((r1_tarski @ (k6_relat_1 @ sk_C) @ sk_D)),
% 0.46/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.70  thf('46', plain,
% 0.46/0.70      (![X23 : $i, X24 : $i]:
% 0.46/0.70         (~ (v1_relat_1 @ X23)
% 0.46/0.70          | (r1_tarski @ (k1_relat_1 @ X24) @ (k1_relat_1 @ X23))
% 0.46/0.70          | ~ (r1_tarski @ X24 @ X23)
% 0.46/0.70          | ~ (v1_relat_1 @ X24))),
% 0.46/0.70      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.46/0.70  thf('47', plain,
% 0.46/0.70      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_C))
% 0.46/0.70        | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ sk_C)) @ (k1_relat_1 @ sk_D))
% 0.46/0.70        | ~ (v1_relat_1 @ sk_D))),
% 0.46/0.70      inference('sup-', [status(thm)], ['45', '46'])).
% 0.46/0.70  thf('48', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.70  thf('49', plain, ((v1_relat_1 @ sk_D)),
% 0.46/0.70      inference('sup-', [status(thm)], ['37', '38'])).
% 0.46/0.70  thf('50', plain,
% 0.46/0.70      ((r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ sk_C)) @ (k1_relat_1 @ sk_D))),
% 0.46/0.70      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.46/0.70  thf('51', plain, (![X0 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 0.46/0.70      inference('demod', [status(thm)], ['28', '35'])).
% 0.46/0.70  thf('52', plain,
% 0.46/0.70      (![X19 : $i, X20 : $i]:
% 0.46/0.70         (~ (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 0.46/0.70          | (v5_relat_1 @ X19 @ X20)
% 0.46/0.70          | ~ (v1_relat_1 @ X19))),
% 0.46/0.70      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.46/0.70  thf('53', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (~ (r1_tarski @ X0 @ X1)
% 0.46/0.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.46/0.70          | (v5_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.46/0.70      inference('sup-', [status(thm)], ['51', '52'])).
% 0.46/0.70  thf('54', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.70  thf('55', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (~ (r1_tarski @ X0 @ X1) | (v5_relat_1 @ (k6_relat_1 @ X0) @ X1))),
% 0.46/0.70      inference('demod', [status(thm)], ['53', '54'])).
% 0.46/0.70  thf('56', plain,
% 0.46/0.70      ((v5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ (k6_relat_1 @ sk_C))) @ 
% 0.46/0.70        (k1_relat_1 @ sk_D))),
% 0.46/0.70      inference('sup-', [status(thm)], ['50', '55'])).
% 0.46/0.70  thf('57', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.46/0.70      inference('simplify', [status(thm)], ['17'])).
% 0.46/0.70  thf(t77_relat_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( v1_relat_1 @ B ) =>
% 0.46/0.70       ( ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) =>
% 0.46/0.70         ( ( k5_relat_1 @ ( k6_relat_1 @ A ) @ B ) = ( B ) ) ) ))).
% 0.46/0.70  thf('58', plain,
% 0.46/0.70      (![X25 : $i, X26 : $i]:
% 0.46/0.70         (~ (r1_tarski @ (k1_relat_1 @ X25) @ X26)
% 0.46/0.70          | ((k5_relat_1 @ (k6_relat_1 @ X26) @ X25) = (X25))
% 0.46/0.70          | ~ (v1_relat_1 @ X25))),
% 0.46/0.70      inference('cnf', [status(esa)], [t77_relat_1])).
% 0.46/0.70  thf('59', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v1_relat_1 @ X0)
% 0.46/0.70          | ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ X0)) @ X0) = (X0)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['57', '58'])).
% 0.46/0.70  thf('60', plain,
% 0.46/0.70      (![X43 : $i]:
% 0.46/0.70         (m1_subset_1 @ (k6_relat_1 @ X43) @ 
% 0.46/0.70          (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X43)))),
% 0.46/0.70      inference('cnf', [status(esa)], [t29_relset_1])).
% 0.46/0.70  thf('61', plain,
% 0.46/0.70      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.46/0.70         ((v4_relat_1 @ X34 @ X35)
% 0.46/0.70          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.46/0.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.46/0.70  thf('62', plain, (![X0 : $i]: (v4_relat_1 @ (k6_relat_1 @ X0) @ X0)),
% 0.46/0.70      inference('sup-', [status(thm)], ['60', '61'])).
% 0.46/0.70  thf(d18_relat_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( v1_relat_1 @ B ) =>
% 0.46/0.70       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.46/0.70  thf('63', plain,
% 0.46/0.70      (![X17 : $i, X18 : $i]:
% 0.46/0.70         (~ (v4_relat_1 @ X17 @ X18)
% 0.46/0.70          | (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 0.46/0.70          | ~ (v1_relat_1 @ X17))),
% 0.46/0.70      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.46/0.70  thf('64', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.46/0.70          | (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['62', '63'])).
% 0.46/0.70  thf('65', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.70  thf('66', plain,
% 0.46/0.70      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ (k6_relat_1 @ X0)) @ X0)),
% 0.46/0.70      inference('demod', [status(thm)], ['64', '65'])).
% 0.46/0.70  thf('67', plain, (![X0 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 0.46/0.70      inference('demod', [status(thm)], ['28', '35'])).
% 0.46/0.70  thf(t79_relat_1, axiom,
% 0.46/0.70    (![A:$i,B:$i]:
% 0.46/0.70     ( ( v1_relat_1 @ B ) =>
% 0.46/0.70       ( ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) =>
% 0.46/0.70         ( ( k5_relat_1 @ B @ ( k6_relat_1 @ A ) ) = ( B ) ) ) ))).
% 0.46/0.70  thf('68', plain,
% 0.46/0.70      (![X27 : $i, X28 : $i]:
% 0.46/0.70         (~ (r1_tarski @ (k2_relat_1 @ X27) @ X28)
% 0.46/0.70          | ((k5_relat_1 @ X27 @ (k6_relat_1 @ X28)) = (X27))
% 0.46/0.70          | ~ (v1_relat_1 @ X27))),
% 0.46/0.70      inference('cnf', [status(esa)], [t79_relat_1])).
% 0.46/0.70  thf('69', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (~ (r1_tarski @ X0 @ X1)
% 0.46/0.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X0))
% 0.46/0.70          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.46/0.70              = (k6_relat_1 @ X0)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['67', '68'])).
% 0.46/0.70  thf('70', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.70  thf('71', plain,
% 0.46/0.70      (![X0 : $i, X1 : $i]:
% 0.46/0.70         (~ (r1_tarski @ X0 @ X1)
% 0.46/0.70          | ((k5_relat_1 @ (k6_relat_1 @ X0) @ (k6_relat_1 @ X1))
% 0.46/0.70              = (k6_relat_1 @ X0)))),
% 0.46/0.70      inference('demod', [status(thm)], ['69', '70'])).
% 0.46/0.70  thf('72', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((k5_relat_1 @ (k6_relat_1 @ (k1_relat_1 @ (k6_relat_1 @ X0))) @ 
% 0.46/0.70           (k6_relat_1 @ X0)) = (k6_relat_1 @ (k1_relat_1 @ (k6_relat_1 @ X0))))),
% 0.46/0.70      inference('sup-', [status(thm)], ['66', '71'])).
% 0.46/0.70  thf('73', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         (((k6_relat_1 @ X0) = (k6_relat_1 @ (k1_relat_1 @ (k6_relat_1 @ X0))))
% 0.46/0.70          | ~ (v1_relat_1 @ (k6_relat_1 @ X0)))),
% 0.46/0.70      inference('sup+', [status(thm)], ['59', '72'])).
% 0.46/0.70  thf('74', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.70  thf('75', plain,
% 0.46/0.70      (![X0 : $i]:
% 0.46/0.70         ((k6_relat_1 @ X0) = (k6_relat_1 @ (k1_relat_1 @ (k6_relat_1 @ X0))))),
% 0.46/0.70      inference('demod', [status(thm)], ['73', '74'])).
% 0.46/0.70  thf('76', plain, ((v5_relat_1 @ (k6_relat_1 @ sk_C) @ (k1_relat_1 @ sk_D))),
% 0.46/0.70      inference('demod', [status(thm)], ['56', '75'])).
% 0.46/0.70  thf('77', plain,
% 0.46/0.70      (![X19 : $i, X20 : $i]:
% 0.46/0.70         (~ (v5_relat_1 @ X19 @ X20)
% 0.46/0.70          | (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 0.46/0.70          | ~ (v1_relat_1 @ X19))),
% 0.46/0.70      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.46/0.70  thf('78', plain,
% 0.46/0.70      ((~ (v1_relat_1 @ (k6_relat_1 @ sk_C))
% 0.46/0.70        | (r1_tarski @ (k2_relat_1 @ (k6_relat_1 @ sk_C)) @ (k1_relat_1 @ sk_D)))),
% 0.46/0.70      inference('sup-', [status(thm)], ['76', '77'])).
% 0.46/0.70  thf('79', plain, (![X0 : $i]: (v1_relat_1 @ (k6_relat_1 @ X0))),
% 0.46/0.70      inference('sup-', [status(thm)], ['14', '15'])).
% 0.46/0.70  thf('80', plain, (![X0 : $i]: ((k2_relat_1 @ (k6_relat_1 @ X0)) = (X0))),
% 0.46/0.70      inference('demod', [status(thm)], ['28', '35'])).
% 0.46/0.70  thf('81', plain, ((r1_tarski @ sk_C @ (k1_relat_1 @ sk_D))),
% 0.46/0.70      inference('demod', [status(thm)], ['78', '79', '80'])).
% 0.46/0.70  thf('82', plain, ($false), inference('demod', [status(thm)], ['44', '81'])).
% 0.46/0.70  
% 0.46/0.70  % SZS output end Refutation
% 0.46/0.70  
% 0.56/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
