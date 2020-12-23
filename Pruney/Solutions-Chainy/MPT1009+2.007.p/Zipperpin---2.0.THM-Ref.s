%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.icLeLG3BKi

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:49 EST 2020

% Result     : Theorem 3.25s
% Output     : Refutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :  249 (1557 expanded)
%              Number of leaves         :   45 ( 488 expanded)
%              Depth                    :   40
%              Number of atoms          : 2089 (14223 expanded)
%              Number of equality atoms :  136 ( 631 expanded)
%              Maximal formula depth    :   15 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(t64_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X74: $i,X75: $i,X76: $i,X77: $i] :
      ( ~ ( m1_subset_1 @ X74 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X75 @ X76 ) ) )
      | ( ( k7_relset_1 @ X75 @ X76 @ X74 @ X77 )
        = ( k9_relat_1 @ X74 @ X77 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('5',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t205_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) )
      <=> ( ( k11_relat_1 @ B @ A )
         != k1_xboole_0 ) ) ) )).

thf('6',plain,(
    ! [X48: $i,X49: $i] :
      ( ( ( k11_relat_1 @ X48 @ X49 )
        = k1_xboole_0 )
      | ( r2_hidden @ X49 @ ( k1_relat_1 @ X48 ) )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf('7',plain,(
    ! [X48: $i,X49: $i] :
      ( ( ( k11_relat_1 @ X48 @ X49 )
        = k1_xboole_0 )
      | ( r2_hidden @ X49 @ ( k1_relat_1 @ X48 ) )
      | ~ ( v1_relat_1 @ X48 ) ) ),
    inference(cnf,[status(esa)],[t205_relat_1])).

thf(t38_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ C ) ) ) )).

thf('8',plain,(
    ! [X35: $i,X37: $i,X38: $i] :
      ( ( r1_tarski @ ( k2_tarski @ X35 @ X37 ) @ X38 )
      | ~ ( r2_hidden @ X37 @ X38 )
      | ~ ( r2_hidden @ X35 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t38_zfmisc_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ X0 ) )
      | ( r1_tarski @ ( k2_tarski @ X2 @ X1 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X2 ) @ ( k1_relat_1 @ X0 ) )
      | ( ( k11_relat_1 @ X0 @ X2 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['6','9'])).

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( ( k11_relat_1 @ X0 @ X2 )
        = k1_xboole_0 )
      | ( r1_tarski @ ( k2_tarski @ X1 @ X2 ) @ ( k1_relat_1 @ X0 ) )
      | ( ( k11_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_relat_1 @ X1 ) )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['5','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k11_relat_1 @ X1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k1_tarski @ X0 ) @ ( k1_relat_1 @ X1 ) ) ) ),
    inference(simplify,[status(thm)],['12'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('15',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['14'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X39: $i,X41: $i] :
      ( ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( r1_tarski @ X39 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('17',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('18',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ( v4_relat_1 @ X61 @ X62 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X63 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i] :
      ( v4_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ( v4_relat_1 @ X61 @ X62 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X63 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('22',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('23',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( v4_relat_1 @ X44 @ X45 )
      | ( r1_tarski @ ( k1_relat_1 @ X44 ) @ X45 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('24',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('26',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ( v1_relat_1 @ X58 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X60 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('27',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['24','27'])).

thf(t217_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
     => ! [C: $i] :
          ( ( ( v1_relat_1 @ C )
            & ( v4_relat_1 @ C @ A ) )
         => ( v4_relat_1 @ C @ B ) ) ) )).

thf('29',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( v1_relat_1 @ X52 )
      | ~ ( v4_relat_1 @ X52 @ X53 )
      | ( v4_relat_1 @ X52 @ X54 )
      | ~ ( r1_tarski @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t217_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ ( k1_tarski @ sk_A ) )
      | ~ ( v4_relat_1 @ X0 @ ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) )
      | ( v4_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['19','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('33',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ( v1_relat_1 @ X58 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X60 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( v4_relat_1 @ X44 @ X45 )
      | ( r1_tarski @ ( k1_relat_1 @ X44 ) @ X45 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('39',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) ) )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) )
      | ( ( k11_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) @ sk_A )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['13','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(d16_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( k11_relat_1 @ A @ B )
          = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) )).

thf('44',plain,(
    ! [X42: $i,X43: $i] :
      ( ( ( k11_relat_1 @ X42 @ X43 )
        = ( k9_relat_1 @ X42 @ ( k1_tarski @ X43 ) ) )
      | ~ ( v1_relat_1 @ X42 ) ) ),
    inference(cnf,[status(esa)],[d16_relat_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['31','34'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('46',plain,(
    ! [X50: $i,X51: $i] :
      ( ( X50
        = ( k7_relat_1 @ X50 @ X51 ) )
      | ~ ( v4_relat_1 @ X50 @ X51 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) )
      | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 )
        = ( k7_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) @ ( k1_tarski @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 )
      = ( k7_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('50',plain,(
    ! [X46: $i,X47: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X46 @ X47 ) )
        = ( k9_relat_1 @ X46 @ X47 ) )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) )
        = ( k9_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) @ ( k1_tarski @ sk_A ) ) )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) )
      = ( k9_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) @ ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) )
        = ( k11_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) @ sk_A ) )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ) ),
    inference('sup+',[status(thm)],['44','53'])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) )
      = ( k11_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) @ sk_A ) ) ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['42','43','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) )
        = k1_xboole_0 )
      | ( ( k1_tarski @ sk_A )
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['42','43','56'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( v4_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('60',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( v4_relat_1 @ X44 @ X45 )
      | ( r1_tarski @ ( k1_relat_1 @ X44 ) @ X45 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X0 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) )
      | ( X0
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_D )
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['58','65'])).

thf('67',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['24','27'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_D )
        = ( k1_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D )
        = ( k1_tarski @ sk_A ) )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) )
        = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) )
        = k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['57','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_D )
        = ( k1_tarski @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('72',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf(t14_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) )
     => ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ) )).

thf('73',plain,(
    ! [X82: $i,X83: $i,X84: $i,X85: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X82 ) @ X83 )
      | ( m1_subset_1 @ X82 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X84 @ X83 ) ) )
      | ~ ( m1_subset_1 @ X82 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X84 @ X85 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['71','74'])).

thf('76',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r1_tarski @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k2_zfmisc_1 @ X1 @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ k1_xboole_0 ) )
      | ( ( k1_relat_1 @ sk_D )
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['70','77'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('79',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k2_zfmisc_1 @ X33 @ X34 )
        = k1_xboole_0 )
      | ( X34 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('80',plain,(
    ! [X33: $i] :
      ( ( k2_zfmisc_1 @ X33 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) @ k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_D )
        = ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['78','80'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('82',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('83',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('84',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D )
        = ( k1_tarski @ sk_A ) )
      | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( v4_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('87',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('88',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('89',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('90',plain,(
    ! [X78: $i,X79: $i,X80: $i,X81: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X78 ) @ X79 )
      | ( m1_subset_1 @ X78 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X79 @ X80 ) ) )
      | ~ ( m1_subset_1 @ X78 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X81 @ X80 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['88','91'])).

thf('93',plain,(
    ! [X82: $i,X83: $i,X84: $i,X85: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X82 ) @ X83 )
      | ( m1_subset_1 @ X82 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X84 @ X83 ) ) )
      | ~ ( m1_subset_1 @ X82 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X84 @ X85 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['87','94'])).

thf('96',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r1_tarski @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('97',plain,(
    r1_tarski @ sk_D @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X52: $i,X53: $i,X54: $i] :
      ( ~ ( v1_relat_1 @ X52 )
      | ~ ( v4_relat_1 @ X52 @ X53 )
      | ( v4_relat_1 @ X52 @ X54 )
      | ~ ( r1_tarski @ X53 @ X54 ) ) ),
    inference(cnf,[status(esa)],[t217_relat_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( v4_relat_1 @ X0 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) )
      | ~ ( v4_relat_1 @ X0 @ sk_D )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_D @ X0 ) )
      | ( v4_relat_1 @ ( k2_zfmisc_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['86','99'])).

thf('101',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('102',plain,(
    ! [X0: $i] :
      ( v4_relat_1 @ ( k2_zfmisc_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( v4_relat_1 @ X44 @ X45 )
      | ( r1_tarski @ ( k1_relat_1 @ X44 ) @ X45 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('104',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_D @ X0 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_D @ X0 ) ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('106',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_D @ X0 ) ) @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('108',plain,(
    ! [X78: $i,X79: $i,X80: $i,X81: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X78 ) @ X79 )
      | ( m1_subset_1 @ X78 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X79 @ X80 ) ) )
      | ~ ( m1_subset_1 @ X78 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X81 @ X80 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X0 ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_zfmisc_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['106','109'])).

thf('111',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r1_tarski @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('112',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_zfmisc_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_D @ X0 ) @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( ( k1_relat_1 @ sk_D )
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['85','112'])).

thf('114',plain,(
    ! [X33: $i,X34: $i] :
      ( ( ( k2_zfmisc_1 @ X33 @ X34 )
        = k1_xboole_0 )
      | ( X33 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('115',plain,(
    ! [X34: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X34 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k2_zfmisc_1 @ sk_D @ X0 ) @ k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_D )
        = ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['113','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D )
        = ( k1_tarski @ sk_A ) )
      | ( ( k2_zfmisc_1 @ sk_D @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D )
        = ( k1_tarski @ sk_A ) )
      | ( ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['81','84'])).

thf('120',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_relat_1 @ sk_D ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['87','94'])).

thf('121',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['119','120'])).

thf('122',plain,(
    ! [X33: $i] :
      ( ( k2_zfmisc_1 @ X33 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['79'])).

thf('123',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ( v4_relat_1 @ X61 @ X62 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X63 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('124',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
      | ( v4_relat_1 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D )
        = ( k1_tarski @ sk_A ) )
      | ( v4_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['121','124'])).

thf('126',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( v4_relat_1 @ X44 @ X45 )
      | ( r1_tarski @ ( k1_relat_1 @ X44 ) @ X45 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D )
        = ( k1_tarski @ sk_A ) )
      | ~ ( v1_relat_1 @ sk_D )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['125','126'])).

thf('128',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['25','26'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D )
        = ( k1_tarski @ sk_A ) )
      | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ),
    inference(demod,[status(thm)],['127','128'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D )
        = ( k1_tarski @ sk_A ) )
      | ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r1_tarski @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D )
        = ( k1_tarski @ sk_A ) )
      | ( r1_tarski @ sk_D @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['131','132'])).

thf('134',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D )
        = ( k1_tarski @ sk_A ) )
      | ~ ( r1_tarski @ ( k2_zfmisc_1 @ X0 @ sk_B ) @ sk_D )
      | ( ( k2_zfmisc_1 @ X0 @ sk_B )
        = sk_D ) ) ),
    inference('sup-',[status(thm)],['133','134'])).

thf('136',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_B )
      = sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['118','135'])).

thf('137',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('138',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k2_zfmisc_1 @ sk_D @ sk_B )
      = sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['136','137'])).

thf('139',plain,
    ( ( ( k2_zfmisc_1 @ sk_D @ sk_B )
      = sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D )
        = ( k1_tarski @ sk_A ) )
      | ( ( k2_zfmisc_1 @ sk_D @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['116','117'])).

thf('141',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('142',plain,(
    ! [X74: $i,X75: $i,X76: $i,X77: $i] :
      ( ~ ( m1_subset_1 @ X74 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X75 @ X76 ) ) )
      | ( ( k7_relset_1 @ X75 @ X76 @ X74 @ X77 )
        = ( k9_relat_1 @ X74 @ X77 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('143',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relset_1 @ X1 @ X0 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 )
      = ( k9_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X2 ) ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relset_1 @ sk_D @ X1 @ k1_xboole_0 @ X0 )
        = ( k9_relat_1 @ ( k2_zfmisc_1 @ sk_D @ X1 ) @ X0 ) )
      | ( ( k1_relat_1 @ sk_D )
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['140','143'])).

thf('145',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('146',plain,(
    ! [X39: $i,X41: $i] :
      ( ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X41 ) )
      | ~ ( r1_tarski @ X39 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('147',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('148',plain,(
    ! [X74: $i,X75: $i,X76: $i,X77: $i] :
      ( ~ ( m1_subset_1 @ X74 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X75 @ X76 ) ) )
      | ( ( k7_relset_1 @ X75 @ X76 @ X74 @ X77 )
        = ( k9_relat_1 @ X74 @ X77 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('149',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k9_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('151',plain,(
    ! [X61: $i,X62: $i,X63: $i] :
      ( ( v4_relat_1 @ X61 @ X62 )
      | ~ ( m1_subset_1 @ X61 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X62 @ X63 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('152',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('153',plain,(
    ! [X50: $i,X51: $i] :
      ( ( X50
        = ( k7_relat_1 @ X50 @ X51 ) )
      | ~ ( v4_relat_1 @ X50 @ X51 )
      | ~ ( v1_relat_1 @ X50 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('154',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['145','146'])).

thf('156',plain,(
    ! [X58: $i,X59: $i,X60: $i] :
      ( ( v1_relat_1 @ X58 )
      | ~ ( m1_subset_1 @ X58 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X59 @ X60 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('157',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['154','157'])).

thf('159',plain,(
    ! [X46: $i,X47: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X46 @ X47 ) )
        = ( k9_relat_1 @ X46 @ X47 ) )
      | ~ ( v1_relat_1 @ X46 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('160',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['158','159'])).

thf('161',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['150','151'])).

thf('162',plain,(
    ! [X44: $i,X45: $i] :
      ( ~ ( v4_relat_1 @ X44 @ X45 )
      | ( r1_tarski @ ( k1_relat_1 @ X44 ) @ X45 )
      | ~ ( v1_relat_1 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('163',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['155','156'])).

thf('165',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['163','164'])).

thf('166',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf('167',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['165','166'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('168',plain,(
    ! [X55: $i] :
      ( ( ( k1_relat_1 @ X55 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X55 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X55 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('169',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['167','168'])).

thf('170',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['155','156'])).

thf('171',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['155','156'])).

thf('174',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['160','172','173'])).

thf('175',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['149','174'])).

thf('176',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k1_xboole_0
        = ( k9_relat_1 @ ( k2_zfmisc_1 @ sk_D @ X1 ) @ X0 ) )
      | ( ( k1_relat_1 @ sk_D )
        = ( k1_tarski @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['144','175'])).

thf('177',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0
        = ( k9_relat_1 @ sk_D @ X0 ) )
      | ( ( k1_relat_1 @ sk_D )
        = ( k1_tarski @ sk_A ) )
      | ( ( k1_relat_1 @ sk_D )
        = ( k1_tarski @ sk_A ) ) ) ),
    inference('sup+',[status(thm)],['139','176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D )
        = ( k1_tarski @ sk_A ) )
      | ( k1_xboole_0
        = ( k9_relat_1 @ sk_D @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('180',plain,
    ( ~ ( r1_tarski @ k1_xboole_0 @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('182',plain,
    ( ( k1_relat_1 @ sk_D )
    = ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['180','181'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('183',plain,(
    ! [X56: $i,X57: $i] :
      ( ( ( k1_relat_1 @ X57 )
       != ( k1_tarski @ X56 ) )
      | ( ( k2_relat_1 @ X57 )
        = ( k1_tarski @ ( k1_funct_1 @ X57 @ X56 ) ) )
      | ~ ( v1_funct_1 @ X57 )
      | ~ ( v1_relat_1 @ X57 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference(eq_res,[status(thm)],['184'])).

thf('186',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['25','26'])).

thf('188',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ),
    inference(demod,[status(thm)],['185','186','187'])).

thf('189',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['14'])).

thf('190',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,(
    ! [X82: $i,X83: $i,X84: $i,X85: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ X82 ) @ X83 )
      | ( m1_subset_1 @ X82 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X84 @ X83 ) ) )
      | ~ ( m1_subset_1 @ X82 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X84 @ X85 ) ) ) ) ),
    inference(cnf,[status(esa)],[t14_relset_1])).

thf('192',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ X0 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['189','192'])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('194',plain,(
    ! [X67: $i,X68: $i,X69: $i,X70: $i] :
      ( ~ ( m1_subset_1 @ X67 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X68 @ X69 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X68 @ X69 @ X67 @ X70 ) @ ( k1_zfmisc_1 @ X69 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('195',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_D ) @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['193','194'])).

thf('196',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['189','192'])).

thf('197',plain,(
    ! [X74: $i,X75: $i,X76: $i,X77: $i] :
      ( ~ ( m1_subset_1 @ X74 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X75 @ X76 ) ) )
      | ( ( k7_relset_1 @ X75 @ X76 @ X74 @ X77 )
        = ( k9_relat_1 @ X74 @ X77 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ ( k2_relat_1 @ sk_D ) @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['196','197'])).

thf('199',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k9_relat_1 @ sk_D @ X0 ) @ ( k1_zfmisc_1 @ ( k2_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['195','198'])).

thf('200',plain,(
    ! [X39: $i,X40: $i] :
      ( ( r1_tarski @ X39 @ X40 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('201',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['199','200'])).

thf('202',plain,(
    $false ),
    inference(demod,[status(thm)],['4','188','201'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.icLeLG3BKi
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:29:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 3.25/3.44  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 3.25/3.44  % Solved by: fo/fo7.sh
% 3.25/3.44  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 3.25/3.44  % done 7678 iterations in 2.981s
% 3.25/3.44  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 3.25/3.44  % SZS output start Refutation
% 3.25/3.44  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 3.25/3.44  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 3.25/3.44  thf(sk_A_type, type, sk_A: $i).
% 3.25/3.44  thf(k11_relat_1_type, type, k11_relat_1: $i > $i > $i).
% 3.25/3.44  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 3.25/3.44  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 3.25/3.44  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 3.25/3.44  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 3.25/3.44  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 3.25/3.44  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 3.25/3.44  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 3.25/3.44  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 3.25/3.44  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 3.25/3.44  thf(sk_C_type, type, sk_C: $i).
% 3.25/3.44  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 3.25/3.44  thf(sk_D_type, type, sk_D: $i).
% 3.25/3.44  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 3.25/3.44  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 3.25/3.44  thf(sk_B_type, type, sk_B: $i).
% 3.25/3.44  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 3.25/3.44  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 3.25/3.44  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 3.25/3.44  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 3.25/3.44  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 3.25/3.44  thf(t64_funct_2, conjecture,
% 3.25/3.44    (![A:$i,B:$i,C:$i,D:$i]:
% 3.25/3.44     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 3.25/3.44         ( m1_subset_1 @
% 3.25/3.44           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 3.25/3.44       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 3.25/3.44         ( r1_tarski @
% 3.25/3.44           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 3.25/3.44           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 3.25/3.44  thf(zf_stmt_0, negated_conjecture,
% 3.25/3.44    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 3.25/3.44        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 3.25/3.44            ( m1_subset_1 @
% 3.25/3.44              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 3.25/3.44          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 3.25/3.44            ( r1_tarski @
% 3.25/3.44              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 3.25/3.44              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 3.25/3.44    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 3.25/3.44  thf('0', plain,
% 3.25/3.44      (~ (r1_tarski @ 
% 3.25/3.44          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 3.25/3.44          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 3.25/3.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.44  thf('1', plain,
% 3.25/3.44      ((m1_subset_1 @ sk_D @ 
% 3.25/3.44        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 3.25/3.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.44  thf(redefinition_k7_relset_1, axiom,
% 3.25/3.44    (![A:$i,B:$i,C:$i,D:$i]:
% 3.25/3.44     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.25/3.44       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 3.25/3.44  thf('2', plain,
% 3.25/3.44      (![X74 : $i, X75 : $i, X76 : $i, X77 : $i]:
% 3.25/3.44         (~ (m1_subset_1 @ X74 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X75 @ X76)))
% 3.25/3.44          | ((k7_relset_1 @ X75 @ X76 @ X74 @ X77) = (k9_relat_1 @ X74 @ X77)))),
% 3.25/3.44      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 3.25/3.44  thf('3', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 3.25/3.44           = (k9_relat_1 @ sk_D @ X0))),
% 3.25/3.44      inference('sup-', [status(thm)], ['1', '2'])).
% 3.25/3.44  thf('4', plain,
% 3.25/3.44      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 3.25/3.44          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 3.25/3.44      inference('demod', [status(thm)], ['0', '3'])).
% 3.25/3.44  thf(t69_enumset1, axiom,
% 3.25/3.44    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 3.25/3.44  thf('5', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 3.25/3.44      inference('cnf', [status(esa)], [t69_enumset1])).
% 3.25/3.44  thf(t205_relat_1, axiom,
% 3.25/3.44    (![A:$i,B:$i]:
% 3.25/3.44     ( ( v1_relat_1 @ B ) =>
% 3.25/3.44       ( ( r2_hidden @ A @ ( k1_relat_1 @ B ) ) <=>
% 3.25/3.44         ( ( k11_relat_1 @ B @ A ) != ( k1_xboole_0 ) ) ) ))).
% 3.25/3.44  thf('6', plain,
% 3.25/3.44      (![X48 : $i, X49 : $i]:
% 3.25/3.44         (((k11_relat_1 @ X48 @ X49) = (k1_xboole_0))
% 3.25/3.44          | (r2_hidden @ X49 @ (k1_relat_1 @ X48))
% 3.25/3.44          | ~ (v1_relat_1 @ X48))),
% 3.25/3.44      inference('cnf', [status(esa)], [t205_relat_1])).
% 3.25/3.44  thf('7', plain,
% 3.25/3.44      (![X48 : $i, X49 : $i]:
% 3.25/3.44         (((k11_relat_1 @ X48 @ X49) = (k1_xboole_0))
% 3.25/3.44          | (r2_hidden @ X49 @ (k1_relat_1 @ X48))
% 3.25/3.44          | ~ (v1_relat_1 @ X48))),
% 3.25/3.44      inference('cnf', [status(esa)], [t205_relat_1])).
% 3.25/3.44  thf(t38_zfmisc_1, axiom,
% 3.25/3.44    (![A:$i,B:$i,C:$i]:
% 3.25/3.44     ( ( r1_tarski @ ( k2_tarski @ A @ B ) @ C ) <=>
% 3.25/3.44       ( ( r2_hidden @ A @ C ) & ( r2_hidden @ B @ C ) ) ))).
% 3.25/3.44  thf('8', plain,
% 3.25/3.44      (![X35 : $i, X37 : $i, X38 : $i]:
% 3.25/3.44         ((r1_tarski @ (k2_tarski @ X35 @ X37) @ X38)
% 3.25/3.44          | ~ (r2_hidden @ X37 @ X38)
% 3.25/3.44          | ~ (r2_hidden @ X35 @ X38))),
% 3.25/3.44      inference('cnf', [status(esa)], [t38_zfmisc_1])).
% 3.25/3.44  thf('9', plain,
% 3.25/3.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.25/3.44         (~ (v1_relat_1 @ X0)
% 3.25/3.44          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 3.25/3.44          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ X0))
% 3.25/3.44          | (r1_tarski @ (k2_tarski @ X2 @ X1) @ (k1_relat_1 @ X0)))),
% 3.25/3.44      inference('sup-', [status(thm)], ['7', '8'])).
% 3.25/3.44  thf('10', plain,
% 3.25/3.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.25/3.44         (~ (v1_relat_1 @ X0)
% 3.25/3.44          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 3.25/3.44          | (r1_tarski @ (k2_tarski @ X1 @ X2) @ (k1_relat_1 @ X0))
% 3.25/3.44          | ((k11_relat_1 @ X0 @ X2) = (k1_xboole_0))
% 3.25/3.44          | ~ (v1_relat_1 @ X0))),
% 3.25/3.44      inference('sup-', [status(thm)], ['6', '9'])).
% 3.25/3.44  thf('11', plain,
% 3.25/3.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.25/3.44         (((k11_relat_1 @ X0 @ X2) = (k1_xboole_0))
% 3.25/3.44          | (r1_tarski @ (k2_tarski @ X1 @ X2) @ (k1_relat_1 @ X0))
% 3.25/3.44          | ((k11_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 3.25/3.44          | ~ (v1_relat_1 @ X0))),
% 3.25/3.44      inference('simplify', [status(thm)], ['10'])).
% 3.25/3.44  thf('12', plain,
% 3.25/3.44      (![X0 : $i, X1 : $i]:
% 3.25/3.44         ((r1_tarski @ (k1_tarski @ X0) @ (k1_relat_1 @ X1))
% 3.25/3.44          | ~ (v1_relat_1 @ X1)
% 3.25/3.44          | ((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 3.25/3.44          | ((k11_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 3.25/3.44      inference('sup+', [status(thm)], ['5', '11'])).
% 3.25/3.44  thf('13', plain,
% 3.25/3.44      (![X0 : $i, X1 : $i]:
% 3.25/3.44         (((k11_relat_1 @ X1 @ X0) = (k1_xboole_0))
% 3.25/3.44          | ~ (v1_relat_1 @ X1)
% 3.25/3.44          | (r1_tarski @ (k1_tarski @ X0) @ (k1_relat_1 @ X1)))),
% 3.25/3.44      inference('simplify', [status(thm)], ['12'])).
% 3.25/3.44  thf(d10_xboole_0, axiom,
% 3.25/3.44    (![A:$i,B:$i]:
% 3.25/3.44     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 3.25/3.44  thf('14', plain,
% 3.25/3.44      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 3.25/3.44      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.25/3.44  thf('15', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.25/3.44      inference('simplify', [status(thm)], ['14'])).
% 3.25/3.44  thf(t3_subset, axiom,
% 3.25/3.44    (![A:$i,B:$i]:
% 3.25/3.44     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 3.25/3.44  thf('16', plain,
% 3.25/3.44      (![X39 : $i, X41 : $i]:
% 3.25/3.44         ((m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X41)) | ~ (r1_tarski @ X39 @ X41))),
% 3.25/3.44      inference('cnf', [status(esa)], [t3_subset])).
% 3.25/3.44  thf('17', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 3.25/3.44      inference('sup-', [status(thm)], ['15', '16'])).
% 3.25/3.44  thf(cc2_relset_1, axiom,
% 3.25/3.44    (![A:$i,B:$i,C:$i]:
% 3.25/3.44     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.25/3.44       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 3.25/3.44  thf('18', plain,
% 3.25/3.44      (![X61 : $i, X62 : $i, X63 : $i]:
% 3.25/3.44         ((v4_relat_1 @ X61 @ X62)
% 3.25/3.44          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X63))))),
% 3.25/3.44      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.25/3.44  thf('19', plain,
% 3.25/3.44      (![X0 : $i, X1 : $i]: (v4_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X1)),
% 3.25/3.44      inference('sup-', [status(thm)], ['17', '18'])).
% 3.25/3.44  thf('20', plain,
% 3.25/3.44      ((m1_subset_1 @ sk_D @ 
% 3.25/3.44        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 3.25/3.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.44  thf('21', plain,
% 3.25/3.44      (![X61 : $i, X62 : $i, X63 : $i]:
% 3.25/3.44         ((v4_relat_1 @ X61 @ X62)
% 3.25/3.44          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X63))))),
% 3.25/3.44      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.25/3.44  thf('22', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 3.25/3.44      inference('sup-', [status(thm)], ['20', '21'])).
% 3.25/3.44  thf(d18_relat_1, axiom,
% 3.25/3.44    (![A:$i,B:$i]:
% 3.25/3.44     ( ( v1_relat_1 @ B ) =>
% 3.25/3.44       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 3.25/3.44  thf('23', plain,
% 3.25/3.44      (![X44 : $i, X45 : $i]:
% 3.25/3.44         (~ (v4_relat_1 @ X44 @ X45)
% 3.25/3.44          | (r1_tarski @ (k1_relat_1 @ X44) @ X45)
% 3.25/3.44          | ~ (v1_relat_1 @ X44))),
% 3.25/3.44      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.25/3.44  thf('24', plain,
% 3.25/3.44      ((~ (v1_relat_1 @ sk_D)
% 3.25/3.44        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 3.25/3.44      inference('sup-', [status(thm)], ['22', '23'])).
% 3.25/3.44  thf('25', plain,
% 3.25/3.44      ((m1_subset_1 @ sk_D @ 
% 3.25/3.44        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 3.25/3.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.44  thf(cc1_relset_1, axiom,
% 3.25/3.44    (![A:$i,B:$i,C:$i]:
% 3.25/3.44     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.25/3.44       ( v1_relat_1 @ C ) ))).
% 3.25/3.44  thf('26', plain,
% 3.25/3.44      (![X58 : $i, X59 : $i, X60 : $i]:
% 3.25/3.44         ((v1_relat_1 @ X58)
% 3.25/3.44          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X60))))),
% 3.25/3.44      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.25/3.44  thf('27', plain, ((v1_relat_1 @ sk_D)),
% 3.25/3.44      inference('sup-', [status(thm)], ['25', '26'])).
% 3.25/3.44  thf('28', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 3.25/3.44      inference('demod', [status(thm)], ['24', '27'])).
% 3.25/3.44  thf(t217_relat_1, axiom,
% 3.25/3.44    (![A:$i,B:$i]:
% 3.25/3.44     ( ( r1_tarski @ A @ B ) =>
% 3.25/3.44       ( ![C:$i]:
% 3.25/3.44         ( ( ( v1_relat_1 @ C ) & ( v4_relat_1 @ C @ A ) ) =>
% 3.25/3.44           ( v4_relat_1 @ C @ B ) ) ) ))).
% 3.25/3.44  thf('29', plain,
% 3.25/3.44      (![X52 : $i, X53 : $i, X54 : $i]:
% 3.25/3.44         (~ (v1_relat_1 @ X52)
% 3.25/3.44          | ~ (v4_relat_1 @ X52 @ X53)
% 3.25/3.44          | (v4_relat_1 @ X52 @ X54)
% 3.25/3.44          | ~ (r1_tarski @ X53 @ X54))),
% 3.25/3.44      inference('cnf', [status(esa)], [t217_relat_1])).
% 3.25/3.44  thf('30', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         ((v4_relat_1 @ X0 @ (k1_tarski @ sk_A))
% 3.25/3.44          | ~ (v4_relat_1 @ X0 @ (k1_relat_1 @ sk_D))
% 3.25/3.44          | ~ (v1_relat_1 @ X0))),
% 3.25/3.44      inference('sup-', [status(thm)], ['28', '29'])).
% 3.25/3.44  thf('31', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0))
% 3.25/3.44          | (v4_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0) @ 
% 3.25/3.44             (k1_tarski @ sk_A)))),
% 3.25/3.44      inference('sup-', [status(thm)], ['19', '30'])).
% 3.25/3.44  thf('32', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 3.25/3.44      inference('sup-', [status(thm)], ['15', '16'])).
% 3.25/3.44  thf('33', plain,
% 3.25/3.44      (![X58 : $i, X59 : $i, X60 : $i]:
% 3.25/3.44         ((v1_relat_1 @ X58)
% 3.25/3.44          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X60))))),
% 3.25/3.44      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.25/3.44  thf('34', plain,
% 3.25/3.44      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))),
% 3.25/3.44      inference('sup-', [status(thm)], ['32', '33'])).
% 3.25/3.44  thf('35', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (v4_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0) @ 
% 3.25/3.44          (k1_tarski @ sk_A))),
% 3.25/3.44      inference('demod', [status(thm)], ['31', '34'])).
% 3.25/3.44  thf('36', plain,
% 3.25/3.44      (![X44 : $i, X45 : $i]:
% 3.25/3.44         (~ (v4_relat_1 @ X44 @ X45)
% 3.25/3.44          | (r1_tarski @ (k1_relat_1 @ X44) @ X45)
% 3.25/3.44          | ~ (v1_relat_1 @ X44))),
% 3.25/3.44      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.25/3.44  thf('37', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0))
% 3.25/3.44          | (r1_tarski @ 
% 3.25/3.44             (k1_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0)) @ 
% 3.25/3.44             (k1_tarski @ sk_A)))),
% 3.25/3.44      inference('sup-', [status(thm)], ['35', '36'])).
% 3.25/3.44  thf('38', plain,
% 3.25/3.44      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))),
% 3.25/3.44      inference('sup-', [status(thm)], ['32', '33'])).
% 3.25/3.44  thf('39', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (r1_tarski @ 
% 3.25/3.44          (k1_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0)) @ 
% 3.25/3.44          (k1_tarski @ sk_A))),
% 3.25/3.44      inference('demod', [status(thm)], ['37', '38'])).
% 3.25/3.44  thf('40', plain,
% 3.25/3.44      (![X0 : $i, X2 : $i]:
% 3.25/3.44         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.25/3.44      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.25/3.44  thf('41', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (~ (r1_tarski @ (k1_tarski @ sk_A) @ 
% 3.25/3.44             (k1_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0)))
% 3.25/3.44          | ((k1_tarski @ sk_A)
% 3.25/3.44              = (k1_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0))))),
% 3.25/3.44      inference('sup-', [status(thm)], ['39', '40'])).
% 3.25/3.44  thf('42', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0))
% 3.25/3.44          | ((k11_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0) @ sk_A)
% 3.25/3.44              = (k1_xboole_0))
% 3.25/3.44          | ((k1_tarski @ sk_A)
% 3.25/3.44              = (k1_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0))))),
% 3.25/3.44      inference('sup-', [status(thm)], ['13', '41'])).
% 3.25/3.44  thf('43', plain,
% 3.25/3.44      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))),
% 3.25/3.44      inference('sup-', [status(thm)], ['32', '33'])).
% 3.25/3.44  thf(d16_relat_1, axiom,
% 3.25/3.44    (![A:$i]:
% 3.25/3.44     ( ( v1_relat_1 @ A ) =>
% 3.25/3.44       ( ![B:$i]:
% 3.25/3.44         ( ( k11_relat_1 @ A @ B ) = ( k9_relat_1 @ A @ ( k1_tarski @ B ) ) ) ) ))).
% 3.25/3.44  thf('44', plain,
% 3.25/3.44      (![X42 : $i, X43 : $i]:
% 3.25/3.44         (((k11_relat_1 @ X42 @ X43) = (k9_relat_1 @ X42 @ (k1_tarski @ X43)))
% 3.25/3.44          | ~ (v1_relat_1 @ X42))),
% 3.25/3.44      inference('cnf', [status(esa)], [d16_relat_1])).
% 3.25/3.44  thf('45', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (v4_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0) @ 
% 3.25/3.44          (k1_tarski @ sk_A))),
% 3.25/3.44      inference('demod', [status(thm)], ['31', '34'])).
% 3.25/3.44  thf(t209_relat_1, axiom,
% 3.25/3.44    (![A:$i,B:$i]:
% 3.25/3.44     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 3.25/3.44       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 3.25/3.44  thf('46', plain,
% 3.25/3.44      (![X50 : $i, X51 : $i]:
% 3.25/3.44         (((X50) = (k7_relat_1 @ X50 @ X51))
% 3.25/3.44          | ~ (v4_relat_1 @ X50 @ X51)
% 3.25/3.44          | ~ (v1_relat_1 @ X50))),
% 3.25/3.44      inference('cnf', [status(esa)], [t209_relat_1])).
% 3.25/3.44  thf('47', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0))
% 3.25/3.44          | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0)
% 3.25/3.44              = (k7_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0) @ 
% 3.25/3.44                 (k1_tarski @ sk_A))))),
% 3.25/3.44      inference('sup-', [status(thm)], ['45', '46'])).
% 3.25/3.44  thf('48', plain,
% 3.25/3.44      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))),
% 3.25/3.44      inference('sup-', [status(thm)], ['32', '33'])).
% 3.25/3.44  thf('49', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         ((k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0)
% 3.25/3.44           = (k7_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0) @ 
% 3.25/3.44              (k1_tarski @ sk_A)))),
% 3.25/3.44      inference('demod', [status(thm)], ['47', '48'])).
% 3.25/3.44  thf(t148_relat_1, axiom,
% 3.25/3.44    (![A:$i,B:$i]:
% 3.25/3.44     ( ( v1_relat_1 @ B ) =>
% 3.25/3.44       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 3.25/3.44  thf('50', plain,
% 3.25/3.44      (![X46 : $i, X47 : $i]:
% 3.25/3.44         (((k2_relat_1 @ (k7_relat_1 @ X46 @ X47)) = (k9_relat_1 @ X46 @ X47))
% 3.25/3.44          | ~ (v1_relat_1 @ X46))),
% 3.25/3.44      inference('cnf', [status(esa)], [t148_relat_1])).
% 3.25/3.44  thf('51', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (((k2_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0))
% 3.25/3.44            = (k9_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0) @ 
% 3.25/3.44               (k1_tarski @ sk_A)))
% 3.25/3.44          | ~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0)))),
% 3.25/3.44      inference('sup+', [status(thm)], ['49', '50'])).
% 3.25/3.44  thf('52', plain,
% 3.25/3.44      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))),
% 3.25/3.44      inference('sup-', [status(thm)], ['32', '33'])).
% 3.25/3.44  thf('53', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         ((k2_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0))
% 3.25/3.44           = (k9_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0) @ 
% 3.25/3.44              (k1_tarski @ sk_A)))),
% 3.25/3.44      inference('demod', [status(thm)], ['51', '52'])).
% 3.25/3.44  thf('54', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (((k2_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0))
% 3.25/3.44            = (k11_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0) @ sk_A))
% 3.25/3.44          | ~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0)))),
% 3.25/3.44      inference('sup+', [status(thm)], ['44', '53'])).
% 3.25/3.44  thf('55', plain,
% 3.25/3.44      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))),
% 3.25/3.44      inference('sup-', [status(thm)], ['32', '33'])).
% 3.25/3.44  thf('56', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         ((k2_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0))
% 3.25/3.44           = (k11_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0) @ sk_A))),
% 3.25/3.44      inference('demod', [status(thm)], ['54', '55'])).
% 3.25/3.44  thf('57', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (((k2_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0))
% 3.25/3.44            = (k1_xboole_0))
% 3.25/3.44          | ((k1_tarski @ sk_A)
% 3.25/3.44              = (k1_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0))))),
% 3.25/3.44      inference('demod', [status(thm)], ['42', '43', '56'])).
% 3.25/3.44  thf('58', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (((k2_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0))
% 3.25/3.44            = (k1_xboole_0))
% 3.25/3.44          | ((k1_tarski @ sk_A)
% 3.25/3.44              = (k1_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0))))),
% 3.25/3.44      inference('demod', [status(thm)], ['42', '43', '56'])).
% 3.25/3.44  thf('59', plain,
% 3.25/3.44      (![X0 : $i, X1 : $i]: (v4_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X1)),
% 3.25/3.44      inference('sup-', [status(thm)], ['17', '18'])).
% 3.25/3.44  thf('60', plain,
% 3.25/3.44      (![X44 : $i, X45 : $i]:
% 3.25/3.44         (~ (v4_relat_1 @ X44 @ X45)
% 3.25/3.44          | (r1_tarski @ (k1_relat_1 @ X44) @ X45)
% 3.25/3.44          | ~ (v1_relat_1 @ X44))),
% 3.25/3.44      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.25/3.44  thf('61', plain,
% 3.25/3.44      (![X0 : $i, X1 : $i]:
% 3.25/3.44         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))
% 3.25/3.44          | (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0))),
% 3.25/3.44      inference('sup-', [status(thm)], ['59', '60'])).
% 3.25/3.44  thf('62', plain,
% 3.25/3.44      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))),
% 3.25/3.44      inference('sup-', [status(thm)], ['32', '33'])).
% 3.25/3.44  thf('63', plain,
% 3.25/3.44      (![X0 : $i, X1 : $i]:
% 3.25/3.44         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0)),
% 3.25/3.44      inference('demod', [status(thm)], ['61', '62'])).
% 3.25/3.44  thf('64', plain,
% 3.25/3.44      (![X0 : $i, X2 : $i]:
% 3.25/3.44         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.25/3.44      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.25/3.44  thf('65', plain,
% 3.25/3.44      (![X0 : $i, X1 : $i]:
% 3.25/3.44         (~ (r1_tarski @ X0 @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)))
% 3.25/3.44          | ((X0) = (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 3.25/3.44      inference('sup-', [status(thm)], ['63', '64'])).
% 3.25/3.44  thf('66', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (~ (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))
% 3.25/3.44          | ((k2_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0))
% 3.25/3.44              = (k1_xboole_0))
% 3.25/3.44          | ((k1_relat_1 @ sk_D)
% 3.25/3.44              = (k1_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0))))),
% 3.25/3.44      inference('sup-', [status(thm)], ['58', '65'])).
% 3.25/3.44  thf('67', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 3.25/3.44      inference('demod', [status(thm)], ['24', '27'])).
% 3.25/3.44  thf('68', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (((k2_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0))
% 3.25/3.44            = (k1_xboole_0))
% 3.25/3.44          | ((k1_relat_1 @ sk_D)
% 3.25/3.44              = (k1_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0))))),
% 3.25/3.44      inference('demod', [status(thm)], ['66', '67'])).
% 3.25/3.44  thf('69', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 3.25/3.44          | ((k2_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0))
% 3.25/3.44              = (k1_xboole_0))
% 3.25/3.44          | ((k2_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0))
% 3.25/3.44              = (k1_xboole_0)))),
% 3.25/3.44      inference('sup+', [status(thm)], ['57', '68'])).
% 3.25/3.44  thf('70', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (((k2_relat_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0))
% 3.25/3.44            = (k1_xboole_0))
% 3.25/3.44          | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 3.25/3.44      inference('simplify', [status(thm)], ['69'])).
% 3.25/3.44  thf('71', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.25/3.44      inference('simplify', [status(thm)], ['14'])).
% 3.25/3.44  thf('72', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 3.25/3.44      inference('sup-', [status(thm)], ['15', '16'])).
% 3.25/3.44  thf(t14_relset_1, axiom,
% 3.25/3.44    (![A:$i,B:$i,C:$i,D:$i]:
% 3.25/3.44     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) =>
% 3.25/3.44       ( ( r1_tarski @ ( k2_relat_1 @ D ) @ B ) =>
% 3.25/3.44         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) ))).
% 3.25/3.44  thf('73', plain,
% 3.25/3.44      (![X82 : $i, X83 : $i, X84 : $i, X85 : $i]:
% 3.25/3.44         (~ (r1_tarski @ (k2_relat_1 @ X82) @ X83)
% 3.25/3.44          | (m1_subset_1 @ X82 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X84 @ X83)))
% 3.25/3.44          | ~ (m1_subset_1 @ X82 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X84 @ X85))))),
% 3.25/3.44      inference('cnf', [status(esa)], [t14_relset_1])).
% 3.25/3.44  thf('74', plain,
% 3.25/3.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.25/3.44         ((m1_subset_1 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 3.25/3.44           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ X2)))
% 3.25/3.44          | ~ (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X2))),
% 3.25/3.44      inference('sup-', [status(thm)], ['72', '73'])).
% 3.25/3.44  thf('75', plain,
% 3.25/3.44      (![X0 : $i, X1 : $i]:
% 3.25/3.44         (m1_subset_1 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 3.25/3.44          (k1_zfmisc_1 @ 
% 3.25/3.44           (k2_zfmisc_1 @ X1 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)))))),
% 3.25/3.44      inference('sup-', [status(thm)], ['71', '74'])).
% 3.25/3.44  thf('76', plain,
% 3.25/3.44      (![X39 : $i, X40 : $i]:
% 3.25/3.44         ((r1_tarski @ X39 @ X40) | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40)))),
% 3.25/3.44      inference('cnf', [status(esa)], [t3_subset])).
% 3.25/3.44  thf('77', plain,
% 3.25/3.44      (![X0 : $i, X1 : $i]:
% 3.25/3.44         (r1_tarski @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 3.25/3.44          (k2_zfmisc_1 @ X1 @ (k2_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))))),
% 3.25/3.44      inference('sup-', [status(thm)], ['75', '76'])).
% 3.25/3.44  thf('78', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         ((r1_tarski @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0) @ 
% 3.25/3.44           (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ k1_xboole_0))
% 3.25/3.44          | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 3.25/3.44      inference('sup+', [status(thm)], ['70', '77'])).
% 3.25/3.44  thf(t113_zfmisc_1, axiom,
% 3.25/3.44    (![A:$i,B:$i]:
% 3.25/3.44     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 3.25/3.44       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 3.25/3.44  thf('79', plain,
% 3.25/3.44      (![X33 : $i, X34 : $i]:
% 3.25/3.44         (((k2_zfmisc_1 @ X33 @ X34) = (k1_xboole_0))
% 3.25/3.44          | ((X34) != (k1_xboole_0)))),
% 3.25/3.44      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.25/3.44  thf('80', plain,
% 3.25/3.44      (![X33 : $i]: ((k2_zfmisc_1 @ X33 @ k1_xboole_0) = (k1_xboole_0))),
% 3.25/3.44      inference('simplify', [status(thm)], ['79'])).
% 3.25/3.44  thf('81', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         ((r1_tarski @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0) @ k1_xboole_0)
% 3.25/3.44          | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 3.25/3.44      inference('demod', [status(thm)], ['78', '80'])).
% 3.25/3.44  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 3.25/3.44  thf('82', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 3.25/3.44      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.25/3.44  thf('83', plain,
% 3.25/3.44      (![X0 : $i, X2 : $i]:
% 3.25/3.44         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.25/3.44      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.25/3.44  thf('84', plain,
% 3.25/3.44      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 3.25/3.44      inference('sup-', [status(thm)], ['82', '83'])).
% 3.25/3.44  thf('85', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 3.25/3.44          | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0) = (k1_xboole_0)))),
% 3.25/3.44      inference('sup-', [status(thm)], ['81', '84'])).
% 3.25/3.44  thf('86', plain,
% 3.25/3.44      (![X0 : $i, X1 : $i]: (v4_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X1)),
% 3.25/3.44      inference('sup-', [status(thm)], ['17', '18'])).
% 3.25/3.44  thf('87', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.25/3.44      inference('simplify', [status(thm)], ['14'])).
% 3.25/3.44  thf('88', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.25/3.44      inference('simplify', [status(thm)], ['14'])).
% 3.25/3.44  thf('89', plain,
% 3.25/3.44      ((m1_subset_1 @ sk_D @ 
% 3.25/3.44        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 3.25/3.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.44  thf(t13_relset_1, axiom,
% 3.25/3.44    (![A:$i,B:$i,C:$i,D:$i]:
% 3.25/3.44     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 3.25/3.44       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 3.25/3.44         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 3.25/3.44  thf('90', plain,
% 3.25/3.44      (![X78 : $i, X79 : $i, X80 : $i, X81 : $i]:
% 3.25/3.44         (~ (r1_tarski @ (k1_relat_1 @ X78) @ X79)
% 3.25/3.44          | (m1_subset_1 @ X78 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X79 @ X80)))
% 3.25/3.44          | ~ (m1_subset_1 @ X78 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X81 @ X80))))),
% 3.25/3.44      inference('cnf', [status(esa)], [t13_relset_1])).
% 3.25/3.44  thf('91', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 3.25/3.44          | ~ (r1_tarski @ (k1_relat_1 @ sk_D) @ X0))),
% 3.25/3.44      inference('sup-', [status(thm)], ['89', '90'])).
% 3.25/3.44  thf('92', plain,
% 3.25/3.44      ((m1_subset_1 @ sk_D @ 
% 3.25/3.44        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ sk_B)))),
% 3.25/3.44      inference('sup-', [status(thm)], ['88', '91'])).
% 3.25/3.44  thf('93', plain,
% 3.25/3.44      (![X82 : $i, X83 : $i, X84 : $i, X85 : $i]:
% 3.25/3.44         (~ (r1_tarski @ (k2_relat_1 @ X82) @ X83)
% 3.25/3.44          | (m1_subset_1 @ X82 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X84 @ X83)))
% 3.25/3.44          | ~ (m1_subset_1 @ X82 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X84 @ X85))))),
% 3.25/3.44      inference('cnf', [status(esa)], [t14_relset_1])).
% 3.25/3.44  thf('94', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         ((m1_subset_1 @ sk_D @ 
% 3.25/3.44           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0)))
% 3.25/3.44          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 3.25/3.44      inference('sup-', [status(thm)], ['92', '93'])).
% 3.25/3.44  thf('95', plain,
% 3.25/3.44      ((m1_subset_1 @ sk_D @ 
% 3.25/3.44        (k1_zfmisc_1 @ 
% 3.25/3.44         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D))))),
% 3.25/3.44      inference('sup-', [status(thm)], ['87', '94'])).
% 3.25/3.44  thf('96', plain,
% 3.25/3.44      (![X39 : $i, X40 : $i]:
% 3.25/3.44         ((r1_tarski @ X39 @ X40) | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40)))),
% 3.25/3.44      inference('cnf', [status(esa)], [t3_subset])).
% 3.25/3.44  thf('97', plain,
% 3.25/3.44      ((r1_tarski @ sk_D @ 
% 3.25/3.44        (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D)))),
% 3.25/3.44      inference('sup-', [status(thm)], ['95', '96'])).
% 3.25/3.44  thf('98', plain,
% 3.25/3.44      (![X52 : $i, X53 : $i, X54 : $i]:
% 3.25/3.44         (~ (v1_relat_1 @ X52)
% 3.25/3.44          | ~ (v4_relat_1 @ X52 @ X53)
% 3.25/3.44          | (v4_relat_1 @ X52 @ X54)
% 3.25/3.44          | ~ (r1_tarski @ X53 @ X54))),
% 3.25/3.44      inference('cnf', [status(esa)], [t217_relat_1])).
% 3.25/3.44  thf('99', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         ((v4_relat_1 @ X0 @ 
% 3.25/3.44           (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D)))
% 3.25/3.44          | ~ (v4_relat_1 @ X0 @ sk_D)
% 3.25/3.44          | ~ (v1_relat_1 @ X0))),
% 3.25/3.44      inference('sup-', [status(thm)], ['97', '98'])).
% 3.25/3.44  thf('100', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_D @ X0))
% 3.25/3.44          | (v4_relat_1 @ (k2_zfmisc_1 @ sk_D @ X0) @ 
% 3.25/3.44             (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D))))),
% 3.25/3.44      inference('sup-', [status(thm)], ['86', '99'])).
% 3.25/3.44  thf('101', plain,
% 3.25/3.44      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))),
% 3.25/3.44      inference('sup-', [status(thm)], ['32', '33'])).
% 3.25/3.44  thf('102', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (v4_relat_1 @ (k2_zfmisc_1 @ sk_D @ X0) @ 
% 3.25/3.44          (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D)))),
% 3.25/3.44      inference('demod', [status(thm)], ['100', '101'])).
% 3.25/3.44  thf('103', plain,
% 3.25/3.44      (![X44 : $i, X45 : $i]:
% 3.25/3.44         (~ (v4_relat_1 @ X44 @ X45)
% 3.25/3.44          | (r1_tarski @ (k1_relat_1 @ X44) @ X45)
% 3.25/3.44          | ~ (v1_relat_1 @ X44))),
% 3.25/3.44      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.25/3.44  thf('104', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_D @ X0))
% 3.25/3.44          | (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_D @ X0)) @ 
% 3.25/3.44             (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D))))),
% 3.25/3.44      inference('sup-', [status(thm)], ['102', '103'])).
% 3.25/3.44  thf('105', plain,
% 3.25/3.44      (![X0 : $i, X1 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0))),
% 3.25/3.44      inference('sup-', [status(thm)], ['32', '33'])).
% 3.25/3.44  thf('106', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ sk_D @ X0)) @ 
% 3.25/3.44          (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D)))),
% 3.25/3.44      inference('demod', [status(thm)], ['104', '105'])).
% 3.25/3.44  thf('107', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 3.25/3.44      inference('sup-', [status(thm)], ['15', '16'])).
% 3.25/3.44  thf('108', plain,
% 3.25/3.44      (![X78 : $i, X79 : $i, X80 : $i, X81 : $i]:
% 3.25/3.44         (~ (r1_tarski @ (k1_relat_1 @ X78) @ X79)
% 3.25/3.44          | (m1_subset_1 @ X78 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X79 @ X80)))
% 3.25/3.44          | ~ (m1_subset_1 @ X78 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X81 @ X80))))),
% 3.25/3.44      inference('cnf', [status(esa)], [t13_relset_1])).
% 3.25/3.44  thf('109', plain,
% 3.25/3.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.25/3.44         ((m1_subset_1 @ (k2_zfmisc_1 @ X1 @ X0) @ 
% 3.25/3.44           (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X0)))
% 3.25/3.44          | ~ (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X1 @ X0)) @ X2))),
% 3.25/3.44      inference('sup-', [status(thm)], ['107', '108'])).
% 3.25/3.44  thf('110', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (m1_subset_1 @ (k2_zfmisc_1 @ sk_D @ X0) @ 
% 3.25/3.44          (k1_zfmisc_1 @ 
% 3.25/3.44           (k2_zfmisc_1 @ 
% 3.25/3.44            (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D)) @ X0)))),
% 3.25/3.44      inference('sup-', [status(thm)], ['106', '109'])).
% 3.25/3.44  thf('111', plain,
% 3.25/3.44      (![X39 : $i, X40 : $i]:
% 3.25/3.44         ((r1_tarski @ X39 @ X40) | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40)))),
% 3.25/3.44      inference('cnf', [status(esa)], [t3_subset])).
% 3.25/3.44  thf('112', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (r1_tarski @ (k2_zfmisc_1 @ sk_D @ X0) @ 
% 3.25/3.44          (k2_zfmisc_1 @ 
% 3.25/3.44           (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D)) @ X0))),
% 3.25/3.44      inference('sup-', [status(thm)], ['110', '111'])).
% 3.25/3.44  thf('113', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         ((r1_tarski @ (k2_zfmisc_1 @ sk_D @ X0) @ 
% 3.25/3.44           (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 3.25/3.44          | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 3.25/3.44      inference('sup+', [status(thm)], ['85', '112'])).
% 3.25/3.44  thf('114', plain,
% 3.25/3.44      (![X33 : $i, X34 : $i]:
% 3.25/3.44         (((k2_zfmisc_1 @ X33 @ X34) = (k1_xboole_0))
% 3.25/3.44          | ((X33) != (k1_xboole_0)))),
% 3.25/3.44      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 3.25/3.44  thf('115', plain,
% 3.25/3.44      (![X34 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X34) = (k1_xboole_0))),
% 3.25/3.44      inference('simplify', [status(thm)], ['114'])).
% 3.25/3.44  thf('116', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         ((r1_tarski @ (k2_zfmisc_1 @ sk_D @ X0) @ k1_xboole_0)
% 3.25/3.44          | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 3.25/3.44      inference('demod', [status(thm)], ['113', '115'])).
% 3.25/3.44  thf('117', plain,
% 3.25/3.44      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 3.25/3.44      inference('sup-', [status(thm)], ['82', '83'])).
% 3.25/3.44  thf('118', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 3.25/3.44          | ((k2_zfmisc_1 @ sk_D @ X0) = (k1_xboole_0)))),
% 3.25/3.44      inference('sup-', [status(thm)], ['116', '117'])).
% 3.25/3.44  thf('119', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 3.25/3.44          | ((k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ X0) = (k1_xboole_0)))),
% 3.25/3.44      inference('sup-', [status(thm)], ['81', '84'])).
% 3.25/3.44  thf('120', plain,
% 3.25/3.44      ((m1_subset_1 @ sk_D @ 
% 3.25/3.44        (k1_zfmisc_1 @ 
% 3.25/3.44         (k2_zfmisc_1 @ (k1_relat_1 @ sk_D) @ (k2_relat_1 @ sk_D))))),
% 3.25/3.44      inference('sup-', [status(thm)], ['87', '94'])).
% 3.25/3.44  thf('121', plain,
% 3.25/3.44      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.25/3.44        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 3.25/3.44      inference('sup+', [status(thm)], ['119', '120'])).
% 3.25/3.44  thf('122', plain,
% 3.25/3.44      (![X33 : $i]: ((k2_zfmisc_1 @ X33 @ k1_xboole_0) = (k1_xboole_0))),
% 3.25/3.44      inference('simplify', [status(thm)], ['79'])).
% 3.25/3.44  thf('123', plain,
% 3.25/3.44      (![X61 : $i, X62 : $i, X63 : $i]:
% 3.25/3.44         ((v4_relat_1 @ X61 @ X62)
% 3.25/3.44          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X63))))),
% 3.25/3.44      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.25/3.44  thf('124', plain,
% 3.25/3.44      (![X0 : $i, X1 : $i]:
% 3.25/3.44         (~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ k1_xboole_0))
% 3.25/3.44          | (v4_relat_1 @ X1 @ X0))),
% 3.25/3.44      inference('sup-', [status(thm)], ['122', '123'])).
% 3.25/3.44  thf('125', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)) | (v4_relat_1 @ sk_D @ X0))),
% 3.25/3.44      inference('sup-', [status(thm)], ['121', '124'])).
% 3.25/3.44  thf('126', plain,
% 3.25/3.44      (![X44 : $i, X45 : $i]:
% 3.25/3.44         (~ (v4_relat_1 @ X44 @ X45)
% 3.25/3.44          | (r1_tarski @ (k1_relat_1 @ X44) @ X45)
% 3.25/3.44          | ~ (v1_relat_1 @ X44))),
% 3.25/3.44      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.25/3.44  thf('127', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 3.25/3.44          | ~ (v1_relat_1 @ sk_D)
% 3.25/3.44          | (r1_tarski @ (k1_relat_1 @ sk_D) @ X0))),
% 3.25/3.44      inference('sup-', [status(thm)], ['125', '126'])).
% 3.25/3.44  thf('128', plain, ((v1_relat_1 @ sk_D)),
% 3.25/3.44      inference('sup-', [status(thm)], ['25', '26'])).
% 3.25/3.44  thf('129', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 3.25/3.44          | (r1_tarski @ (k1_relat_1 @ sk_D) @ X0))),
% 3.25/3.44      inference('demod', [status(thm)], ['127', '128'])).
% 3.25/3.44  thf('130', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 3.25/3.44          | ~ (r1_tarski @ (k1_relat_1 @ sk_D) @ X0))),
% 3.25/3.44      inference('sup-', [status(thm)], ['89', '90'])).
% 3.25/3.44  thf('131', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 3.25/3.44          | (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B))))),
% 3.25/3.44      inference('sup-', [status(thm)], ['129', '130'])).
% 3.25/3.44  thf('132', plain,
% 3.25/3.44      (![X39 : $i, X40 : $i]:
% 3.25/3.44         ((r1_tarski @ X39 @ X40) | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40)))),
% 3.25/3.44      inference('cnf', [status(esa)], [t3_subset])).
% 3.25/3.44  thf('133', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 3.25/3.44          | (r1_tarski @ sk_D @ (k2_zfmisc_1 @ X0 @ sk_B)))),
% 3.25/3.44      inference('sup-', [status(thm)], ['131', '132'])).
% 3.25/3.44  thf('134', plain,
% 3.25/3.44      (![X0 : $i, X2 : $i]:
% 3.25/3.44         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 3.25/3.44      inference('cnf', [status(esa)], [d10_xboole_0])).
% 3.25/3.44  thf('135', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 3.25/3.44          | ~ (r1_tarski @ (k2_zfmisc_1 @ X0 @ sk_B) @ sk_D)
% 3.25/3.44          | ((k2_zfmisc_1 @ X0 @ sk_B) = (sk_D)))),
% 3.25/3.44      inference('sup-', [status(thm)], ['133', '134'])).
% 3.25/3.44  thf('136', plain,
% 3.25/3.44      ((~ (r1_tarski @ k1_xboole_0 @ sk_D)
% 3.25/3.44        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 3.25/3.44        | ((k2_zfmisc_1 @ sk_D @ sk_B) = (sk_D))
% 3.25/3.44        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 3.25/3.44      inference('sup-', [status(thm)], ['118', '135'])).
% 3.25/3.44  thf('137', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 3.25/3.44      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.25/3.44  thf('138', plain,
% 3.25/3.44      ((((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 3.25/3.44        | ((k2_zfmisc_1 @ sk_D @ sk_B) = (sk_D))
% 3.25/3.44        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 3.25/3.44      inference('demod', [status(thm)], ['136', '137'])).
% 3.25/3.44  thf('139', plain,
% 3.25/3.44      ((((k2_zfmisc_1 @ sk_D @ sk_B) = (sk_D))
% 3.25/3.44        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 3.25/3.44      inference('simplify', [status(thm)], ['138'])).
% 3.25/3.44  thf('140', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 3.25/3.44          | ((k2_zfmisc_1 @ sk_D @ X0) = (k1_xboole_0)))),
% 3.25/3.44      inference('sup-', [status(thm)], ['116', '117'])).
% 3.25/3.44  thf('141', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 3.25/3.44      inference('sup-', [status(thm)], ['15', '16'])).
% 3.25/3.44  thf('142', plain,
% 3.25/3.44      (![X74 : $i, X75 : $i, X76 : $i, X77 : $i]:
% 3.25/3.44         (~ (m1_subset_1 @ X74 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X75 @ X76)))
% 3.25/3.44          | ((k7_relset_1 @ X75 @ X76 @ X74 @ X77) = (k9_relat_1 @ X74 @ X77)))),
% 3.25/3.44      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 3.25/3.44  thf('143', plain,
% 3.25/3.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.25/3.44         ((k7_relset_1 @ X1 @ X0 @ (k2_zfmisc_1 @ X1 @ X0) @ X2)
% 3.25/3.44           = (k9_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X2))),
% 3.25/3.44      inference('sup-', [status(thm)], ['141', '142'])).
% 3.25/3.44  thf('144', plain,
% 3.25/3.44      (![X0 : $i, X1 : $i]:
% 3.25/3.44         (((k7_relset_1 @ sk_D @ X1 @ k1_xboole_0 @ X0)
% 3.25/3.44            = (k9_relat_1 @ (k2_zfmisc_1 @ sk_D @ X1) @ X0))
% 3.25/3.44          | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 3.25/3.44      inference('sup+', [status(thm)], ['140', '143'])).
% 3.25/3.44  thf('145', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 3.25/3.44      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.25/3.44  thf('146', plain,
% 3.25/3.44      (![X39 : $i, X41 : $i]:
% 3.25/3.44         ((m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X41)) | ~ (r1_tarski @ X39 @ X41))),
% 3.25/3.44      inference('cnf', [status(esa)], [t3_subset])).
% 3.25/3.44  thf('147', plain,
% 3.25/3.44      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.25/3.44      inference('sup-', [status(thm)], ['145', '146'])).
% 3.25/3.44  thf('148', plain,
% 3.25/3.44      (![X74 : $i, X75 : $i, X76 : $i, X77 : $i]:
% 3.25/3.44         (~ (m1_subset_1 @ X74 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X75 @ X76)))
% 3.25/3.44          | ((k7_relset_1 @ X75 @ X76 @ X74 @ X77) = (k9_relat_1 @ X74 @ X77)))),
% 3.25/3.44      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 3.25/3.44  thf('149', plain,
% 3.25/3.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.25/3.44         ((k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 3.25/3.44           = (k9_relat_1 @ k1_xboole_0 @ X2))),
% 3.25/3.44      inference('sup-', [status(thm)], ['147', '148'])).
% 3.25/3.44  thf('150', plain,
% 3.25/3.44      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.25/3.44      inference('sup-', [status(thm)], ['145', '146'])).
% 3.25/3.44  thf('151', plain,
% 3.25/3.44      (![X61 : $i, X62 : $i, X63 : $i]:
% 3.25/3.44         ((v4_relat_1 @ X61 @ X62)
% 3.25/3.44          | ~ (m1_subset_1 @ X61 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X62 @ X63))))),
% 3.25/3.44      inference('cnf', [status(esa)], [cc2_relset_1])).
% 3.25/3.44  thf('152', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 3.25/3.44      inference('sup-', [status(thm)], ['150', '151'])).
% 3.25/3.44  thf('153', plain,
% 3.25/3.44      (![X50 : $i, X51 : $i]:
% 3.25/3.44         (((X50) = (k7_relat_1 @ X50 @ X51))
% 3.25/3.44          | ~ (v4_relat_1 @ X50 @ X51)
% 3.25/3.44          | ~ (v1_relat_1 @ X50))),
% 3.25/3.44      inference('cnf', [status(esa)], [t209_relat_1])).
% 3.25/3.44  thf('154', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (~ (v1_relat_1 @ k1_xboole_0)
% 3.25/3.44          | ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0)))),
% 3.25/3.44      inference('sup-', [status(thm)], ['152', '153'])).
% 3.25/3.44  thf('155', plain,
% 3.25/3.44      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 3.25/3.44      inference('sup-', [status(thm)], ['145', '146'])).
% 3.25/3.44  thf('156', plain,
% 3.25/3.44      (![X58 : $i, X59 : $i, X60 : $i]:
% 3.25/3.44         ((v1_relat_1 @ X58)
% 3.25/3.44          | ~ (m1_subset_1 @ X58 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X59 @ X60))))),
% 3.25/3.44      inference('cnf', [status(esa)], [cc1_relset_1])).
% 3.25/3.44  thf('157', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.25/3.44      inference('sup-', [status(thm)], ['155', '156'])).
% 3.25/3.44  thf('158', plain,
% 3.25/3.44      (![X0 : $i]: ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0))),
% 3.25/3.44      inference('demod', [status(thm)], ['154', '157'])).
% 3.25/3.44  thf('159', plain,
% 3.25/3.44      (![X46 : $i, X47 : $i]:
% 3.25/3.44         (((k2_relat_1 @ (k7_relat_1 @ X46 @ X47)) = (k9_relat_1 @ X46 @ X47))
% 3.25/3.44          | ~ (v1_relat_1 @ X46))),
% 3.25/3.44      inference('cnf', [status(esa)], [t148_relat_1])).
% 3.25/3.44  thf('160', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))
% 3.25/3.44          | ~ (v1_relat_1 @ k1_xboole_0))),
% 3.25/3.44      inference('sup+', [status(thm)], ['158', '159'])).
% 3.25/3.44  thf('161', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 3.25/3.44      inference('sup-', [status(thm)], ['150', '151'])).
% 3.25/3.44  thf('162', plain,
% 3.25/3.44      (![X44 : $i, X45 : $i]:
% 3.25/3.44         (~ (v4_relat_1 @ X44 @ X45)
% 3.25/3.44          | (r1_tarski @ (k1_relat_1 @ X44) @ X45)
% 3.25/3.44          | ~ (v1_relat_1 @ X44))),
% 3.25/3.44      inference('cnf', [status(esa)], [d18_relat_1])).
% 3.25/3.44  thf('163', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (~ (v1_relat_1 @ k1_xboole_0)
% 3.25/3.44          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 3.25/3.44      inference('sup-', [status(thm)], ['161', '162'])).
% 3.25/3.44  thf('164', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.25/3.44      inference('sup-', [status(thm)], ['155', '156'])).
% 3.25/3.44  thf('165', plain,
% 3.25/3.44      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 3.25/3.44      inference('demod', [status(thm)], ['163', '164'])).
% 3.25/3.44  thf('166', plain,
% 3.25/3.44      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 3.25/3.44      inference('sup-', [status(thm)], ['82', '83'])).
% 3.25/3.44  thf('167', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.25/3.44      inference('sup-', [status(thm)], ['165', '166'])).
% 3.25/3.44  thf(t65_relat_1, axiom,
% 3.25/3.44    (![A:$i]:
% 3.25/3.44     ( ( v1_relat_1 @ A ) =>
% 3.25/3.44       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 3.25/3.44         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 3.25/3.44  thf('168', plain,
% 3.25/3.44      (![X55 : $i]:
% 3.25/3.44         (((k1_relat_1 @ X55) != (k1_xboole_0))
% 3.25/3.44          | ((k2_relat_1 @ X55) = (k1_xboole_0))
% 3.25/3.44          | ~ (v1_relat_1 @ X55))),
% 3.25/3.44      inference('cnf', [status(esa)], [t65_relat_1])).
% 3.25/3.44  thf('169', plain,
% 3.25/3.44      ((((k1_xboole_0) != (k1_xboole_0))
% 3.25/3.44        | ~ (v1_relat_1 @ k1_xboole_0)
% 3.25/3.44        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 3.25/3.44      inference('sup-', [status(thm)], ['167', '168'])).
% 3.25/3.44  thf('170', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.25/3.44      inference('sup-', [status(thm)], ['155', '156'])).
% 3.25/3.44  thf('171', plain,
% 3.25/3.44      ((((k1_xboole_0) != (k1_xboole_0))
% 3.25/3.44        | ((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 3.25/3.44      inference('demod', [status(thm)], ['169', '170'])).
% 3.25/3.44  thf('172', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 3.25/3.44      inference('simplify', [status(thm)], ['171'])).
% 3.25/3.44  thf('173', plain, ((v1_relat_1 @ k1_xboole_0)),
% 3.25/3.44      inference('sup-', [status(thm)], ['155', '156'])).
% 3.25/3.44  thf('174', plain,
% 3.25/3.44      (![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))),
% 3.25/3.44      inference('demod', [status(thm)], ['160', '172', '173'])).
% 3.25/3.44  thf('175', plain,
% 3.25/3.44      (![X0 : $i, X1 : $i, X2 : $i]:
% 3.25/3.44         ((k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2) = (k1_xboole_0))),
% 3.25/3.44      inference('demod', [status(thm)], ['149', '174'])).
% 3.25/3.44  thf('176', plain,
% 3.25/3.44      (![X0 : $i, X1 : $i]:
% 3.25/3.44         (((k1_xboole_0) = (k9_relat_1 @ (k2_zfmisc_1 @ sk_D @ X1) @ X0))
% 3.25/3.44          | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 3.25/3.44      inference('demod', [status(thm)], ['144', '175'])).
% 3.25/3.44  thf('177', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (((k1_xboole_0) = (k9_relat_1 @ sk_D @ X0))
% 3.25/3.44          | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 3.25/3.44          | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 3.25/3.44      inference('sup+', [status(thm)], ['139', '176'])).
% 3.25/3.44  thf('178', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 3.25/3.44          | ((k1_xboole_0) = (k9_relat_1 @ sk_D @ X0)))),
% 3.25/3.44      inference('simplify', [status(thm)], ['177'])).
% 3.25/3.44  thf('179', plain,
% 3.25/3.44      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 3.25/3.44          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 3.25/3.44      inference('demod', [status(thm)], ['0', '3'])).
% 3.25/3.44  thf('180', plain,
% 3.25/3.44      ((~ (r1_tarski @ k1_xboole_0 @ (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 3.25/3.44        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 3.25/3.44      inference('sup-', [status(thm)], ['178', '179'])).
% 3.25/3.44  thf('181', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 3.25/3.44      inference('cnf', [status(esa)], [t2_xboole_1])).
% 3.25/3.44  thf('182', plain, (((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))),
% 3.25/3.44      inference('demod', [status(thm)], ['180', '181'])).
% 3.25/3.44  thf(t14_funct_1, axiom,
% 3.25/3.44    (![A:$i,B:$i]:
% 3.25/3.44     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 3.25/3.44       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 3.25/3.44         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 3.25/3.44  thf('183', plain,
% 3.25/3.44      (![X56 : $i, X57 : $i]:
% 3.25/3.44         (((k1_relat_1 @ X57) != (k1_tarski @ X56))
% 3.25/3.44          | ((k2_relat_1 @ X57) = (k1_tarski @ (k1_funct_1 @ X57 @ X56)))
% 3.25/3.44          | ~ (v1_funct_1 @ X57)
% 3.25/3.44          | ~ (v1_relat_1 @ X57))),
% 3.25/3.44      inference('cnf', [status(esa)], [t14_funct_1])).
% 3.25/3.44  thf('184', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 3.25/3.44          | ~ (v1_relat_1 @ X0)
% 3.25/3.44          | ~ (v1_funct_1 @ X0)
% 3.25/3.44          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 3.25/3.44      inference('sup-', [status(thm)], ['182', '183'])).
% 3.25/3.44  thf('185', plain,
% 3.25/3.44      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 3.25/3.44        | ~ (v1_funct_1 @ sk_D)
% 3.25/3.44        | ~ (v1_relat_1 @ sk_D))),
% 3.25/3.44      inference('eq_res', [status(thm)], ['184'])).
% 3.25/3.44  thf('186', plain, ((v1_funct_1 @ sk_D)),
% 3.25/3.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.44  thf('187', plain, ((v1_relat_1 @ sk_D)),
% 3.25/3.44      inference('sup-', [status(thm)], ['25', '26'])).
% 3.25/3.44  thf('188', plain,
% 3.25/3.44      (((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 3.25/3.44      inference('demod', [status(thm)], ['185', '186', '187'])).
% 3.25/3.44  thf('189', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 3.25/3.44      inference('simplify', [status(thm)], ['14'])).
% 3.25/3.44  thf('190', plain,
% 3.25/3.44      ((m1_subset_1 @ sk_D @ 
% 3.25/3.44        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 3.25/3.44      inference('cnf', [status(esa)], [zf_stmt_0])).
% 3.25/3.44  thf('191', plain,
% 3.25/3.44      (![X82 : $i, X83 : $i, X84 : $i, X85 : $i]:
% 3.25/3.44         (~ (r1_tarski @ (k2_relat_1 @ X82) @ X83)
% 3.25/3.44          | (m1_subset_1 @ X82 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X84 @ X83)))
% 3.25/3.44          | ~ (m1_subset_1 @ X82 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X84 @ X85))))),
% 3.25/3.44      inference('cnf', [status(esa)], [t14_relset_1])).
% 3.25/3.44  thf('192', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         ((m1_subset_1 @ sk_D @ 
% 3.25/3.44           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ X0)))
% 3.25/3.44          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ X0))),
% 3.25/3.44      inference('sup-', [status(thm)], ['190', '191'])).
% 3.25/3.44  thf('193', plain,
% 3.25/3.44      ((m1_subset_1 @ sk_D @ 
% 3.25/3.44        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_D))))),
% 3.25/3.44      inference('sup-', [status(thm)], ['189', '192'])).
% 3.25/3.44  thf(dt_k7_relset_1, axiom,
% 3.25/3.44    (![A:$i,B:$i,C:$i,D:$i]:
% 3.25/3.44     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 3.25/3.44       ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 3.25/3.44  thf('194', plain,
% 3.25/3.44      (![X67 : $i, X68 : $i, X69 : $i, X70 : $i]:
% 3.25/3.44         (~ (m1_subset_1 @ X67 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X68 @ X69)))
% 3.25/3.44          | (m1_subset_1 @ (k7_relset_1 @ X68 @ X69 @ X67 @ X70) @ 
% 3.25/3.44             (k1_zfmisc_1 @ X69)))),
% 3.25/3.44      inference('cnf', [status(esa)], [dt_k7_relset_1])).
% 3.25/3.44  thf('195', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (m1_subset_1 @ 
% 3.25/3.44          (k7_relset_1 @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_D) @ sk_D @ X0) @ 
% 3.25/3.44          (k1_zfmisc_1 @ (k2_relat_1 @ sk_D)))),
% 3.25/3.44      inference('sup-', [status(thm)], ['193', '194'])).
% 3.25/3.44  thf('196', plain,
% 3.25/3.44      ((m1_subset_1 @ sk_D @ 
% 3.25/3.44        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_D))))),
% 3.25/3.44      inference('sup-', [status(thm)], ['189', '192'])).
% 3.25/3.44  thf('197', plain,
% 3.25/3.44      (![X74 : $i, X75 : $i, X76 : $i, X77 : $i]:
% 3.25/3.44         (~ (m1_subset_1 @ X74 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X75 @ X76)))
% 3.25/3.44          | ((k7_relset_1 @ X75 @ X76 @ X74 @ X77) = (k9_relat_1 @ X74 @ X77)))),
% 3.25/3.44      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 3.25/3.44  thf('198', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         ((k7_relset_1 @ (k1_tarski @ sk_A) @ (k2_relat_1 @ sk_D) @ sk_D @ X0)
% 3.25/3.44           = (k9_relat_1 @ sk_D @ X0))),
% 3.25/3.44      inference('sup-', [status(thm)], ['196', '197'])).
% 3.25/3.44  thf('199', plain,
% 3.25/3.44      (![X0 : $i]:
% 3.25/3.44         (m1_subset_1 @ (k9_relat_1 @ sk_D @ X0) @ 
% 3.25/3.44          (k1_zfmisc_1 @ (k2_relat_1 @ sk_D)))),
% 3.25/3.44      inference('demod', [status(thm)], ['195', '198'])).
% 3.25/3.44  thf('200', plain,
% 3.25/3.44      (![X39 : $i, X40 : $i]:
% 3.25/3.44         ((r1_tarski @ X39 @ X40) | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X40)))),
% 3.25/3.44      inference('cnf', [status(esa)], [t3_subset])).
% 3.25/3.44  thf('201', plain,
% 3.25/3.44      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ sk_D @ X0) @ (k2_relat_1 @ sk_D))),
% 3.25/3.44      inference('sup-', [status(thm)], ['199', '200'])).
% 3.25/3.44  thf('202', plain, ($false),
% 3.25/3.44      inference('demod', [status(thm)], ['4', '188', '201'])).
% 3.25/3.44  
% 3.25/3.44  % SZS output end Refutation
% 3.25/3.44  
% 3.25/3.45  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
