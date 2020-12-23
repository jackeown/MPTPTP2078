%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1842+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dVE4360lUy

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:54:23 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   34 (  44 expanded)
%              Number of leaves         :   14 (  19 expanded)
%              Depth                    :    9
%              Number of atoms          :  161 ( 281 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :   10 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_domain_1_type,type,(
    k6_domain_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_zfmisc_1_type,type,(
    v1_zfmisc_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_subset_1_type,type,(
    v1_subset_1: $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(t7_tex_2,conjecture,(
    ! [A: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_zfmisc_1 @ A ) )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ A )
         => ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ( ~ ( v1_xboole_0 @ A )
          & ~ ( v1_zfmisc_1 @ A ) )
       => ! [B: $i] :
            ( ( m1_subset_1 @ B @ A )
           => ( v1_subset_1 @ ( k6_domain_1 @ A @ B ) @ A ) ) ) ),
    inference('cnf.neg',[status(esa)],[t7_tex_2])).

thf('0',plain,(
    ~ ( v1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( ( k6_domain_1 @ A @ B )
        = ( k1_tarski @ B ) ) ) )).

thf('2',plain,(
    ! [X5: $i,X6: $i] :
      ( ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X6 @ X5 )
      | ( ( k6_domain_1 @ X5 @ X6 )
        = ( k1_tarski @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_domain_1])).

thf('3',plain,
    ( ( ( k6_domain_1 @ sk_A @ sk_B )
      = ( k1_tarski @ sk_B ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B )
    = ( k1_tarski @ sk_B ) ),
    inference(clc,[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k6_domain_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( m1_subset_1 @ B @ A ) )
     => ( m1_subset_1 @ ( k6_domain_1 @ A @ B ) @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('7',plain,(
    ! [X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ~ ( m1_subset_1 @ X3 @ X2 )
      | ( m1_subset_1 @ ( k6_domain_1 @ X2 @ X3 ) @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k6_domain_1])).

thf('8',plain,
    ( ( m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['8','9'])).

thf(d7_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
     => ( ( v1_subset_1 @ B @ A )
      <=> ( B != A ) ) ) )).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ( v1_subset_1 @ X1 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(cnf,[status(esa)],[d7_subset_1])).

thf('12',plain,
    ( ( v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ sk_A )
    | ( ( k6_domain_1 @ sk_A @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ~ ( v1_subset_1 @ ( k6_domain_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k6_domain_1 @ sk_A @ sk_B )
    = sk_A ),
    inference(clc,[status(thm)],['12','13'])).

thf('15',plain,
    ( ( k1_tarski @ sk_B )
    = sk_A ),
    inference('sup+',[status(thm)],['5','14'])).

thf(fc2_zfmisc_1,axiom,(
    ! [A: $i] :
      ( v1_zfmisc_1 @ ( k1_tarski @ A ) ) )).

thf('16',plain,(
    ! [X4: $i] :
      ( v1_zfmisc_1 @ ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[fc2_zfmisc_1])).

thf('17',plain,(
    v1_zfmisc_1 @ sk_A ),
    inference('sup+',[status(thm)],['15','16'])).

thf('18',plain,(
    $false ),
    inference(demod,[status(thm)],['0','17'])).


%------------------------------------------------------------------------------
