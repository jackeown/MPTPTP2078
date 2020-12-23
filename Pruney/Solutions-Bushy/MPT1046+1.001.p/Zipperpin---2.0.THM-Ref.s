%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1046+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aTyG9WN3fn

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 169 expanded)
%              Number of leaves         :   13 (  56 expanded)
%              Depth                    :   10
%              Number of atoms          :  296 (2613 expanded)
%              Number of equality atoms :   28 ( 171 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k3_partfun1_type,type,(
    k3_partfun1: $i > $i > $i > $i )).

thf(t162_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k5_partfun1 @ A @ A @ ( k3_partfun1 @ B @ A @ A ) )
        = ( k1_tarski @ B ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ( ( v1_funct_1 @ B )
          & ( v1_funct_2 @ B @ A @ A )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
       => ( ( k5_partfun1 @ A @ A @ ( k3_partfun1 @ B @ A @ A ) )
          = ( k1_tarski @ B ) ) ) ),
    inference('cnf.neg',[status(esa)],[t162_funct_2])).

thf('0',plain,(
    ( k5_partfun1 @ sk_A @ sk_A @ ( k3_partfun1 @ sk_B @ sk_A @ sk_A ) )
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t161_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k5_partfun1 @ A @ B @ ( k3_partfun1 @ C @ A @ B ) )
          = ( k1_tarski @ C ) ) ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ( ( k5_partfun1 @ X0 @ X2 @ ( k3_partfun1 @ X1 @ X0 @ X2 ) )
        = ( k1_tarski @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t161_funct_2])).

thf('3',plain,
    ( ( ( k5_partfun1 @ sk_A @ sk_A @ ( k3_partfun1 @ sk_B @ sk_A @ sk_A ) )
      = ( k1_tarski @ sk_B ) )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( ( k5_partfun1 @ sk_A @ sk_A @ ( k3_partfun1 @ sk_B @ sk_A @ sk_A ) )
      = ( k1_tarski @ sk_B ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ( k5_partfun1 @ sk_A @ sk_A @ ( k3_partfun1 @ sk_B @ sk_A @ sk_A ) )
 != ( k1_tarski @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('9',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('10',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('11',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('12',plain,(
    ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ ( k3_partfun1 @ sk_B @ k1_xboole_0 @ k1_xboole_0 ) )
 != ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['0','8','9','10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('15',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('16',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X0 != k1_xboole_0 )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_2 @ X1 @ X0 @ X2 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ( ( k5_partfun1 @ X0 @ X2 @ ( k3_partfun1 @ X1 @ X0 @ X2 ) )
        = ( k1_tarski @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[t161_funct_2])).

thf('18',plain,(
    ! [X1: $i,X2: $i] :
      ( ( ( k5_partfun1 @ k1_xboole_0 @ X2 @ ( k3_partfun1 @ X1 @ k1_xboole_0 @ X2 ) )
        = ( k1_tarski @ X1 ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X2 ) ) )
      | ~ ( v1_funct_2 @ X1 @ k1_xboole_0 @ X2 )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ k1_xboole_0 @ k1_xboole_0 )
    | ( ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ ( k3_partfun1 @ sk_B @ k1_xboole_0 @ k1_xboole_0 ) )
      = ( k1_tarski @ sk_B ) ) ),
    inference('sup-',[status(thm)],['16','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('23',plain,(
    sk_A = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['6','7'])).

thf('24',plain,(
    v1_funct_2 @ sk_B @ k1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ( k5_partfun1 @ k1_xboole_0 @ k1_xboole_0 @ ( k3_partfun1 @ sk_B @ k1_xboole_0 @ k1_xboole_0 ) )
    = ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['19','20','24'])).

thf('26',plain,(
    ( k1_tarski @ sk_B )
 != ( k1_tarski @ sk_B ) ),
    inference(demod,[status(thm)],['12','25'])).

thf('27',plain,(
    $false ),
    inference(simplify,[status(thm)],['26'])).


%------------------------------------------------------------------------------
