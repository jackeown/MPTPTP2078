%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1045+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1py3T9tcW8

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:57 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 295 expanded)
%              Number of leaves         :   20 (  89 expanded)
%              Depth                    :   16
%              Number of atoms          :  473 (4359 expanded)
%              Number of equality atoms :   49 ( 433 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k5_partfun1_type,type,(
    k5_partfun1: $i > $i > $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k3_partfun1_type,type,(
    k3_partfun1: $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t161_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( A = k1_xboole_0 ) )
       => ( ( k5_partfun1 @ A @ B @ ( k3_partfun1 @ C @ A @ B ) )
          = ( k1_tarski @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( k5_partfun1 @ A @ B @ ( k3_partfun1 @ C @ A @ B ) )
            = ( k1_tarski @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t161_funct_2])).

thf('0',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('2',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['1','2'])).

thf(t174_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( v1_partfun1 @ C @ A )
      <=> ( ( k5_partfun1 @ A @ B @ C )
          = ( k1_tarski @ C ) ) ) ) )).

thf('4',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_partfun1 @ X6 @ X7 )
      | ( ( k5_partfun1 @ X7 @ X8 @ X6 )
        = ( k1_tarski @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t174_partfun1])).

thf('5',plain,
    ( ( ~ ( v1_funct_1 @ sk_C )
      | ( ( k5_partfun1 @ k1_xboole_0 @ sk_B @ sk_C )
        = ( k1_tarski @ sk_C ) )
      | ~ ( v1_partfun1 @ sk_C @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( ( ( k5_partfun1 @ k1_xboole_0 @ sk_B @ sk_C )
        = ( k1_tarski @ sk_C ) )
      | ~ ( v1_partfun1 @ sk_C @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['5','6'])).

thf('8',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('9',plain,(
    ( k5_partfun1 @ sk_A @ sk_B @ ( k3_partfun1 @ sk_C @ sk_A @ sk_B ) )
 != ( k1_tarski @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t87_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k3_partfun1 @ C @ A @ B )
        = C ) ) )).

thf('11',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k3_partfun1 @ X10 @ X11 @ X12 )
        = X10 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) )
      | ~ ( v1_funct_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t87_partfun1])).

thf('12',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k3_partfun1 @ sk_C @ sk_A @ sk_B )
      = sk_C ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( k3_partfun1 @ sk_C @ sk_A @ sk_B )
    = sk_C ),
    inference(demod,[status(thm)],['12','13'])).

thf('15',plain,(
    ( k5_partfun1 @ sk_A @ sk_B @ sk_C )
 != ( k1_tarski @ sk_C ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('16',plain,
    ( ( ( k5_partfun1 @ k1_xboole_0 @ sk_B @ sk_C )
     != ( k1_tarski @ sk_C ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf('17',plain,
    ( ~ ( v1_partfun1 @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['7','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) )
      | ( v1_partfun1 @ X3 @ X4 )
      | ~ ( v1_funct_2 @ X3 @ X4 @ X5 )
      | ~ ( v1_funct_1 @ X3 )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ~ ( v1_partfun1 @ X6 @ X7 )
      | ( ( k5_partfun1 @ X7 @ X8 @ X6 )
        = ( k1_tarski @ X6 ) )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ~ ( v1_funct_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t174_partfun1])).

thf('26',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ( ( k5_partfun1 @ sk_A @ sk_B @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ~ ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( ( k5_partfun1 @ sk_A @ sk_B @ sk_C )
      = ( k1_tarski @ sk_C ) )
    | ~ ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['26','27'])).

thf('29',plain,(
    ( k5_partfun1 @ sk_A @ sk_B @ sk_C )
 != ( k1_tarski @ sk_C ) ),
    inference(demod,[status(thm)],['9','14'])).

thf('30',plain,(
    ~ ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['23','30'])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('32',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('33',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( sk_B != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('35',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( sk_B != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    sk_B = k1_xboole_0 ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B != k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('38',plain,(
    sk_A = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['36','37'])).

thf('39',plain,(
    ~ ( v1_partfun1 @ sk_C @ k1_xboole_0 ) ),
    inference(simpl_trail,[status(thm)],['17','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('42',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['0'])).

thf('44',plain,(
    sk_A = k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['36','37'])).

thf('45',plain,(
    sk_A = k1_xboole_0 ),
    inference(simpl_trail,[status(thm)],['43','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['42','45'])).

thf(cc1_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_partfun1 @ C @ A ) ) ) )).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ X2 ) ) )
      | ( v1_partfun1 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[cc1_partfun1])).

thf('48',plain,
    ( ( v1_partfun1 @ sk_C @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['23','30'])).

thf('50',plain,(
    sk_B = k1_xboole_0 ),
    inference('sup-',[status(thm)],['31','32'])).

thf('51',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['49','50'])).

thf('52',plain,(
    v1_partfun1 @ sk_C @ k1_xboole_0 ),
    inference(demod,[status(thm)],['48','51'])).

thf('53',plain,(
    $false ),
    inference(demod,[status(thm)],['39','52'])).


%------------------------------------------------------------------------------
