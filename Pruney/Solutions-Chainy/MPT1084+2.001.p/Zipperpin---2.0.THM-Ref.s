%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3ZI6LPQjqT

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 435 expanded)
%              Number of leaves         :   33 ( 144 expanded)
%              Depth                    :   15
%              Number of atoms          :  909 (6507 expanded)
%              Number of equality atoms :   56 ( 229 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(t201_funct_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ( v1_funct_1 @ B )
            & ( v1_funct_2 @ B @ A @ A )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ( ! [C: $i] :
                ( ( m1_subset_1 @ C @ A )
               => ( ( k3_funct_2 @ A @ A @ B @ C )
                  = C ) )
           => ( r2_funct_2 @ A @ A @ B @ ( k6_partfun1 @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( ( v1_funct_1 @ B )
              & ( v1_funct_2 @ B @ A @ A )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ( ! [C: $i] :
                  ( ( m1_subset_1 @ C @ A )
                 => ( ( k3_funct_2 @ A @ A @ B @ C )
                    = C ) )
             => ( r2_funct_2 @ A @ A @ B @ ( k6_partfun1 @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t201_funct_2])).

thf('0',plain,(
    ~ ( r2_funct_2 @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t34_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( B
          = ( k6_relat_1 @ A ) )
      <=> ( ( ( k1_relat_1 @ B )
            = A )
          & ! [C: $i] :
              ( ( r2_hidden @ C @ A )
             => ( ( k1_funct_1 @ B @ C )
                = C ) ) ) ) ) )).

thf('1',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k1_relat_1 @ X9 )
       != X8 )
      | ( r2_hidden @ ( sk_C @ X9 @ X8 ) @ X8 )
      | ( X9
        = ( k6_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('2',plain,(
    ! [X9: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( X9
        = ( k6_relat_1 @ ( k1_relat_1 @ X9 ) ) )
      | ( r2_hidden @ ( sk_C @ X9 @ ( k1_relat_1 @ X9 ) ) @ ( k1_relat_1 @ X9 ) ) ) ),
    inference(simplify,[status(thm)],['1'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('3',plain,(
    ! [X26: $i] :
      ( ( k6_partfun1 @ X26 )
      = ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('4',plain,(
    ! [X9: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( X9
        = ( k6_partfun1 @ ( k1_relat_1 @ X9 ) ) )
      | ( r2_hidden @ ( sk_C @ X9 @ ( k1_relat_1 @ X9 ) ) @ ( k1_relat_1 @ X9 ) ) ) ),
    inference(demod,[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( v4_relat_1 @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('7',plain,(
    v4_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v4_relat_1 @ X6 @ X7 )
      | ( r1_tarski @ ( k1_relat_1 @ X6 ) @ X7 )
      | ~ ( v1_relat_1 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('9',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ( r1_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X11: $i,X12: $i,X13: $i] :
      ( ( v1_relat_1 @ X11 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X12 @ X13 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['9','12'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('14',plain,(
    ! [X0: $i,X2: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('15',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_B ) @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('16',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ~ ( m1_subset_1 @ X4 @ ( k1_zfmisc_1 @ X5 ) )
      | ( m1_subset_1 @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ ( k1_relat_1 @ sk_B ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['4','17'])).

thf('19',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('21',plain,
    ( ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ ( k1_relat_1 @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('22',plain,(
    ! [X31: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X31 )
        = X31 )
      | ~ ( m1_subset_1 @ X31 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
    | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ ( sk_C @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
      = ( sk_C @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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

thf('25',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) )
      | ( v1_partfun1 @ X17 @ X18 )
      | ~ ( v1_funct_2 @ X17 @ X18 @ X19 )
      | ~ ( v1_funct_1 @ X17 )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('26',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ( v1_partfun1 @ sk_B @ sk_A ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_partfun1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(clc,[status(thm)],['29','30'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('32',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( v1_partfun1 @ X21 @ X20 )
      | ( ( k1_relat_1 @ X21 )
        = X20 )
      | ~ ( v4_relat_1 @ X21 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('33',plain,
    ( ~ ( v1_relat_1 @ sk_B )
    | ~ ( v4_relat_1 @ sk_B @ sk_A )
    | ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('35',plain,(
    v4_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['5','6'])).

thf('36',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('37',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('38',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('39',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
      = ( sk_C @ sk_B @ sk_A ) ) ),
    inference(demod,[status(thm)],['23','36','37','38'])).

thf('40',plain,
    ( ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ ( k1_relat_1 @ sk_B ) ) @ sk_A ) ),
    inference(demod,[status(thm)],['18','19','20'])).

thf('41',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('42',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('43',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k3_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k3_funct_2 @ A @ B @ C @ D )
        = ( k1_funct_1 @ C @ D ) ) ) )).

thf('45',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X22 @ X23 @ X24 )
      | ~ ( v1_funct_1 @ X22 )
      | ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X25 @ X23 )
      | ( ( k3_funct_2 @ X23 @ X24 @ X22 @ X25 )
        = ( k1_funct_1 @ X22 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47','48'])).

thf('50',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['43','51'])).

thf('53',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['39','52'])).

thf('54',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['53'])).

thf('55',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('56',plain,(
    ! [X8: $i,X9: $i] :
      ( ( ( k1_relat_1 @ X9 )
       != X8 )
      | ( ( k1_funct_1 @ X9 @ ( sk_C @ X9 @ X8 ) )
       != ( sk_C @ X9 @ X8 ) )
      | ( X9
        = ( k6_relat_1 @ X8 ) )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_relat_1 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('57',plain,(
    ! [X9: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( X9
        = ( k6_relat_1 @ ( k1_relat_1 @ X9 ) ) )
      | ( ( k1_funct_1 @ X9 @ ( sk_C @ X9 @ ( k1_relat_1 @ X9 ) ) )
       != ( sk_C @ X9 @ ( k1_relat_1 @ X9 ) ) ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,(
    ! [X26: $i] :
      ( ( k6_partfun1 @ X26 )
      = ( k6_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('59',plain,(
    ! [X9: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_funct_1 @ X9 )
      | ( X9
        = ( k6_partfun1 @ ( k1_relat_1 @ X9 ) ) )
      | ( ( k1_funct_1 @ X9 @ ( sk_C @ X9 @ ( k1_relat_1 @ X9 ) ) )
       != ( sk_C @ X9 @ ( k1_relat_1 @ X9 ) ) ) ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
     != ( sk_C @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
    | ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['55','59'])).

thf('61',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('62',plain,
    ( ( k1_relat_1 @ sk_B )
    = sk_A ),
    inference(demod,[status(thm)],['33','34','35'])).

thf('63',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('65',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
     != ( sk_C @ sk_B @ sk_A ) )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['60','61','62','63','64'])).

thf('66',plain,
    ( sk_B
    = ( k6_partfun1 @ sk_A ) ),
    inference(clc,[status(thm)],['54','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('69',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( r2_funct_2 @ X27 @ X28 @ X29 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X27 @ X28 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_2 @ X30 @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
      | ( r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,
    ( ( r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['67','73'])).

thf('75',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['74','75','76'])).

thf('78',plain,(
    $false ),
    inference(demod,[status(thm)],['0','66','77'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3ZI6LPQjqT
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:15:15 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.22/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.54  % Solved by: fo/fo7.sh
% 0.22/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.54  % done 58 iterations in 0.027s
% 0.22/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.54  % SZS output start Refutation
% 0.22/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.54  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.54  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.22/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.54  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.22/0.54  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.54  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.22/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.54  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.22/0.54  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.22/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.54  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.22/0.54  thf(t201_funct_2, conjecture,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.54             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.54           ( ( ![C:$i]:
% 0.22/0.54               ( ( m1_subset_1 @ C @ A ) =>
% 0.22/0.54                 ( ( k3_funct_2 @ A @ A @ B @ C ) = ( C ) ) ) ) =>
% 0.22/0.54             ( r2_funct_2 @ A @ A @ B @ ( k6_partfun1 @ A ) ) ) ) ) ))).
% 0.22/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.54    (~( ![A:$i]:
% 0.22/0.54        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.54          ( ![B:$i]:
% 0.22/0.54            ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.22/0.54                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.54              ( ( ![C:$i]:
% 0.22/0.54                  ( ( m1_subset_1 @ C @ A ) =>
% 0.22/0.54                    ( ( k3_funct_2 @ A @ A @ B @ C ) = ( C ) ) ) ) =>
% 0.22/0.54                ( r2_funct_2 @ A @ A @ B @ ( k6_partfun1 @ A ) ) ) ) ) ) )),
% 0.22/0.54    inference('cnf.neg', [status(esa)], [t201_funct_2])).
% 0.22/0.54  thf('0', plain, (~ (r2_funct_2 @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(t34_funct_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.22/0.54       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.22/0.54         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.22/0.54           ( ![C:$i]:
% 0.22/0.54             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.22/0.54  thf('1', plain,
% 0.22/0.54      (![X8 : $i, X9 : $i]:
% 0.22/0.54         (((k1_relat_1 @ X9) != (X8))
% 0.22/0.54          | (r2_hidden @ (sk_C @ X9 @ X8) @ X8)
% 0.22/0.54          | ((X9) = (k6_relat_1 @ X8))
% 0.22/0.54          | ~ (v1_funct_1 @ X9)
% 0.22/0.54          | ~ (v1_relat_1 @ X9))),
% 0.22/0.54      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.22/0.54  thf('2', plain,
% 0.22/0.54      (![X9 : $i]:
% 0.22/0.54         (~ (v1_relat_1 @ X9)
% 0.22/0.54          | ~ (v1_funct_1 @ X9)
% 0.22/0.54          | ((X9) = (k6_relat_1 @ (k1_relat_1 @ X9)))
% 0.22/0.54          | (r2_hidden @ (sk_C @ X9 @ (k1_relat_1 @ X9)) @ (k1_relat_1 @ X9)))),
% 0.22/0.54      inference('simplify', [status(thm)], ['1'])).
% 0.22/0.54  thf(redefinition_k6_partfun1, axiom,
% 0.22/0.54    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.22/0.54  thf('3', plain, (![X26 : $i]: ((k6_partfun1 @ X26) = (k6_relat_1 @ X26))),
% 0.22/0.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.22/0.54  thf('4', plain,
% 0.22/0.54      (![X9 : $i]:
% 0.22/0.54         (~ (v1_relat_1 @ X9)
% 0.22/0.54          | ~ (v1_funct_1 @ X9)
% 0.22/0.54          | ((X9) = (k6_partfun1 @ (k1_relat_1 @ X9)))
% 0.22/0.54          | (r2_hidden @ (sk_C @ X9 @ (k1_relat_1 @ X9)) @ (k1_relat_1 @ X9)))),
% 0.22/0.54      inference('demod', [status(thm)], ['2', '3'])).
% 0.22/0.54  thf('5', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(cc2_relset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.54       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.54  thf('6', plain,
% 0.22/0.54      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.22/0.54         ((v4_relat_1 @ X14 @ X15)
% 0.22/0.54          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16))))),
% 0.22/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.54  thf('7', plain, ((v4_relat_1 @ sk_B @ sk_A)),
% 0.22/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.54  thf(d18_relat_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ B ) =>
% 0.22/0.54       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.54  thf('8', plain,
% 0.22/0.54      (![X6 : $i, X7 : $i]:
% 0.22/0.54         (~ (v4_relat_1 @ X6 @ X7)
% 0.22/0.54          | (r1_tarski @ (k1_relat_1 @ X6) @ X7)
% 0.22/0.54          | ~ (v1_relat_1 @ X6))),
% 0.22/0.54      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.22/0.54  thf('9', plain,
% 0.22/0.54      ((~ (v1_relat_1 @ sk_B) | (r1_tarski @ (k1_relat_1 @ sk_B) @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['7', '8'])).
% 0.22/0.54  thf('10', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(cc1_relset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.54       ( v1_relat_1 @ C ) ))).
% 0.22/0.54  thf('11', plain,
% 0.22/0.54      (![X11 : $i, X12 : $i, X13 : $i]:
% 0.22/0.54         ((v1_relat_1 @ X11)
% 0.22/0.54          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X12 @ X13))))),
% 0.22/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.54  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.54  thf('13', plain, ((r1_tarski @ (k1_relat_1 @ sk_B) @ sk_A)),
% 0.22/0.54      inference('demod', [status(thm)], ['9', '12'])).
% 0.22/0.54  thf(t3_subset, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.54  thf('14', plain,
% 0.22/0.54      (![X0 : $i, X2 : $i]:
% 0.22/0.54         ((m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X2)) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.54  thf('15', plain,
% 0.22/0.54      ((m1_subset_1 @ (k1_relat_1 @ sk_B) @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.22/0.54  thf(t4_subset, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.22/0.54       ( m1_subset_1 @ A @ C ) ))).
% 0.22/0.54  thf('16', plain,
% 0.22/0.54      (![X3 : $i, X4 : $i, X5 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X3 @ X4)
% 0.22/0.54          | ~ (m1_subset_1 @ X4 @ (k1_zfmisc_1 @ X5))
% 0.22/0.54          | (m1_subset_1 @ X3 @ X5))),
% 0.22/0.54      inference('cnf', [status(esa)], [t4_subset])).
% 0.22/0.54  thf('17', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((m1_subset_1 @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_B)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.54  thf('18', plain,
% 0.22/0.54      ((((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 0.22/0.54        | ~ (v1_funct_1 @ sk_B)
% 0.22/0.54        | ~ (v1_relat_1 @ sk_B)
% 0.22/0.54        | (m1_subset_1 @ (sk_C @ sk_B @ (k1_relat_1 @ sk_B)) @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['4', '17'])).
% 0.22/0.54  thf('19', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('20', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.54  thf('21', plain,
% 0.22/0.54      ((((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 0.22/0.54        | (m1_subset_1 @ (sk_C @ sk_B @ (k1_relat_1 @ sk_B)) @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.22/0.54  thf('22', plain,
% 0.22/0.54      (![X31 : $i]:
% 0.22/0.54         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X31) = (X31))
% 0.22/0.54          | ~ (m1_subset_1 @ X31 @ sk_A))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('23', plain,
% 0.22/0.54      ((((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 0.22/0.54        | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ 
% 0.22/0.54            (sk_C @ sk_B @ (k1_relat_1 @ sk_B)))
% 0.22/0.54            = (sk_C @ sk_B @ (k1_relat_1 @ sk_B))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['21', '22'])).
% 0.22/0.54  thf('24', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(cc5_funct_2, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.54       ( ![C:$i]:
% 0.22/0.54         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.54           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.22/0.54             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.22/0.54  thf('25', plain,
% 0.22/0.54      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19)))
% 0.22/0.54          | (v1_partfun1 @ X17 @ X18)
% 0.22/0.54          | ~ (v1_funct_2 @ X17 @ X18 @ X19)
% 0.22/0.54          | ~ (v1_funct_1 @ X17)
% 0.22/0.54          | (v1_xboole_0 @ X19))),
% 0.22/0.54      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.22/0.54  thf('26', plain,
% 0.22/0.54      (((v1_xboole_0 @ sk_A)
% 0.22/0.54        | ~ (v1_funct_1 @ sk_B)
% 0.22/0.54        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.22/0.54        | (v1_partfun1 @ sk_B @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['24', '25'])).
% 0.22/0.54  thf('27', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('28', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('29', plain, (((v1_xboole_0 @ sk_A) | (v1_partfun1 @ sk_B @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.22/0.54  thf('30', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('31', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.22/0.54      inference('clc', [status(thm)], ['29', '30'])).
% 0.22/0.54  thf(d4_partfun1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.22/0.54       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.22/0.54  thf('32', plain,
% 0.22/0.54      (![X20 : $i, X21 : $i]:
% 0.22/0.54         (~ (v1_partfun1 @ X21 @ X20)
% 0.22/0.54          | ((k1_relat_1 @ X21) = (X20))
% 0.22/0.54          | ~ (v4_relat_1 @ X21 @ X20)
% 0.22/0.54          | ~ (v1_relat_1 @ X21))),
% 0.22/0.54      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.22/0.54  thf('33', plain,
% 0.22/0.54      ((~ (v1_relat_1 @ sk_B)
% 0.22/0.54        | ~ (v4_relat_1 @ sk_B @ sk_A)
% 0.22/0.54        | ((k1_relat_1 @ sk_B) = (sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.22/0.54  thf('34', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.54  thf('35', plain, ((v4_relat_1 @ sk_B @ sk_A)),
% 0.22/0.54      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.54  thf('36', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.22/0.54  thf('37', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.22/0.54  thf('38', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.22/0.54  thf('39', plain,
% 0.22/0.54      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.22/0.54        | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.22/0.54            = (sk_C @ sk_B @ sk_A)))),
% 0.22/0.54      inference('demod', [status(thm)], ['23', '36', '37', '38'])).
% 0.22/0.54  thf('40', plain,
% 0.22/0.54      ((((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 0.22/0.54        | (m1_subset_1 @ (sk_C @ sk_B @ (k1_relat_1 @ sk_B)) @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['18', '19', '20'])).
% 0.22/0.54  thf('41', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.22/0.54  thf('42', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.22/0.54  thf('43', plain,
% 0.22/0.54      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.22/0.54        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.22/0.54  thf('44', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(redefinition_k3_funct_2, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.54     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.22/0.54         ( v1_funct_2 @ C @ A @ B ) & 
% 0.22/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.22/0.54         ( m1_subset_1 @ D @ A ) ) =>
% 0.22/0.54       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.22/0.54  thf('45', plain,
% 0.22/0.54      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24)))
% 0.22/0.54          | ~ (v1_funct_2 @ X22 @ X23 @ X24)
% 0.22/0.54          | ~ (v1_funct_1 @ X22)
% 0.22/0.54          | (v1_xboole_0 @ X23)
% 0.22/0.54          | ~ (m1_subset_1 @ X25 @ X23)
% 0.22/0.54          | ((k3_funct_2 @ X23 @ X24 @ X22 @ X25) = (k1_funct_1 @ X22 @ X25)))),
% 0.22/0.54      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.22/0.54  thf('46', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0))
% 0.22/0.54          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.22/0.54          | (v1_xboole_0 @ sk_A)
% 0.22/0.54          | ~ (v1_funct_1 @ sk_B)
% 0.22/0.54          | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['44', '45'])).
% 0.22/0.54  thf('47', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('48', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('49', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0))
% 0.22/0.54          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.22/0.54          | (v1_xboole_0 @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['46', '47', '48'])).
% 0.22/0.54  thf('50', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('51', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.22/0.54          | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0)))),
% 0.22/0.54      inference('clc', [status(thm)], ['49', '50'])).
% 0.22/0.54  thf('52', plain,
% 0.22/0.54      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.22/0.54        | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.22/0.54            = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['43', '51'])).
% 0.22/0.54  thf('53', plain,
% 0.22/0.54      ((((sk_C @ sk_B @ sk_A) = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A)))
% 0.22/0.54        | ((sk_B) = (k6_partfun1 @ sk_A))
% 0.22/0.54        | ((sk_B) = (k6_partfun1 @ sk_A)))),
% 0.22/0.54      inference('sup+', [status(thm)], ['39', '52'])).
% 0.22/0.54  thf('54', plain,
% 0.22/0.54      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.22/0.54        | ((sk_C @ sk_B @ sk_A) = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))))),
% 0.22/0.54      inference('simplify', [status(thm)], ['53'])).
% 0.22/0.54  thf('55', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.22/0.54  thf('56', plain,
% 0.22/0.54      (![X8 : $i, X9 : $i]:
% 0.22/0.54         (((k1_relat_1 @ X9) != (X8))
% 0.22/0.54          | ((k1_funct_1 @ X9 @ (sk_C @ X9 @ X8)) != (sk_C @ X9 @ X8))
% 0.22/0.54          | ((X9) = (k6_relat_1 @ X8))
% 0.22/0.54          | ~ (v1_funct_1 @ X9)
% 0.22/0.54          | ~ (v1_relat_1 @ X9))),
% 0.22/0.54      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.22/0.54  thf('57', plain,
% 0.22/0.54      (![X9 : $i]:
% 0.22/0.54         (~ (v1_relat_1 @ X9)
% 0.22/0.54          | ~ (v1_funct_1 @ X9)
% 0.22/0.54          | ((X9) = (k6_relat_1 @ (k1_relat_1 @ X9)))
% 0.22/0.54          | ((k1_funct_1 @ X9 @ (sk_C @ X9 @ (k1_relat_1 @ X9)))
% 0.22/0.54              != (sk_C @ X9 @ (k1_relat_1 @ X9))))),
% 0.22/0.54      inference('simplify', [status(thm)], ['56'])).
% 0.22/0.54  thf('58', plain, (![X26 : $i]: ((k6_partfun1 @ X26) = (k6_relat_1 @ X26))),
% 0.22/0.54      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.22/0.54  thf('59', plain,
% 0.22/0.54      (![X9 : $i]:
% 0.22/0.54         (~ (v1_relat_1 @ X9)
% 0.22/0.54          | ~ (v1_funct_1 @ X9)
% 0.22/0.54          | ((X9) = (k6_partfun1 @ (k1_relat_1 @ X9)))
% 0.22/0.54          | ((k1_funct_1 @ X9 @ (sk_C @ X9 @ (k1_relat_1 @ X9)))
% 0.22/0.54              != (sk_C @ X9 @ (k1_relat_1 @ X9))))),
% 0.22/0.54      inference('demod', [status(thm)], ['57', '58'])).
% 0.22/0.54  thf('60', plain,
% 0.22/0.54      ((((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.22/0.54          != (sk_C @ sk_B @ (k1_relat_1 @ sk_B)))
% 0.22/0.54        | ((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 0.22/0.54        | ~ (v1_funct_1 @ sk_B)
% 0.22/0.54        | ~ (v1_relat_1 @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['55', '59'])).
% 0.22/0.54  thf('61', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.22/0.54  thf('62', plain, (((k1_relat_1 @ sk_B) = (sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['33', '34', '35'])).
% 0.22/0.54  thf('63', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('64', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.22/0.54  thf('65', plain,
% 0.22/0.54      ((((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A)) != (sk_C @ sk_B @ sk_A))
% 0.22/0.54        | ((sk_B) = (k6_partfun1 @ sk_A)))),
% 0.22/0.54      inference('demod', [status(thm)], ['60', '61', '62', '63', '64'])).
% 0.22/0.54  thf('66', plain, (((sk_B) = (k6_partfun1 @ sk_A))),
% 0.22/0.54      inference('clc', [status(thm)], ['54', '65'])).
% 0.22/0.54  thf('67', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('68', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(reflexivity_r2_funct_2, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.54     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.22/0.54         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.22/0.54         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.22/0.54         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.22/0.54       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.22/0.54  thf('69', plain,
% 0.22/0.54      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.22/0.54         ((r2_funct_2 @ X27 @ X28 @ X29 @ X29)
% 0.22/0.54          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28)))
% 0.22/0.54          | ~ (v1_funct_2 @ X29 @ X27 @ X28)
% 0.22/0.54          | ~ (v1_funct_1 @ X29)
% 0.22/0.54          | ~ (v1_funct_1 @ X30)
% 0.22/0.54          | ~ (v1_funct_2 @ X30 @ X27 @ X28)
% 0.22/0.54          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.22/0.54      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.22/0.54  thf('70', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.22/0.54          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.22/0.54          | ~ (v1_funct_1 @ X0)
% 0.22/0.54          | ~ (v1_funct_1 @ sk_B)
% 0.22/0.54          | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.22/0.54          | (r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B))),
% 0.22/0.54      inference('sup-', [status(thm)], ['68', '69'])).
% 0.22/0.54  thf('71', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('72', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('73', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.22/0.54          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.22/0.54          | ~ (v1_funct_1 @ X0)
% 0.22/0.54          | (r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B))),
% 0.22/0.54      inference('demod', [status(thm)], ['70', '71', '72'])).
% 0.22/0.54  thf('74', plain,
% 0.22/0.54      (((r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B)
% 0.22/0.54        | ~ (v1_funct_1 @ sk_B)
% 0.22/0.54        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['67', '73'])).
% 0.22/0.54  thf('75', plain, ((v1_funct_1 @ sk_B)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('76', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('77', plain, ((r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 0.22/0.54      inference('demod', [status(thm)], ['74', '75', '76'])).
% 0.22/0.54  thf('78', plain, ($false),
% 0.22/0.54      inference('demod', [status(thm)], ['0', '66', '77'])).
% 0.22/0.54  
% 0.22/0.54  % SZS output end Refutation
% 0.22/0.54  
% 0.22/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
