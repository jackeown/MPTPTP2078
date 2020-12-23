%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UVK6eXRDJh

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:37 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 346 expanded)
%              Number of leaves         :   32 ( 114 expanded)
%              Depth                    :   22
%              Number of atoms          :  982 (5401 expanded)
%              Number of equality atoms :   97 ( 283 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t132_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ( ( ( B = k1_xboole_0 )
            & ( A != k1_xboole_0 ) )
          | ( v1_partfun1 @ C @ A ) ) ) ) )).

thf('2',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( X22 = k1_xboole_0 )
      | ~ ( v1_funct_1 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X22 ) ) )
      | ( v1_partfun1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X22 ) ) )
      | ~ ( v1_funct_2 @ X23 @ X24 @ X22 )
      | ~ ( v1_funct_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t132_funct_2])).

thf('3',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ~ ( v1_funct_2 @ X23 @ X24 @ X22 )
      | ( v1_partfun1 @ X23 @ X24 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X23 )
      | ( X22 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['2'])).

thf('4',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v1_funct_1 @ sk_B )
    | ( v1_partfun1 @ sk_B @ sk_A )
    | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['1','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( v1_partfun1 @ sk_B @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_partfun1 @ X12 @ X11 )
      | ( ( k1_relat_1 @ X12 )
        = X11 )
      | ~ ( v4_relat_1 @ X12 @ X11 )
      | ~ ( v1_relat_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('9',plain,
    ( ( sk_A = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_B )
    | ~ ( v4_relat_1 @ sk_B @ sk_A )
    | ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('11',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ( v1_relat_1 @ X5 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X7 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('12',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( v4_relat_1 @ X8 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('15',plain,(
    v4_relat_1 @ sk_B @ sk_A ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(demod,[status(thm)],['9','12','15'])).

thf('17',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(demod,[status(thm)],['9','12','15'])).

thf('18',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(demod,[status(thm)],['9','12','15'])).

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

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k1_relat_1 @ X3 )
       != X2 )
      | ( r2_hidden @ ( sk_C @ X3 @ X2 ) @ X2 )
      | ( X3
        = ( k6_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('20',plain,(
    ! [X3: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( X3
        = ( k6_relat_1 @ ( k1_relat_1 @ X3 ) ) )
      | ( r2_hidden @ ( sk_C @ X3 @ ( k1_relat_1 @ X3 ) ) @ ( k1_relat_1 @ X3 ) ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('21',plain,(
    ! [X17: $i] :
      ( ( k6_partfun1 @ X17 )
      = ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('22',plain,(
    ! [X3: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( X3
        = ( k6_partfun1 @ ( k1_relat_1 @ X3 ) ) )
      | ( r2_hidden @ ( sk_C @ X3 @ ( k1_relat_1 @ X3 ) ) @ ( k1_relat_1 @ X3 ) ) ) ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ ( k1_relat_1 @ sk_B ) ) @ sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup+',[status(thm)],['18','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('26',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ ( k1_relat_1 @ sk_B ) ) @ sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['17','26'])).

thf('28',plain,
    ( ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
    | ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference(simplify,[status(thm)],['27'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X0 @ X1 )
      | ~ ( r2_hidden @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('30',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X25: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X25 )
        = X25 )
      | ~ ( m1_subset_1 @ X25 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
    | ( sk_A = k1_xboole_0 )
    | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
      = ( sk_C @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
    | ( m1_subset_1 @ ( sk_C @ sk_B @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('34',plain,(
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

thf('35',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( v1_funct_2 @ X13 @ X14 @ X15 )
      | ~ ( v1_funct_1 @ X13 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X16 @ X14 )
      | ( ( k3_funct_2 @ X14 @ X15 @ X13 @ X16 )
        = ( k1_funct_1 @ X13 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_B )
      | ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0 )
        = ( k1_funct_1 @ sk_B @ X0 ) ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
    | ( sk_A = k1_xboole_0 )
    | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['33','41'])).

thf('43',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference('sup+',[status(thm)],['32','42'])).

thf('44',plain,
    ( ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
    | ( sk_A = k1_xboole_0 )
    | ( ( sk_C @ sk_B @ sk_A )
      = ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(demod,[status(thm)],['9','12','15'])).

thf('46',plain,(
    ! [X2: $i,X3: $i] :
      ( ( ( k1_relat_1 @ X3 )
       != X2 )
      | ( ( k1_funct_1 @ X3 @ ( sk_C @ X3 @ X2 ) )
       != ( sk_C @ X3 @ X2 ) )
      | ( X3
        = ( k6_relat_1 @ X2 ) )
      | ~ ( v1_funct_1 @ X3 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('47',plain,(
    ! [X3: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( X3
        = ( k6_relat_1 @ ( k1_relat_1 @ X3 ) ) )
      | ( ( k1_funct_1 @ X3 @ ( sk_C @ X3 @ ( k1_relat_1 @ X3 ) ) )
       != ( sk_C @ X3 @ ( k1_relat_1 @ X3 ) ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,(
    ! [X17: $i] :
      ( ( k6_partfun1 @ X17 )
      = ( k6_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('49',plain,(
    ! [X3: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( v1_funct_1 @ X3 )
      | ( X3
        = ( k6_partfun1 @ ( k1_relat_1 @ X3 ) ) )
      | ( ( k1_funct_1 @ X3 @ ( sk_C @ X3 @ ( k1_relat_1 @ X3 ) ) )
       != ( sk_C @ X3 @ ( k1_relat_1 @ X3 ) ) ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
     != ( sk_C @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
    | ~ ( v1_funct_1 @ sk_B )
    | ~ ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['45','49'])).

thf('51',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_relat_1 @ sk_B ),
    inference('sup-',[status(thm)],['10','11'])).

thf('53',plain,
    ( ( ( k1_funct_1 @ sk_B @ ( sk_C @ sk_B @ sk_A ) )
     != ( sk_C @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ( ( sk_C @ sk_B @ sk_A )
     != ( sk_C @ sk_B @ ( k1_relat_1 @ sk_B ) ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
    | ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['44','53'])).

thf('55',plain,
    ( ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) )
    | ( sk_A = k1_xboole_0 )
    | ( ( sk_C @ sk_B @ sk_A )
     != ( sk_C @ sk_B @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_B )
      = sk_A ) ),
    inference(demod,[status(thm)],['9','12','15'])).

thf('57',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['55','56'])).

thf('58',plain,
    ( ( sk_B
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_A = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','57'])).

thf('59',plain,
    ( ( sk_A = k1_xboole_0 )
    | ( sk_B
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,(
    ~ ( r2_funct_2 @ sk_A @ sk_A @ sk_B @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,
    ( ~ ( r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_funct_2 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('63',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ~ ( v1_funct_2 @ X18 @ X19 @ X20 )
      | ~ ( v1_funct_1 @ X18 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) )
      | ( r2_funct_2 @ X19 @ X20 @ X18 @ X21 )
      | ( X18 != X21 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_funct_2])).

thf('64',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( r2_funct_2 @ X19 @ X20 @ X21 @ X21 )
      | ~ ( v1_funct_1 @ X21 )
      | ~ ( v1_funct_2 @ X21 @ X19 @ X20 )
      | ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,
    ( ~ ( v1_funct_2 @ sk_B @ sk_A @ sk_A )
    | ~ ( v1_funct_1 @ sk_B )
    | ( r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,(
    v1_funct_2 @ sk_B @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B ),
    inference(demod,[status(thm)],['65','66','67'])).

thf('69',plain,(
    sk_A = k1_xboole_0 ),
    inference(demod,[status(thm)],['61','68'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('70',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['0','69','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.UVK6eXRDJh
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:56:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.19/0.48  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.48  % Solved by: fo/fo7.sh
% 0.19/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.48  % done 70 iterations in 0.031s
% 0.19/0.48  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.48  % SZS output start Refutation
% 0.19/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.19/0.48  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.19/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.19/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.48  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.48  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.48  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.19/0.48  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.19/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.48  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.19/0.48  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.19/0.48  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.19/0.48  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.19/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.48  thf(t201_funct_2, conjecture,
% 0.19/0.48    (![A:$i]:
% 0.19/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.48       ( ![B:$i]:
% 0.19/0.48         ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.19/0.48             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.19/0.48           ( ( ![C:$i]:
% 0.19/0.48               ( ( m1_subset_1 @ C @ A ) =>
% 0.19/0.48                 ( ( k3_funct_2 @ A @ A @ B @ C ) = ( C ) ) ) ) =>
% 0.19/0.48             ( r2_funct_2 @ A @ A @ B @ ( k6_partfun1 @ A ) ) ) ) ) ))).
% 0.19/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.48    (~( ![A:$i]:
% 0.19/0.48        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.19/0.48          ( ![B:$i]:
% 0.19/0.48            ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.19/0.48                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.19/0.48              ( ( ![C:$i]:
% 0.19/0.48                  ( ( m1_subset_1 @ C @ A ) =>
% 0.19/0.48                    ( ( k3_funct_2 @ A @ A @ B @ C ) = ( C ) ) ) ) =>
% 0.19/0.48                ( r2_funct_2 @ A @ A @ B @ ( k6_partfun1 @ A ) ) ) ) ) ) )),
% 0.19/0.48    inference('cnf.neg', [status(esa)], [t201_funct_2])).
% 0.19/0.48  thf('0', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('1', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(t132_funct_2, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( ( v1_funct_1 @ C ) & 
% 0.19/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.48       ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.19/0.48           ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.48         ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.19/0.48           ( v1_partfun1 @ C @ A ) ) ) ))).
% 0.19/0.48  thf('2', plain,
% 0.19/0.48      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.19/0.48         (((X22) = (k1_xboole_0))
% 0.19/0.48          | ~ (v1_funct_1 @ X23)
% 0.19/0.48          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X22)))
% 0.19/0.48          | (v1_partfun1 @ X23 @ X24)
% 0.19/0.48          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X22)))
% 0.19/0.48          | ~ (v1_funct_2 @ X23 @ X24 @ X22)
% 0.19/0.48          | ~ (v1_funct_1 @ X23))),
% 0.19/0.48      inference('cnf', [status(esa)], [t132_funct_2])).
% 0.19/0.48  thf('3', plain,
% 0.19/0.48      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.19/0.48         (~ (v1_funct_2 @ X23 @ X24 @ X22)
% 0.19/0.48          | (v1_partfun1 @ X23 @ X24)
% 0.19/0.48          | ~ (m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X22)))
% 0.19/0.48          | ~ (v1_funct_1 @ X23)
% 0.19/0.48          | ((X22) = (k1_xboole_0)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['2'])).
% 0.19/0.48  thf('4', plain,
% 0.19/0.48      ((((sk_A) = (k1_xboole_0))
% 0.19/0.48        | ~ (v1_funct_1 @ sk_B)
% 0.19/0.48        | (v1_partfun1 @ sk_B @ sk_A)
% 0.19/0.48        | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['1', '3'])).
% 0.19/0.48  thf('5', plain, ((v1_funct_1 @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('6', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('7', plain, ((((sk_A) = (k1_xboole_0)) | (v1_partfun1 @ sk_B @ sk_A))),
% 0.19/0.48      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.19/0.48  thf(d4_partfun1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.19/0.48       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.19/0.48  thf('8', plain,
% 0.19/0.48      (![X11 : $i, X12 : $i]:
% 0.19/0.48         (~ (v1_partfun1 @ X12 @ X11)
% 0.19/0.48          | ((k1_relat_1 @ X12) = (X11))
% 0.19/0.48          | ~ (v4_relat_1 @ X12 @ X11)
% 0.19/0.48          | ~ (v1_relat_1 @ X12))),
% 0.19/0.48      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.19/0.48  thf('9', plain,
% 0.19/0.48      ((((sk_A) = (k1_xboole_0))
% 0.19/0.48        | ~ (v1_relat_1 @ sk_B)
% 0.19/0.48        | ~ (v4_relat_1 @ sk_B @ sk_A)
% 0.19/0.48        | ((k1_relat_1 @ sk_B) = (sk_A)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['7', '8'])).
% 0.19/0.48  thf('10', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(cc1_relset_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.48       ( v1_relat_1 @ C ) ))).
% 0.19/0.48  thf('11', plain,
% 0.19/0.48      (![X5 : $i, X6 : $i, X7 : $i]:
% 0.19/0.48         ((v1_relat_1 @ X5)
% 0.19/0.48          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X6 @ X7))))),
% 0.19/0.48      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.19/0.48  thf('12', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.48  thf('13', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(cc2_relset_1, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i]:
% 0.19/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.48       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.19/0.48  thf('14', plain,
% 0.19/0.48      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.19/0.48         ((v4_relat_1 @ X8 @ X9)
% 0.19/0.48          | ~ (m1_subset_1 @ X8 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10))))),
% 0.19/0.48      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.48  thf('15', plain, ((v4_relat_1 @ sk_B @ sk_A)),
% 0.19/0.48      inference('sup-', [status(thm)], ['13', '14'])).
% 0.19/0.48  thf('16', plain,
% 0.19/0.48      ((((sk_A) = (k1_xboole_0)) | ((k1_relat_1 @ sk_B) = (sk_A)))),
% 0.19/0.48      inference('demod', [status(thm)], ['9', '12', '15'])).
% 0.19/0.48  thf('17', plain,
% 0.19/0.48      ((((sk_A) = (k1_xboole_0)) | ((k1_relat_1 @ sk_B) = (sk_A)))),
% 0.19/0.48      inference('demod', [status(thm)], ['9', '12', '15'])).
% 0.19/0.48  thf('18', plain,
% 0.19/0.48      ((((sk_A) = (k1_xboole_0)) | ((k1_relat_1 @ sk_B) = (sk_A)))),
% 0.19/0.48      inference('demod', [status(thm)], ['9', '12', '15'])).
% 0.19/0.48  thf(t34_funct_1, axiom,
% 0.19/0.48    (![A:$i,B:$i]:
% 0.19/0.48     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.19/0.48       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.19/0.48         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.19/0.48           ( ![C:$i]:
% 0.19/0.48             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.19/0.48  thf('19', plain,
% 0.19/0.48      (![X2 : $i, X3 : $i]:
% 0.19/0.48         (((k1_relat_1 @ X3) != (X2))
% 0.19/0.48          | (r2_hidden @ (sk_C @ X3 @ X2) @ X2)
% 0.19/0.48          | ((X3) = (k6_relat_1 @ X2))
% 0.19/0.48          | ~ (v1_funct_1 @ X3)
% 0.19/0.48          | ~ (v1_relat_1 @ X3))),
% 0.19/0.48      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.19/0.48  thf('20', plain,
% 0.19/0.48      (![X3 : $i]:
% 0.19/0.48         (~ (v1_relat_1 @ X3)
% 0.19/0.48          | ~ (v1_funct_1 @ X3)
% 0.19/0.48          | ((X3) = (k6_relat_1 @ (k1_relat_1 @ X3)))
% 0.19/0.48          | (r2_hidden @ (sk_C @ X3 @ (k1_relat_1 @ X3)) @ (k1_relat_1 @ X3)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['19'])).
% 0.19/0.48  thf(redefinition_k6_partfun1, axiom,
% 0.19/0.48    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.19/0.48  thf('21', plain, (![X17 : $i]: ((k6_partfun1 @ X17) = (k6_relat_1 @ X17))),
% 0.19/0.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.19/0.48  thf('22', plain,
% 0.19/0.48      (![X3 : $i]:
% 0.19/0.48         (~ (v1_relat_1 @ X3)
% 0.19/0.48          | ~ (v1_funct_1 @ X3)
% 0.19/0.48          | ((X3) = (k6_partfun1 @ (k1_relat_1 @ X3)))
% 0.19/0.48          | (r2_hidden @ (sk_C @ X3 @ (k1_relat_1 @ X3)) @ (k1_relat_1 @ X3)))),
% 0.19/0.48      inference('demod', [status(thm)], ['20', '21'])).
% 0.19/0.48  thf('23', plain,
% 0.19/0.48      (((r2_hidden @ (sk_C @ sk_B @ (k1_relat_1 @ sk_B)) @ sk_A)
% 0.19/0.48        | ((sk_A) = (k1_xboole_0))
% 0.19/0.48        | ((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 0.19/0.48        | ~ (v1_funct_1 @ sk_B)
% 0.19/0.48        | ~ (v1_relat_1 @ sk_B))),
% 0.19/0.48      inference('sup+', [status(thm)], ['18', '22'])).
% 0.19/0.48  thf('24', plain, ((v1_funct_1 @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.48  thf('26', plain,
% 0.19/0.48      (((r2_hidden @ (sk_C @ sk_B @ (k1_relat_1 @ sk_B)) @ sk_A)
% 0.19/0.48        | ((sk_A) = (k1_xboole_0))
% 0.19/0.48        | ((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B))))),
% 0.19/0.48      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.19/0.48  thf('27', plain,
% 0.19/0.48      (((r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_A)
% 0.19/0.48        | ((sk_A) = (k1_xboole_0))
% 0.19/0.48        | ((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 0.19/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup+', [status(thm)], ['17', '26'])).
% 0.19/0.48  thf('28', plain,
% 0.19/0.48      ((((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 0.19/0.48        | ((sk_A) = (k1_xboole_0))
% 0.19/0.48        | (r2_hidden @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.19/0.48      inference('simplify', [status(thm)], ['27'])).
% 0.19/0.48  thf(t1_subset, axiom,
% 0.19/0.48    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.19/0.48  thf('29', plain,
% 0.19/0.48      (![X0 : $i, X1 : $i]: ((m1_subset_1 @ X0 @ X1) | ~ (r2_hidden @ X0 @ X1))),
% 0.19/0.48      inference('cnf', [status(esa)], [t1_subset])).
% 0.19/0.48  thf('30', plain,
% 0.19/0.48      ((((sk_A) = (k1_xboole_0))
% 0.19/0.48        | ((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 0.19/0.48        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['28', '29'])).
% 0.19/0.48  thf('31', plain,
% 0.19/0.48      (![X25 : $i]:
% 0.19/0.48         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X25) = (X25))
% 0.19/0.48          | ~ (m1_subset_1 @ X25 @ sk_A))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('32', plain,
% 0.19/0.48      ((((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 0.19/0.48        | ((sk_A) = (k1_xboole_0))
% 0.19/0.48        | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.19/0.48            = (sk_C @ sk_B @ sk_A)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['30', '31'])).
% 0.19/0.48  thf('33', plain,
% 0.19/0.48      ((((sk_A) = (k1_xboole_0))
% 0.19/0.48        | ((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 0.19/0.48        | (m1_subset_1 @ (sk_C @ sk_B @ sk_A) @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['28', '29'])).
% 0.19/0.48  thf('34', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(redefinition_k3_funct_2, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.48     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.19/0.48         ( v1_funct_2 @ C @ A @ B ) & 
% 0.19/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.19/0.48         ( m1_subset_1 @ D @ A ) ) =>
% 0.19/0.48       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.19/0.48  thf('35', plain,
% 0.19/0.48      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15)))
% 0.19/0.48          | ~ (v1_funct_2 @ X13 @ X14 @ X15)
% 0.19/0.48          | ~ (v1_funct_1 @ X13)
% 0.19/0.48          | (v1_xboole_0 @ X14)
% 0.19/0.48          | ~ (m1_subset_1 @ X16 @ X14)
% 0.19/0.48          | ((k3_funct_2 @ X14 @ X15 @ X13 @ X16) = (k1_funct_1 @ X13 @ X16)))),
% 0.19/0.48      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.19/0.48  thf('36', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0))
% 0.19/0.48          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.19/0.48          | (v1_xboole_0 @ sk_A)
% 0.19/0.48          | ~ (v1_funct_1 @ sk_B)
% 0.19/0.48          | ~ (v1_funct_2 @ sk_B @ sk_A @ sk_A))),
% 0.19/0.48      inference('sup-', [status(thm)], ['34', '35'])).
% 0.19/0.48  thf('37', plain, ((v1_funct_1 @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('38', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('39', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0))
% 0.19/0.48          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.19/0.48          | (v1_xboole_0 @ sk_A))),
% 0.19/0.48      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.19/0.48  thf('40', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('41', plain,
% 0.19/0.48      (![X0 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.19/0.48          | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ X0) = (k1_funct_1 @ sk_B @ X0)))),
% 0.19/0.48      inference('clc', [status(thm)], ['39', '40'])).
% 0.19/0.48  thf('42', plain,
% 0.19/0.48      ((((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 0.19/0.48        | ((sk_A) = (k1_xboole_0))
% 0.19/0.48        | ((k3_funct_2 @ sk_A @ sk_A @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.19/0.48            = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))))),
% 0.19/0.48      inference('sup-', [status(thm)], ['33', '41'])).
% 0.19/0.48  thf('43', plain,
% 0.19/0.48      ((((sk_C @ sk_B @ sk_A) = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A)))
% 0.19/0.48        | ((sk_A) = (k1_xboole_0))
% 0.19/0.48        | ((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 0.19/0.48        | ((sk_A) = (k1_xboole_0))
% 0.19/0.48        | ((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B))))),
% 0.19/0.48      inference('sup+', [status(thm)], ['32', '42'])).
% 0.19/0.48  thf('44', plain,
% 0.19/0.48      ((((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 0.19/0.48        | ((sk_A) = (k1_xboole_0))
% 0.19/0.48        | ((sk_C @ sk_B @ sk_A) = (k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))))),
% 0.19/0.48      inference('simplify', [status(thm)], ['43'])).
% 0.19/0.48  thf('45', plain,
% 0.19/0.48      ((((sk_A) = (k1_xboole_0)) | ((k1_relat_1 @ sk_B) = (sk_A)))),
% 0.19/0.48      inference('demod', [status(thm)], ['9', '12', '15'])).
% 0.19/0.48  thf('46', plain,
% 0.19/0.48      (![X2 : $i, X3 : $i]:
% 0.19/0.48         (((k1_relat_1 @ X3) != (X2))
% 0.19/0.48          | ((k1_funct_1 @ X3 @ (sk_C @ X3 @ X2)) != (sk_C @ X3 @ X2))
% 0.19/0.48          | ((X3) = (k6_relat_1 @ X2))
% 0.19/0.48          | ~ (v1_funct_1 @ X3)
% 0.19/0.48          | ~ (v1_relat_1 @ X3))),
% 0.19/0.48      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.19/0.48  thf('47', plain,
% 0.19/0.48      (![X3 : $i]:
% 0.19/0.48         (~ (v1_relat_1 @ X3)
% 0.19/0.48          | ~ (v1_funct_1 @ X3)
% 0.19/0.48          | ((X3) = (k6_relat_1 @ (k1_relat_1 @ X3)))
% 0.19/0.48          | ((k1_funct_1 @ X3 @ (sk_C @ X3 @ (k1_relat_1 @ X3)))
% 0.19/0.48              != (sk_C @ X3 @ (k1_relat_1 @ X3))))),
% 0.19/0.48      inference('simplify', [status(thm)], ['46'])).
% 0.19/0.48  thf('48', plain, (![X17 : $i]: ((k6_partfun1 @ X17) = (k6_relat_1 @ X17))),
% 0.19/0.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.19/0.48  thf('49', plain,
% 0.19/0.48      (![X3 : $i]:
% 0.19/0.48         (~ (v1_relat_1 @ X3)
% 0.19/0.48          | ~ (v1_funct_1 @ X3)
% 0.19/0.48          | ((X3) = (k6_partfun1 @ (k1_relat_1 @ X3)))
% 0.19/0.48          | ((k1_funct_1 @ X3 @ (sk_C @ X3 @ (k1_relat_1 @ X3)))
% 0.19/0.48              != (sk_C @ X3 @ (k1_relat_1 @ X3))))),
% 0.19/0.48      inference('demod', [status(thm)], ['47', '48'])).
% 0.19/0.48  thf('50', plain,
% 0.19/0.48      ((((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.19/0.48          != (sk_C @ sk_B @ (k1_relat_1 @ sk_B)))
% 0.19/0.48        | ((sk_A) = (k1_xboole_0))
% 0.19/0.48        | ((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 0.19/0.48        | ~ (v1_funct_1 @ sk_B)
% 0.19/0.48        | ~ (v1_relat_1 @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['45', '49'])).
% 0.19/0.48  thf('51', plain, ((v1_funct_1 @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('52', plain, ((v1_relat_1 @ sk_B)),
% 0.19/0.48      inference('sup-', [status(thm)], ['10', '11'])).
% 0.19/0.48  thf('53', plain,
% 0.19/0.48      ((((k1_funct_1 @ sk_B @ (sk_C @ sk_B @ sk_A))
% 0.19/0.48          != (sk_C @ sk_B @ (k1_relat_1 @ sk_B)))
% 0.19/0.48        | ((sk_A) = (k1_xboole_0))
% 0.19/0.48        | ((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B))))),
% 0.19/0.48      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.19/0.48  thf('54', plain,
% 0.19/0.48      ((((sk_C @ sk_B @ sk_A) != (sk_C @ sk_B @ (k1_relat_1 @ sk_B)))
% 0.19/0.48        | ((sk_A) = (k1_xboole_0))
% 0.19/0.48        | ((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 0.19/0.48        | ((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 0.19/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['44', '53'])).
% 0.19/0.48  thf('55', plain,
% 0.19/0.48      ((((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B)))
% 0.19/0.48        | ((sk_A) = (k1_xboole_0))
% 0.19/0.48        | ((sk_C @ sk_B @ sk_A) != (sk_C @ sk_B @ (k1_relat_1 @ sk_B))))),
% 0.19/0.48      inference('simplify', [status(thm)], ['54'])).
% 0.19/0.48  thf('56', plain,
% 0.19/0.48      ((((sk_A) = (k1_xboole_0)) | ((k1_relat_1 @ sk_B) = (sk_A)))),
% 0.19/0.48      inference('demod', [status(thm)], ['9', '12', '15'])).
% 0.19/0.48  thf('57', plain,
% 0.19/0.48      ((((sk_A) = (k1_xboole_0))
% 0.19/0.48        | ((sk_B) = (k6_partfun1 @ (k1_relat_1 @ sk_B))))),
% 0.19/0.48      inference('clc', [status(thm)], ['55', '56'])).
% 0.19/0.48  thf('58', plain,
% 0.19/0.48      ((((sk_B) = (k6_partfun1 @ sk_A))
% 0.19/0.48        | ((sk_A) = (k1_xboole_0))
% 0.19/0.48        | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup+', [status(thm)], ['16', '57'])).
% 0.19/0.48  thf('59', plain,
% 0.19/0.48      ((((sk_A) = (k1_xboole_0)) | ((sk_B) = (k6_partfun1 @ sk_A)))),
% 0.19/0.48      inference('simplify', [status(thm)], ['58'])).
% 0.19/0.48  thf('60', plain,
% 0.19/0.48      (~ (r2_funct_2 @ sk_A @ sk_A @ sk_B @ (k6_partfun1 @ sk_A))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('61', plain,
% 0.19/0.48      ((~ (r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B) | ((sk_A) = (k1_xboole_0)))),
% 0.19/0.48      inference('sup-', [status(thm)], ['59', '60'])).
% 0.19/0.48  thf('62', plain,
% 0.19/0.48      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf(redefinition_r2_funct_2, axiom,
% 0.19/0.48    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.48     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.19/0.48         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.19/0.48         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.19/0.48         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.19/0.48       ( ( r2_funct_2 @ A @ B @ C @ D ) <=> ( ( C ) = ( D ) ) ) ))).
% 0.19/0.48  thf('63', plain,
% 0.19/0.48      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.19/0.48         (~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.19/0.48          | ~ (v1_funct_2 @ X18 @ X19 @ X20)
% 0.19/0.48          | ~ (v1_funct_1 @ X18)
% 0.19/0.48          | ~ (v1_funct_1 @ X21)
% 0.19/0.48          | ~ (v1_funct_2 @ X21 @ X19 @ X20)
% 0.19/0.48          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20)))
% 0.19/0.48          | (r2_funct_2 @ X19 @ X20 @ X18 @ X21)
% 0.19/0.48          | ((X18) != (X21)))),
% 0.19/0.48      inference('cnf', [status(esa)], [redefinition_r2_funct_2])).
% 0.19/0.48  thf('64', plain,
% 0.19/0.48      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.19/0.48         ((r2_funct_2 @ X19 @ X20 @ X21 @ X21)
% 0.19/0.48          | ~ (v1_funct_1 @ X21)
% 0.19/0.48          | ~ (v1_funct_2 @ X21 @ X19 @ X20)
% 0.19/0.48          | ~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.19/0.48      inference('simplify', [status(thm)], ['63'])).
% 0.19/0.48  thf('65', plain,
% 0.19/0.48      ((~ (v1_funct_2 @ sk_B @ sk_A @ sk_A)
% 0.19/0.48        | ~ (v1_funct_1 @ sk_B)
% 0.19/0.48        | (r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B))),
% 0.19/0.48      inference('sup-', [status(thm)], ['62', '64'])).
% 0.19/0.48  thf('66', plain, ((v1_funct_2 @ sk_B @ sk_A @ sk_A)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('67', plain, ((v1_funct_1 @ sk_B)),
% 0.19/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.48  thf('68', plain, ((r2_funct_2 @ sk_A @ sk_A @ sk_B @ sk_B)),
% 0.19/0.48      inference('demod', [status(thm)], ['65', '66', '67'])).
% 0.19/0.48  thf('69', plain, (((sk_A) = (k1_xboole_0))),
% 0.19/0.48      inference('demod', [status(thm)], ['61', '68'])).
% 0.19/0.48  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.19/0.48  thf('70', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.19/0.48      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.19/0.48  thf('71', plain, ($false),
% 0.19/0.48      inference('demod', [status(thm)], ['0', '69', '70'])).
% 0.19/0.48  
% 0.19/0.48  % SZS output end Refutation
% 0.19/0.48  
% 0.19/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
