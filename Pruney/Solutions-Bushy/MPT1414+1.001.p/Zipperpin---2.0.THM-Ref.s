%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1414+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.n7nRNFYPjp

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  241 ( 852 expanded)
%              Number of leaves         :   44 ( 267 expanded)
%              Depth                    :   19
%              Number of atoms          : 2465 (18232 expanded)
%              Number of equality atoms :   23 (  72 expanded)
%              Maximal formula depth    :   20 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_eqrel_1_type,type,(
    m1_eqrel_1: $i > $i > $o )).

thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(v3_relat_2_type,type,(
    v3_relat_2: $i > $o )).

thf(r3_binop_1_type,type,(
    r3_binop_1: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m2_subset_1_type,type,(
    m2_subset_1: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_binop_1_type,type,(
    r2_binop_1: $i > $i > $i > $o )).

thf(k3_filter_1_type,type,(
    k3_filter_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k9_eqrel_1_type,type,(
    k9_eqrel_1: $i > $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(m2_filter_1_type,type,(
    m2_filter_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k7_eqrel_1_type,type,(
    k7_eqrel_1: $i > $i > $i )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k8_eqrel_1_type,type,(
    k8_eqrel_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_binop_1_type,type,(
    r1_binop_1: $i > $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t8_filter_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ( v1_partfun1 @ B @ A )
            & ( v3_relat_2 @ B )
            & ( v8_relat_2 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ! [D: $i] :
                  ( ( m2_filter_1 @ D @ A @ B )
                 => ( ( r3_binop_1 @ A @ C @ D )
                   => ( r3_binop_1 @ ( k8_eqrel_1 @ A @ B ) @ ( k9_eqrel_1 @ A @ B @ C ) @ ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ( ( v1_partfun1 @ B @ A )
              & ( v3_relat_2 @ B )
              & ( v8_relat_2 @ B )
              & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ A )
               => ! [D: $i] :
                    ( ( m2_filter_1 @ D @ A @ B )
                   => ( ( r3_binop_1 @ A @ C @ D )
                     => ( r3_binop_1 @ ( k8_eqrel_1 @ A @ B ) @ ( k9_eqrel_1 @ A @ B @ C ) @ ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t8_filter_1])).

thf('0',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_eqrel_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_relat_2 @ B )
        & ( v8_relat_2 @ B )
        & ( v1_partfun1 @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( m1_eqrel_1 @ ( k8_eqrel_1 @ A @ B ) @ A ) ) )).

thf('1',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_eqrel_1 @ ( k8_eqrel_1 @ X13 @ X14 ) @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X13 ) ) )
      | ~ ( v1_partfun1 @ X14 @ X13 )
      | ~ ( v8_relat_2 @ X14 )
      | ~ ( v3_relat_2 @ X14 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_eqrel_1])).

thf('2',plain,
    ( ~ ( v3_relat_2 @ sk_B_1 )
    | ~ ( v8_relat_2 @ sk_B_1 )
    | ~ ( v1_partfun1 @ sk_B_1 @ sk_A )
    | ( m1_eqrel_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    v3_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    v8_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_partfun1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_eqrel_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['2','3','4','5'])).

thf(cc1_eqrel_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_eqrel_1 @ B @ A )
         => ~ ( v1_xboole_0 @ B ) ) ) )).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_eqrel_1 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_eqrel_1])).

thf('8',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    ~ ( v1_xboole_0 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k8_eqrel_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_relat_2 @ B )
        & ( v8_relat_2 @ B )
        & ( v1_partfun1 @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k8_eqrel_1 @ A @ B )
        = ( k7_eqrel_1 @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X22: $i,X23: $i] :
      ( ( ( k8_eqrel_1 @ X22 @ X23 )
        = ( k7_eqrel_1 @ X22 @ X23 ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) )
      | ~ ( v1_partfun1 @ X23 @ X22 )
      | ~ ( v8_relat_2 @ X23 )
      | ~ ( v3_relat_2 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_eqrel_1])).

thf('13',plain,
    ( ~ ( v3_relat_2 @ sk_B_1 )
    | ~ ( v8_relat_2 @ sk_B_1 )
    | ~ ( v1_partfun1 @ sk_B_1 @ sk_A )
    | ( ( k8_eqrel_1 @ sk_A @ sk_B_1 )
      = ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v3_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v8_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    v1_partfun1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B_1 )
    = ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('18',plain,(
    ~ ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['10','17'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('19',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( sk_B @ X21 ) @ X21 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r2_hidden @ X31 @ X32 )
      | ( v1_xboole_0 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_eqrel_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_relat_2 @ B )
        & ( v8_relat_2 @ B )
        & ( v1_partfun1 @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( m1_subset_1 @ ( k7_eqrel_1 @ A @ B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('23',plain,(
    ! [X11: $i,X12: $i] :
      ( ( m1_subset_1 @ ( k7_eqrel_1 @ X11 @ X12 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X11 ) ) )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X11 ) ) )
      | ~ ( v1_partfun1 @ X12 @ X11 )
      | ~ ( v8_relat_2 @ X12 )
      | ~ ( v3_relat_2 @ X12 ) ) ),
    inference(cnf,[status(esa)],[dt_k7_eqrel_1])).

thf('24',plain,
    ( ~ ( v3_relat_2 @ sk_B_1 )
    | ~ ( v8_relat_2 @ sk_B_1 )
    | ~ ( v1_partfun1 @ sk_B_1 @ sk_A )
    | ( m1_subset_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v3_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v8_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_partfun1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('29',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( r2_hidden @ X33 @ X34 )
      | ~ ( v1_xboole_0 @ X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_eqrel_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v3_relat_2 @ B )
        & ( v8_relat_2 @ B )
        & ( v1_partfun1 @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
        & ( m1_subset_1 @ C @ A ) )
     => ( m2_subset_1 @ ( k9_eqrel_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) @ ( k8_eqrel_1 @ A @ B ) ) ) )).

thf('33',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X16 ) ) )
      | ~ ( v1_partfun1 @ X15 @ X16 )
      | ~ ( v8_relat_2 @ X15 )
      | ~ ( v3_relat_2 @ X15 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X17 @ X16 )
      | ( m2_subset_1 @ ( k9_eqrel_1 @ X16 @ X15 @ X17 ) @ ( k1_zfmisc_1 @ X16 ) @ ( k8_eqrel_1 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_eqrel_1])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( m2_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v3_relat_2 @ sk_B_1 )
      | ~ ( v8_relat_2 @ sk_B_1 )
      | ~ ( v1_partfun1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B_1 )
    = ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('36',plain,(
    v3_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v8_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_partfun1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( m2_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['34','35','36','37','38'])).

thf('40',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( m2_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,(
    m2_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_eqrel_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v3_relat_2 @ B )
        & ( v8_relat_2 @ B )
        & ( v1_partfun1 @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
        & ( m1_subset_1 @ C @ A ) )
     => ( ( k9_eqrel_1 @ A @ B @ C )
        = ( k11_relat_1 @ B @ C ) ) ) )).

thf('45',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) ) )
      | ~ ( v1_partfun1 @ X24 @ X25 )
      | ~ ( v8_relat_2 @ X24 )
      | ~ ( v3_relat_2 @ X24 )
      | ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X26 @ X25 )
      | ( ( k9_eqrel_1 @ X25 @ X24 @ X26 )
        = ( k11_relat_1 @ X24 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_eqrel_1])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k9_eqrel_1 @ sk_A @ sk_B_1 @ X0 )
        = ( k11_relat_1 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v3_relat_2 @ sk_B_1 )
      | ~ ( v8_relat_2 @ sk_B_1 )
      | ~ ( v1_partfun1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v3_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    v8_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_partfun1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( ( k9_eqrel_1 @ sk_A @ sk_B_1 @ X0 )
        = ( k11_relat_1 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['46','47','48','49'])).

thf('51',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k9_eqrel_1 @ sk_A @ sk_B_1 @ X0 )
        = ( k11_relat_1 @ sk_B_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k9_eqrel_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k11_relat_1 @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','52'])).

thf('54',plain,(
    m2_subset_1 @ ( k11_relat_1 @ sk_B_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['42','53'])).

thf('55',plain,(
    m1_subset_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26','27'])).

thf(redefinition_m2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m2_subset_1 @ C @ A @ B )
        <=> ( m1_subset_1 @ C @ B ) ) ) )).

thf('56',plain,(
    ! [X27: $i,X28: $i,X30: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X27 ) )
      | ( m1_subset_1 @ X30 @ X28 )
      | ~ ( m2_subset_1 @ X30 @ X27 @ X28 ) ) ),
    inference(cnf,[status(esa)],[redefinition_m2_subset_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ~ ( m2_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ( m1_subset_1 @ X0 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) )
    | ( m1_subset_1 @ ( k11_relat_1 @ sk_B_1 @ sk_C ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['54','57'])).

thf('59',plain,(
    ~ ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['10','17'])).

thf('60',plain,
    ( ( m1_subset_1 @ ( k11_relat_1 @ sk_B_1 @ sk_C ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    r3_binop_1 @ sk_A @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m2_filter_1 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_m2_filter_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_relat_1 @ B ) )
     => ! [C: $i] :
          ( ( m2_filter_1 @ C @ A @ B )
         => ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) ) ) ) )).

thf('63',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( v1_relat_1 @ X19 )
      | ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) @ X18 ) ) )
      | ~ ( m2_filter_1 @ X20 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_filter_1])).

thf('64',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('66',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('67',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['64','67'])).

thf('69',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf(d7_binop_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ B @ A )
     => ! [C: $i] :
          ( ( ( v1_funct_1 @ C )
            & ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A )
            & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) )
         => ( ( r3_binop_1 @ A @ B @ C )
          <=> ( ( r1_binop_1 @ A @ B @ C )
              & ( r2_binop_1 @ A @ B @ C ) ) ) ) ) )).

thf('71',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_funct_2 @ X5 @ ( k2_zfmisc_1 @ X6 @ X6 ) @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X6 ) @ X6 ) ) )
      | ~ ( r3_binop_1 @ X6 @ X7 @ X5 )
      | ( r2_binop_1 @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d7_binop_1])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r2_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( r3_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    m2_filter_1 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( v1_relat_1 @ X19 )
      | ( v1_funct_2 @ X20 @ ( k2_zfmisc_1 @ X18 @ X18 ) @ X18 )
      | ~ ( m2_filter_1 @ X20 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_filter_1])).

thf('75',plain,
    ( ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('77',plain,
    ( ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    m2_filter_1 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( v1_relat_1 @ X19 )
      | ( v1_funct_1 @ X20 )
      | ~ ( m2_filter_1 @ X20 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_filter_1])).

thf('82',plain,
    ( ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('84',plain,
    ( ( v1_funct_1 @ sk_D )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['82','83'])).

thf('85',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r2_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( r3_binop_1 @ sk_A @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['72','79','86'])).

thf('88',plain,
    ( ( r2_binop_1 @ sk_A @ sk_C @ sk_D )
    | ~ ( m1_subset_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['61','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    r2_binop_1 @ sk_A @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['88','89'])).

thf('91',plain,(
    m2_filter_1 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t7_filter_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ( v1_partfun1 @ B @ A )
            & ( v3_relat_2 @ B )
            & ( v8_relat_2 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ! [D: $i] :
                  ( ( m2_filter_1 @ D @ A @ B )
                 => ( ( r2_binop_1 @ A @ C @ D )
                   => ( r2_binop_1 @ ( k8_eqrel_1 @ A @ B ) @ ( k9_eqrel_1 @ A @ B @ C ) @ ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) )).

thf('93',plain,(
    ! [X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( v1_partfun1 @ X40 @ X41 )
      | ~ ( v3_relat_2 @ X40 )
      | ~ ( v8_relat_2 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X41 ) ) )
      | ~ ( m2_filter_1 @ X42 @ X41 @ X40 )
      | ( r2_binop_1 @ ( k8_eqrel_1 @ X41 @ X40 ) @ ( k9_eqrel_1 @ X41 @ X40 @ X43 ) @ ( k3_filter_1 @ X41 @ X40 @ X42 ) )
      | ~ ( r2_binop_1 @ X41 @ X43 @ X42 )
      | ~ ( m1_subset_1 @ X43 @ X41 )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t7_filter_1])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r2_binop_1 @ sk_A @ X0 @ X1 )
      | ( r2_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B_1 @ X1 ) )
      | ~ ( m2_filter_1 @ X1 @ sk_A @ sk_B_1 )
      | ~ ( v8_relat_2 @ sk_B_1 )
      | ~ ( v3_relat_2 @ sk_B_1 )
      | ~ ( v1_partfun1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B_1 )
    = ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('96',plain,(
    v8_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    v3_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_partfun1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r2_binop_1 @ sk_A @ X0 @ X1 )
      | ( r2_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B_1 @ X1 ) )
      | ~ ( m2_filter_1 @ X1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['94','95','96','97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( r2_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) )
      | ~ ( r2_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['91','99'])).

thf('101',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r2_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['90','100'])).

thf('102',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,
    ( ( k9_eqrel_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k11_relat_1 @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','52'])).

thf('104',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['101','102','103'])).

thf('105',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    r2_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf(dt_k3_filter_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_partfun1 @ B @ A )
        & ( v3_relat_2 @ B )
        & ( v8_relat_2 @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) )
     => ( ( v1_funct_1 @ ( k3_filter_1 @ A @ B @ C ) )
        & ( v1_funct_2 @ ( k3_filter_1 @ A @ B @ C ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ A @ B ) @ ( k8_eqrel_1 @ A @ B ) ) @ ( k8_eqrel_1 @ A @ B ) )
        & ( m1_subset_1 @ ( k3_filter_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ A @ B ) @ ( k8_eqrel_1 @ A @ B ) ) @ ( k8_eqrel_1 @ A @ B ) ) ) ) ) ) )).

thf('109',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X9 ) ) )
      | ~ ( v8_relat_2 @ X8 )
      | ~ ( v3_relat_2 @ X8 )
      | ~ ( v1_partfun1 @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_funct_2 @ X10 @ ( k2_zfmisc_1 @ X9 @ X9 ) @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X9 ) @ X9 ) ) )
      | ( m1_subset_1 @ ( k3_filter_1 @ X9 @ X8 @ X10 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ X9 @ X8 ) @ ( k8_eqrel_1 @ X9 @ X8 ) ) @ ( k8_eqrel_1 @ X9 @ X8 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_filter_1])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['77','78'])).

thf('112',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['84','85'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,
    ( ~ ( v8_relat_2 @ sk_B_1 )
    | ~ ( v3_relat_2 @ sk_B_1 )
    | ~ ( v1_partfun1 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['107','113'])).

thf('115',plain,(
    v8_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v3_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    v1_partfun1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B_1 )
    = ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('119',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B_1 )
    = ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('120',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B_1 )
    = ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('121',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['114','115','116','117','118','119','120'])).

thf('122',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    m1_subset_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['121','122'])).

thf('124',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_funct_2 @ X5 @ ( k2_zfmisc_1 @ X6 @ X6 ) @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X6 ) @ X6 ) ) )
      | ~ ( r1_binop_1 @ X6 @ X7 @ X5 )
      | ~ ( r2_binop_1 @ X6 @ X7 @ X5 )
      | ( r3_binop_1 @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d7_binop_1])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ( r3_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) )
      | ~ ( r2_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) )
      | ~ ( r1_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) )
      | ~ ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) @ ( k2_zfmisc_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('128',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X9 ) ) )
      | ~ ( v8_relat_2 @ X8 )
      | ~ ( v3_relat_2 @ X8 )
      | ~ ( v1_partfun1 @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_funct_2 @ X10 @ ( k2_zfmisc_1 @ X9 @ X9 ) @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X9 ) @ X9 ) ) )
      | ( v1_funct_2 @ ( k3_filter_1 @ X9 @ X8 @ X10 ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ X9 @ X8 ) @ ( k8_eqrel_1 @ X9 @ X8 ) ) @ ( k8_eqrel_1 @ X9 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_filter_1])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['127','128'])).

thf('130',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['77','78'])).

thf('131',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['84','85'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['129','130','131'])).

thf('133',plain,
    ( ~ ( v8_relat_2 @ sk_B_1 )
    | ~ ( v3_relat_2 @ sk_B_1 )
    | ~ ( v1_partfun1 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['126','132'])).

thf('134',plain,(
    v8_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v3_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v1_partfun1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B_1 )
    = ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('138',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B_1 )
    = ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('139',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B_1 )
    = ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('140',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) @ ( k2_zfmisc_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['133','134','135','136','137','138','139'])).

thf('141',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) @ ( k2_zfmisc_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['140','141'])).

thf('143',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('145',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X9 ) ) )
      | ~ ( v8_relat_2 @ X8 )
      | ~ ( v3_relat_2 @ X8 )
      | ~ ( v1_partfun1 @ X8 @ X9 )
      | ( v1_xboole_0 @ X9 )
      | ~ ( v1_funct_1 @ X10 )
      | ~ ( v1_funct_2 @ X10 @ ( k2_zfmisc_1 @ X9 @ X9 ) @ X9 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X9 ) @ X9 ) ) )
      | ( v1_funct_1 @ ( k3_filter_1 @ X9 @ X8 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_filter_1])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['77','78'])).

thf('148',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['84','85'])).

thf('149',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['146','147','148'])).

thf('150',plain,
    ( ~ ( v8_relat_2 @ sk_B_1 )
    | ~ ( v3_relat_2 @ sk_B_1 )
    | ~ ( v1_partfun1 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['143','149'])).

thf('151',plain,(
    v8_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    v3_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v1_partfun1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['150','151','152','153'])).

thf('155',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) ),
    inference(clc,[status(thm)],['154','155'])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ( r3_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) )
      | ~ ( r2_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) )
      | ~ ( r1_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['125','142','156'])).

thf('158',plain,
    ( ~ ( r1_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) )
    | ( r3_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) )
    | ~ ( m1_subset_1 @ ( k11_relat_1 @ sk_B_1 @ sk_C ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['106','157'])).

thf('159',plain,(
    r3_binop_1 @ sk_A @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('161',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_funct_2 @ X5 @ ( k2_zfmisc_1 @ X6 @ X6 ) @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X6 ) @ X6 ) ) )
      | ~ ( r3_binop_1 @ X6 @ X7 @ X5 )
      | ( r1_binop_1 @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d7_binop_1])).

thf('162',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r1_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( r3_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['77','78'])).

thf('164',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['84','85'])).

thf('165',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r1_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( r3_binop_1 @ sk_A @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['162','163','164'])).

thf('166',plain,
    ( ( r1_binop_1 @ sk_A @ sk_C @ sk_D )
    | ~ ( m1_subset_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['159','165'])).

thf('167',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    r1_binop_1 @ sk_A @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['166','167'])).

thf('169',plain,(
    m2_filter_1 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t6_filter_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ( v1_partfun1 @ B @ A )
            & ( v3_relat_2 @ B )
            & ( v8_relat_2 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ! [D: $i] :
                  ( ( m2_filter_1 @ D @ A @ B )
                 => ( ( r1_binop_1 @ A @ C @ D )
                   => ( r1_binop_1 @ ( k8_eqrel_1 @ A @ B ) @ ( k9_eqrel_1 @ A @ B @ C ) @ ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) )).

thf('171',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( v1_partfun1 @ X36 @ X37 )
      | ~ ( v3_relat_2 @ X36 )
      | ~ ( v8_relat_2 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X37 ) ) )
      | ~ ( m2_filter_1 @ X38 @ X37 @ X36 )
      | ( r1_binop_1 @ ( k8_eqrel_1 @ X37 @ X36 ) @ ( k9_eqrel_1 @ X37 @ X36 @ X39 ) @ ( k3_filter_1 @ X37 @ X36 @ X38 ) )
      | ~ ( r1_binop_1 @ X37 @ X39 @ X38 )
      | ~ ( m1_subset_1 @ X39 @ X37 )
      | ( v1_xboole_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t6_filter_1])).

thf('172',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r1_binop_1 @ sk_A @ X0 @ X1 )
      | ( r1_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B_1 @ X1 ) )
      | ~ ( m2_filter_1 @ X1 @ sk_A @ sk_B_1 )
      | ~ ( v8_relat_2 @ sk_B_1 )
      | ~ ( v3_relat_2 @ sk_B_1 )
      | ~ ( v1_partfun1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B_1 )
    = ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('174',plain,(
    v8_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v3_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v1_partfun1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r1_binop_1 @ sk_A @ X0 @ X1 )
      | ( r1_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B_1 @ X1 ) )
      | ~ ( m2_filter_1 @ X1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['172','173','174','175','176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( r1_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) )
      | ~ ( r1_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['169','177'])).

thf('179',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r1_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['168','178'])).

thf('180',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( k9_eqrel_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k11_relat_1 @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','52'])).

thf('182',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r1_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['179','180','181'])).

thf('183',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    r1_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) ),
    inference(clc,[status(thm)],['182','183'])).

thf('185',plain,
    ( ( r3_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) )
    | ~ ( m1_subset_1 @ ( k11_relat_1 @ sk_B_1 @ sk_C ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['158','184'])).

thf('186',plain,(
    ~ ( r3_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B_1 )
    = ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('188',plain,(
    ~ ( r3_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,
    ( ( k9_eqrel_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k11_relat_1 @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['43','52'])).

thf('190',plain,(
    ~ ( r3_binop_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,(
    ~ ( m1_subset_1 @ ( k11_relat_1 @ sk_B_1 @ sk_C ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['185','190'])).

thf('192',plain,(
    v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','191'])).

thf('193',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['30','192'])).

thf('194',plain,(
    v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['21','193'])).

thf('195',plain,(
    $false ),
    inference(demod,[status(thm)],['18','194'])).


%------------------------------------------------------------------------------
