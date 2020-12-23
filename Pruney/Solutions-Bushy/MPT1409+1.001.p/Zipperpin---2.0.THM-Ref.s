%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1409+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.TRBtNhT3Gc

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:38 EST 2020

% Result     : Theorem 0.48s
% Output     : Refutation 0.48s
% Verified   : 
% Statistics : Number of formulae       :  276 (1148 expanded)
%              Number of leaves         :   48 ( 359 expanded)
%              Depth                    :   22
%              Number of atoms          : 3077 (30310 expanded)
%              Number of equality atoms :   59 ( 609 expanded)
%              Maximal formula depth    :   31 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k11_relat_1_type,type,(
    k11_relat_1: $i > $i > $i )).

thf(m2_filter_1_type,type,(
    m2_filter_1: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_eqrel_1_type,type,(
    m1_eqrel_1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v3_relat_2_type,type,(
    v3_relat_2: $i > $o )).

thf(sk_E_1_type,type,(
    sk_E_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(k8_eqrel_1_type,type,(
    k8_eqrel_1: $i > $i > $i )).

thf(k7_eqrel_1_type,type,(
    k7_eqrel_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_eqrel_1_type,type,(
    k6_eqrel_1: $i > $i > $i > $i > $i )).

thf(k1_binop_1_type,type,(
    k1_binop_1: $i > $i > $i > $i )).

thf(k3_filter_1_type,type,(
    k3_filter_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k9_eqrel_1_type,type,(
    k9_eqrel_1: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_binop_1_type,type,(
    k4_binop_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m2_subset_1_type,type,(
    m2_subset_1: $i > $i > $i > $o )).

thf(v1_relat_2_type,type,(
    v1_relat_2: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t3_filter_1,conjecture,(
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
                  ( ( m1_subset_1 @ D @ A )
                 => ! [E: $i] :
                      ( ( m2_filter_1 @ E @ A @ B )
                     => ( ( k1_binop_1 @ ( k3_filter_1 @ A @ B @ E ) @ ( k6_eqrel_1 @ A @ A @ B @ C ) @ ( k6_eqrel_1 @ A @ A @ B @ D ) )
                        = ( k6_eqrel_1 @ A @ A @ B @ ( k4_binop_1 @ A @ E @ C @ D ) ) ) ) ) ) ) ) )).

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
                    ( ( m1_subset_1 @ D @ A )
                   => ! [E: $i] :
                        ( ( m2_filter_1 @ E @ A @ B )
                       => ( ( k1_binop_1 @ ( k3_filter_1 @ A @ B @ E ) @ ( k6_eqrel_1 @ A @ A @ B @ C ) @ ( k6_eqrel_1 @ A @ A @ B @ D ) )
                          = ( k6_eqrel_1 @ A @ A @ B @ ( k4_binop_1 @ A @ E @ C @ D ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t3_filter_1])).

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
    ! [X19: $i,X20: $i] :
      ( ( m1_eqrel_1 @ ( k8_eqrel_1 @ X19 @ X20 ) @ X19 )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X19 ) ) )
      | ~ ( v1_partfun1 @ X20 @ X19 )
      | ~ ( v8_relat_2 @ X20 )
      | ~ ( v3_relat_2 @ X20 ) ) ),
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
    ! [X36: $i,X37: $i] :
      ( ( ( k8_eqrel_1 @ X36 @ X37 )
        = ( k7_eqrel_1 @ X36 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) )
      | ~ ( v1_partfun1 @ X37 @ X36 )
      | ~ ( v8_relat_2 @ X37 )
      | ~ ( v3_relat_2 @ X37 ) ) ),
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
    ! [X27: $i] :
      ( m1_subset_1 @ ( sk_B @ X27 ) @ X27 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('20',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r2_hidden @ X48 @ X49 )
      | ( v1_xboole_0 @ X49 )
      | ~ ( m1_subset_1 @ X48 @ X49 ) ) ),
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
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ ( k7_eqrel_1 @ X17 @ X18 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X17 ) ) )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X17 ) ) )
      | ~ ( v1_partfun1 @ X18 @ X17 )
      | ~ ( v8_relat_2 @ X18 )
      | ~ ( v3_relat_2 @ X18 ) ) ),
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
    ! [X50: $i,X51: $i,X52: $i] :
      ( ~ ( r2_hidden @ X50 @ X51 )
      | ~ ( v1_xboole_0 @ X52 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ X52 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r2_hidden @ X48 @ X49 )
      | ( v1_xboole_0 @ X49 )
      | ~ ( m1_subset_1 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('33',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    r2_hidden @ sk_D @ sk_A ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t28_eqrel_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_2 @ B )
        & ( v3_relat_2 @ B )
        & ( v1_partfun1 @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ ( k6_eqrel_1 @ A @ A @ B @ C ) ) ) ) )).

thf('37',plain,(
    ! [X45: $i,X46: $i,X47: $i] :
      ( ~ ( r2_hidden @ X45 @ X46 )
      | ( r2_hidden @ X45 @ ( k6_eqrel_1 @ X46 @ X46 @ X47 @ X45 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X46 ) ) )
      | ~ ( v1_partfun1 @ X47 @ X46 )
      | ~ ( v3_relat_2 @ X47 )
      | ~ ( v1_relat_2 @ X47 ) ) ),
    inference(cnf,[status(esa)],[t28_eqrel_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_2 @ sk_B_1 )
      | ~ ( v3_relat_2 @ sk_B_1 )
      | ~ ( v1_partfun1 @ sk_B_1 @ sk_A )
      | ( r2_hidden @ X0 @ ( k6_eqrel_1 @ sk_A @ sk_A @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf('39',plain,(
    v3_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc3_partfun1,axiom,(
    ! [A: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v3_relat_2 @ A )
        & ( v8_relat_2 @ A ) )
     => ( ( v1_relat_1 @ A )
        & ( v1_relat_2 @ A ) ) ) )).

thf('40',plain,(
    ! [X5: $i] :
      ( ( v1_relat_2 @ X5 )
      | ~ ( v8_relat_2 @ X5 )
      | ~ ( v3_relat_2 @ X5 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[cc3_partfun1])).

thf('41',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v8_relat_2 @ sk_B_1 )
    | ( v1_relat_2 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v8_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ( v1_relat_2 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('45',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('46',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_relat_2 @ sk_B_1 ),
    inference(demod,[status(thm)],['43','46'])).

thf('48',plain,(
    v3_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_partfun1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_eqrel_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k6_eqrel_1 @ A @ B @ C @ D )
        = ( k11_relat_1 @ C @ D ) ) ) )).

thf('51',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k6_eqrel_1 @ X33 @ X34 @ X32 @ X35 )
        = ( k11_relat_1 @ X32 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_eqrel_1])).

thf('52',plain,(
    ! [X0: $i] :
      ( ( k6_eqrel_1 @ sk_A @ sk_A @ sk_B_1 @ X0 )
      = ( k11_relat_1 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k11_relat_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','47','48','49','52'])).

thf('54',plain,(
    r2_hidden @ sk_D @ ( k11_relat_1 @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['35','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
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

thf('57',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X22 ) ) )
      | ~ ( v1_partfun1 @ X21 @ X22 )
      | ~ ( v8_relat_2 @ X21 )
      | ~ ( v3_relat_2 @ X21 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X23 @ X22 )
      | ( m2_subset_1 @ ( k9_eqrel_1 @ X22 @ X21 @ X23 ) @ ( k1_zfmisc_1 @ X22 ) @ ( k8_eqrel_1 @ X22 @ X21 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_eqrel_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( m2_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v3_relat_2 @ sk_B_1 )
      | ~ ( v8_relat_2 @ sk_B_1 )
      | ~ ( v1_partfun1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B_1 )
    = ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('60',plain,(
    v3_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v8_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_partfun1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( m2_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['58','59','60','61','62'])).

thf('64',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( m2_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('66',plain,(
    m2_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ sk_D ) @ ( k1_zfmisc_1 @ sk_A ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['55','65'])).

thf('67',plain,(
    m1_subset_1 @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
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

thf('69',plain,(
    ! [X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X39 ) ) )
      | ~ ( v1_partfun1 @ X38 @ X39 )
      | ~ ( v8_relat_2 @ X38 )
      | ~ ( v3_relat_2 @ X38 )
      | ( v1_xboole_0 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ X39 )
      | ( ( k9_eqrel_1 @ X39 @ X38 @ X40 )
        = ( k11_relat_1 @ X38 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_eqrel_1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( ( k9_eqrel_1 @ sk_A @ sk_B_1 @ X0 )
        = ( k11_relat_1 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v3_relat_2 @ sk_B_1 )
      | ~ ( v8_relat_2 @ sk_B_1 )
      | ~ ( v1_partfun1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v3_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v8_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_partfun1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( ( k9_eqrel_1 @ sk_A @ sk_B_1 @ X0 )
        = ( k11_relat_1 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k9_eqrel_1 @ sk_A @ sk_B_1 @ X0 )
        = ( k11_relat_1 @ sk_B_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( k9_eqrel_1 @ sk_A @ sk_B_1 @ sk_D )
    = ( k11_relat_1 @ sk_B_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['67','76'])).

thf('78',plain,(
    m2_subset_1 @ ( k11_relat_1 @ sk_B_1 @ sk_D ) @ ( k1_zfmisc_1 @ sk_A ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['66','77'])).

thf('79',plain,(
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

thf('80',plain,(
    ! [X41: $i,X42: $i,X44: $i] :
      ( ( v1_xboole_0 @ X41 )
      | ( v1_xboole_0 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X41 ) )
      | ( m1_subset_1 @ X44 @ X42 )
      | ~ ( m2_subset_1 @ X44 @ X41 @ X42 ) ) ),
    inference(cnf,[status(esa)],[redefinition_m2_subset_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( m2_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ( m1_subset_1 @ X0 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) )
    | ( m1_subset_1 @ ( k11_relat_1 @ sk_B_1 @ sk_D ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['78','81'])).

thf('83',plain,(
    ~ ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['10','17'])).

thf('84',plain,
    ( ( m1_subset_1 @ ( k11_relat_1 @ sk_B_1 @ sk_D ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['82','83'])).

thf('85',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r2_hidden @ X48 @ X49 )
      | ( v1_xboole_0 @ X49 )
      | ~ ( m1_subset_1 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('86',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ ( k11_relat_1 @ sk_B_1 @ sk_D ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ~ ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['10','17'])).

thf('88',plain,
    ( ( r2_hidden @ ( k11_relat_1 @ sk_B_1 @ sk_D ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['86','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r2_hidden @ X48 @ X49 )
      | ( v1_xboole_0 @ X49 )
      | ~ ( m1_subset_1 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('91',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_hidden @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    r2_hidden @ sk_C @ sk_A ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k11_relat_1 @ sk_B_1 @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['38','47','48','49','52'])).

thf('95',plain,(
    r2_hidden @ sk_C @ ( k11_relat_1 @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( m2_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['63','64'])).

thf('98',plain,(
    m2_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k9_eqrel_1 @ sk_A @ sk_B_1 @ X0 )
        = ( k11_relat_1 @ sk_B_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('101',plain,
    ( ( k9_eqrel_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k11_relat_1 @ sk_B_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['99','100'])).

thf('102',plain,(
    m2_subset_1 @ ( k11_relat_1 @ sk_B_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['98','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ~ ( m2_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ( m1_subset_1 @ X0 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('104',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) )
    | ( m1_subset_1 @ ( k11_relat_1 @ sk_B_1 @ sk_C ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ~ ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['10','17'])).

thf('106',plain,
    ( ( m1_subset_1 @ ( k11_relat_1 @ sk_B_1 @ sk_C ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['104','105'])).

thf('107',plain,(
    ! [X48: $i,X49: $i] :
      ( ( r2_hidden @ X48 @ X49 )
      | ( v1_xboole_0 @ X49 )
      | ~ ( m1_subset_1 @ X48 @ X49 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('108',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) )
    | ( r2_hidden @ ( k11_relat_1 @ sk_B_1 @ sk_C ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,(
    ~ ( v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['10','17'])).

thf('110',plain,
    ( ( r2_hidden @ ( k11_relat_1 @ sk_B_1 @ sk_C ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['108','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    m2_filter_1 @ sk_E_1 @ sk_A @ sk_B_1 ),
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

thf('113',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ~ ( v1_relat_1 @ X25 )
      | ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X24 ) @ X24 ) ) )
      | ~ ( m2_filter_1 @ X26 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_filter_1])).

thf('114',plain,
    ( ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['44','45'])).

thf('116',plain,
    ( ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['114','115'])).

thf('117',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['116','117'])).

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

thf('119',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) )
      | ~ ( v8_relat_2 @ X14 )
      | ~ ( v3_relat_2 @ X14 )
      | ~ ( v1_partfun1 @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_2 @ X16 @ ( k2_zfmisc_1 @ X15 @ X15 ) @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) @ X15 ) ) )
      | ( m1_subset_1 @ ( k3_filter_1 @ X15 @ X14 @ X16 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ X15 @ X14 ) @ ( k8_eqrel_1 @ X15 @ X14 ) ) @ ( k8_eqrel_1 @ X15 @ X14 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_filter_1])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_E_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    m2_filter_1 @ sk_E_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ~ ( v1_relat_1 @ X25 )
      | ( v1_funct_2 @ X26 @ ( k2_zfmisc_1 @ X24 @ X24 ) @ X24 )
      | ~ ( m2_filter_1 @ X26 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_filter_1])).

thf('123',plain,
    ( ( v1_funct_2 @ sk_E_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['44','45'])).

thf('125',plain,
    ( ( v1_funct_2 @ sk_E_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v1_funct_2 @ sk_E_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['125','126'])).

thf('128',plain,(
    m2_filter_1 @ sk_E_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ~ ( v1_relat_1 @ X25 )
      | ( v1_funct_1 @ X26 )
      | ~ ( m2_filter_1 @ X26 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_filter_1])).

thf('130',plain,
    ( ( v1_funct_1 @ sk_E_1 )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['44','45'])).

thf('132',plain,
    ( ( v1_funct_1 @ sk_E_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['130','131'])).

thf('133',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(clc,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['120','127','134'])).

thf('136',plain,
    ( ~ ( v8_relat_2 @ sk_B_1 )
    | ~ ( v3_relat_2 @ sk_B_1 )
    | ~ ( v1_partfun1 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['111','135'])).

thf('137',plain,(
    v8_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v3_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,(
    v1_partfun1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B_1 )
    = ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('141',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B_1 )
    = ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('142',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B_1 )
    = ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('143',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['136','137','138','139','140','141','142'])).

thf('144',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    m1_subset_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_E_1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['143','144'])).

thf('146',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B_1 )
    = ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf(d4_filter_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( ( v1_partfun1 @ B @ A )
            & ( v3_relat_2 @ B )
            & ( v8_relat_2 @ B )
            & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) )
             => ( ( m2_filter_1 @ C @ A @ B )
               => ! [D: $i] :
                    ( ( ( v1_funct_1 @ D )
                      & ( v1_funct_2 @ D @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ A @ B ) @ ( k8_eqrel_1 @ A @ B ) ) @ ( k8_eqrel_1 @ A @ B ) )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ A @ B ) @ ( k8_eqrel_1 @ A @ B ) ) @ ( k8_eqrel_1 @ A @ B ) ) ) ) )
                   => ( ( D
                        = ( k3_filter_1 @ A @ B @ C ) )
                    <=> ! [E: $i,F: $i,G: $i,H: $i] :
                          ( ( ( r2_hidden @ E @ ( k8_eqrel_1 @ A @ B ) )
                            & ( r2_hidden @ F @ ( k8_eqrel_1 @ A @ B ) )
                            & ( r2_hidden @ G @ E )
                            & ( r2_hidden @ H @ F ) )
                         => ( ( k1_binop_1 @ D @ E @ F )
                            = ( k6_eqrel_1 @ A @ A @ B @ ( k1_binop_1 @ C @ G @ H ) ) ) ) ) ) ) ) ) ) )).

thf('147',plain,(
    ! [X6: $i,X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( v1_partfun1 @ X6 @ X7 )
      | ~ ( v3_relat_2 @ X6 )
      | ~ ( v8_relat_2 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) ) )
      | ~ ( m2_filter_1 @ X8 @ X7 @ X6 )
      | ~ ( v1_funct_1 @ X9 )
      | ~ ( v1_funct_2 @ X9 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ X7 @ X6 ) @ ( k8_eqrel_1 @ X7 @ X6 ) ) @ ( k8_eqrel_1 @ X7 @ X6 ) )
      | ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ X7 @ X6 ) @ ( k8_eqrel_1 @ X7 @ X6 ) ) @ ( k8_eqrel_1 @ X7 @ X6 ) ) ) )
      | ( X9
       != ( k3_filter_1 @ X7 @ X6 @ X8 ) )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( r2_hidden @ X12 @ ( k8_eqrel_1 @ X7 @ X6 ) )
      | ~ ( r2_hidden @ X11 @ ( k8_eqrel_1 @ X7 @ X6 ) )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ( ( k1_binop_1 @ X9 @ X11 @ X12 )
        = ( k6_eqrel_1 @ X7 @ X7 @ X6 @ ( k1_binop_1 @ X8 @ X10 @ X13 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) @ X7 ) ) )
      | ~ ( v1_funct_2 @ X8 @ ( k2_zfmisc_1 @ X7 @ X7 ) @ X7 )
      | ~ ( v1_funct_1 @ X8 )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(cnf,[status(esa)],[d4_filter_1])).

thf('148',plain,(
    ! [X6: $i,X7: $i,X8: $i,X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( v1_xboole_0 @ X7 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_funct_2 @ X8 @ ( k2_zfmisc_1 @ X7 @ X7 ) @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) @ X7 ) ) )
      | ( ( k1_binop_1 @ ( k3_filter_1 @ X7 @ X6 @ X8 ) @ X11 @ X12 )
        = ( k6_eqrel_1 @ X7 @ X7 @ X6 @ ( k1_binop_1 @ X8 @ X10 @ X13 ) ) )
      | ~ ( r2_hidden @ X13 @ X12 )
      | ~ ( r2_hidden @ X11 @ ( k8_eqrel_1 @ X7 @ X6 ) )
      | ~ ( r2_hidden @ X12 @ ( k8_eqrel_1 @ X7 @ X6 ) )
      | ~ ( r2_hidden @ X10 @ X11 )
      | ~ ( m1_subset_1 @ ( k3_filter_1 @ X7 @ X6 @ X8 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ X7 @ X6 ) @ ( k8_eqrel_1 @ X7 @ X6 ) ) @ ( k8_eqrel_1 @ X7 @ X6 ) ) ) )
      | ~ ( v1_funct_2 @ ( k3_filter_1 @ X7 @ X6 @ X8 ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ X7 @ X6 ) @ ( k8_eqrel_1 @ X7 @ X6 ) ) @ ( k8_eqrel_1 @ X7 @ X6 ) )
      | ~ ( v1_funct_1 @ ( k3_filter_1 @ X7 @ X6 @ X8 ) )
      | ~ ( m2_filter_1 @ X8 @ X7 @ X6 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X7 ) ) )
      | ~ ( v8_relat_2 @ X6 )
      | ~ ( v3_relat_2 @ X6 )
      | ~ ( v1_partfun1 @ X6 @ X7 ) ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) ) )
      | ~ ( v1_partfun1 @ sk_B_1 @ sk_A )
      | ~ ( v3_relat_2 @ sk_B_1 )
      | ~ ( v8_relat_2 @ sk_B_1 )
      | ~ ( m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( m2_filter_1 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ X0 ) )
      | ~ ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ X0 ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ~ ( r2_hidden @ X3 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X4 @ X3 )
      | ( ( k1_binop_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ X0 ) @ X1 @ X3 )
        = ( k6_eqrel_1 @ sk_A @ sk_A @ sk_B_1 @ ( k1_binop_1 @ X0 @ X2 @ X4 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['146','148'])).

thf('150',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B_1 )
    = ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('151',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B_1 )
    = ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('152',plain,(
    v1_partfun1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    v3_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,(
    v8_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B_1 )
    = ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('157',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B_1 )
    = ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('158',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B_1 )
    = ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('159',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B_1 )
    = ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('160',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B_1 )
    = ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('161',plain,(
    ! [X0: $i] :
      ( ( k6_eqrel_1 @ sk_A @ sk_A @ sk_B_1 @ X0 )
      = ( k11_relat_1 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('162',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) ) )
      | ~ ( m2_filter_1 @ X0 @ sk_A @ sk_B_1 )
      | ~ ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ X0 ) )
      | ~ ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ X0 ) @ ( k2_zfmisc_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ~ ( r2_hidden @ X3 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X4 @ X3 )
      | ( ( k1_binop_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ X0 ) @ X1 @ X3 )
        = ( k11_relat_1 @ sk_B_1 @ ( k1_binop_1 @ X0 @ X2 @ X4 ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['149','150','151','152','153','154','155','156','157','158','159','160','161'])).

thf('163',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_E_1 )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
      | ( ( k1_binop_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_E_1 ) @ X1 @ X0 )
        = ( k11_relat_1 @ sk_B_1 @ ( k1_binop_1 @ sk_E_1 @ X3 @ X2 ) ) )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X3 @ X1 )
      | ~ ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_E_1 ) @ ( k2_zfmisc_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_E_1 ) )
      | ~ ( m2_filter_1 @ sk_E_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['145','162'])).

thf('164',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(clc,[status(thm)],['132','133'])).

thf('165',plain,(
    v1_funct_2 @ sk_E_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['125','126'])).

thf('166',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('167',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('169',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) )
      | ~ ( v8_relat_2 @ X14 )
      | ~ ( v3_relat_2 @ X14 )
      | ~ ( v1_partfun1 @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_2 @ X16 @ ( k2_zfmisc_1 @ X15 @ X15 ) @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) @ X15 ) ) )
      | ( v1_funct_2 @ ( k3_filter_1 @ X15 @ X14 @ X16 ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ X15 @ X14 ) @ ( k8_eqrel_1 @ X15 @ X14 ) ) @ ( k8_eqrel_1 @ X15 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_filter_1])).

thf('170',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ X0 @ sk_E_1 ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_E_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    v1_funct_2 @ sk_E_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['125','126'])).

thf('172',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(clc,[status(thm)],['132','133'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ X0 @ sk_E_1 ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('174',plain,
    ( ~ ( v8_relat_2 @ sk_B_1 )
    | ~ ( v3_relat_2 @ sk_B_1 )
    | ~ ( v1_partfun1 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_E_1 ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['167','173'])).

thf('175',plain,(
    v8_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v3_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    v1_partfun1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B_1 )
    = ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('179',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B_1 )
    = ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('180',plain,
    ( ( k8_eqrel_1 @ sk_A @ sk_B_1 )
    = ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference(demod,[status(thm)],['13','14','15','16'])).

thf('181',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_E_1 ) @ ( k2_zfmisc_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['174','175','176','177','178','179','180'])).

thf('182',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_E_1 ) @ ( k2_zfmisc_1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['181','182'])).

thf('184',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('186',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) ) )
      | ~ ( v8_relat_2 @ X14 )
      | ~ ( v3_relat_2 @ X14 )
      | ~ ( v1_partfun1 @ X14 @ X15 )
      | ( v1_xboole_0 @ X15 )
      | ~ ( v1_funct_1 @ X16 )
      | ~ ( v1_funct_2 @ X16 @ ( k2_zfmisc_1 @ X15 @ X15 ) @ X15 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X15 ) @ X15 ) ) )
      | ( v1_funct_1 @ ( k3_filter_1 @ X15 @ X14 @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_filter_1])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_E_1 ) )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_E_1 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['185','186'])).

thf('188',plain,(
    v1_funct_2 @ sk_E_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['125','126'])).

thf('189',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(clc,[status(thm)],['132','133'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_E_1 ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['187','188','189'])).

thf('191',plain,
    ( ~ ( v8_relat_2 @ sk_B_1 )
    | ~ ( v3_relat_2 @ sk_B_1 )
    | ~ ( v1_partfun1 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_E_1 ) ) ),
    inference('sup-',[status(thm)],['184','190'])).

thf('192',plain,(
    v8_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    v3_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('194',plain,(
    v1_partfun1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_E_1 ) ) ),
    inference(demod,[status(thm)],['191','192','193','194'])).

thf('196',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('197',plain,(
    v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_E_1 ) ),
    inference(clc,[status(thm)],['195','196'])).

thf('198',plain,(
    m2_filter_1 @ sk_E_1 @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( ( k1_binop_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_E_1 ) @ X1 @ X0 )
        = ( k11_relat_1 @ sk_B_1 @ ( k1_binop_1 @ sk_E_1 @ X3 @ X2 ) ) )
      | ~ ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X3 @ X1 ) ) ),
    inference(demod,[status(thm)],['163','164','165','166','183','197','198'])).

thf('200',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k11_relat_1 @ sk_B_1 @ sk_C ) )
      | ~ ( r2_hidden @ X1 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X2 @ X1 )
      | ( ( k1_binop_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_E_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_C ) @ X1 )
        = ( k11_relat_1 @ sk_B_1 @ ( k1_binop_1 @ sk_E_1 @ X0 @ X2 ) ) )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['110','199'])).

thf('201',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( ( k1_binop_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_E_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_C ) @ X0 )
        = ( k11_relat_1 @ sk_B_1 @ ( k1_binop_1 @ sk_E_1 @ sk_C @ X1 ) ) )
      | ~ ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ X0 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['95','200'])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k11_relat_1 @ sk_B_1 @ sk_D ) )
      | ( ( k1_binop_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_E_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_C ) @ ( k11_relat_1 @ sk_B_1 @ sk_D ) )
        = ( k11_relat_1 @ sk_B_1 @ ( k1_binop_1 @ sk_E_1 @ sk_C @ X0 ) ) )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['88','201'])).

thf('203',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( ( k1_binop_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_E_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_C ) @ ( k11_relat_1 @ sk_B_1 @ sk_D ) )
        = ( k11_relat_1 @ sk_B_1 @ ( k1_binop_1 @ sk_E_1 @ sk_C @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k11_relat_1 @ sk_B_1 @ sk_D ) )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['202'])).

thf('204',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( ( k1_binop_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_E_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_C ) @ ( k11_relat_1 @ sk_B_1 @ sk_D ) )
      = ( k11_relat_1 @ sk_B_1 @ ( k1_binop_1 @ sk_E_1 @ sk_C @ sk_D ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['54','203'])).

thf('205',plain,(
    ( k1_binop_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_E_1 ) @ ( k6_eqrel_1 @ sk_A @ sk_A @ sk_B_1 @ sk_C ) @ ( k6_eqrel_1 @ sk_A @ sk_A @ sk_B_1 @ sk_D ) )
 != ( k6_eqrel_1 @ sk_A @ sk_A @ sk_B_1 @ ( k4_binop_1 @ sk_A @ sk_E_1 @ sk_C @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( k6_eqrel_1 @ sk_A @ sk_A @ sk_B_1 @ X0 )
      = ( k11_relat_1 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('207',plain,(
    ! [X0: $i] :
      ( ( k6_eqrel_1 @ sk_A @ sk_A @ sk_B_1 @ X0 )
      = ( k11_relat_1 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( k6_eqrel_1 @ sk_A @ sk_A @ sk_B_1 @ X0 )
      = ( k11_relat_1 @ sk_B_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('209',plain,(
    ( k1_binop_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_E_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_C ) @ ( k11_relat_1 @ sk_B_1 @ sk_D ) )
 != ( k11_relat_1 @ sk_B_1 @ ( k4_binop_1 @ sk_A @ sk_E_1 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['205','206','207','208'])).

thf('210',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    m1_subset_1 @ sk_D @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    m1_subset_1 @ sk_E_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['116','117'])).

thf(redefinition_k4_binop_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ ( k2_zfmisc_1 @ A @ A ) @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) )
        & ( m1_subset_1 @ C @ A )
        & ( m1_subset_1 @ D @ A ) )
     => ( ( k4_binop_1 @ A @ B @ C @ D )
        = ( k1_binop_1 @ B @ C @ D ) ) ) )).

thf('213',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( m1_subset_1 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) @ X29 ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( k2_zfmisc_1 @ X29 @ X29 ) @ X29 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ X29 )
      | ( ( k4_binop_1 @ X29 @ X30 @ X28 @ X31 )
        = ( k1_binop_1 @ X30 @ X28 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k4_binop_1])).

thf('214',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_binop_1 @ sk_A @ sk_E_1 @ X1 @ X0 )
        = ( k1_binop_1 @ sk_E_1 @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_E_1 )
      | ~ ( v1_funct_2 @ sk_E_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['212','213'])).

thf('215',plain,(
    v1_funct_1 @ sk_E_1 ),
    inference(clc,[status(thm)],['132','133'])).

thf('216',plain,(
    v1_funct_2 @ sk_E_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['125','126'])).

thf('217',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k4_binop_1 @ sk_A @ sk_E_1 @ X1 @ X0 )
        = ( k1_binop_1 @ sk_E_1 @ X1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['214','215','216'])).

thf('218',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k4_binop_1 @ sk_A @ sk_E_1 @ X0 @ sk_D )
        = ( k1_binop_1 @ sk_E_1 @ X0 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['211','217'])).

thf('219',plain,
    ( ( k4_binop_1 @ sk_A @ sk_E_1 @ sk_C @ sk_D )
    = ( k1_binop_1 @ sk_E_1 @ sk_C @ sk_D ) ),
    inference('sup-',[status(thm)],['210','218'])).

thf('220',plain,(
    ( k1_binop_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_E_1 ) @ ( k11_relat_1 @ sk_B_1 @ sk_C ) @ ( k11_relat_1 @ sk_B_1 @ sk_D ) )
 != ( k11_relat_1 @ sk_B_1 @ ( k1_binop_1 @ sk_E_1 @ sk_C @ sk_D ) ) ),
    inference(demod,[status(thm)],['209','219'])).

thf('221',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('simplify_reflect-',[status(thm)],['204','220'])).

thf('222',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('223',plain,(
    v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(clc,[status(thm)],['221','222'])).

thf('224',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['30','223'])).

thf('225',plain,(
    v1_xboole_0 @ ( k7_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['21','224'])).

thf('226',plain,(
    $false ),
    inference(demod,[status(thm)],['18','225'])).


%------------------------------------------------------------------------------
