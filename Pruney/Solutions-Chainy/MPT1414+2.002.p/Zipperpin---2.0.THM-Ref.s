%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Yzum0hYc0r

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:07:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 599 expanded)
%              Number of leaves         :   37 ( 190 expanded)
%              Depth                    :   16
%              Number of atoms          : 2071 (11548 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m2_filter_1_type,type,(
    m2_filter_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k8_eqrel_1_type,type,(
    k8_eqrel_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r3_binop_1_type,type,(
    r3_binop_1: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v3_relat_2_type,type,(
    v3_relat_2: $i > $o )).

thf(m1_eqrel_1_type,type,(
    m1_eqrel_1: $i > $i > $o )).

thf(r1_binop_1_type,type,(
    r1_binop_1: $i > $i > $i > $o )).

thf(k9_eqrel_1_type,type,(
    k9_eqrel_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v8_relat_2_type,type,(
    v8_relat_2: $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m2_subset_1_type,type,(
    m2_subset_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k3_filter_1_type,type,(
    k3_filter_1: $i > $i > $i > $i )).

thf(r2_binop_1_type,type,(
    r2_binop_1: $i > $i > $i > $o )).

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
    ~ ( r3_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    r3_binop_1 @ sk_A @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m2_filter_1 @ sk_D @ sk_A @ sk_B ),
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

thf('3',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( v1_relat_1 @ X26 )
      | ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X25 ) @ X25 ) ) )
      | ~ ( m2_filter_1 @ X27 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_filter_1])).

thf('4',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ X3 ) )
      | ( v1_relat_1 @ X2 )
      | ~ ( v1_relat_1 @ X3 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('8',plain,(
    ! [X4: $i,X5: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('9',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['4','9'])).

thf('11',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['10','11'])).

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

thf('13',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ ( k2_zfmisc_1 @ X13 @ X13 ) @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X13 ) @ X13 ) ) )
      | ~ ( r3_binop_1 @ X13 @ X14 @ X12 )
      | ( r2_binop_1 @ X13 @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d7_binop_1])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r2_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( r3_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m2_filter_1 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( v1_relat_1 @ X26 )
      | ( v1_funct_2 @ X27 @ ( k2_zfmisc_1 @ X25 @ X25 ) @ X25 )
      | ~ ( m2_filter_1 @ X27 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_filter_1])).

thf('17',plain,
    ( ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf('19',plain,
    ( ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf('22',plain,(
    m2_filter_1 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ~ ( v1_relat_1 @ X26 )
      | ( v1_funct_1 @ X27 )
      | ~ ( m2_filter_1 @ X27 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_filter_1])).

thf('24',plain,
    ( ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_B ),
    inference(demod,[status(thm)],['7','8'])).

thf('26',plain,
    ( ( v1_funct_1 @ sk_D )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r2_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( r3_binop_1 @ sk_A @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['14','21','28'])).

thf('30',plain,
    ( ( r2_binop_1 @ sk_A @ sk_C @ sk_D )
    | ~ ( m1_subset_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['1','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    r2_binop_1 @ sk_A @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m2_filter_1 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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

thf('35',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( v1_partfun1 @ X32 @ X33 )
      | ~ ( v3_relat_2 @ X32 )
      | ~ ( v8_relat_2 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X33 ) ) )
      | ~ ( m2_filter_1 @ X34 @ X33 @ X32 )
      | ( r2_binop_1 @ ( k8_eqrel_1 @ X33 @ X32 ) @ ( k9_eqrel_1 @ X33 @ X32 @ X35 ) @ ( k3_filter_1 @ X33 @ X32 @ X34 ) )
      | ~ ( r2_binop_1 @ X33 @ X35 @ X34 )
      | ~ ( m1_subset_1 @ X35 @ X33 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[t7_filter_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r2_binop_1 @ sk_A @ X0 @ X1 )
      | ( r2_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B @ X1 ) )
      | ~ ( m2_filter_1 @ X1 @ sk_A @ sk_B )
      | ~ ( v8_relat_2 @ sk_B )
      | ~ ( v3_relat_2 @ sk_B )
      | ~ ( v1_partfun1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r2_binop_1 @ sk_A @ X0 @ X1 )
      | ( r2_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B @ X1 ) )
      | ~ ( m2_filter_1 @ X1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['36','37','38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r2_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( r2_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','40'])).

thf('42',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r2_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['32','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    r2_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['10','11'])).

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

thf('49',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X16 ) ) )
      | ~ ( v8_relat_2 @ X15 )
      | ~ ( v3_relat_2 @ X15 )
      | ~ ( v1_partfun1 @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_2 @ X17 @ ( k2_zfmisc_1 @ X16 @ X16 ) @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X16 ) @ X16 ) ) )
      | ( m1_subset_1 @ ( k3_filter_1 @ X16 @ X15 @ X17 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ X16 @ X15 ) @ ( k8_eqrel_1 @ X16 @ X15 ) ) @ ( k8_eqrel_1 @ X16 @ X15 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_filter_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf('52',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['26','27'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['50','51','52'])).

thf('54',plain,
    ( ~ ( v8_relat_2 @ sk_B )
    | ~ ( v3_relat_2 @ sk_B )
    | ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['47','53'])).

thf('55',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['54','55','56','57'])).

thf('59',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    m1_subset_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ ( k2_zfmisc_1 @ X13 @ X13 ) @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X13 ) @ X13 ) ) )
      | ~ ( r1_binop_1 @ X13 @ X14 @ X12 )
      | ~ ( r2_binop_1 @ X13 @ X14 @ X12 )
      | ( r3_binop_1 @ X13 @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d7_binop_1])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k8_eqrel_1 @ sk_A @ sk_B ) )
      | ( r3_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( r2_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( r1_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) )
      | ~ ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('65',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X16 ) ) )
      | ~ ( v8_relat_2 @ X15 )
      | ~ ( v3_relat_2 @ X15 )
      | ~ ( v1_partfun1 @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_2 @ X17 @ ( k2_zfmisc_1 @ X16 @ X16 ) @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X16 ) @ X16 ) ) )
      | ( v1_funct_2 @ ( k3_filter_1 @ X16 @ X15 @ X17 ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ X16 @ X15 ) @ ( k8_eqrel_1 @ X16 @ X15 ) ) @ ( k8_eqrel_1 @ X16 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_filter_1])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf('68',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['26','27'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['66','67','68'])).

thf('70',plain,
    ( ~ ( v8_relat_2 @ sk_B )
    | ~ ( v3_relat_2 @ sk_B )
    | ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','69'])).

thf('71',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['70','71','72','73'])).

thf('75',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('78',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('79',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X16 ) ) )
      | ~ ( v8_relat_2 @ X15 )
      | ~ ( v3_relat_2 @ X15 )
      | ~ ( v1_partfun1 @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( v1_funct_1 @ X17 )
      | ~ ( v1_funct_2 @ X17 @ ( k2_zfmisc_1 @ X16 @ X16 ) @ X16 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X16 ) @ X16 ) ) )
      | ( v1_funct_1 @ ( k3_filter_1 @ X16 @ X15 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k3_filter_1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf('82',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['26','27'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['80','81','82'])).

thf('84',plain,
    ( ~ ( v8_relat_2 @ sk_B )
    | ~ ( v3_relat_2 @ sk_B )
    | ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['77','83'])).

thf('85',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['84','85','86','87'])).

thf('89',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k8_eqrel_1 @ sk_A @ sk_B ) )
      | ( r3_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( r2_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( r1_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['62','76','90'])).

thf('92',plain,
    ( ~ ( r1_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
    | ( r3_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
    | ~ ( m1_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','91'])).

thf('93',plain,(
    r3_binop_1 @ sk_A @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['10','11'])).

thf('95',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( v1_funct_1 @ X12 )
      | ~ ( v1_funct_2 @ X12 @ ( k2_zfmisc_1 @ X13 @ X13 ) @ X13 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X13 @ X13 ) @ X13 ) ) )
      | ~ ( r3_binop_1 @ X13 @ X14 @ X12 )
      | ( r1_binop_1 @ X13 @ X14 @ X12 )
      | ~ ( m1_subset_1 @ X14 @ X13 ) ) ),
    inference(cnf,[status(esa)],[d7_binop_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r1_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( r3_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['19','20'])).

thf('98',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['26','27'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r1_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( r3_binop_1 @ sk_A @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['96','97','98'])).

thf('100',plain,
    ( ( r1_binop_1 @ sk_A @ sk_C @ sk_D )
    | ~ ( m1_subset_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['93','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    r1_binop_1 @ sk_A @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    m2_filter_1 @ sk_D @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('104',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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

thf('105',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ~ ( v1_partfun1 @ X28 @ X29 )
      | ~ ( v3_relat_2 @ X28 )
      | ~ ( v8_relat_2 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) )
      | ~ ( m2_filter_1 @ X30 @ X29 @ X28 )
      | ( r1_binop_1 @ ( k8_eqrel_1 @ X29 @ X28 ) @ ( k9_eqrel_1 @ X29 @ X28 @ X31 ) @ ( k3_filter_1 @ X29 @ X28 @ X30 ) )
      | ~ ( r1_binop_1 @ X29 @ X31 @ X30 )
      | ~ ( m1_subset_1 @ X31 @ X29 )
      | ( v1_xboole_0 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t6_filter_1])).

thf('106',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r1_binop_1 @ sk_A @ X0 @ X1 )
      | ( r1_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B @ X1 ) )
      | ~ ( m2_filter_1 @ X1 @ sk_A @ sk_B )
      | ~ ( v8_relat_2 @ sk_B )
      | ~ ( v3_relat_2 @ sk_B )
      | ~ ( v1_partfun1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['104','105'])).

thf('107',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('108',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r1_binop_1 @ sk_A @ X0 @ X1 )
      | ( r1_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B @ X1 ) )
      | ~ ( m2_filter_1 @ X1 @ sk_A @ sk_B ) ) ),
    inference(demod,[status(thm)],['106','107','108','109'])).

thf('111',plain,(
    ! [X0: $i] :
      ( ( r1_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) )
      | ~ ( r1_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['103','110'])).

thf('112',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r1_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference('sup-',[status(thm)],['102','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r1_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ) ),
    inference(demod,[status(thm)],['112','113'])).

thf('115',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    r1_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ),
    inference(clc,[status(thm)],['114','115'])).

thf('117',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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

thf('119',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X21 ) ) )
      | ~ ( v1_partfun1 @ X20 @ X21 )
      | ~ ( v8_relat_2 @ X20 )
      | ~ ( v3_relat_2 @ X20 )
      | ( v1_xboole_0 @ X21 )
      | ~ ( m1_subset_1 @ X22 @ X21 )
      | ( m2_subset_1 @ ( k9_eqrel_1 @ X21 @ X20 @ X22 ) @ ( k1_zfmisc_1 @ X21 ) @ ( k8_eqrel_1 @ X21 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_eqrel_1])).

thf('120',plain,(
    ! [X0: $i] :
      ( ( m2_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v3_relat_2 @ sk_B )
      | ~ ( v8_relat_2 @ sk_B )
      | ~ ( v1_partfun1 @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['118','119'])).

thf('121',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    ! [X0: $i] :
      ( ( m2_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['120','121','122','123'])).

thf('125',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( m2_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['124','125'])).

thf('127',plain,(
    m2_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['117','126'])).

thf('128',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_eqrel_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v3_relat_2 @ B )
        & ( v8_relat_2 @ B )
        & ( v1_partfun1 @ B @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( m1_eqrel_1 @ ( k8_eqrel_1 @ A @ B ) @ A ) ) )).

thf('129',plain,(
    ! [X18: $i,X19: $i] :
      ( ( m1_eqrel_1 @ ( k8_eqrel_1 @ X18 @ X19 ) @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) ) )
      | ~ ( v1_partfun1 @ X19 @ X18 )
      | ~ ( v8_relat_2 @ X19 )
      | ~ ( v3_relat_2 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_eqrel_1])).

thf('130',plain,
    ( ~ ( v3_relat_2 @ sk_B )
    | ~ ( v8_relat_2 @ sk_B )
    | ~ ( v1_partfun1 @ sk_B @ sk_A )
    | ( m1_eqrel_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ sk_A ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    v3_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v8_relat_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_partfun1 @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    m1_eqrel_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['130','131','132','133'])).

thf(dt_m1_eqrel_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_eqrel_1 @ B @ A )
     => ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('135',plain,(
    ! [X23: $i,X24: $i] :
      ( ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X24 ) ) )
      | ~ ( m1_eqrel_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_eqrel_1])).

thf('136',plain,(
    m1_subset_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf(redefinition_m2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m2_subset_1 @ C @ A @ B )
        <=> ( m1_subset_1 @ C @ B ) ) ) )).

thf('137',plain,(
    ! [X6: $i,X7: $i,X9: $i] :
      ( ( v1_xboole_0 @ X6 )
      | ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X6 ) )
      | ( m1_subset_1 @ X9 @ X7 )
      | ~ ( m2_subset_1 @ X9 @ X6 @ X7 ) ) ),
    inference(cnf,[status(esa)],[redefinition_m2_subset_1])).

thf('138',plain,(
    ! [X0: $i] :
      ( ~ ( m2_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) )
      | ( m1_subset_1 @ X0 @ ( k8_eqrel_1 @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( k8_eqrel_1 @ sk_A @ sk_B ) )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['136','137'])).

thf('139',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( k8_eqrel_1 @ sk_A @ sk_B ) )
    | ( m1_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['127','138'])).

thf('140',plain,(
    m1_subset_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('142',plain,
    ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    m1_eqrel_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ sk_A ),
    inference(demod,[status(thm)],['130','131','132','133'])).

thf(cc1_eqrel_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_eqrel_1 @ B @ A )
         => ~ ( v1_xboole_0 @ B ) ) ) )).

thf('144',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( m1_eqrel_1 @ X10 @ X11 )
      | ~ ( v1_xboole_0 @ X10 )
      | ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[cc1_eqrel_1])).

thf('145',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_xboole_0 @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['143','144'])).

thf('146',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ~ ( v1_xboole_0 @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['145','146'])).

thf('148',plain,(
    ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['142','147'])).

thf('149',plain,
    ( ( m1_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) )
    | ( v1_xboole_0 @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['139','148'])).

thf('150',plain,(
    ~ ( v1_xboole_0 @ ( k8_eqrel_1 @ sk_A @ sk_B ) ) ),
    inference(clc,[status(thm)],['145','146'])).

thf('151',plain,(
    m1_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k8_eqrel_1 @ sk_A @ sk_B ) ),
    inference(clc,[status(thm)],['149','150'])).

thf('152',plain,(
    r3_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B ) @ ( k9_eqrel_1 @ sk_A @ sk_B @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B @ sk_D ) ),
    inference(demod,[status(thm)],['92','116','151'])).

thf('153',plain,(
    $false ),
    inference(demod,[status(thm)],['0','152'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Yzum0hYc0r
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:04:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.22/0.52  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.52  % Solved by: fo/fo7.sh
% 0.22/0.52  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.52  % done 73 iterations in 0.050s
% 0.22/0.52  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.52  % SZS output start Refutation
% 0.22/0.52  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.52  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.52  thf(m2_filter_1_type, type, m2_filter_1: $i > $i > $i > $o).
% 0.22/0.52  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.52  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.52  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.52  thf(k8_eqrel_1_type, type, k8_eqrel_1: $i > $i > $i).
% 0.22/0.52  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.52  thf(r3_binop_1_type, type, r3_binop_1: $i > $i > $i > $o).
% 0.22/0.52  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.52  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.52  thf(v3_relat_2_type, type, v3_relat_2: $i > $o).
% 0.22/0.52  thf(m1_eqrel_1_type, type, m1_eqrel_1: $i > $i > $o).
% 0.22/0.52  thf(r1_binop_1_type, type, r1_binop_1: $i > $i > $i > $o).
% 0.22/0.52  thf(k9_eqrel_1_type, type, k9_eqrel_1: $i > $i > $i > $i).
% 0.22/0.52  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.52  thf(v8_relat_2_type, type, v8_relat_2: $i > $o).
% 0.22/0.52  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.22/0.52  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.52  thf(m2_subset_1_type, type, m2_subset_1: $i > $i > $i > $o).
% 0.22/0.52  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.52  thf(k3_filter_1_type, type, k3_filter_1: $i > $i > $i > $i).
% 0.22/0.52  thf(r2_binop_1_type, type, r2_binop_1: $i > $i > $i > $o).
% 0.22/0.52  thf(t8_filter_1, conjecture,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( ( v1_partfun1 @ B @ A ) & ( v3_relat_2 @ B ) & 
% 0.22/0.52             ( v8_relat_2 @ B ) & 
% 0.22/0.52             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( m1_subset_1 @ C @ A ) =>
% 0.22/0.52               ( ![D:$i]:
% 0.22/0.52                 ( ( m2_filter_1 @ D @ A @ B ) =>
% 0.22/0.52                   ( ( r3_binop_1 @ A @ C @ D ) =>
% 0.22/0.52                     ( r3_binop_1 @
% 0.22/0.52                       ( k8_eqrel_1 @ A @ B ) @ ( k9_eqrel_1 @ A @ B @ C ) @ 
% 0.22/0.52                       ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.52    (~( ![A:$i]:
% 0.22/0.52        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.52          ( ![B:$i]:
% 0.22/0.52            ( ( ( v1_partfun1 @ B @ A ) & ( v3_relat_2 @ B ) & 
% 0.22/0.52                ( v8_relat_2 @ B ) & 
% 0.22/0.52                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.52              ( ![C:$i]:
% 0.22/0.52                ( ( m1_subset_1 @ C @ A ) =>
% 0.22/0.52                  ( ![D:$i]:
% 0.22/0.52                    ( ( m2_filter_1 @ D @ A @ B ) =>
% 0.22/0.52                      ( ( r3_binop_1 @ A @ C @ D ) =>
% 0.22/0.52                        ( r3_binop_1 @
% 0.22/0.52                          ( k8_eqrel_1 @ A @ B ) @ 
% 0.22/0.52                          ( k9_eqrel_1 @ A @ B @ C ) @ 
% 0.22/0.52                          ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.52    inference('cnf.neg', [status(esa)], [t8_filter_1])).
% 0.22/0.52  thf('0', plain,
% 0.22/0.52      (~ (r3_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.52          (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.22/0.52          (k3_filter_1 @ sk_A @ sk_B @ sk_D))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('1', plain, ((r3_binop_1 @ sk_A @ sk_C @ sk_D)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('2', plain, ((m2_filter_1 @ sk_D @ sk_A @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(dt_m2_filter_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_relat_1 @ B ) ) =>
% 0.22/0.52       ( ![C:$i]:
% 0.22/0.52         ( ( m2_filter_1 @ C @ A @ B ) =>
% 0.22/0.52           ( ( v1_funct_1 @ C ) & 
% 0.22/0.52             ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A ) & 
% 0.22/0.52             ( m1_subset_1 @
% 0.22/0.52               C @ 
% 0.22/0.52               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) ) ) ) ))).
% 0.22/0.52  thf('3', plain,
% 0.22/0.52      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.22/0.52         ((v1_xboole_0 @ X25)
% 0.22/0.52          | ~ (v1_relat_1 @ X26)
% 0.22/0.52          | (m1_subset_1 @ X27 @ 
% 0.22/0.52             (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X25) @ X25)))
% 0.22/0.52          | ~ (m2_filter_1 @ X27 @ X25 @ X26))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_m2_filter_1])).
% 0.22/0.52  thf('4', plain,
% 0.22/0.52      (((m1_subset_1 @ sk_D @ 
% 0.22/0.52         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))
% 0.22/0.52        | ~ (v1_relat_1 @ sk_B)
% 0.22/0.52        | (v1_xboole_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['2', '3'])).
% 0.22/0.52  thf('5', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(cc2_relat_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( v1_relat_1 @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.22/0.52  thf('6', plain,
% 0.22/0.52      (![X2 : $i, X3 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ X3))
% 0.22/0.52          | (v1_relat_1 @ X2)
% 0.22/0.52          | ~ (v1_relat_1 @ X3))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.22/0.52  thf('7', plain,
% 0.22/0.52      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['5', '6'])).
% 0.22/0.52  thf(fc6_relat_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.22/0.52  thf('8', plain,
% 0.22/0.52      (![X4 : $i, X5 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X4 @ X5))),
% 0.22/0.52      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.52  thf('9', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.52  thf('10', plain,
% 0.22/0.52      (((m1_subset_1 @ sk_D @ 
% 0.22/0.52         (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))
% 0.22/0.52        | (v1_xboole_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['4', '9'])).
% 0.22/0.52  thf('11', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('12', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_D @ 
% 0.22/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.22/0.52      inference('clc', [status(thm)], ['10', '11'])).
% 0.22/0.52  thf(d7_binop_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_subset_1 @ B @ A ) =>
% 0.22/0.52       ( ![C:$i]:
% 0.22/0.52         ( ( ( v1_funct_1 @ C ) & 
% 0.22/0.52             ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A ) & 
% 0.22/0.52             ( m1_subset_1 @
% 0.22/0.52               C @ 
% 0.22/0.52               ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) ) =>
% 0.22/0.52           ( ( r3_binop_1 @ A @ B @ C ) <=>
% 0.22/0.52             ( ( r1_binop_1 @ A @ B @ C ) & ( r2_binop_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.22/0.52  thf('13', plain,
% 0.22/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.52         (~ (v1_funct_1 @ X12)
% 0.22/0.52          | ~ (v1_funct_2 @ X12 @ (k2_zfmisc_1 @ X13 @ X13) @ X13)
% 0.22/0.52          | ~ (m1_subset_1 @ X12 @ 
% 0.22/0.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X13) @ X13)))
% 0.22/0.52          | ~ (r3_binop_1 @ X13 @ X14 @ X12)
% 0.22/0.52          | (r2_binop_1 @ X13 @ X14 @ X12)
% 0.22/0.52          | ~ (m1_subset_1 @ X14 @ X13))),
% 0.22/0.52      inference('cnf', [status(esa)], [d7_binop_1])).
% 0.22/0.52  thf('14', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.22/0.52          | (r2_binop_1 @ sk_A @ X0 @ sk_D)
% 0.22/0.52          | ~ (r3_binop_1 @ sk_A @ X0 @ sk_D)
% 0.22/0.52          | ~ (v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.22/0.52          | ~ (v1_funct_1 @ sk_D))),
% 0.22/0.52      inference('sup-', [status(thm)], ['12', '13'])).
% 0.22/0.52  thf('15', plain, ((m2_filter_1 @ sk_D @ sk_A @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('16', plain,
% 0.22/0.52      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.22/0.52         ((v1_xboole_0 @ X25)
% 0.22/0.52          | ~ (v1_relat_1 @ X26)
% 0.22/0.52          | (v1_funct_2 @ X27 @ (k2_zfmisc_1 @ X25 @ X25) @ X25)
% 0.22/0.52          | ~ (m2_filter_1 @ X27 @ X25 @ X26))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_m2_filter_1])).
% 0.22/0.52  thf('17', plain,
% 0.22/0.52      (((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.22/0.52        | ~ (v1_relat_1 @ sk_B)
% 0.22/0.52        | (v1_xboole_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.52  thf('18', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.52  thf('19', plain,
% 0.22/0.52      (((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.22/0.52        | (v1_xboole_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['17', '18'])).
% 0.22/0.52  thf('20', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('21', plain, ((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.22/0.52      inference('clc', [status(thm)], ['19', '20'])).
% 0.22/0.52  thf('22', plain, ((m2_filter_1 @ sk_D @ sk_A @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('23', plain,
% 0.22/0.52      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.22/0.52         ((v1_xboole_0 @ X25)
% 0.22/0.52          | ~ (v1_relat_1 @ X26)
% 0.22/0.52          | (v1_funct_1 @ X27)
% 0.22/0.52          | ~ (m2_filter_1 @ X27 @ X25 @ X26))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_m2_filter_1])).
% 0.22/0.52  thf('24', plain,
% 0.22/0.52      (((v1_funct_1 @ sk_D) | ~ (v1_relat_1 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.52  thf('25', plain, ((v1_relat_1 @ sk_B)),
% 0.22/0.52      inference('demod', [status(thm)], ['7', '8'])).
% 0.22/0.52  thf('26', plain, (((v1_funct_1 @ sk_D) | (v1_xboole_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['24', '25'])).
% 0.22/0.52  thf('27', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('28', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.52      inference('clc', [status(thm)], ['26', '27'])).
% 0.22/0.52  thf('29', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.22/0.52          | (r2_binop_1 @ sk_A @ X0 @ sk_D)
% 0.22/0.52          | ~ (r3_binop_1 @ sk_A @ X0 @ sk_D))),
% 0.22/0.52      inference('demod', [status(thm)], ['14', '21', '28'])).
% 0.22/0.52  thf('30', plain,
% 0.22/0.52      (((r2_binop_1 @ sk_A @ sk_C @ sk_D) | ~ (m1_subset_1 @ sk_C @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['1', '29'])).
% 0.22/0.52  thf('31', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('32', plain, ((r2_binop_1 @ sk_A @ sk_C @ sk_D)),
% 0.22/0.52      inference('demod', [status(thm)], ['30', '31'])).
% 0.22/0.52  thf('33', plain, ((m2_filter_1 @ sk_D @ sk_A @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('34', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t7_filter_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( ( v1_partfun1 @ B @ A ) & ( v3_relat_2 @ B ) & 
% 0.22/0.52             ( v8_relat_2 @ B ) & 
% 0.22/0.52             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( m1_subset_1 @ C @ A ) =>
% 0.22/0.52               ( ![D:$i]:
% 0.22/0.52                 ( ( m2_filter_1 @ D @ A @ B ) =>
% 0.22/0.52                   ( ( r2_binop_1 @ A @ C @ D ) =>
% 0.22/0.52                     ( r2_binop_1 @
% 0.22/0.52                       ( k8_eqrel_1 @ A @ B ) @ ( k9_eqrel_1 @ A @ B @ C ) @ 
% 0.22/0.52                       ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf('35', plain,
% 0.22/0.52      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.22/0.52         (~ (v1_partfun1 @ X32 @ X33)
% 0.22/0.52          | ~ (v3_relat_2 @ X32)
% 0.22/0.52          | ~ (v8_relat_2 @ X32)
% 0.22/0.52          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X33)))
% 0.22/0.52          | ~ (m2_filter_1 @ X34 @ X33 @ X32)
% 0.22/0.52          | (r2_binop_1 @ (k8_eqrel_1 @ X33 @ X32) @ 
% 0.22/0.52             (k9_eqrel_1 @ X33 @ X32 @ X35) @ (k3_filter_1 @ X33 @ X32 @ X34))
% 0.22/0.52          | ~ (r2_binop_1 @ X33 @ X35 @ X34)
% 0.22/0.52          | ~ (m1_subset_1 @ X35 @ X33)
% 0.22/0.52          | (v1_xboole_0 @ X33))),
% 0.22/0.52      inference('cnf', [status(esa)], [t7_filter_1])).
% 0.22/0.52  thf('36', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((v1_xboole_0 @ sk_A)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.22/0.52          | ~ (r2_binop_1 @ sk_A @ X0 @ X1)
% 0.22/0.52          | (r2_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.52             (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ (k3_filter_1 @ sk_A @ sk_B @ X1))
% 0.22/0.52          | ~ (m2_filter_1 @ X1 @ sk_A @ sk_B)
% 0.22/0.52          | ~ (v8_relat_2 @ sk_B)
% 0.22/0.52          | ~ (v3_relat_2 @ sk_B)
% 0.22/0.52          | ~ (v1_partfun1 @ sk_B @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.52  thf('37', plain, ((v8_relat_2 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('38', plain, ((v3_relat_2 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('39', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('40', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((v1_xboole_0 @ sk_A)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.22/0.52          | ~ (r2_binop_1 @ sk_A @ X0 @ X1)
% 0.22/0.52          | (r2_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.52             (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ (k3_filter_1 @ sk_A @ sk_B @ X1))
% 0.22/0.52          | ~ (m2_filter_1 @ X1 @ sk_A @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['36', '37', '38', '39'])).
% 0.22/0.52  thf('41', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((r2_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.52           (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.22/0.52          | ~ (r2_binop_1 @ sk_A @ X0 @ sk_D)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.22/0.52          | (v1_xboole_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['33', '40'])).
% 0.22/0.52  thf('42', plain,
% 0.22/0.52      (((v1_xboole_0 @ sk_A)
% 0.22/0.52        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 0.22/0.52        | (r2_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.52           (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.22/0.52           (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['32', '41'])).
% 0.22/0.52  thf('43', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('44', plain,
% 0.22/0.52      (((v1_xboole_0 @ sk_A)
% 0.22/0.52        | (r2_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.52           (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.22/0.52           (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.22/0.52      inference('demod', [status(thm)], ['42', '43'])).
% 0.22/0.52  thf('45', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('46', plain,
% 0.22/0.52      ((r2_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.52        (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ (k3_filter_1 @ sk_A @ sk_B @ sk_D))),
% 0.22/0.52      inference('clc', [status(thm)], ['44', '45'])).
% 0.22/0.52  thf('47', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('48', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_D @ 
% 0.22/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.22/0.52      inference('clc', [status(thm)], ['10', '11'])).
% 0.22/0.52  thf(dt_k3_filter_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_partfun1 @ B @ A ) & 
% 0.22/0.52         ( v3_relat_2 @ B ) & ( v8_relat_2 @ B ) & 
% 0.22/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.22/0.52         ( v1_funct_1 @ C ) & 
% 0.22/0.52         ( v1_funct_2 @ C @ ( k2_zfmisc_1 @ A @ A ) @ A ) & 
% 0.22/0.52         ( m1_subset_1 @
% 0.22/0.52           C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) @ A ) ) ) ) =>
% 0.22/0.52       ( ( v1_funct_1 @ ( k3_filter_1 @ A @ B @ C ) ) & 
% 0.22/0.52         ( v1_funct_2 @
% 0.22/0.52           ( k3_filter_1 @ A @ B @ C ) @ 
% 0.22/0.52           ( k2_zfmisc_1 @ ( k8_eqrel_1 @ A @ B ) @ ( k8_eqrel_1 @ A @ B ) ) @ 
% 0.22/0.52           ( k8_eqrel_1 @ A @ B ) ) & 
% 0.22/0.52         ( m1_subset_1 @
% 0.22/0.52           ( k3_filter_1 @ A @ B @ C ) @ 
% 0.22/0.52           ( k1_zfmisc_1 @
% 0.22/0.52             ( k2_zfmisc_1 @
% 0.22/0.52               ( k2_zfmisc_1 @ ( k8_eqrel_1 @ A @ B ) @ ( k8_eqrel_1 @ A @ B ) ) @ 
% 0.22/0.52               ( k8_eqrel_1 @ A @ B ) ) ) ) ) ))).
% 0.22/0.52  thf('49', plain,
% 0.22/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X16)))
% 0.22/0.52          | ~ (v8_relat_2 @ X15)
% 0.22/0.52          | ~ (v3_relat_2 @ X15)
% 0.22/0.52          | ~ (v1_partfun1 @ X15 @ X16)
% 0.22/0.52          | (v1_xboole_0 @ X16)
% 0.22/0.52          | ~ (v1_funct_1 @ X17)
% 0.22/0.52          | ~ (v1_funct_2 @ X17 @ (k2_zfmisc_1 @ X16 @ X16) @ X16)
% 0.22/0.52          | ~ (m1_subset_1 @ X17 @ 
% 0.22/0.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X16) @ X16)))
% 0.22/0.52          | (m1_subset_1 @ (k3_filter_1 @ X16 @ X15 @ X17) @ 
% 0.22/0.52             (k1_zfmisc_1 @ 
% 0.22/0.52              (k2_zfmisc_1 @ 
% 0.22/0.52               (k2_zfmisc_1 @ (k8_eqrel_1 @ X16 @ X15) @ 
% 0.22/0.52                (k8_eqrel_1 @ X16 @ X15)) @ 
% 0.22/0.52               (k8_eqrel_1 @ X16 @ X15)))))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k3_filter_1])).
% 0.22/0.52  thf('50', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((m1_subset_1 @ (k3_filter_1 @ sk_A @ X0 @ sk_D) @ 
% 0.22/0.52           (k1_zfmisc_1 @ 
% 0.22/0.52            (k2_zfmisc_1 @ 
% 0.22/0.52             (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ X0) @ (k8_eqrel_1 @ sk_A @ X0)) @ 
% 0.22/0.52             (k8_eqrel_1 @ sk_A @ X0))))
% 0.22/0.52          | ~ (v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.22/0.52          | ~ (v1_funct_1 @ sk_D)
% 0.22/0.52          | (v1_xboole_0 @ sk_A)
% 0.22/0.52          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.22/0.52          | ~ (v3_relat_2 @ X0)
% 0.22/0.52          | ~ (v8_relat_2 @ X0)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['48', '49'])).
% 0.22/0.52  thf('51', plain, ((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.22/0.52      inference('clc', [status(thm)], ['19', '20'])).
% 0.22/0.52  thf('52', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.52      inference('clc', [status(thm)], ['26', '27'])).
% 0.22/0.52  thf('53', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((m1_subset_1 @ (k3_filter_1 @ sk_A @ X0 @ sk_D) @ 
% 0.22/0.52           (k1_zfmisc_1 @ 
% 0.22/0.52            (k2_zfmisc_1 @ 
% 0.22/0.52             (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ X0) @ (k8_eqrel_1 @ sk_A @ X0)) @ 
% 0.22/0.52             (k8_eqrel_1 @ sk_A @ X0))))
% 0.22/0.52          | (v1_xboole_0 @ sk_A)
% 0.22/0.52          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.22/0.52          | ~ (v3_relat_2 @ X0)
% 0.22/0.52          | ~ (v8_relat_2 @ X0)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.22/0.52      inference('demod', [status(thm)], ['50', '51', '52'])).
% 0.22/0.52  thf('54', plain,
% 0.22/0.52      ((~ (v8_relat_2 @ sk_B)
% 0.22/0.52        | ~ (v3_relat_2 @ sk_B)
% 0.22/0.52        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.22/0.52        | (v1_xboole_0 @ sk_A)
% 0.22/0.52        | (m1_subset_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.22/0.52           (k1_zfmisc_1 @ 
% 0.22/0.52            (k2_zfmisc_1 @ 
% 0.22/0.52             (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.52              (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.22/0.52             (k8_eqrel_1 @ sk_A @ sk_B)))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['47', '53'])).
% 0.22/0.52  thf('55', plain, ((v8_relat_2 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('56', plain, ((v3_relat_2 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('57', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('58', plain,
% 0.22/0.52      (((v1_xboole_0 @ sk_A)
% 0.22/0.52        | (m1_subset_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.22/0.52           (k1_zfmisc_1 @ 
% 0.22/0.52            (k2_zfmisc_1 @ 
% 0.22/0.52             (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.52              (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.22/0.52             (k8_eqrel_1 @ sk_A @ sk_B)))))),
% 0.22/0.52      inference('demod', [status(thm)], ['54', '55', '56', '57'])).
% 0.22/0.52  thf('59', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('60', plain,
% 0.22/0.52      ((m1_subset_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.22/0.52        (k1_zfmisc_1 @ 
% 0.22/0.52         (k2_zfmisc_1 @ 
% 0.22/0.52          (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.52           (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.22/0.52          (k8_eqrel_1 @ sk_A @ sk_B))))),
% 0.22/0.52      inference('clc', [status(thm)], ['58', '59'])).
% 0.22/0.52  thf('61', plain,
% 0.22/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.52         (~ (v1_funct_1 @ X12)
% 0.22/0.52          | ~ (v1_funct_2 @ X12 @ (k2_zfmisc_1 @ X13 @ X13) @ X13)
% 0.22/0.52          | ~ (m1_subset_1 @ X12 @ 
% 0.22/0.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X13) @ X13)))
% 0.22/0.52          | ~ (r1_binop_1 @ X13 @ X14 @ X12)
% 0.22/0.52          | ~ (r2_binop_1 @ X13 @ X14 @ X12)
% 0.22/0.52          | (r3_binop_1 @ X13 @ X14 @ X12)
% 0.22/0.52          | ~ (m1_subset_1 @ X14 @ X13))),
% 0.22/0.52      inference('cnf', [status(esa)], [d7_binop_1])).
% 0.22/0.52  thf('62', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X0 @ (k8_eqrel_1 @ sk_A @ sk_B))
% 0.22/0.52          | (r3_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.22/0.52             (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.22/0.52          | ~ (r2_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.22/0.52               (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.22/0.52          | ~ (r1_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.22/0.52               (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.22/0.52          | ~ (v1_funct_2 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.22/0.52               (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.52                (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.22/0.52               (k8_eqrel_1 @ sk_A @ sk_B))
% 0.22/0.52          | ~ (v1_funct_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['60', '61'])).
% 0.22/0.52  thf('63', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('64', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_D @ 
% 0.22/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.22/0.52      inference('clc', [status(thm)], ['10', '11'])).
% 0.22/0.52  thf('65', plain,
% 0.22/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X16)))
% 0.22/0.52          | ~ (v8_relat_2 @ X15)
% 0.22/0.52          | ~ (v3_relat_2 @ X15)
% 0.22/0.52          | ~ (v1_partfun1 @ X15 @ X16)
% 0.22/0.52          | (v1_xboole_0 @ X16)
% 0.22/0.52          | ~ (v1_funct_1 @ X17)
% 0.22/0.52          | ~ (v1_funct_2 @ X17 @ (k2_zfmisc_1 @ X16 @ X16) @ X16)
% 0.22/0.52          | ~ (m1_subset_1 @ X17 @ 
% 0.22/0.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X16) @ X16)))
% 0.22/0.52          | (v1_funct_2 @ (k3_filter_1 @ X16 @ X15 @ X17) @ 
% 0.22/0.52             (k2_zfmisc_1 @ (k8_eqrel_1 @ X16 @ X15) @ (k8_eqrel_1 @ X16 @ X15)) @ 
% 0.22/0.52             (k8_eqrel_1 @ X16 @ X15)))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k3_filter_1])).
% 0.22/0.52  thf('66', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v1_funct_2 @ (k3_filter_1 @ sk_A @ X0 @ sk_D) @ 
% 0.22/0.52           (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ X0) @ (k8_eqrel_1 @ sk_A @ X0)) @ 
% 0.22/0.52           (k8_eqrel_1 @ sk_A @ X0))
% 0.22/0.52          | ~ (v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.22/0.52          | ~ (v1_funct_1 @ sk_D)
% 0.22/0.52          | (v1_xboole_0 @ sk_A)
% 0.22/0.52          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.22/0.52          | ~ (v3_relat_2 @ X0)
% 0.22/0.52          | ~ (v8_relat_2 @ X0)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['64', '65'])).
% 0.22/0.52  thf('67', plain, ((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.22/0.52      inference('clc', [status(thm)], ['19', '20'])).
% 0.22/0.52  thf('68', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.52      inference('clc', [status(thm)], ['26', '27'])).
% 0.22/0.52  thf('69', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v1_funct_2 @ (k3_filter_1 @ sk_A @ X0 @ sk_D) @ 
% 0.22/0.52           (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ X0) @ (k8_eqrel_1 @ sk_A @ X0)) @ 
% 0.22/0.52           (k8_eqrel_1 @ sk_A @ X0))
% 0.22/0.52          | (v1_xboole_0 @ sk_A)
% 0.22/0.52          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.22/0.52          | ~ (v3_relat_2 @ X0)
% 0.22/0.52          | ~ (v8_relat_2 @ X0)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.22/0.52      inference('demod', [status(thm)], ['66', '67', '68'])).
% 0.22/0.52  thf('70', plain,
% 0.22/0.52      ((~ (v8_relat_2 @ sk_B)
% 0.22/0.52        | ~ (v3_relat_2 @ sk_B)
% 0.22/0.52        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.22/0.52        | (v1_xboole_0 @ sk_A)
% 0.22/0.52        | (v1_funct_2 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.22/0.52           (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.52            (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.22/0.52           (k8_eqrel_1 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['63', '69'])).
% 0.22/0.52  thf('71', plain, ((v8_relat_2 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('72', plain, ((v3_relat_2 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('73', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('74', plain,
% 0.22/0.52      (((v1_xboole_0 @ sk_A)
% 0.22/0.52        | (v1_funct_2 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.22/0.52           (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.52            (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.22/0.52           (k8_eqrel_1 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('demod', [status(thm)], ['70', '71', '72', '73'])).
% 0.22/0.52  thf('75', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('76', plain,
% 0.22/0.52      ((v1_funct_2 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D) @ 
% 0.22/0.52        (k2_zfmisc_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ (k8_eqrel_1 @ sk_A @ sk_B)) @ 
% 0.22/0.52        (k8_eqrel_1 @ sk_A @ sk_B))),
% 0.22/0.52      inference('clc', [status(thm)], ['74', '75'])).
% 0.22/0.52  thf('77', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('78', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_D @ 
% 0.22/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.22/0.52      inference('clc', [status(thm)], ['10', '11'])).
% 0.22/0.52  thf('79', plain,
% 0.22/0.52      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X16)))
% 0.22/0.52          | ~ (v8_relat_2 @ X15)
% 0.22/0.52          | ~ (v3_relat_2 @ X15)
% 0.22/0.52          | ~ (v1_partfun1 @ X15 @ X16)
% 0.22/0.52          | (v1_xboole_0 @ X16)
% 0.22/0.52          | ~ (v1_funct_1 @ X17)
% 0.22/0.52          | ~ (v1_funct_2 @ X17 @ (k2_zfmisc_1 @ X16 @ X16) @ X16)
% 0.22/0.52          | ~ (m1_subset_1 @ X17 @ 
% 0.22/0.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X16) @ X16)))
% 0.22/0.52          | (v1_funct_1 @ (k3_filter_1 @ X16 @ X15 @ X17)))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k3_filter_1])).
% 0.22/0.52  thf('80', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v1_funct_1 @ (k3_filter_1 @ sk_A @ X0 @ sk_D))
% 0.22/0.52          | ~ (v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.22/0.52          | ~ (v1_funct_1 @ sk_D)
% 0.22/0.52          | (v1_xboole_0 @ sk_A)
% 0.22/0.52          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.22/0.52          | ~ (v3_relat_2 @ X0)
% 0.22/0.52          | ~ (v8_relat_2 @ X0)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.22/0.52      inference('sup-', [status(thm)], ['78', '79'])).
% 0.22/0.52  thf('81', plain, ((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.22/0.52      inference('clc', [status(thm)], ['19', '20'])).
% 0.22/0.52  thf('82', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.52      inference('clc', [status(thm)], ['26', '27'])).
% 0.22/0.52  thf('83', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((v1_funct_1 @ (k3_filter_1 @ sk_A @ X0 @ sk_D))
% 0.22/0.52          | (v1_xboole_0 @ sk_A)
% 0.22/0.52          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.22/0.52          | ~ (v3_relat_2 @ X0)
% 0.22/0.52          | ~ (v8_relat_2 @ X0)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A))))),
% 0.22/0.52      inference('demod', [status(thm)], ['80', '81', '82'])).
% 0.22/0.52  thf('84', plain,
% 0.22/0.52      ((~ (v8_relat_2 @ sk_B)
% 0.22/0.52        | ~ (v3_relat_2 @ sk_B)
% 0.22/0.52        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.22/0.52        | (v1_xboole_0 @ sk_A)
% 0.22/0.52        | (v1_funct_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['77', '83'])).
% 0.22/0.52  thf('85', plain, ((v8_relat_2 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('86', plain, ((v3_relat_2 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('87', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('88', plain,
% 0.22/0.52      (((v1_xboole_0 @ sk_A)
% 0.22/0.52        | (v1_funct_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.22/0.52      inference('demod', [status(thm)], ['84', '85', '86', '87'])).
% 0.22/0.52  thf('89', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('90', plain, ((v1_funct_1 @ (k3_filter_1 @ sk_A @ sk_B @ sk_D))),
% 0.22/0.52      inference('clc', [status(thm)], ['88', '89'])).
% 0.22/0.52  thf('91', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X0 @ (k8_eqrel_1 @ sk_A @ sk_B))
% 0.22/0.52          | (r3_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.22/0.52             (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.22/0.52          | ~ (r2_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.22/0.52               (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.22/0.52          | ~ (r1_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ X0 @ 
% 0.22/0.52               (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.22/0.52      inference('demod', [status(thm)], ['62', '76', '90'])).
% 0.22/0.52  thf('92', plain,
% 0.22/0.52      ((~ (r1_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.52           (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.22/0.52           (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.22/0.52        | (r3_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.52           (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.22/0.52           (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.22/0.52        | ~ (m1_subset_1 @ (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.22/0.52             (k8_eqrel_1 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['46', '91'])).
% 0.22/0.52  thf('93', plain, ((r3_binop_1 @ sk_A @ sk_C @ sk_D)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('94', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_D @ 
% 0.22/0.52        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)))),
% 0.22/0.52      inference('clc', [status(thm)], ['10', '11'])).
% 0.22/0.52  thf('95', plain,
% 0.22/0.52      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.52         (~ (v1_funct_1 @ X12)
% 0.22/0.52          | ~ (v1_funct_2 @ X12 @ (k2_zfmisc_1 @ X13 @ X13) @ X13)
% 0.22/0.52          | ~ (m1_subset_1 @ X12 @ 
% 0.22/0.52               (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k2_zfmisc_1 @ X13 @ X13) @ X13)))
% 0.22/0.52          | ~ (r3_binop_1 @ X13 @ X14 @ X12)
% 0.22/0.52          | (r1_binop_1 @ X13 @ X14 @ X12)
% 0.22/0.52          | ~ (m1_subset_1 @ X14 @ X13))),
% 0.22/0.52      inference('cnf', [status(esa)], [d7_binop_1])).
% 0.22/0.52  thf('96', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.22/0.52          | (r1_binop_1 @ sk_A @ X0 @ sk_D)
% 0.22/0.52          | ~ (r3_binop_1 @ sk_A @ X0 @ sk_D)
% 0.22/0.52          | ~ (v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)
% 0.22/0.52          | ~ (v1_funct_1 @ sk_D))),
% 0.22/0.52      inference('sup-', [status(thm)], ['94', '95'])).
% 0.22/0.52  thf('97', plain, ((v1_funct_2 @ sk_D @ (k2_zfmisc_1 @ sk_A @ sk_A) @ sk_A)),
% 0.22/0.52      inference('clc', [status(thm)], ['19', '20'])).
% 0.22/0.52  thf('98', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.52      inference('clc', [status(thm)], ['26', '27'])).
% 0.22/0.52  thf('99', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.22/0.52          | (r1_binop_1 @ sk_A @ X0 @ sk_D)
% 0.22/0.52          | ~ (r3_binop_1 @ sk_A @ X0 @ sk_D))),
% 0.22/0.52      inference('demod', [status(thm)], ['96', '97', '98'])).
% 0.22/0.52  thf('100', plain,
% 0.22/0.52      (((r1_binop_1 @ sk_A @ sk_C @ sk_D) | ~ (m1_subset_1 @ sk_C @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['93', '99'])).
% 0.22/0.52  thf('101', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('102', plain, ((r1_binop_1 @ sk_A @ sk_C @ sk_D)),
% 0.22/0.52      inference('demod', [status(thm)], ['100', '101'])).
% 0.22/0.52  thf('103', plain, ((m2_filter_1 @ sk_D @ sk_A @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('104', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(t6_filter_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( ( v1_partfun1 @ B @ A ) & ( v3_relat_2 @ B ) & 
% 0.22/0.52             ( v8_relat_2 @ B ) & 
% 0.22/0.52             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.52           ( ![C:$i]:
% 0.22/0.52             ( ( m1_subset_1 @ C @ A ) =>
% 0.22/0.52               ( ![D:$i]:
% 0.22/0.52                 ( ( m2_filter_1 @ D @ A @ B ) =>
% 0.22/0.52                   ( ( r1_binop_1 @ A @ C @ D ) =>
% 0.22/0.52                     ( r1_binop_1 @
% 0.22/0.52                       ( k8_eqrel_1 @ A @ B ) @ ( k9_eqrel_1 @ A @ B @ C ) @ 
% 0.22/0.52                       ( k3_filter_1 @ A @ B @ D ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.52  thf('105', plain,
% 0.22/0.52      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.22/0.52         (~ (v1_partfun1 @ X28 @ X29)
% 0.22/0.52          | ~ (v3_relat_2 @ X28)
% 0.22/0.52          | ~ (v8_relat_2 @ X28)
% 0.22/0.52          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))
% 0.22/0.52          | ~ (m2_filter_1 @ X30 @ X29 @ X28)
% 0.22/0.52          | (r1_binop_1 @ (k8_eqrel_1 @ X29 @ X28) @ 
% 0.22/0.52             (k9_eqrel_1 @ X29 @ X28 @ X31) @ (k3_filter_1 @ X29 @ X28 @ X30))
% 0.22/0.52          | ~ (r1_binop_1 @ X29 @ X31 @ X30)
% 0.22/0.52          | ~ (m1_subset_1 @ X31 @ X29)
% 0.22/0.52          | (v1_xboole_0 @ X29))),
% 0.22/0.52      inference('cnf', [status(esa)], [t6_filter_1])).
% 0.22/0.52  thf('106', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((v1_xboole_0 @ sk_A)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.22/0.52          | ~ (r1_binop_1 @ sk_A @ X0 @ X1)
% 0.22/0.52          | (r1_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.52             (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ (k3_filter_1 @ sk_A @ sk_B @ X1))
% 0.22/0.52          | ~ (m2_filter_1 @ X1 @ sk_A @ sk_B)
% 0.22/0.52          | ~ (v8_relat_2 @ sk_B)
% 0.22/0.52          | ~ (v3_relat_2 @ sk_B)
% 0.22/0.52          | ~ (v1_partfun1 @ sk_B @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['104', '105'])).
% 0.22/0.52  thf('107', plain, ((v8_relat_2 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('108', plain, ((v3_relat_2 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('109', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('110', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         ((v1_xboole_0 @ sk_A)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.22/0.52          | ~ (r1_binop_1 @ sk_A @ X0 @ X1)
% 0.22/0.52          | (r1_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.52             (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ (k3_filter_1 @ sk_A @ sk_B @ X1))
% 0.22/0.52          | ~ (m2_filter_1 @ X1 @ sk_A @ sk_B))),
% 0.22/0.52      inference('demod', [status(thm)], ['106', '107', '108', '109'])).
% 0.22/0.52  thf('111', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((r1_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.52           (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ (k3_filter_1 @ sk_A @ sk_B @ sk_D))
% 0.22/0.52          | ~ (r1_binop_1 @ sk_A @ X0 @ sk_D)
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.22/0.52          | (v1_xboole_0 @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['103', '110'])).
% 0.22/0.52  thf('112', plain,
% 0.22/0.52      (((v1_xboole_0 @ sk_A)
% 0.22/0.52        | ~ (m1_subset_1 @ sk_C @ sk_A)
% 0.22/0.52        | (r1_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.52           (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.22/0.52           (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['102', '111'])).
% 0.22/0.52  thf('113', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('114', plain,
% 0.22/0.52      (((v1_xboole_0 @ sk_A)
% 0.22/0.52        | (r1_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.52           (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.22/0.52           (k3_filter_1 @ sk_A @ sk_B @ sk_D)))),
% 0.22/0.52      inference('demod', [status(thm)], ['112', '113'])).
% 0.22/0.52  thf('115', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('116', plain,
% 0.22/0.52      ((r1_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.52        (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ (k3_filter_1 @ sk_A @ sk_B @ sk_D))),
% 0.22/0.52      inference('clc', [status(thm)], ['114', '115'])).
% 0.22/0.52  thf('117', plain, ((m1_subset_1 @ sk_C @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('118', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(dt_k9_eqrel_1, axiom,
% 0.22/0.52    (![A:$i,B:$i,C:$i]:
% 0.22/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v3_relat_2 @ B ) & ( v8_relat_2 @ B ) & 
% 0.22/0.52         ( v1_partfun1 @ B @ A ) & 
% 0.22/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) & 
% 0.22/0.52         ( m1_subset_1 @ C @ A ) ) =>
% 0.22/0.52       ( m2_subset_1 @
% 0.22/0.52         ( k9_eqrel_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ A ) @ 
% 0.22/0.52         ( k8_eqrel_1 @ A @ B ) ) ))).
% 0.22/0.52  thf('119', plain,
% 0.22/0.52      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X21)))
% 0.22/0.52          | ~ (v1_partfun1 @ X20 @ X21)
% 0.22/0.52          | ~ (v8_relat_2 @ X20)
% 0.22/0.52          | ~ (v3_relat_2 @ X20)
% 0.22/0.52          | (v1_xboole_0 @ X21)
% 0.22/0.52          | ~ (m1_subset_1 @ X22 @ X21)
% 0.22/0.52          | (m2_subset_1 @ (k9_eqrel_1 @ X21 @ X20 @ X22) @ 
% 0.22/0.52             (k1_zfmisc_1 @ X21) @ (k8_eqrel_1 @ X21 @ X20)))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k9_eqrel_1])).
% 0.22/0.52  thf('120', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((m2_subset_1 @ (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ 
% 0.22/0.52           (k1_zfmisc_1 @ sk_A) @ (k8_eqrel_1 @ sk_A @ sk_B))
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.22/0.52          | (v1_xboole_0 @ sk_A)
% 0.22/0.52          | ~ (v3_relat_2 @ sk_B)
% 0.22/0.52          | ~ (v8_relat_2 @ sk_B)
% 0.22/0.52          | ~ (v1_partfun1 @ sk_B @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['118', '119'])).
% 0.22/0.52  thf('121', plain, ((v3_relat_2 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('122', plain, ((v8_relat_2 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('123', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('124', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         ((m2_subset_1 @ (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ 
% 0.22/0.52           (k1_zfmisc_1 @ sk_A) @ (k8_eqrel_1 @ sk_A @ sk_B))
% 0.22/0.52          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.22/0.52          | (v1_xboole_0 @ sk_A))),
% 0.22/0.52      inference('demod', [status(thm)], ['120', '121', '122', '123'])).
% 0.22/0.52  thf('125', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('126', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.22/0.52          | (m2_subset_1 @ (k9_eqrel_1 @ sk_A @ sk_B @ X0) @ 
% 0.22/0.52             (k1_zfmisc_1 @ sk_A) @ (k8_eqrel_1 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('clc', [status(thm)], ['124', '125'])).
% 0.22/0.52  thf('127', plain,
% 0.22/0.52      ((m2_subset_1 @ (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.22/0.52        (k1_zfmisc_1 @ sk_A) @ (k8_eqrel_1 @ sk_A @ sk_B))),
% 0.22/0.52      inference('sup-', [status(thm)], ['117', '126'])).
% 0.22/0.52  thf('128', plain,
% 0.22/0.52      ((m1_subset_1 @ sk_B @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf(dt_k8_eqrel_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( v3_relat_2 @ B ) & ( v8_relat_2 @ B ) & ( v1_partfun1 @ B @ A ) & 
% 0.22/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.22/0.52       ( m1_eqrel_1 @ ( k8_eqrel_1 @ A @ B ) @ A ) ))).
% 0.22/0.52  thf('129', plain,
% 0.22/0.52      (![X18 : $i, X19 : $i]:
% 0.22/0.52         ((m1_eqrel_1 @ (k8_eqrel_1 @ X18 @ X19) @ X18)
% 0.22/0.52          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X18)))
% 0.22/0.52          | ~ (v1_partfun1 @ X19 @ X18)
% 0.22/0.52          | ~ (v8_relat_2 @ X19)
% 0.22/0.52          | ~ (v3_relat_2 @ X19))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_k8_eqrel_1])).
% 0.22/0.52  thf('130', plain,
% 0.22/0.52      ((~ (v3_relat_2 @ sk_B)
% 0.22/0.52        | ~ (v8_relat_2 @ sk_B)
% 0.22/0.52        | ~ (v1_partfun1 @ sk_B @ sk_A)
% 0.22/0.52        | (m1_eqrel_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ sk_A))),
% 0.22/0.52      inference('sup-', [status(thm)], ['128', '129'])).
% 0.22/0.52  thf('131', plain, ((v3_relat_2 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('132', plain, ((v8_relat_2 @ sk_B)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('133', plain, ((v1_partfun1 @ sk_B @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('134', plain, ((m1_eqrel_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.52      inference('demod', [status(thm)], ['130', '131', '132', '133'])).
% 0.22/0.52  thf(dt_m1_eqrel_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( m1_eqrel_1 @ B @ A ) =>
% 0.22/0.52       ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ))).
% 0.22/0.52  thf('135', plain,
% 0.22/0.52      (![X23 : $i, X24 : $i]:
% 0.22/0.52         ((m1_subset_1 @ X23 @ (k1_zfmisc_1 @ (k1_zfmisc_1 @ X24)))
% 0.22/0.52          | ~ (m1_eqrel_1 @ X23 @ X24))),
% 0.22/0.52      inference('cnf', [status(esa)], [dt_m1_eqrel_1])).
% 0.22/0.52  thf('136', plain,
% 0.22/0.52      ((m1_subset_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['134', '135'])).
% 0.22/0.52  thf(redefinition_m2_subset_1, axiom,
% 0.22/0.52    (![A:$i,B:$i]:
% 0.22/0.52     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.22/0.52         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.22/0.52       ( ![C:$i]: ( ( m2_subset_1 @ C @ A @ B ) <=> ( m1_subset_1 @ C @ B ) ) ) ))).
% 0.22/0.52  thf('137', plain,
% 0.22/0.52      (![X6 : $i, X7 : $i, X9 : $i]:
% 0.22/0.52         ((v1_xboole_0 @ X6)
% 0.22/0.52          | (v1_xboole_0 @ X7)
% 0.22/0.52          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X6))
% 0.22/0.52          | (m1_subset_1 @ X9 @ X7)
% 0.22/0.52          | ~ (m2_subset_1 @ X9 @ X6 @ X7))),
% 0.22/0.52      inference('cnf', [status(esa)], [redefinition_m2_subset_1])).
% 0.22/0.52  thf('138', plain,
% 0.22/0.52      (![X0 : $i]:
% 0.22/0.52         (~ (m2_subset_1 @ X0 @ (k1_zfmisc_1 @ sk_A) @ 
% 0.22/0.52             (k8_eqrel_1 @ sk_A @ sk_B))
% 0.22/0.52          | (m1_subset_1 @ X0 @ (k8_eqrel_1 @ sk_A @ sk_B))
% 0.22/0.52          | (v1_xboole_0 @ (k8_eqrel_1 @ sk_A @ sk_B))
% 0.22/0.52          | (v1_xboole_0 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['136', '137'])).
% 0.22/0.52  thf('139', plain,
% 0.22/0.52      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.52        | (v1_xboole_0 @ (k8_eqrel_1 @ sk_A @ sk_B))
% 0.22/0.52        | (m1_subset_1 @ (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.22/0.52           (k8_eqrel_1 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['127', '138'])).
% 0.22/0.52  thf('140', plain,
% 0.22/0.52      ((m1_subset_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.52        (k1_zfmisc_1 @ (k1_zfmisc_1 @ sk_A)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['134', '135'])).
% 0.22/0.52  thf(cc1_subset_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( v1_xboole_0 @ A ) =>
% 0.22/0.52       ( ![B:$i]:
% 0.22/0.52         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_xboole_0 @ B ) ) ) ))).
% 0.22/0.52  thf('141', plain,
% 0.22/0.52      (![X0 : $i, X1 : $i]:
% 0.22/0.52         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.22/0.52          | (v1_xboole_0 @ X0)
% 0.22/0.52          | ~ (v1_xboole_0 @ X1))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc1_subset_1])).
% 0.22/0.52  thf('142', plain,
% 0.22/0.52      ((~ (v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))
% 0.22/0.52        | (v1_xboole_0 @ (k8_eqrel_1 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['140', '141'])).
% 0.22/0.52  thf('143', plain, ((m1_eqrel_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ sk_A)),
% 0.22/0.52      inference('demod', [status(thm)], ['130', '131', '132', '133'])).
% 0.22/0.52  thf(cc1_eqrel_1, axiom,
% 0.22/0.52    (![A:$i]:
% 0.22/0.52     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.52       ( ![B:$i]: ( ( m1_eqrel_1 @ B @ A ) => ( ~( v1_xboole_0 @ B ) ) ) ) ))).
% 0.22/0.52  thf('144', plain,
% 0.22/0.52      (![X10 : $i, X11 : $i]:
% 0.22/0.52         (~ (m1_eqrel_1 @ X10 @ X11)
% 0.22/0.52          | ~ (v1_xboole_0 @ X10)
% 0.22/0.52          | (v1_xboole_0 @ X11))),
% 0.22/0.52      inference('cnf', [status(esa)], [cc1_eqrel_1])).
% 0.22/0.52  thf('145', plain,
% 0.22/0.52      (((v1_xboole_0 @ sk_A) | ~ (v1_xboole_0 @ (k8_eqrel_1 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('sup-', [status(thm)], ['143', '144'])).
% 0.22/0.52  thf('146', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.22/0.52      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.52  thf('147', plain, (~ (v1_xboole_0 @ (k8_eqrel_1 @ sk_A @ sk_B))),
% 0.22/0.52      inference('clc', [status(thm)], ['145', '146'])).
% 0.22/0.52  thf('148', plain, (~ (v1_xboole_0 @ (k1_zfmisc_1 @ sk_A))),
% 0.22/0.52      inference('clc', [status(thm)], ['142', '147'])).
% 0.22/0.52  thf('149', plain,
% 0.22/0.52      (((m1_subset_1 @ (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.22/0.52         (k8_eqrel_1 @ sk_A @ sk_B))
% 0.22/0.52        | (v1_xboole_0 @ (k8_eqrel_1 @ sk_A @ sk_B)))),
% 0.22/0.52      inference('clc', [status(thm)], ['139', '148'])).
% 0.22/0.52  thf('150', plain, (~ (v1_xboole_0 @ (k8_eqrel_1 @ sk_A @ sk_B))),
% 0.22/0.52      inference('clc', [status(thm)], ['145', '146'])).
% 0.22/0.52  thf('151', plain,
% 0.22/0.52      ((m1_subset_1 @ (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ 
% 0.22/0.52        (k8_eqrel_1 @ sk_A @ sk_B))),
% 0.22/0.52      inference('clc', [status(thm)], ['149', '150'])).
% 0.22/0.52  thf('152', plain,
% 0.22/0.52      ((r3_binop_1 @ (k8_eqrel_1 @ sk_A @ sk_B) @ 
% 0.22/0.52        (k9_eqrel_1 @ sk_A @ sk_B @ sk_C) @ (k3_filter_1 @ sk_A @ sk_B @ sk_D))),
% 0.22/0.52      inference('demod', [status(thm)], ['92', '116', '151'])).
% 0.22/0.52  thf('153', plain, ($false), inference('demod', [status(thm)], ['0', '152'])).
% 0.22/0.52  
% 0.22/0.52  % SZS output end Refutation
% 0.22/0.52  
% 0.22/0.53  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
