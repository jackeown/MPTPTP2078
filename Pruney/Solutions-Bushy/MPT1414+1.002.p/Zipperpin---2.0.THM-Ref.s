%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1414+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1YzIGcnjCP

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  199 ( 564 expanded)
%              Number of leaves         :   40 ( 179 expanded)
%              Depth                    :   20
%              Number of atoms          : 2152 (11433 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k9_eqrel_1_type,type,(
    k9_eqrel_1: $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_eqrel_1_type,type,(
    m1_eqrel_1: $i > $i > $o )).

thf(v3_relat_2_type,type,(
    v3_relat_2: $i > $o )).

thf(r3_binop_1_type,type,(
    r3_binop_1: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r2_binop_1_type,type,(
    r2_binop_1: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_filter_1_type,type,(
    k3_filter_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m2_subset_1_type,type,(
    m2_subset_1: $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(m2_filter_1_type,type,(
    m2_filter_1: $i > $i > $i > $o )).

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
    ! [X11: $i,X12: $i] :
      ( ( m1_eqrel_1 @ ( k8_eqrel_1 @ X11 @ X12 ) @ X11 )
      | ~ ( m1_subset_1 @ X12 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X11 ) ) )
      | ~ ( v1_partfun1 @ X12 @ X11 )
      | ~ ( v8_relat_2 @ X12 )
      | ~ ( v3_relat_2 @ X12 ) ) ),
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

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('11',plain,(
    ! [X21: $i] :
      ( m1_subset_1 @ ( sk_B @ X21 ) @ X21 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('12',plain,(
    ! [X26: $i,X27: $i] :
      ( ( r2_hidden @ X26 @ X27 )
      | ( v1_xboole_0 @ X27 )
      | ~ ( m1_subset_1 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    m1_eqrel_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ sk_A ),
    inference(demod,[status(thm)],['2','3','4','5'])).

thf(dt_m1_eqrel_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_eqrel_1 @ B @ A )
     => ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('15',plain,(
    ! [X16: $i,X17: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X17 ) ) )
      | ~ ( m1_eqrel_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[dt_m1_eqrel_1])).

thf('16',plain,(
    m1_subset_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('17',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( r2_hidden @ X28 @ X29 )
      | ~ ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
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

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X14 ) ) )
      | ~ ( v1_partfun1 @ X13 @ X14 )
      | ~ ( v8_relat_2 @ X13 )
      | ~ ( v3_relat_2 @ X13 )
      | ( v1_xboole_0 @ X14 )
      | ~ ( m1_subset_1 @ X15 @ X14 )
      | ( m2_subset_1 @ ( k9_eqrel_1 @ X14 @ X13 @ X15 ) @ ( k1_zfmisc_1 @ X14 ) @ ( k8_eqrel_1 @ X14 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_eqrel_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( m2_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v3_relat_2 @ sk_B_1 )
      | ~ ( v8_relat_2 @ sk_B_1 )
      | ~ ( v1_partfun1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v3_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v8_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_partfun1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( m2_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23','24','25'])).

thf('27',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( m2_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_A ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['26','27'])).

thf('29',plain,(
    m2_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ sk_C ) @ ( k1_zfmisc_1 @ sk_A ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['19','28'])).

thf('30',plain,(
    m1_subset_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(redefinition_m2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) )
     => ! [C: $i] :
          ( ( m2_subset_1 @ C @ A @ B )
        <=> ( m1_subset_1 @ C @ B ) ) ) )).

thf('31',plain,(
    ! [X22: $i,X23: $i,X25: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ X22 ) )
      | ( m1_subset_1 @ X25 @ X23 )
      | ~ ( m2_subset_1 @ X25 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_m2_subset_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( m2_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_A ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ( m1_subset_1 @ X0 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) )
    | ( m1_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ sk_C ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ~ ( v1_xboole_0 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['8','9'])).

thf('35',plain,
    ( ( m1_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ sk_C ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) )
    | ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(clc,[status(thm)],['33','34'])).

thf('36',plain,(
    r3_binop_1 @ sk_A @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
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

thf('38',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( v1_relat_1 @ X19 )
      | ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X18 ) @ X18 ) ) )
      | ~ ( m2_filter_1 @ X20 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_filter_1])).

thf('39',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('41',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( v1_relat_1 @ X2 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('42',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['39','42'])).

thf('44',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['43','44'])).

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

thf('46',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_funct_2 @ X5 @ ( k2_zfmisc_1 @ X6 @ X6 ) @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X6 ) @ X6 ) ) )
      | ~ ( r3_binop_1 @ X6 @ X7 @ X5 )
      | ( r2_binop_1 @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d7_binop_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r2_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( r3_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    m2_filter_1 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( v1_relat_1 @ X19 )
      | ( v1_funct_2 @ X20 @ ( k2_zfmisc_1 @ X18 @ X18 ) @ X18 )
      | ~ ( m2_filter_1 @ X20 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_filter_1])).

thf('50',plain,
    ( ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['40','41'])).

thf('52',plain,
    ( ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['52','53'])).

thf('55',plain,(
    m2_filter_1 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_xboole_0 @ X18 )
      | ~ ( v1_relat_1 @ X19 )
      | ( v1_funct_1 @ X20 )
      | ~ ( m2_filter_1 @ X20 @ X18 @ X19 ) ) ),
    inference(cnf,[status(esa)],[dt_m2_filter_1])).

thf('57',plain,
    ( ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['40','41'])).

thf('59',plain,
    ( ( v1_funct_1 @ sk_D )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('60',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r2_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( r3_binop_1 @ sk_A @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['47','54','61'])).

thf('63',plain,
    ( ( r2_binop_1 @ sk_A @ sk_C @ sk_D )
    | ~ ( m1_subset_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['36','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    r2_binop_1 @ sk_A @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    m2_filter_1 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
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

thf('68',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_partfun1 @ X35 @ X36 )
      | ~ ( v3_relat_2 @ X35 )
      | ~ ( v8_relat_2 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X36 ) ) )
      | ~ ( m2_filter_1 @ X37 @ X36 @ X35 )
      | ( r2_binop_1 @ ( k8_eqrel_1 @ X36 @ X35 ) @ ( k9_eqrel_1 @ X36 @ X35 @ X38 ) @ ( k3_filter_1 @ X36 @ X35 @ X37 ) )
      | ~ ( r2_binop_1 @ X36 @ X38 @ X37 )
      | ~ ( m1_subset_1 @ X38 @ X36 )
      | ( v1_xboole_0 @ X36 ) ) ),
    inference(cnf,[status(esa)],[t7_filter_1])).

thf('69',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r2_binop_1 @ sk_A @ X0 @ X1 )
      | ( r2_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B_1 @ X1 ) )
      | ~ ( m2_filter_1 @ X1 @ sk_A @ sk_B_1 )
      | ~ ( v8_relat_2 @ sk_B_1 )
      | ~ ( v3_relat_2 @ sk_B_1 )
      | ~ ( v1_partfun1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    v8_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v3_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    v1_partfun1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r2_binop_1 @ sk_A @ X0 @ X1 )
      | ( r2_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B_1 @ X1 ) )
      | ~ ( m2_filter_1 @ X1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['69','70','71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( r2_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) )
      | ~ ( r2_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['66','73'])).

thf('75',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r2_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['65','74'])).

thf('76',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r2_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    r2_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) ),
    inference(clc,[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['43','44'])).

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

thf('82',plain,(
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

thf('83',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) ) )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['52','53'])).

thf('85',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['59','60'])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['83','84','85'])).

thf('87',plain,
    ( ~ ( v8_relat_2 @ sk_B_1 )
    | ~ ( v3_relat_2 @ sk_B_1 )
    | ~ ( v1_partfun1 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['80','86'])).

thf('88',plain,(
    v8_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    v3_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_partfun1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['87','88','89','90'])).

thf('92',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    m1_subset_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_funct_2 @ X5 @ ( k2_zfmisc_1 @ X6 @ X6 ) @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X6 ) @ X6 ) ) )
      | ~ ( r1_binop_1 @ X6 @ X7 @ X5 )
      | ~ ( r2_binop_1 @ X6 @ X7 @ X5 )
      | ( r3_binop_1 @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d7_binop_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ( r3_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) )
      | ~ ( r2_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) )
      | ~ ( r1_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) )
      | ~ ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ~ ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('98',plain,(
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

thf('99',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['52','53'])).

thf('101',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['59','60'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['99','100','101'])).

thf('103',plain,
    ( ~ ( v8_relat_2 @ sk_B_1 )
    | ~ ( v3_relat_2 @ sk_B_1 )
    | ~ ( v1_partfun1 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['96','102'])).

thf('104',plain,(
    v8_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v3_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    v1_partfun1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['103','104','105','106'])).

thf('108',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_funct_1 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) ),
    inference(clc,[status(thm)],['107','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ( r3_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) )
      | ~ ( r2_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) )
      | ~ ( r1_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) )
      | ~ ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['95','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('113',plain,(
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

thf('114',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['52','53'])).

thf('116',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['59','60'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ X0 @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ X0 ) @ ( k8_eqrel_1 @ sk_A @ X0 ) ) @ ( k8_eqrel_1 @ sk_A @ X0 ) )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v3_relat_2 @ X0 )
      | ~ ( v8_relat_2 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,
    ( ~ ( v8_relat_2 @ sk_B_1 )
    | ~ ( v3_relat_2 @ sk_B_1 )
    | ~ ( v1_partfun1 @ sk_B_1 @ sk_A )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['111','117'])).

thf('119',plain,(
    v8_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v3_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    v1_partfun1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['118','119','120','121'])).

thf('123',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_2 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) @ ( k2_zfmisc_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) )
      | ( r3_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) )
      | ~ ( r2_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) )
      | ~ ( r1_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ X0 @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['110','124'])).

thf('126',plain,
    ( ~ ( r1_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) )
    | ( r3_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) )
    | ~ ( m1_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ sk_C ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['79','125'])).

thf('127',plain,(
    r3_binop_1 @ sk_A @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ) ) ),
    inference(clc,[status(thm)],['43','44'])).

thf('129',plain,(
    ! [X5: $i,X6: $i,X7: $i] :
      ( ~ ( v1_funct_1 @ X5 )
      | ~ ( v1_funct_2 @ X5 @ ( k2_zfmisc_1 @ X6 @ X6 ) @ X6 )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X6 @ X6 ) @ X6 ) ) )
      | ~ ( r3_binop_1 @ X6 @ X7 @ X5 )
      | ( r1_binop_1 @ X6 @ X7 @ X5 )
      | ~ ( m1_subset_1 @ X7 @ X6 ) ) ),
    inference(cnf,[status(esa)],[d7_binop_1])).

thf('130',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r1_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( r3_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['128','129'])).

thf('131',plain,(
    v1_funct_2 @ sk_D @ ( k2_zfmisc_1 @ sk_A @ sk_A ) @ sk_A ),
    inference(clc,[status(thm)],['52','53'])).

thf('132',plain,(
    v1_funct_1 @ sk_D ),
    inference(clc,[status(thm)],['59','60'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r1_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( r3_binop_1 @ sk_A @ X0 @ sk_D ) ) ),
    inference(demod,[status(thm)],['130','131','132'])).

thf('134',plain,
    ( ( r1_binop_1 @ sk_A @ sk_C @ sk_D )
    | ~ ( m1_subset_1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['127','133'])).

thf('135',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    r1_binop_1 @ sk_A @ sk_C @ sk_D ),
    inference(demod,[status(thm)],['134','135'])).

thf('137',plain,(
    m2_filter_1 @ sk_D @ sk_A @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
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

thf('139',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( v1_partfun1 @ X31 @ X32 )
      | ~ ( v3_relat_2 @ X31 )
      | ~ ( v8_relat_2 @ X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X32 ) ) )
      | ~ ( m2_filter_1 @ X33 @ X32 @ X31 )
      | ( r1_binop_1 @ ( k8_eqrel_1 @ X32 @ X31 ) @ ( k9_eqrel_1 @ X32 @ X31 @ X34 ) @ ( k3_filter_1 @ X32 @ X31 @ X33 ) )
      | ~ ( r1_binop_1 @ X32 @ X34 @ X33 )
      | ~ ( m1_subset_1 @ X34 @ X32 )
      | ( v1_xboole_0 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t6_filter_1])).

thf('140',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r1_binop_1 @ sk_A @ X0 @ X1 )
      | ( r1_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B_1 @ X1 ) )
      | ~ ( m2_filter_1 @ X1 @ sk_A @ sk_B_1 )
      | ~ ( v8_relat_2 @ sk_B_1 )
      | ~ ( v3_relat_2 @ sk_B_1 )
      | ~ ( v1_partfun1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['138','139'])).

thf('141',plain,(
    v8_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v3_relat_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v1_partfun1 @ sk_B_1 @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( r1_binop_1 @ sk_A @ X0 @ X1 )
      | ( r1_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B_1 @ X1 ) )
      | ~ ( m2_filter_1 @ X1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['140','141','142','143'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( r1_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ X0 ) @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) )
      | ~ ( r1_binop_1 @ sk_A @ X0 @ sk_D )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['137','144'])).

thf('146',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( m1_subset_1 @ sk_C @ sk_A )
    | ( r1_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['136','145'])).

thf('147',plain,(
    m1_subset_1 @ sk_C @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( r1_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference(demod,[status(thm)],['146','147'])).

thf('149',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    r1_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) ),
    inference(clc,[status(thm)],['148','149'])).

thf('151',plain,
    ( ( r3_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) )
    | ~ ( m1_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ sk_C ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['126','150'])).

thf('152',plain,(
    ~ ( r3_binop_1 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ sk_C ) @ ( k3_filter_1 @ sk_A @ sk_B_1 @ sk_D ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    ~ ( m1_subset_1 @ ( k9_eqrel_1 @ sk_A @ sk_B_1 @ sk_C ) @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['151','152'])).

thf('154',plain,(
    v1_xboole_0 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['35','153'])).

thf('155',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['18','154'])).

thf('156',plain,(
    v1_xboole_0 @ ( k8_eqrel_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['13','155'])).

thf('157',plain,(
    $false ),
    inference(demod,[status(thm)],['10','156'])).


%------------------------------------------------------------------------------
