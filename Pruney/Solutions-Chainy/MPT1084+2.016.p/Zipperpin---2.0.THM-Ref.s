%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oU6luTv0SE

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 469 expanded)
%              Number of leaves         :   32 ( 155 expanded)
%              Depth                    :   15
%              Number of atoms          :  853 (6764 expanded)
%              Number of equality atoms :   52 ( 236 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

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
    ~ ( r2_funct_2 @ sk_A @ sk_A @ sk_B_1 @ ( k6_partfun1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( v1_partfun1 @ X16 @ X17 )
      | ~ ( v1_funct_2 @ X16 @ X17 @ X18 )
      | ~ ( v1_funct_1 @ X16 )
      | ( v1_xboole_0 @ X18 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('3',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( v1_partfun1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_partfun1 @ sk_B_1 @ sk_A ) ),
    inference(demod,[status(thm)],['3','4','5'])).

thf('7',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    v1_partfun1 @ sk_B_1 @ sk_A ),
    inference(clc,[status(thm)],['6','7'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('9',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v1_partfun1 @ X20 @ X19 )
      | ( ( k1_relat_1 @ X20 )
        = X19 )
      | ~ ( v4_relat_1 @ X20 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v4_relat_1 @ sk_B_1 @ sk_A )
    | ( ( k1_relat_1 @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) )
      | ( v1_relat_1 @ X6 )
      | ~ ( v1_relat_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) )
    | ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X8: $i,X9: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('17',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v4_relat_1 @ X13 @ X14 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('18',plain,(
    v4_relat_1 @ sk_B_1 @ sk_A ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['10','15','18'])).

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

thf('20',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k1_relat_1 @ X11 )
       != X10 )
      | ( r2_hidden @ ( sk_C @ X11 @ X10 ) @ X10 )
      | ( X11
        = ( k6_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('21',plain,(
    ! [X11: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X11
        = ( k6_relat_1 @ ( k1_relat_1 @ X11 ) ) )
      | ( r2_hidden @ ( sk_C @ X11 @ ( k1_relat_1 @ X11 ) ) @ ( k1_relat_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('22',plain,(
    ! [X25: $i] :
      ( ( k6_partfun1 @ X25 )
      = ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('23',plain,(
    ! [X11: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X11
        = ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) )
      | ( r2_hidden @ ( sk_C @ X11 @ ( k1_relat_1 @ X11 ) ) @ ( k1_relat_1 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ ( k1_relat_1 @ sk_B_1 ) )
    | ( sk_B_1
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['19','23'])).

thf('25',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['10','15','18'])).

thf('26',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['10','15','18'])).

thf('27',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('29',plain,
    ( ( r2_hidden @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ( sk_B_1
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','26','27','28'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('30',plain,(
    ! [X3: $i,X4: $i] :
      ( ~ ( r2_hidden @ X3 @ X4 )
      | ( m1_subset_1 @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d2_subset_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('32',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(clc,[status(thm)],['30','31'])).

thf('33',plain,
    ( ( sk_B_1
      = ( k6_partfun1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('34',plain,(
    ! [X30: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B_1 @ X30 )
        = X30 )
      | ~ ( m1_subset_1 @ X30 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( sk_B_1
      = ( k6_partfun1 @ sk_A ) )
    | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      = ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( sk_B_1
      = ( k6_partfun1 @ sk_A ) )
    | ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A ) ),
    inference('sup-',[status(thm)],['29','32'])).

thf('37',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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

thf('38',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X21 @ X22 @ X23 )
      | ~ ( v1_funct_1 @ X21 )
      | ( v1_xboole_0 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ X22 )
      | ( ( k3_funct_2 @ X22 @ X23 @ X21 @ X24 )
        = ( k1_funct_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B_1 @ X0 )
        = ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B_1 @ X0 )
        = ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B_1 @ X0 )
        = ( k1_funct_1 @ sk_B_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_B_1
      = ( k6_partfun1 @ sk_A ) )
    | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      = ( k1_funct_1 @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','44'])).

thf('46',plain,
    ( ( ( sk_C @ sk_B_1 @ sk_A )
      = ( k1_funct_1 @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( sk_B_1
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B_1
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['35','45'])).

thf('47',plain,
    ( ( sk_B_1
      = ( k6_partfun1 @ sk_A ) )
    | ( ( sk_C @ sk_B_1 @ sk_A )
      = ( k1_funct_1 @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['10','15','18'])).

thf('49',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k1_relat_1 @ X11 )
       != X10 )
      | ( ( k1_funct_1 @ X11 @ ( sk_C @ X11 @ X10 ) )
       != ( sk_C @ X11 @ X10 ) )
      | ( X11
        = ( k6_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('50',plain,(
    ! [X11: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X11
        = ( k6_relat_1 @ ( k1_relat_1 @ X11 ) ) )
      | ( ( k1_funct_1 @ X11 @ ( sk_C @ X11 @ ( k1_relat_1 @ X11 ) ) )
       != ( sk_C @ X11 @ ( k1_relat_1 @ X11 ) ) ) ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    ! [X25: $i] :
      ( ( k6_partfun1 @ X25 )
      = ( k6_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('52',plain,(
    ! [X11: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X11
        = ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) )
      | ( ( k1_funct_1 @ X11 @ ( sk_C @ X11 @ ( k1_relat_1 @ X11 ) ) )
       != ( sk_C @ X11 @ ( k1_relat_1 @ X11 ) ) ) ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
     != ( sk_C @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) ) )
    | ( sk_B_1
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['48','52'])).

thf('54',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['10','15','18'])).

thf('55',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['10','15','18'])).

thf('56',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('58',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
     != ( sk_C @ sk_B_1 @ sk_A ) )
    | ( sk_B_1
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['53','54','55','56','57'])).

thf('59',plain,
    ( sk_B_1
    = ( k6_partfun1 @ sk_A ) ),
    inference(clc,[status(thm)],['47','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
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

thf('62',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( r2_funct_2 @ X26 @ X27 @ X28 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X26 @ X27 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ X26 @ X27 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('63',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
      | ( r2_funct_2 @ sk_A @ sk_A @ sk_B_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ sk_A @ sk_A @ sk_B_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['63','64','65'])).

thf('67',plain,
    ( ( r2_funct_2 @ sk_A @ sk_A @ sk_B_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['60','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    r2_funct_2 @ sk_A @ sk_A @ sk_B_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,(
    $false ),
    inference(demod,[status(thm)],['0','59','70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.oU6luTv0SE
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:22:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.35  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.21/0.48  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.48  % Solved by: fo/fo7.sh
% 0.21/0.48  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.48  % done 74 iterations in 0.032s
% 0.21/0.48  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.48  % SZS output start Refutation
% 0.21/0.48  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.21/0.48  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.48  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.21/0.48  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.48  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.48  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.48  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.48  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.48  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.21/0.48  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.48  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.48  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.48  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.48  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.48  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.48  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.48  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.21/0.48  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.48  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.21/0.48  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.21/0.48  thf(t201_funct_2, conjecture,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.48             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.48           ( ( ![C:$i]:
% 0.21/0.48               ( ( m1_subset_1 @ C @ A ) =>
% 0.21/0.48                 ( ( k3_funct_2 @ A @ A @ B @ C ) = ( C ) ) ) ) =>
% 0.21/0.48             ( r2_funct_2 @ A @ A @ B @ ( k6_partfun1 @ A ) ) ) ) ) ))).
% 0.21/0.48  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.48    (~( ![A:$i]:
% 0.21/0.48        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.48          ( ![B:$i]:
% 0.21/0.48            ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.21/0.48                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.21/0.48              ( ( ![C:$i]:
% 0.21/0.48                  ( ( m1_subset_1 @ C @ A ) =>
% 0.21/0.48                    ( ( k3_funct_2 @ A @ A @ B @ C ) = ( C ) ) ) ) =>
% 0.21/0.48                ( r2_funct_2 @ A @ A @ B @ ( k6_partfun1 @ A ) ) ) ) ) ) )),
% 0.21/0.48    inference('cnf.neg', [status(esa)], [t201_funct_2])).
% 0.21/0.48  thf('0', plain,
% 0.21/0.48      (~ (r2_funct_2 @ sk_A @ sk_A @ sk_B_1 @ (k6_partfun1 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('1', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(cc5_funct_2, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.48       ( ![C:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.48           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.21/0.48             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.21/0.48  thf('2', plain,
% 0.21/0.48      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18)))
% 0.21/0.48          | (v1_partfun1 @ X16 @ X17)
% 0.21/0.48          | ~ (v1_funct_2 @ X16 @ X17 @ X18)
% 0.21/0.48          | ~ (v1_funct_1 @ X16)
% 0.21/0.48          | (v1_xboole_0 @ X18))),
% 0.21/0.48      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.21/0.48  thf('3', plain,
% 0.21/0.48      (((v1_xboole_0 @ sk_A)
% 0.21/0.48        | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.48        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.21/0.48        | (v1_partfun1 @ sk_B_1 @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.48  thf('4', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('5', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('6', plain, (((v1_xboole_0 @ sk_A) | (v1_partfun1 @ sk_B_1 @ sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['3', '4', '5'])).
% 0.21/0.48  thf('7', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('8', plain, ((v1_partfun1 @ sk_B_1 @ sk_A)),
% 0.21/0.48      inference('clc', [status(thm)], ['6', '7'])).
% 0.21/0.48  thf(d4_partfun1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.21/0.48       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.21/0.48  thf('9', plain,
% 0.21/0.48      (![X19 : $i, X20 : $i]:
% 0.21/0.48         (~ (v1_partfun1 @ X20 @ X19)
% 0.21/0.48          | ((k1_relat_1 @ X20) = (X19))
% 0.21/0.48          | ~ (v4_relat_1 @ X20 @ X19)
% 0.21/0.48          | ~ (v1_relat_1 @ X20))),
% 0.21/0.48      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.21/0.48  thf('10', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ sk_B_1)
% 0.21/0.48        | ~ (v4_relat_1 @ sk_B_1 @ sk_A)
% 0.21/0.48        | ((k1_relat_1 @ sk_B_1) = (sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.48  thf('11', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(cc2_relat_1, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_relat_1 @ A ) =>
% 0.21/0.48       ( ![B:$i]:
% 0.21/0.48         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.48  thf('12', plain,
% 0.21/0.48      (![X6 : $i, X7 : $i]:
% 0.21/0.48         (~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7))
% 0.21/0.48          | (v1_relat_1 @ X6)
% 0.21/0.48          | ~ (v1_relat_1 @ X7))),
% 0.21/0.48      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.48  thf('13', plain,
% 0.21/0.48      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)) | (v1_relat_1 @ sk_B_1))),
% 0.21/0.48      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.48  thf(fc6_relat_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.48  thf('14', plain,
% 0.21/0.48      (![X8 : $i, X9 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X8 @ X9))),
% 0.21/0.48      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.48  thf('15', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.48      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.48  thf('16', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(cc2_relset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i,C:$i]:
% 0.21/0.48     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.48       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.48  thf('17', plain,
% 0.21/0.48      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.21/0.48         ((v4_relat_1 @ X13 @ X14)
% 0.21/0.48          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.21/0.48      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.48  thf('18', plain, ((v4_relat_1 @ sk_B_1 @ sk_A)),
% 0.21/0.48      inference('sup-', [status(thm)], ['16', '17'])).
% 0.21/0.48  thf('19', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['10', '15', '18'])).
% 0.21/0.48  thf(t34_funct_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.48       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.21/0.48         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.21/0.48           ( ![C:$i]:
% 0.21/0.48             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.21/0.48  thf('20', plain,
% 0.21/0.48      (![X10 : $i, X11 : $i]:
% 0.21/0.48         (((k1_relat_1 @ X11) != (X10))
% 0.21/0.48          | (r2_hidden @ (sk_C @ X11 @ X10) @ X10)
% 0.21/0.48          | ((X11) = (k6_relat_1 @ X10))
% 0.21/0.48          | ~ (v1_funct_1 @ X11)
% 0.21/0.48          | ~ (v1_relat_1 @ X11))),
% 0.21/0.48      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.21/0.48  thf('21', plain,
% 0.21/0.48      (![X11 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X11)
% 0.21/0.48          | ~ (v1_funct_1 @ X11)
% 0.21/0.48          | ((X11) = (k6_relat_1 @ (k1_relat_1 @ X11)))
% 0.21/0.48          | (r2_hidden @ (sk_C @ X11 @ (k1_relat_1 @ X11)) @ (k1_relat_1 @ X11)))),
% 0.21/0.48      inference('simplify', [status(thm)], ['20'])).
% 0.21/0.48  thf(redefinition_k6_partfun1, axiom,
% 0.21/0.48    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.21/0.48  thf('22', plain, (![X25 : $i]: ((k6_partfun1 @ X25) = (k6_relat_1 @ X25))),
% 0.21/0.48      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.48  thf('23', plain,
% 0.21/0.48      (![X11 : $i]:
% 0.21/0.48         (~ (v1_relat_1 @ X11)
% 0.21/0.48          | ~ (v1_funct_1 @ X11)
% 0.21/0.48          | ((X11) = (k6_partfun1 @ (k1_relat_1 @ X11)))
% 0.21/0.48          | (r2_hidden @ (sk_C @ X11 @ (k1_relat_1 @ X11)) @ (k1_relat_1 @ X11)))),
% 0.21/0.48      inference('demod', [status(thm)], ['21', '22'])).
% 0.21/0.48  thf('24', plain,
% 0.21/0.48      (((r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ (k1_relat_1 @ sk_B_1))
% 0.21/0.48        | ((sk_B_1) = (k6_partfun1 @ (k1_relat_1 @ sk_B_1)))
% 0.21/0.48        | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.48        | ~ (v1_relat_1 @ sk_B_1))),
% 0.21/0.48      inference('sup+', [status(thm)], ['19', '23'])).
% 0.21/0.48  thf('25', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['10', '15', '18'])).
% 0.21/0.48  thf('26', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.21/0.48      inference('demod', [status(thm)], ['10', '15', '18'])).
% 0.21/0.48  thf('27', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('28', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.48      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.48  thf('29', plain,
% 0.21/0.48      (((r2_hidden @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.21/0.48        | ((sk_B_1) = (k6_partfun1 @ sk_A)))),
% 0.21/0.48      inference('demod', [status(thm)], ['24', '25', '26', '27', '28'])).
% 0.21/0.48  thf(d2_subset_1, axiom,
% 0.21/0.48    (![A:$i,B:$i]:
% 0.21/0.48     ( ( ( v1_xboole_0 @ A ) =>
% 0.21/0.48         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.21/0.48       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.48         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.48  thf('30', plain,
% 0.21/0.48      (![X3 : $i, X4 : $i]:
% 0.21/0.48         (~ (r2_hidden @ X3 @ X4)
% 0.21/0.48          | (m1_subset_1 @ X3 @ X4)
% 0.21/0.48          | (v1_xboole_0 @ X4))),
% 0.21/0.48      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.21/0.48  thf(d1_xboole_0, axiom,
% 0.21/0.48    (![A:$i]:
% 0.21/0.48     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.48  thf('31', plain,
% 0.21/0.48      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.48      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.48  thf('32', plain,
% 0.21/0.48      (![X3 : $i, X4 : $i]: ((m1_subset_1 @ X3 @ X4) | ~ (r2_hidden @ X3 @ X4))),
% 0.21/0.48      inference('clc', [status(thm)], ['30', '31'])).
% 0.21/0.48  thf('33', plain,
% 0.21/0.48      ((((sk_B_1) = (k6_partfun1 @ sk_A))
% 0.21/0.48        | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['29', '32'])).
% 0.21/0.48  thf('34', plain,
% 0.21/0.48      (![X30 : $i]:
% 0.21/0.48         (((k3_funct_2 @ sk_A @ sk_A @ sk_B_1 @ X30) = (X30))
% 0.21/0.48          | ~ (m1_subset_1 @ X30 @ sk_A))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf('35', plain,
% 0.21/0.48      ((((sk_B_1) = (k6_partfun1 @ sk_A))
% 0.21/0.48        | ((k3_funct_2 @ sk_A @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.21/0.48            = (sk_C @ sk_B_1 @ sk_A)))),
% 0.21/0.48      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.48  thf('36', plain,
% 0.21/0.48      ((((sk_B_1) = (k6_partfun1 @ sk_A))
% 0.21/0.48        | (m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A))),
% 0.21/0.48      inference('sup-', [status(thm)], ['29', '32'])).
% 0.21/0.48  thf('37', plain,
% 0.21/0.48      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.48      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.48  thf(redefinition_k3_funct_2, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.21/0.49         ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.49         ( m1_subset_1 @ D @ A ) ) =>
% 0.21/0.49       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.21/0.49  thf('38', plain,
% 0.21/0.49      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.21/0.49          | ~ (v1_funct_2 @ X21 @ X22 @ X23)
% 0.21/0.49          | ~ (v1_funct_1 @ X21)
% 0.21/0.49          | (v1_xboole_0 @ X22)
% 0.21/0.49          | ~ (m1_subset_1 @ X24 @ X22)
% 0.21/0.49          | ((k3_funct_2 @ X22 @ X23 @ X21 @ X24) = (k1_funct_1 @ X21 @ X24)))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.21/0.49  thf('39', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k3_funct_2 @ sk_A @ sk_A @ sk_B_1 @ X0)
% 0.21/0.49            = (k1_funct_1 @ sk_B_1 @ X0))
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.49          | (v1_xboole_0 @ sk_A)
% 0.21/0.49          | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.49          | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['37', '38'])).
% 0.21/0.49  thf('40', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('41', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('42', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (((k3_funct_2 @ sk_A @ sk_A @ sk_B_1 @ X0)
% 0.21/0.49            = (k1_funct_1 @ sk_B_1 @ X0))
% 0.21/0.49          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.49          | (v1_xboole_0 @ sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.21/0.49  thf('43', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('44', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.21/0.49          | ((k3_funct_2 @ sk_A @ sk_A @ sk_B_1 @ X0)
% 0.21/0.49              = (k1_funct_1 @ sk_B_1 @ X0)))),
% 0.21/0.49      inference('clc', [status(thm)], ['42', '43'])).
% 0.21/0.49  thf('45', plain,
% 0.21/0.49      ((((sk_B_1) = (k6_partfun1 @ sk_A))
% 0.21/0.49        | ((k3_funct_2 @ sk_A @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.21/0.49            = (k1_funct_1 @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))))),
% 0.21/0.49      inference('sup-', [status(thm)], ['36', '44'])).
% 0.21/0.49  thf('46', plain,
% 0.21/0.49      ((((sk_C @ sk_B_1 @ sk_A)
% 0.21/0.49          = (k1_funct_1 @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.21/0.49        | ((sk_B_1) = (k6_partfun1 @ sk_A))
% 0.21/0.49        | ((sk_B_1) = (k6_partfun1 @ sk_A)))),
% 0.21/0.49      inference('sup+', [status(thm)], ['35', '45'])).
% 0.21/0.49  thf('47', plain,
% 0.21/0.49      ((((sk_B_1) = (k6_partfun1 @ sk_A))
% 0.21/0.49        | ((sk_C @ sk_B_1 @ sk_A)
% 0.21/0.49            = (k1_funct_1 @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))))),
% 0.21/0.49      inference('simplify', [status(thm)], ['46'])).
% 0.21/0.49  thf('48', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['10', '15', '18'])).
% 0.21/0.49  thf('49', plain,
% 0.21/0.49      (![X10 : $i, X11 : $i]:
% 0.21/0.49         (((k1_relat_1 @ X11) != (X10))
% 0.21/0.49          | ((k1_funct_1 @ X11 @ (sk_C @ X11 @ X10)) != (sk_C @ X11 @ X10))
% 0.21/0.49          | ((X11) = (k6_relat_1 @ X10))
% 0.21/0.49          | ~ (v1_funct_1 @ X11)
% 0.21/0.49          | ~ (v1_relat_1 @ X11))),
% 0.21/0.49      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.21/0.49  thf('50', plain,
% 0.21/0.49      (![X11 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X11)
% 0.21/0.49          | ~ (v1_funct_1 @ X11)
% 0.21/0.49          | ((X11) = (k6_relat_1 @ (k1_relat_1 @ X11)))
% 0.21/0.49          | ((k1_funct_1 @ X11 @ (sk_C @ X11 @ (k1_relat_1 @ X11)))
% 0.21/0.49              != (sk_C @ X11 @ (k1_relat_1 @ X11))))),
% 0.21/0.49      inference('simplify', [status(thm)], ['49'])).
% 0.21/0.49  thf('51', plain, (![X25 : $i]: ((k6_partfun1 @ X25) = (k6_relat_1 @ X25))),
% 0.21/0.49      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.21/0.49  thf('52', plain,
% 0.21/0.49      (![X11 : $i]:
% 0.21/0.49         (~ (v1_relat_1 @ X11)
% 0.21/0.49          | ~ (v1_funct_1 @ X11)
% 0.21/0.49          | ((X11) = (k6_partfun1 @ (k1_relat_1 @ X11)))
% 0.21/0.49          | ((k1_funct_1 @ X11 @ (sk_C @ X11 @ (k1_relat_1 @ X11)))
% 0.21/0.49              != (sk_C @ X11 @ (k1_relat_1 @ X11))))),
% 0.21/0.49      inference('demod', [status(thm)], ['50', '51'])).
% 0.21/0.49  thf('53', plain,
% 0.21/0.49      ((((k1_funct_1 @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.21/0.49          != (sk_C @ sk_B_1 @ (k1_relat_1 @ sk_B_1)))
% 0.21/0.49        | ((sk_B_1) = (k6_partfun1 @ (k1_relat_1 @ sk_B_1)))
% 0.21/0.49        | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.49        | ~ (v1_relat_1 @ sk_B_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['48', '52'])).
% 0.21/0.49  thf('54', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['10', '15', '18'])).
% 0.21/0.49  thf('55', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.21/0.49      inference('demod', [status(thm)], ['10', '15', '18'])).
% 0.21/0.49  thf('56', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('57', plain, ((v1_relat_1 @ sk_B_1)),
% 0.21/0.49      inference('demod', [status(thm)], ['13', '14'])).
% 0.21/0.49  thf('58', plain,
% 0.21/0.49      ((((k1_funct_1 @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.21/0.49          != (sk_C @ sk_B_1 @ sk_A))
% 0.21/0.49        | ((sk_B_1) = (k6_partfun1 @ sk_A)))),
% 0.21/0.49      inference('demod', [status(thm)], ['53', '54', '55', '56', '57'])).
% 0.21/0.49  thf('59', plain, (((sk_B_1) = (k6_partfun1 @ sk_A))),
% 0.21/0.49      inference('clc', [status(thm)], ['47', '58'])).
% 0.21/0.49  thf('60', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('61', plain,
% 0.21/0.49      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf(reflexivity_r2_funct_2, axiom,
% 0.21/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.49     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.49         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.21/0.49         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.21/0.49         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.21/0.49       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.21/0.49  thf('62', plain,
% 0.21/0.49      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.21/0.49         ((r2_funct_2 @ X26 @ X27 @ X28 @ X28)
% 0.21/0.49          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.21/0.49          | ~ (v1_funct_2 @ X28 @ X26 @ X27)
% 0.21/0.49          | ~ (v1_funct_1 @ X28)
% 0.21/0.49          | ~ (v1_funct_1 @ X29)
% 0.21/0.49          | ~ (v1_funct_2 @ X29 @ X26 @ X27)
% 0.21/0.49          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.21/0.49      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.21/0.49  thf('63', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.21/0.49          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.49          | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.21/0.49          | (r2_funct_2 @ sk_A @ sk_A @ sk_B_1 @ sk_B_1))),
% 0.21/0.49      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.49  thf('64', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('65', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('66', plain,
% 0.21/0.49      (![X0 : $i]:
% 0.21/0.49         (~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.21/0.49          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.21/0.49          | ~ (v1_funct_1 @ X0)
% 0.21/0.49          | (r2_funct_2 @ sk_A @ sk_A @ sk_B_1 @ sk_B_1))),
% 0.21/0.49      inference('demod', [status(thm)], ['63', '64', '65'])).
% 0.21/0.49  thf('67', plain,
% 0.21/0.49      (((r2_funct_2 @ sk_A @ sk_A @ sk_B_1 @ sk_B_1)
% 0.21/0.49        | ~ (v1_funct_1 @ sk_B_1)
% 0.21/0.49        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A))),
% 0.21/0.49      inference('sup-', [status(thm)], ['60', '66'])).
% 0.21/0.49  thf('68', plain, ((v1_funct_1 @ sk_B_1)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('69', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.21/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.49  thf('70', plain, ((r2_funct_2 @ sk_A @ sk_A @ sk_B_1 @ sk_B_1)),
% 0.21/0.49      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.21/0.49  thf('71', plain, ($false),
% 0.21/0.49      inference('demod', [status(thm)], ['0', '59', '70'])).
% 0.21/0.49  
% 0.21/0.49  % SZS output end Refutation
% 0.21/0.49  
% 0.21/0.49  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
