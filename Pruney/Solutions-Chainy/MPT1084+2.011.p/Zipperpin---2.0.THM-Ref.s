%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gfZqij3Zfy

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:37 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 449 expanded)
%              Number of leaves         :   30 ( 154 expanded)
%              Depth                    :   12
%              Number of atoms          :  951 (5999 expanded)
%              Number of equality atoms :   66 ( 342 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k6_relat_1_type,type,(
    k6_relat_1: $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k6_partfun1_type,type,(
    k6_partfun1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k9_setfam_1_type,type,(
    k9_setfam_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_funct_2_type,type,(
    r2_funct_2: $i > $i > $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

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

thf(redefinition_k9_setfam_1,axiom,(
    ! [A: $i] :
      ( ( k9_setfam_1 @ A )
      = ( k1_zfmisc_1 @ A ) ) )).

thf('2',plain,(
    ! [X24: $i] :
      ( ( k9_setfam_1 @ X24 )
      = ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('3',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(t67_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_funct_1 @ B )
        & ( v1_funct_2 @ B @ A @ A )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) )
     => ( ( k1_relset_1 @ A @ A @ B )
        = A ) ) )).

thf('4',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X29 @ X30 )
        = X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X29 @ X29 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t67_funct_2])).

thf('5',plain,(
    ! [X24: $i] :
      ( ( k9_setfam_1 @ X24 )
      = ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('6',plain,(
    ! [X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X29 @ X30 )
        = X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ X29 @ X29 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X29 @ X29 )
      | ~ ( v1_funct_1 @ X30 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,
    ( ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
    | ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
      = sk_A ) ),
    inference('sup-',[status(thm)],['3','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('11',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('12',plain,(
    ! [X24: $i] :
      ( ( k9_setfam_1 @ X24 )
      = ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('13',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k1_relset_1 @ X17 @ X18 @ X16 )
        = ( k1_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(demod,[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_relset_1 @ sk_A @ sk_A @ sk_B_1 )
    = ( k1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['7','8','9','14'])).

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

thf('16',plain,(
    ! [X10: $i,X11: $i] :
      ( ( ( k1_relat_1 @ X11 )
       != X10 )
      | ( r2_hidden @ ( sk_C @ X11 @ X10 ) @ X10 )
      | ( X11
        = ( k6_relat_1 @ X10 ) )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t34_funct_1])).

thf('17',plain,(
    ! [X11: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X11
        = ( k6_relat_1 @ ( k1_relat_1 @ X11 ) ) )
      | ( r2_hidden @ ( sk_C @ X11 @ ( k1_relat_1 @ X11 ) ) @ ( k1_relat_1 @ X11 ) ) ) ),
    inference(simplify,[status(thm)],['16'])).

thf(redefinition_k6_partfun1,axiom,(
    ! [A: $i] :
      ( ( k6_partfun1 @ A )
      = ( k6_relat_1 @ A ) ) )).

thf('18',plain,(
    ! [X23: $i] :
      ( ( k6_partfun1 @ X23 )
      = ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('19',plain,(
    ! [X11: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X11
        = ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) )
      | ( r2_hidden @ ( sk_C @ X11 @ ( k1_relat_1 @ X11 ) ) @ ( k1_relat_1 @ X11 ) ) ) ),
    inference(demod,[status(thm)],['17','18'])).

thf(d2_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( v1_xboole_0 @ B ) ) )
      & ( ~ ( v1_xboole_0 @ A )
       => ( ( m1_subset_1 @ B @ A )
        <=> ( r2_hidden @ B @ A ) ) ) ) )).

thf('20',plain,(
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

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('22',plain,(
    ! [X3: $i,X4: $i] :
      ( ( m1_subset_1 @ X3 @ X4 )
      | ~ ( r2_hidden @ X3 @ X4 ) ) ),
    inference(clc,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k6_partfun1 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k1_relat_1 @ X0 ) ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['19','22'])).

thf('24',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) ) @ sk_A )
    | ~ ( v1_relat_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ( sk_B_1
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B_1 ) ) ) ),
    inference('sup+',[status(thm)],['15','23'])).

thf('25',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['7','8','9','14'])).

thf('26',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('27',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('28',plain,(
    ! [X24: $i] :
      ( ( k9_setfam_1 @ X24 )
      = ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('29',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( v1_relat_1 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['26','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['7','8','9','14'])).

thf('33',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ( sk_B_1
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','30','31','32'])).

thf('34',plain,(
    ! [X31: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B_1 @ X31 )
        = X31 )
      | ~ ( m1_subset_1 @ X31 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( sk_B_1
      = ( k6_partfun1 @ sk_A ) )
    | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      = ( sk_C @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ( m1_subset_1 @ ( sk_C @ sk_B_1 @ sk_A ) @ sk_A )
    | ( sk_B_1
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25','30','31','32'])).

thf('37',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','2'])).

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
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X20 @ X21 )
      | ~ ( v1_funct_1 @ X19 )
      | ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ X20 )
      | ( ( k3_funct_2 @ X20 @ X21 @ X19 @ X22 )
        = ( k1_funct_1 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('39',plain,(
    ! [X24: $i] :
      ( ( k9_setfam_1 @ X24 )
      = ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('40',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X20 @ X21 )
      | ~ ( v1_funct_1 @ X19 )
      | ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ X20 )
      | ( ( k3_funct_2 @ X20 @ X21 @ X19 @ X22 )
        = ( k1_funct_1 @ X19 @ X22 ) ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B_1 @ X0 )
        = ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['37','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B_1 @ X0 )
        = ( k1_funct_1 @ sk_B_1 @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B_1 @ X0 )
        = ( k1_funct_1 @ sk_B_1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( sk_B_1
      = ( k6_partfun1 @ sk_A ) )
    | ( ( k3_funct_2 @ sk_A @ sk_A @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
      = ( k1_funct_1 @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['36','46'])).

thf('48',plain,
    ( ( ( sk_C @ sk_B_1 @ sk_A )
      = ( k1_funct_1 @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) )
    | ( sk_B_1
      = ( k6_partfun1 @ sk_A ) )
    | ( sk_B_1
      = ( k6_partfun1 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['35','47'])).

thf('49',plain,
    ( ( sk_B_1
      = ( k6_partfun1 @ sk_A ) )
    | ( ( sk_C @ sk_B_1 @ sk_A )
      = ( k1_funct_1 @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['7','8','9','14'])).

thf('51',plain,(
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

thf('52',plain,(
    ! [X11: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X11
        = ( k6_relat_1 @ ( k1_relat_1 @ X11 ) ) )
      | ( ( k1_funct_1 @ X11 @ ( sk_C @ X11 @ ( k1_relat_1 @ X11 ) ) )
       != ( sk_C @ X11 @ ( k1_relat_1 @ X11 ) ) ) ) ),
    inference(simplify,[status(thm)],['51'])).

thf('53',plain,(
    ! [X23: $i] :
      ( ( k6_partfun1 @ X23 )
      = ( k6_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_partfun1])).

thf('54',plain,(
    ! [X11: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ~ ( v1_funct_1 @ X11 )
      | ( X11
        = ( k6_partfun1 @ ( k1_relat_1 @ X11 ) ) )
      | ( ( k1_funct_1 @ X11 @ ( sk_C @ X11 @ ( k1_relat_1 @ X11 ) ) )
       != ( sk_C @ X11 @ ( k1_relat_1 @ X11 ) ) ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
     != ( sk_C @ sk_B_1 @ ( k1_relat_1 @ sk_B_1 ) ) )
    | ( sk_B_1
      = ( k6_partfun1 @ ( k1_relat_1 @ sk_B_1 ) ) )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_relat_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['50','54'])).

thf('56',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['7','8','9','14'])).

thf('57',plain,
    ( ( k1_relat_1 @ sk_B_1 )
    = sk_A ),
    inference(demod,[status(thm)],['7','8','9','14'])).

thf('58',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_relat_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['26','29'])).

thf('60',plain,
    ( ( ( k1_funct_1 @ sk_B_1 @ ( sk_C @ sk_B_1 @ sk_A ) )
     != ( sk_C @ sk_B_1 @ sk_A ) )
    | ( sk_B_1
      = ( k6_partfun1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['55','56','57','58','59'])).

thf('61',plain,
    ( sk_B_1
    = ( k6_partfun1 @ sk_A ) ),
    inference(clc,[status(thm)],['49','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf('63',plain,(
    m1_subset_1 @ sk_B_1 @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) ),
    inference(demod,[status(thm)],['1','2'])).

thf(reflexivity_r2_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_funct_2 @ A @ B @ C @ C ) ) )).

thf('64',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r2_funct_2 @ X25 @ X26 @ X27 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_funct_2])).

thf('65',plain,(
    ! [X24: $i] :
      ( ( k9_setfam_1 @ X24 )
      = ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('66',plain,(
    ! [X24: $i] :
      ( ( k9_setfam_1 @ X24 )
      = ( k1_zfmisc_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_setfam_1])).

thf('67',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r2_funct_2 @ X25 @ X26 @ X27 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X28 @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(demod,[status(thm)],['64','65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_B_1 )
      | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A )
      | ( r2_funct_2 @ sk_A @ sk_A @ sk_B_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['63','67'])).

thf('69',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ ( k9_setfam_1 @ ( k2_zfmisc_1 @ sk_A @ sk_A ) ) )
      | ~ ( v1_funct_2 @ X0 @ sk_A @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ( r2_funct_2 @ sk_A @ sk_A @ sk_B_1 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['68','69','70'])).

thf('72',plain,
    ( ( r2_funct_2 @ sk_A @ sk_A @ sk_B_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_B_1 )
    | ~ ( v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ) ),
    inference('sup-',[status(thm)],['62','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ sk_B_1 @ sk_A @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    r2_funct_2 @ sk_A @ sk_A @ sk_B_1 @ sk_B_1 ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    $false ),
    inference(demod,[status(thm)],['0','61','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.gfZqij3Zfy
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:28:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running portfolio for 600 s
% 0.12/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.12/0.34  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.35  % Running in FO mode
% 0.20/0.59  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.59  % Solved by: fo/fo7.sh
% 0.20/0.59  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.59  % done 228 iterations in 0.123s
% 0.20/0.59  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.59  % SZS output start Refutation
% 0.20/0.59  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.59  thf(k6_relat_1_type, type, k6_relat_1: $i > $i).
% 0.20/0.59  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.59  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.59  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.59  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.59  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.20/0.59  thf(k6_partfun1_type, type, k6_partfun1: $i > $i).
% 0.20/0.59  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.59  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.59  thf(k9_setfam_1_type, type, k9_setfam_1: $i > $i).
% 0.20/0.59  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.20/0.59  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.59  thf(r2_funct_2_type, type, r2_funct_2: $i > $i > $i > $i > $o).
% 0.20/0.59  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.59  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.59  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.59  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.59  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.59  thf(t201_funct_2, conjecture,
% 0.20/0.59    (![A:$i]:
% 0.20/0.59     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.59       ( ![B:$i]:
% 0.20/0.59         ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.59             ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.59           ( ( ![C:$i]:
% 0.20/0.59               ( ( m1_subset_1 @ C @ A ) =>
% 0.20/0.59                 ( ( k3_funct_2 @ A @ A @ B @ C ) = ( C ) ) ) ) =>
% 0.20/0.59             ( r2_funct_2 @ A @ A @ B @ ( k6_partfun1 @ A ) ) ) ) ) ))).
% 0.20/0.59  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.59    (~( ![A:$i]:
% 0.20/0.59        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.59          ( ![B:$i]:
% 0.20/0.59            ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.59                ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.59              ( ( ![C:$i]:
% 0.20/0.59                  ( ( m1_subset_1 @ C @ A ) =>
% 0.20/0.59                    ( ( k3_funct_2 @ A @ A @ B @ C ) = ( C ) ) ) ) =>
% 0.20/0.59                ( r2_funct_2 @ A @ A @ B @ ( k6_partfun1 @ A ) ) ) ) ) ) )),
% 0.20/0.59    inference('cnf.neg', [status(esa)], [t201_funct_2])).
% 0.20/0.59  thf('0', plain,
% 0.20/0.59      (~ (r2_funct_2 @ sk_A @ sk_A @ sk_B_1 @ (k6_partfun1 @ sk_A))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('1', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_B_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf(redefinition_k9_setfam_1, axiom,
% 0.20/0.59    (![A:$i]: ( ( k9_setfam_1 @ A ) = ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.59  thf('2', plain, (![X24 : $i]: ((k9_setfam_1 @ X24) = (k1_zfmisc_1 @ X24))),
% 0.20/0.59      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.59  thf('3', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.59      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.59  thf(t67_funct_2, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( ( v1_funct_1 @ B ) & ( v1_funct_2 @ B @ A @ A ) & 
% 0.20/0.59         ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ A ) ) ) ) =>
% 0.20/0.59       ( ( k1_relset_1 @ A @ A @ B ) = ( A ) ) ))).
% 0.20/0.59  thf('4', plain,
% 0.20/0.59      (![X29 : $i, X30 : $i]:
% 0.20/0.59         (((k1_relset_1 @ X29 @ X29 @ X30) = (X29))
% 0.20/0.59          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X29)))
% 0.20/0.59          | ~ (v1_funct_2 @ X30 @ X29 @ X29)
% 0.20/0.59          | ~ (v1_funct_1 @ X30))),
% 0.20/0.59      inference('cnf', [status(esa)], [t67_funct_2])).
% 0.20/0.59  thf('5', plain, (![X24 : $i]: ((k9_setfam_1 @ X24) = (k1_zfmisc_1 @ X24))),
% 0.20/0.59      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.59  thf('6', plain,
% 0.20/0.59      (![X29 : $i, X30 : $i]:
% 0.20/0.59         (((k1_relset_1 @ X29 @ X29 @ X30) = (X29))
% 0.20/0.59          | ~ (m1_subset_1 @ X30 @ (k9_setfam_1 @ (k2_zfmisc_1 @ X29 @ X29)))
% 0.20/0.59          | ~ (v1_funct_2 @ X30 @ X29 @ X29)
% 0.20/0.59          | ~ (v1_funct_1 @ X30))),
% 0.20/0.59      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.59  thf('7', plain,
% 0.20/0.59      ((~ (v1_funct_1 @ sk_B_1)
% 0.20/0.59        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.20/0.59        | ((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (sk_A)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['3', '6'])).
% 0.20/0.59  thf('8', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('9', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('10', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.59      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.59  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.59       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.59  thf('11', plain,
% 0.20/0.59      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.59         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.20/0.59          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.20/0.59      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.59  thf('12', plain, (![X24 : $i]: ((k9_setfam_1 @ X24) = (k1_zfmisc_1 @ X24))),
% 0.20/0.59      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.59  thf('13', plain,
% 0.20/0.59      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.59         (((k1_relset_1 @ X17 @ X18 @ X16) = (k1_relat_1 @ X16))
% 0.20/0.59          | ~ (m1_subset_1 @ X16 @ (k9_setfam_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.20/0.59      inference('demod', [status(thm)], ['11', '12'])).
% 0.20/0.59  thf('14', plain,
% 0.20/0.59      (((k1_relset_1 @ sk_A @ sk_A @ sk_B_1) = (k1_relat_1 @ sk_B_1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['10', '13'])).
% 0.20/0.59  thf('15', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.20/0.59      inference('demod', [status(thm)], ['7', '8', '9', '14'])).
% 0.20/0.59  thf(t34_funct_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.20/0.59       ( ( ( B ) = ( k6_relat_1 @ A ) ) <=>
% 0.20/0.59         ( ( ( k1_relat_1 @ B ) = ( A ) ) & 
% 0.20/0.59           ( ![C:$i]:
% 0.20/0.59             ( ( r2_hidden @ C @ A ) => ( ( k1_funct_1 @ B @ C ) = ( C ) ) ) ) ) ) ))).
% 0.20/0.59  thf('16', plain,
% 0.20/0.59      (![X10 : $i, X11 : $i]:
% 0.20/0.59         (((k1_relat_1 @ X11) != (X10))
% 0.20/0.59          | (r2_hidden @ (sk_C @ X11 @ X10) @ X10)
% 0.20/0.59          | ((X11) = (k6_relat_1 @ X10))
% 0.20/0.59          | ~ (v1_funct_1 @ X11)
% 0.20/0.59          | ~ (v1_relat_1 @ X11))),
% 0.20/0.59      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.20/0.59  thf('17', plain,
% 0.20/0.59      (![X11 : $i]:
% 0.20/0.59         (~ (v1_relat_1 @ X11)
% 0.20/0.59          | ~ (v1_funct_1 @ X11)
% 0.20/0.59          | ((X11) = (k6_relat_1 @ (k1_relat_1 @ X11)))
% 0.20/0.59          | (r2_hidden @ (sk_C @ X11 @ (k1_relat_1 @ X11)) @ (k1_relat_1 @ X11)))),
% 0.20/0.59      inference('simplify', [status(thm)], ['16'])).
% 0.20/0.59  thf(redefinition_k6_partfun1, axiom,
% 0.20/0.59    (![A:$i]: ( ( k6_partfun1 @ A ) = ( k6_relat_1 @ A ) ))).
% 0.20/0.59  thf('18', plain, (![X23 : $i]: ((k6_partfun1 @ X23) = (k6_relat_1 @ X23))),
% 0.20/0.59      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.59  thf('19', plain,
% 0.20/0.59      (![X11 : $i]:
% 0.20/0.59         (~ (v1_relat_1 @ X11)
% 0.20/0.59          | ~ (v1_funct_1 @ X11)
% 0.20/0.59          | ((X11) = (k6_partfun1 @ (k1_relat_1 @ X11)))
% 0.20/0.59          | (r2_hidden @ (sk_C @ X11 @ (k1_relat_1 @ X11)) @ (k1_relat_1 @ X11)))),
% 0.20/0.59      inference('demod', [status(thm)], ['17', '18'])).
% 0.20/0.59  thf(d2_subset_1, axiom,
% 0.20/0.59    (![A:$i,B:$i]:
% 0.20/0.59     ( ( ( v1_xboole_0 @ A ) =>
% 0.20/0.59         ( ( m1_subset_1 @ B @ A ) <=> ( v1_xboole_0 @ B ) ) ) & 
% 0.20/0.59       ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.59         ( ( m1_subset_1 @ B @ A ) <=> ( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.59  thf('20', plain,
% 0.20/0.59      (![X3 : $i, X4 : $i]:
% 0.20/0.59         (~ (r2_hidden @ X3 @ X4)
% 0.20/0.59          | (m1_subset_1 @ X3 @ X4)
% 0.20/0.59          | (v1_xboole_0 @ X4))),
% 0.20/0.59      inference('cnf', [status(esa)], [d2_subset_1])).
% 0.20/0.59  thf(d1_xboole_0, axiom,
% 0.20/0.59    (![A:$i]:
% 0.20/0.59     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.59  thf('21', plain,
% 0.20/0.59      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.20/0.59      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.59  thf('22', plain,
% 0.20/0.59      (![X3 : $i, X4 : $i]: ((m1_subset_1 @ X3 @ X4) | ~ (r2_hidden @ X3 @ X4))),
% 0.20/0.59      inference('clc', [status(thm)], ['20', '21'])).
% 0.20/0.59  thf('23', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (((X0) = (k6_partfun1 @ (k1_relat_1 @ X0)))
% 0.20/0.59          | ~ (v1_funct_1 @ X0)
% 0.20/0.59          | ~ (v1_relat_1 @ X0)
% 0.20/0.59          | (m1_subset_1 @ (sk_C @ X0 @ (k1_relat_1 @ X0)) @ (k1_relat_1 @ X0)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['19', '22'])).
% 0.20/0.59  thf('24', plain,
% 0.20/0.59      (((m1_subset_1 @ (sk_C @ sk_B_1 @ (k1_relat_1 @ sk_B_1)) @ sk_A)
% 0.20/0.59        | ~ (v1_relat_1 @ sk_B_1)
% 0.20/0.59        | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.59        | ((sk_B_1) = (k6_partfun1 @ (k1_relat_1 @ sk_B_1))))),
% 0.20/0.59      inference('sup+', [status(thm)], ['15', '23'])).
% 0.20/0.59  thf('25', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.20/0.59      inference('demod', [status(thm)], ['7', '8', '9', '14'])).
% 0.20/0.59  thf('26', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.59      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.59  thf(cc1_relset_1, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i]:
% 0.20/0.59     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.59       ( v1_relat_1 @ C ) ))).
% 0.20/0.59  thf('27', plain,
% 0.20/0.59      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.59         ((v1_relat_1 @ X13)
% 0.20/0.59          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.20/0.59      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.59  thf('28', plain, (![X24 : $i]: ((k9_setfam_1 @ X24) = (k1_zfmisc_1 @ X24))),
% 0.20/0.59      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.59  thf('29', plain,
% 0.20/0.59      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.59         ((v1_relat_1 @ X13)
% 0.20/0.59          | ~ (m1_subset_1 @ X13 @ (k9_setfam_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.20/0.59      inference('demod', [status(thm)], ['27', '28'])).
% 0.20/0.59  thf('30', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.59      inference('sup-', [status(thm)], ['26', '29'])).
% 0.20/0.59  thf('31', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('32', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.20/0.59      inference('demod', [status(thm)], ['7', '8', '9', '14'])).
% 0.20/0.59  thf('33', plain,
% 0.20/0.59      (((m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.20/0.59        | ((sk_B_1) = (k6_partfun1 @ sk_A)))),
% 0.20/0.59      inference('demod', [status(thm)], ['24', '25', '30', '31', '32'])).
% 0.20/0.59  thf('34', plain,
% 0.20/0.59      (![X31 : $i]:
% 0.20/0.59         (((k3_funct_2 @ sk_A @ sk_A @ sk_B_1 @ X31) = (X31))
% 0.20/0.59          | ~ (m1_subset_1 @ X31 @ sk_A))),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('35', plain,
% 0.20/0.59      ((((sk_B_1) = (k6_partfun1 @ sk_A))
% 0.20/0.59        | ((k3_funct_2 @ sk_A @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.59            = (sk_C @ sk_B_1 @ sk_A)))),
% 0.20/0.59      inference('sup-', [status(thm)], ['33', '34'])).
% 0.20/0.59  thf('36', plain,
% 0.20/0.59      (((m1_subset_1 @ (sk_C @ sk_B_1 @ sk_A) @ sk_A)
% 0.20/0.59        | ((sk_B_1) = (k6_partfun1 @ sk_A)))),
% 0.20/0.59      inference('demod', [status(thm)], ['24', '25', '30', '31', '32'])).
% 0.20/0.59  thf('37', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.59      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.59  thf(redefinition_k3_funct_2, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.59     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.20/0.59         ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.59         ( m1_subset_1 @ D @ A ) ) =>
% 0.20/0.59       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.20/0.59  thf('38', plain,
% 0.20/0.59      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.59         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.20/0.59          | ~ (v1_funct_2 @ X19 @ X20 @ X21)
% 0.20/0.59          | ~ (v1_funct_1 @ X19)
% 0.20/0.59          | (v1_xboole_0 @ X20)
% 0.20/0.59          | ~ (m1_subset_1 @ X22 @ X20)
% 0.20/0.59          | ((k3_funct_2 @ X20 @ X21 @ X19 @ X22) = (k1_funct_1 @ X19 @ X22)))),
% 0.20/0.59      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.20/0.59  thf('39', plain, (![X24 : $i]: ((k9_setfam_1 @ X24) = (k1_zfmisc_1 @ X24))),
% 0.20/0.59      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.59  thf('40', plain,
% 0.20/0.59      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.59         (~ (m1_subset_1 @ X19 @ (k9_setfam_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.20/0.59          | ~ (v1_funct_2 @ X19 @ X20 @ X21)
% 0.20/0.59          | ~ (v1_funct_1 @ X19)
% 0.20/0.59          | (v1_xboole_0 @ X20)
% 0.20/0.59          | ~ (m1_subset_1 @ X22 @ X20)
% 0.20/0.59          | ((k3_funct_2 @ X20 @ X21 @ X19 @ X22) = (k1_funct_1 @ X19 @ X22)))),
% 0.20/0.59      inference('demod', [status(thm)], ['38', '39'])).
% 0.20/0.59  thf('41', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (((k3_funct_2 @ sk_A @ sk_A @ sk_B_1 @ X0)
% 0.20/0.59            = (k1_funct_1 @ sk_B_1 @ X0))
% 0.20/0.59          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.59          | (v1_xboole_0 @ sk_A)
% 0.20/0.59          | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.59          | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A))),
% 0.20/0.59      inference('sup-', [status(thm)], ['37', '40'])).
% 0.20/0.59  thf('42', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('43', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('44', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (((k3_funct_2 @ sk_A @ sk_A @ sk_B_1 @ X0)
% 0.20/0.59            = (k1_funct_1 @ sk_B_1 @ X0))
% 0.20/0.59          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.59          | (v1_xboole_0 @ sk_A))),
% 0.20/0.59      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.20/0.59  thf('45', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('46', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.59          | ((k3_funct_2 @ sk_A @ sk_A @ sk_B_1 @ X0)
% 0.20/0.59              = (k1_funct_1 @ sk_B_1 @ X0)))),
% 0.20/0.59      inference('clc', [status(thm)], ['44', '45'])).
% 0.20/0.59  thf('47', plain,
% 0.20/0.59      ((((sk_B_1) = (k6_partfun1 @ sk_A))
% 0.20/0.59        | ((k3_funct_2 @ sk_A @ sk_A @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.59            = (k1_funct_1 @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))))),
% 0.20/0.59      inference('sup-', [status(thm)], ['36', '46'])).
% 0.20/0.59  thf('48', plain,
% 0.20/0.59      ((((sk_C @ sk_B_1 @ sk_A)
% 0.20/0.59          = (k1_funct_1 @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A)))
% 0.20/0.59        | ((sk_B_1) = (k6_partfun1 @ sk_A))
% 0.20/0.59        | ((sk_B_1) = (k6_partfun1 @ sk_A)))),
% 0.20/0.59      inference('sup+', [status(thm)], ['35', '47'])).
% 0.20/0.59  thf('49', plain,
% 0.20/0.59      ((((sk_B_1) = (k6_partfun1 @ sk_A))
% 0.20/0.59        | ((sk_C @ sk_B_1 @ sk_A)
% 0.20/0.59            = (k1_funct_1 @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))))),
% 0.20/0.59      inference('simplify', [status(thm)], ['48'])).
% 0.20/0.59  thf('50', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.20/0.59      inference('demod', [status(thm)], ['7', '8', '9', '14'])).
% 0.20/0.59  thf('51', plain,
% 0.20/0.59      (![X10 : $i, X11 : $i]:
% 0.20/0.59         (((k1_relat_1 @ X11) != (X10))
% 0.20/0.59          | ((k1_funct_1 @ X11 @ (sk_C @ X11 @ X10)) != (sk_C @ X11 @ X10))
% 0.20/0.59          | ((X11) = (k6_relat_1 @ X10))
% 0.20/0.59          | ~ (v1_funct_1 @ X11)
% 0.20/0.59          | ~ (v1_relat_1 @ X11))),
% 0.20/0.59      inference('cnf', [status(esa)], [t34_funct_1])).
% 0.20/0.59  thf('52', plain,
% 0.20/0.59      (![X11 : $i]:
% 0.20/0.59         (~ (v1_relat_1 @ X11)
% 0.20/0.59          | ~ (v1_funct_1 @ X11)
% 0.20/0.59          | ((X11) = (k6_relat_1 @ (k1_relat_1 @ X11)))
% 0.20/0.59          | ((k1_funct_1 @ X11 @ (sk_C @ X11 @ (k1_relat_1 @ X11)))
% 0.20/0.59              != (sk_C @ X11 @ (k1_relat_1 @ X11))))),
% 0.20/0.59      inference('simplify', [status(thm)], ['51'])).
% 0.20/0.59  thf('53', plain, (![X23 : $i]: ((k6_partfun1 @ X23) = (k6_relat_1 @ X23))),
% 0.20/0.59      inference('cnf', [status(esa)], [redefinition_k6_partfun1])).
% 0.20/0.59  thf('54', plain,
% 0.20/0.59      (![X11 : $i]:
% 0.20/0.59         (~ (v1_relat_1 @ X11)
% 0.20/0.59          | ~ (v1_funct_1 @ X11)
% 0.20/0.59          | ((X11) = (k6_partfun1 @ (k1_relat_1 @ X11)))
% 0.20/0.59          | ((k1_funct_1 @ X11 @ (sk_C @ X11 @ (k1_relat_1 @ X11)))
% 0.20/0.59              != (sk_C @ X11 @ (k1_relat_1 @ X11))))),
% 0.20/0.59      inference('demod', [status(thm)], ['52', '53'])).
% 0.20/0.59  thf('55', plain,
% 0.20/0.59      ((((k1_funct_1 @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.59          != (sk_C @ sk_B_1 @ (k1_relat_1 @ sk_B_1)))
% 0.20/0.59        | ((sk_B_1) = (k6_partfun1 @ (k1_relat_1 @ sk_B_1)))
% 0.20/0.59        | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.59        | ~ (v1_relat_1 @ sk_B_1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['50', '54'])).
% 0.20/0.59  thf('56', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.20/0.59      inference('demod', [status(thm)], ['7', '8', '9', '14'])).
% 0.20/0.59  thf('57', plain, (((k1_relat_1 @ sk_B_1) = (sk_A))),
% 0.20/0.59      inference('demod', [status(thm)], ['7', '8', '9', '14'])).
% 0.20/0.59  thf('58', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('59', plain, ((v1_relat_1 @ sk_B_1)),
% 0.20/0.59      inference('sup-', [status(thm)], ['26', '29'])).
% 0.20/0.59  thf('60', plain,
% 0.20/0.59      ((((k1_funct_1 @ sk_B_1 @ (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.59          != (sk_C @ sk_B_1 @ sk_A))
% 0.20/0.59        | ((sk_B_1) = (k6_partfun1 @ sk_A)))),
% 0.20/0.59      inference('demod', [status(thm)], ['55', '56', '57', '58', '59'])).
% 0.20/0.59  thf('61', plain, (((sk_B_1) = (k6_partfun1 @ sk_A))),
% 0.20/0.59      inference('clc', [status(thm)], ['49', '60'])).
% 0.20/0.59  thf('62', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.59      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.59  thf('63', plain,
% 0.20/0.59      ((m1_subset_1 @ sk_B_1 @ (k9_setfam_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))),
% 0.20/0.59      inference('demod', [status(thm)], ['1', '2'])).
% 0.20/0.59  thf(reflexivity_r2_funct_2, axiom,
% 0.20/0.59    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.59     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.59         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.59         ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.59         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.59       ( r2_funct_2 @ A @ B @ C @ C ) ))).
% 0.20/0.59  thf('64', plain,
% 0.20/0.59      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.59         ((r2_funct_2 @ X25 @ X26 @ X27 @ X27)
% 0.20/0.59          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.20/0.59          | ~ (v1_funct_2 @ X27 @ X25 @ X26)
% 0.20/0.59          | ~ (v1_funct_1 @ X27)
% 0.20/0.59          | ~ (v1_funct_1 @ X28)
% 0.20/0.59          | ~ (v1_funct_2 @ X28 @ X25 @ X26)
% 0.20/0.59          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.20/0.59      inference('cnf', [status(esa)], [reflexivity_r2_funct_2])).
% 0.20/0.59  thf('65', plain, (![X24 : $i]: ((k9_setfam_1 @ X24) = (k1_zfmisc_1 @ X24))),
% 0.20/0.59      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.59  thf('66', plain, (![X24 : $i]: ((k9_setfam_1 @ X24) = (k1_zfmisc_1 @ X24))),
% 0.20/0.59      inference('cnf', [status(esa)], [redefinition_k9_setfam_1])).
% 0.20/0.59  thf('67', plain,
% 0.20/0.59      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.20/0.59         ((r2_funct_2 @ X25 @ X26 @ X27 @ X27)
% 0.20/0.59          | ~ (m1_subset_1 @ X27 @ (k9_setfam_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.20/0.59          | ~ (v1_funct_2 @ X27 @ X25 @ X26)
% 0.20/0.59          | ~ (v1_funct_1 @ X27)
% 0.20/0.59          | ~ (v1_funct_1 @ X28)
% 0.20/0.59          | ~ (v1_funct_2 @ X28 @ X25 @ X26)
% 0.20/0.59          | ~ (m1_subset_1 @ X28 @ (k9_setfam_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.20/0.59      inference('demod', [status(thm)], ['64', '65', '66'])).
% 0.20/0.59  thf('68', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (m1_subset_1 @ X0 @ (k9_setfam_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.20/0.59          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.20/0.59          | ~ (v1_funct_1 @ X0)
% 0.20/0.59          | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.59          | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)
% 0.20/0.59          | (r2_funct_2 @ sk_A @ sk_A @ sk_B_1 @ sk_B_1))),
% 0.20/0.59      inference('sup-', [status(thm)], ['63', '67'])).
% 0.20/0.59  thf('69', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('70', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('71', plain,
% 0.20/0.59      (![X0 : $i]:
% 0.20/0.59         (~ (m1_subset_1 @ X0 @ (k9_setfam_1 @ (k2_zfmisc_1 @ sk_A @ sk_A)))
% 0.20/0.59          | ~ (v1_funct_2 @ X0 @ sk_A @ sk_A)
% 0.20/0.59          | ~ (v1_funct_1 @ X0)
% 0.20/0.59          | (r2_funct_2 @ sk_A @ sk_A @ sk_B_1 @ sk_B_1))),
% 0.20/0.59      inference('demod', [status(thm)], ['68', '69', '70'])).
% 0.20/0.59  thf('72', plain,
% 0.20/0.59      (((r2_funct_2 @ sk_A @ sk_A @ sk_B_1 @ sk_B_1)
% 0.20/0.59        | ~ (v1_funct_1 @ sk_B_1)
% 0.20/0.59        | ~ (v1_funct_2 @ sk_B_1 @ sk_A @ sk_A))),
% 0.20/0.59      inference('sup-', [status(thm)], ['62', '71'])).
% 0.20/0.59  thf('73', plain, ((v1_funct_1 @ sk_B_1)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('74', plain, ((v1_funct_2 @ sk_B_1 @ sk_A @ sk_A)),
% 0.20/0.59      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.59  thf('75', plain, ((r2_funct_2 @ sk_A @ sk_A @ sk_B_1 @ sk_B_1)),
% 0.20/0.59      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.20/0.59  thf('76', plain, ($false),
% 0.20/0.59      inference('demod', [status(thm)], ['0', '61', '75'])).
% 0.20/0.59  
% 0.20/0.59  % SZS output end Refutation
% 0.20/0.59  
% 0.20/0.60  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
