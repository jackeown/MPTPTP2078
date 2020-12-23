%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.F6SLXPgMiJ

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:28 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  201 ( 413 expanded)
%              Number of leaves         :   44 ( 138 expanded)
%              Depth                    :   19
%              Number of atoms          : 1935 (9811 expanded)
%              Number of equality atoms :   60 ( 215 expanded)
%              Maximal formula depth    :   22 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(k8_funct_2_type,type,(
    k8_funct_2: $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_partfun1_type,type,(
    k7_partfun1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(t193_funct_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i,D: $i] :
              ( ( ( v1_funct_1 @ D )
                & ( v1_funct_2 @ D @ B @ A )
                & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
             => ! [E: $i] :
                  ( ( ( v1_funct_1 @ E )
                    & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) )
                 => ! [F: $i] :
                      ( ( m1_subset_1 @ F @ B )
                     => ( ( v1_partfun1 @ E @ A )
                       => ( ( k3_funct_2 @ B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F )
                          = ( k7_partfun1 @ C @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i,D: $i] :
                ( ( ( v1_funct_1 @ D )
                  & ( v1_funct_2 @ D @ B @ A )
                  & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) )
               => ! [E: $i] :
                    ( ( ( v1_funct_1 @ E )
                      & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) )
                   => ! [F: $i] :
                        ( ( m1_subset_1 @ F @ B )
                       => ( ( v1_partfun1 @ E @ A )
                         => ( ( k3_funct_2 @ B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F )
                            = ( k7_partfun1 @ C @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t193_funct_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('3',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k1_relset_1 @ X14 @ X15 @ X13 )
        = ( k1_relat_1 @ X13 ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('4',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_E )
    = ( k1_relat_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_partfun1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('6',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_partfun1 @ X29 @ X28 )
      | ( ( k1_relat_1 @ X29 )
        = X28 )
      | ~ ( v4_relat_1 @ X29 @ X28 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v4_relat_1 @ sk_E @ sk_A )
    | ( ( k1_relat_1 @ sk_E )
      = sk_A ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('9',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('10',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v4_relat_1 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('13',plain,(
    v4_relat_1 @ sk_E @ sk_A ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( k1_relat_1 @ sk_E )
    = sk_A ),
    inference(demod,[status(thm)],['7','10','13'])).

thf('15',plain,
    ( ( k1_relset_1 @ sk_A @ sk_C @ sk_E )
    = sk_A ),
    inference(demod,[status(thm)],['4','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t185_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ B @ C )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
         => ! [E: $i] :
              ( ( ( v1_funct_1 @ E )
                & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) )
             => ! [F: $i] :
                  ( ( m1_subset_1 @ F @ B )
                 => ( ( r1_tarski @ ( k2_relset_1 @ B @ C @ D ) @ ( k1_relset_1 @ C @ A @ E ) )
                   => ( ( B = k1_xboole_0 )
                      | ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F )
                        = ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) )).

thf('17',plain,(
    ! [X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X44 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X44 @ X45 ) ) )
      | ~ ( m1_subset_1 @ X46 @ X44 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ X44 @ X45 @ X48 @ X43 @ X47 ) @ X46 )
        = ( k1_funct_1 @ X47 @ ( k1_funct_1 @ X43 @ X46 ) ) )
      | ( X44 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( k2_relset_1 @ X44 @ X45 @ X43 ) @ ( k1_relset_1 @ X45 @ X48 @ X47 ) )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X48 ) ) )
      | ~ ( v1_funct_1 @ X47 )
      | ( v1_xboole_0 @ X45 ) ) ),
    inference(cnf,[status(esa)],[t185_funct_2])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relset_1 @ sk_B @ sk_A @ sk_D ) @ ( k1_relset_1 @ sk_A @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('20',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( ( k2_relset_1 @ X17 @ X18 @ X16 )
        = ( k2_relat_1 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('21',plain,
    ( ( k2_relset_1 @ sk_B @ sk_A @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ ( k1_relset_1 @ sk_A @ X1 @ X0 ) )
      | ( sk_B = k1_xboole_0 )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0 ) @ X2 )
        = ( k1_funct_1 @ X0 @ ( k1_funct_1 @ sk_D @ X2 ) ) )
      | ~ ( m1_subset_1 @ X2 @ sk_B ) ) ),
    inference(demod,[status(thm)],['18','21','22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( sk_B = k1_xboole_0 )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['15','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v5_relat_1 @ X10 @ X12 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('28',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['26','27'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('29',plain,(
    ! [X2: $i,X3: $i] :
      ( ~ ( v5_relat_1 @ X2 @ X3 )
      | ( r1_tarski @ ( k2_relat_1 @ X2 ) @ X3 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X7: $i,X8: $i,X9: $i] :
      ( ( v1_relat_1 @ X7 )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('33',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_D ) @ sk_A ),
    inference(demod,[status(thm)],['30','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ( sk_B = k1_xboole_0 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['25','34','35','36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_B = k1_xboole_0 )
    | ( ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
      = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['1','37'])).

thf('39',plain,(
    ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_C @ sk_E @ ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
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

thf('42',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( v1_funct_1 @ X35 )
      | ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X38 @ X36 )
      | ( ( k3_funct_2 @ X36 @ X37 @ X35 @ X38 )
        = ( k1_funct_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) ) ) ),
    inference(clc,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F )
    = ( k1_funct_1 @ sk_D @ sk_F ) ),
    inference('sup-',[status(thm)],['40','48'])).

thf('50',plain,(
    ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['39','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( v1_funct_1 @ E )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) )
     => ( ( v1_funct_1 @ ( k8_funct_2 @ A @ B @ C @ D @ E ) )
        & ( v1_funct_2 @ ( k8_funct_2 @ A @ B @ C @ D @ E ) @ A @ C )
        & ( m1_subset_1 @ ( k8_funct_2 @ A @ B @ C @ D @ E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) )).

thf('54',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X32 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X34 ) ) )
      | ( m1_subset_1 @ ( k8_funct_2 @ X31 @ X32 @ X34 @ X30 @ X33 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_funct_2])).

thf('55',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ X0 ) ) )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( m1_subset_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['52','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(demod,[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( v1_funct_1 @ X35 )
      | ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X38 @ X36 )
      | ( ( k3_funct_2 @ X36 @ X37 @ X35 @ X38 )
        = ( k1_funct_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) )
      | ~ ( v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X32 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X34 ) ) )
      | ( v1_funct_1 @ ( k8_funct_2 @ X31 @ X32 @ X34 @ X30 @ X33 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_funct_2])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X1 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68','69'])).

thf('71',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) ) ),
    inference('sup-',[status(thm)],['64','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    v1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X32 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( v1_funct_1 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X34 ) ) )
      | ( v1_funct_2 @ ( k8_funct_2 @ X31 @ X32 @ X34 @ X30 @ X33 ) @ X31 @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k8_funct_2])).

thf('77',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1 ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1 ) @ sk_B @ X0 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ X0 ) ) )
      | ~ ( v1_funct_1 @ X1 ) ) ),
    inference(demod,[status(thm)],['77','78','79'])).

thf('81',plain,
    ( ~ ( v1_funct_1 @ sk_E )
    | ( v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_B @ sk_C ) ),
    inference('sup-',[status(thm)],['74','80'])).

thf('82',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_2 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_B @ sk_C ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['63','73','83'])).

thf('85',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_B )
      | ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 )
        = ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['84','85'])).

thf('87',plain,
    ( ( k3_funct_2 @ sk_B @ sk_C @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
    = ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F ) ),
    inference('sup-',[status(thm)],['51','86'])).

thf('88',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
 != ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['50','87'])).

thf('89',plain,(
    v5_relat_1 @ sk_D @ sk_A ),
    inference('sup-',[status(thm)],['26','27'])).

thf('90',plain,(
    m1_subset_1 @ sk_F @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ X0 @ X1 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('92',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ sk_F @ sk_B ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('94',plain,(
    r2_hidden @ sk_F @ sk_B ),
    inference(clc,[status(thm)],['92','93'])).

thf('95',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
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

thf('96',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) )
      | ( v1_partfun1 @ X25 @ X26 )
      | ~ ( v1_funct_2 @ X25 @ X26 @ X27 )
      | ~ ( v1_funct_1 @ X25 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('97',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_B @ sk_A )
    | ( v1_partfun1 @ sk_D @ sk_B ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_funct_2 @ sk_D @ sk_B @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_partfun1 @ sk_D @ sk_B ) ),
    inference(demod,[status(thm)],['97','98','99'])).

thf('101',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    v1_partfun1 @ sk_D @ sk_B ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X28: $i,X29: $i] :
      ( ~ ( v1_partfun1 @ X29 @ X28 )
      | ( ( k1_relat_1 @ X29 )
        = X28 )
      | ~ ( v4_relat_1 @ X29 @ X28 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('104',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ~ ( v4_relat_1 @ sk_D @ sk_B )
    | ( ( k1_relat_1 @ sk_D )
      = sk_B ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['31','32'])).

thf('106',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( v4_relat_1 @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('108',plain,(
    v4_relat_1 @ sk_D @ sk_B ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k1_relat_1 @ sk_D )
    = sk_B ),
    inference(demod,[status(thm)],['104','105','108'])).

thf(t176_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v5_relat_1 @ C @ A )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) )
       => ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ) )).

thf('110',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X4 @ ( k1_relat_1 @ X5 ) )
      | ( m1_subset_1 @ ( k1_funct_1 @ X5 @ X4 ) @ X6 )
      | ~ ( v1_funct_1 @ X5 )
      | ~ ( v5_relat_1 @ X5 @ X6 )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t176_funct_1])).

thf('111',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ~ ( v1_funct_1 @ sk_D )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['31','32'])).

thf('113',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('114',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_B )
      | ~ ( v5_relat_1 @ sk_D @ X1 )
      | ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ X0 ) @ X1 ) ) ),
    inference(demod,[status(thm)],['111','112','113'])).

thf('115',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_F ) @ X0 )
      | ~ ( v5_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['94','114'])).

thf('116',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_F ) @ sk_A ),
    inference('sup-',[status(thm)],['89','115'])).

thf('117',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t176_funct_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ A )
                 => ( ( k7_partfun1 @ B @ C @ D )
                    = ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) )).

thf('118',plain,(
    ! [X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( v1_xboole_0 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ X41 )
      | ( ( k7_partfun1 @ X39 @ X42 @ X40 )
        = ( k3_funct_2 @ X41 @ X39 @ X42 @ X40 ) )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X39 ) ) )
      | ~ ( v1_funct_2 @ X42 @ X41 @ X39 )
      | ~ ( v1_funct_1 @ X42 )
      | ( v1_xboole_0 @ X41 ) ) ),
    inference(cnf,[status(esa)],[t176_funct_2])).

thf('119',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_A @ sk_C )
      | ( ( k7_partfun1 @ sk_C @ sk_E @ X0 )
        = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['117','118'])).

thf('120',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( v1_funct_1 @ C )
          & ( v1_partfun1 @ C @ A ) )
       => ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B ) ) ) ) )).

thf('122',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( v1_funct_1 @ X19 )
      | ~ ( v1_partfun1 @ X19 @ X20 )
      | ( v1_funct_2 @ X19 @ X20 @ X21 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_funct_2])).

thf('123',plain,
    ( ( v1_funct_2 @ sk_E @ sk_A @ sk_C )
    | ~ ( v1_partfun1 @ sk_E @ sk_A )
    | ~ ( v1_funct_1 @ sk_E ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_partfun1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_funct_2 @ sk_E @ sk_A @ sk_C ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( ( k7_partfun1 @ sk_C @ sk_E @ X0 )
        = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['119','120','126'])).

thf('128',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['116','127'])).

thf('129',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_xboole_0 @ B ) )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ~ ( v1_partfun1 @ C @ A ) ) ) )).

thf('130',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ~ ( v1_xboole_0 @ X23 )
      | ~ ( v1_partfun1 @ X24 @ X22 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_partfun1])).

thf('131',plain,
    ( ~ ( v1_partfun1 @ sk_E @ sk_A )
    | ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v1_partfun1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,
    ( ~ ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(clc,[status(thm)],['133','134'])).

thf('136',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
      = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ) ),
    inference(clc,[status(thm)],['128','135'])).

thf('137',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('139',plain,(
    m1_subset_1 @ ( k1_funct_1 @ sk_D @ sk_F ) @ sk_A ),
    inference('sup-',[status(thm)],['89','115'])).

thf('140',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( v1_funct_1 @ X35 )
      | ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X38 @ X36 )
      | ( ( k3_funct_2 @ X36 @ X37 @ X35 @ X38 )
        = ( k1_funct_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_A @ sk_C ) ) ),
    inference('sup-',[status(thm)],['140','141'])).

thf('143',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v1_funct_2 @ sk_E @ sk_A @ sk_C ),
    inference(demod,[status(thm)],['123','124','125'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['142','143','144'])).

thf('146',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0 )
        = ( k1_funct_1 @ sk_E @ X0 ) ) ) ),
    inference(clc,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( k3_funct_2 @ sk_A @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup-',[status(thm)],['139','147'])).

thf('149',plain,
    ( ( k7_partfun1 @ sk_C @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) )
    = ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference('sup+',[status(thm)],['138','148'])).

thf('150',plain,(
    ( k1_funct_1 @ ( k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E ) @ sk_F )
 != ( k1_funct_1 @ sk_E @ ( k1_funct_1 @ sk_D @ sk_F ) ) ),
    inference(demod,[status(thm)],['88','149'])).

thf('151',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( sk_B = k1_xboole_0 ) ),
    inference('simplify_reflect-',[status(thm)],['38','150'])).

thf('152',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,(
    sk_B = k1_xboole_0 ),
    inference(clc,[status(thm)],['151','152'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('154',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('155',plain,(
    $false ),
    inference(demod,[status(thm)],['0','153','154'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.F6SLXPgMiJ
% 0.13/0.37  % Computer   : n025.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 14:45:51 EST 2020
% 0.13/0.38  % CPUTime    : 
% 0.13/0.38  % Running portfolio for 600 s
% 0.13/0.38  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.38  % Number of cores: 8
% 0.23/0.38  % Python version: Python 3.6.8
% 0.23/0.38  % Running in FO mode
% 0.39/0.57  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.57  % Solved by: fo/fo7.sh
% 0.39/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.57  % done 113 iterations in 0.067s
% 0.39/0.57  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.57  % SZS output start Refutation
% 0.39/0.57  thf(sk_D_type, type, sk_D: $i).
% 0.39/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.39/0.57  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.39/0.57  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.39/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.39/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.57  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.57  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.39/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.57  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.39/0.57  thf(k8_funct_2_type, type, k8_funct_2: $i > $i > $i > $i > $i > $i).
% 0.39/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.39/0.57  thf(sk_F_type, type, sk_F: $i).
% 0.39/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.39/0.57  thf(k7_partfun1_type, type, k7_partfun1: $i > $i > $i > $i).
% 0.39/0.57  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.39/0.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.39/0.57  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.39/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.57  thf(sk_E_type, type, sk_E: $i).
% 0.39/0.57  thf(t193_funct_2, conjecture,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.39/0.57           ( ![C:$i,D:$i]:
% 0.39/0.57             ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.39/0.57                 ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.39/0.57               ( ![E:$i]:
% 0.39/0.57                 ( ( ( v1_funct_1 @ E ) & 
% 0.39/0.57                     ( m1_subset_1 @
% 0.39/0.57                       E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) =>
% 0.39/0.57                   ( ![F:$i]:
% 0.39/0.57                     ( ( m1_subset_1 @ F @ B ) =>
% 0.39/0.57                       ( ( v1_partfun1 @ E @ A ) =>
% 0.39/0.57                         ( ( k3_funct_2 @
% 0.39/0.57                             B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F ) =
% 0.39/0.57                           ( k7_partfun1 @
% 0.39/0.57                             C @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.57    (~( ![A:$i]:
% 0.39/0.57        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.57          ( ![B:$i]:
% 0.39/0.57            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.39/0.57              ( ![C:$i,D:$i]:
% 0.39/0.57                ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ A ) & 
% 0.39/0.57                    ( m1_subset_1 @
% 0.39/0.57                      D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) ) =>
% 0.39/0.57                  ( ![E:$i]:
% 0.39/0.57                    ( ( ( v1_funct_1 @ E ) & 
% 0.39/0.57                        ( m1_subset_1 @
% 0.39/0.57                          E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) =>
% 0.39/0.57                      ( ![F:$i]:
% 0.39/0.57                        ( ( m1_subset_1 @ F @ B ) =>
% 0.39/0.57                          ( ( v1_partfun1 @ E @ A ) =>
% 0.39/0.57                            ( ( k3_funct_2 @
% 0.39/0.57                                B @ C @ ( k8_funct_2 @ B @ A @ C @ D @ E ) @ F ) =
% 0.39/0.57                              ( k7_partfun1 @
% 0.39/0.57                                C @ E @ ( k3_funct_2 @ B @ A @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.39/0.57    inference('cnf.neg', [status(esa)], [t193_funct_2])).
% 0.39/0.57  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('1', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('2', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(redefinition_k1_relset_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.57       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.39/0.57  thf('3', plain,
% 0.39/0.57      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.39/0.57         (((k1_relset_1 @ X14 @ X15 @ X13) = (k1_relat_1 @ X13))
% 0.39/0.57          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X14 @ X15))))),
% 0.39/0.57      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.39/0.57  thf('4', plain, (((k1_relset_1 @ sk_A @ sk_C @ sk_E) = (k1_relat_1 @ sk_E))),
% 0.39/0.57      inference('sup-', [status(thm)], ['2', '3'])).
% 0.39/0.57  thf('5', plain, ((v1_partfun1 @ sk_E @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(d4_partfun1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.39/0.57       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.39/0.57  thf('6', plain,
% 0.39/0.57      (![X28 : $i, X29 : $i]:
% 0.39/0.57         (~ (v1_partfun1 @ X29 @ X28)
% 0.39/0.57          | ((k1_relat_1 @ X29) = (X28))
% 0.39/0.57          | ~ (v4_relat_1 @ X29 @ X28)
% 0.39/0.57          | ~ (v1_relat_1 @ X29))),
% 0.39/0.57      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.39/0.57  thf('7', plain,
% 0.39/0.57      ((~ (v1_relat_1 @ sk_E)
% 0.39/0.57        | ~ (v4_relat_1 @ sk_E @ sk_A)
% 0.39/0.57        | ((k1_relat_1 @ sk_E) = (sk_A)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['5', '6'])).
% 0.39/0.57  thf('8', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(cc1_relset_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.57       ( v1_relat_1 @ C ) ))).
% 0.39/0.57  thf('9', plain,
% 0.39/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.39/0.57         ((v1_relat_1 @ X7)
% 0.39/0.57          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.39/0.57      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.39/0.57  thf('10', plain, ((v1_relat_1 @ sk_E)),
% 0.39/0.57      inference('sup-', [status(thm)], ['8', '9'])).
% 0.39/0.57  thf('11', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(cc2_relset_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.57       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.39/0.57  thf('12', plain,
% 0.39/0.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.39/0.57         ((v4_relat_1 @ X10 @ X11)
% 0.39/0.57          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.39/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.39/0.57  thf('13', plain, ((v4_relat_1 @ sk_E @ sk_A)),
% 0.39/0.57      inference('sup-', [status(thm)], ['11', '12'])).
% 0.39/0.57  thf('14', plain, (((k1_relat_1 @ sk_E) = (sk_A))),
% 0.39/0.57      inference('demod', [status(thm)], ['7', '10', '13'])).
% 0.39/0.57  thf('15', plain, (((k1_relset_1 @ sk_A @ sk_C @ sk_E) = (sk_A))),
% 0.39/0.57      inference('demod', [status(thm)], ['4', '14'])).
% 0.39/0.57  thf('16', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(t185_funct_2, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.39/0.57       ( ![D:$i]:
% 0.39/0.57         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ B @ C ) & 
% 0.39/0.57             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.39/0.57           ( ![E:$i]:
% 0.39/0.57             ( ( ( v1_funct_1 @ E ) & 
% 0.39/0.57                 ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ A ) ) ) ) =>
% 0.39/0.57               ( ![F:$i]:
% 0.39/0.57                 ( ( m1_subset_1 @ F @ B ) =>
% 0.39/0.57                   ( ( r1_tarski @
% 0.39/0.57                       ( k2_relset_1 @ B @ C @ D ) @ 
% 0.39/0.57                       ( k1_relset_1 @ C @ A @ E ) ) =>
% 0.39/0.57                     ( ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.39/0.57                       ( ( k1_funct_1 @ ( k8_funct_2 @ B @ C @ A @ D @ E ) @ F ) =
% 0.39/0.57                         ( k1_funct_1 @ E @ ( k1_funct_1 @ D @ F ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.57  thf('17', plain,
% 0.39/0.57      (![X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.39/0.57         (~ (v1_funct_1 @ X43)
% 0.39/0.57          | ~ (v1_funct_2 @ X43 @ X44 @ X45)
% 0.39/0.57          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X44 @ X45)))
% 0.39/0.57          | ~ (m1_subset_1 @ X46 @ X44)
% 0.39/0.57          | ((k1_funct_1 @ (k8_funct_2 @ X44 @ X45 @ X48 @ X43 @ X47) @ X46)
% 0.39/0.57              = (k1_funct_1 @ X47 @ (k1_funct_1 @ X43 @ X46)))
% 0.39/0.57          | ((X44) = (k1_xboole_0))
% 0.39/0.57          | ~ (r1_tarski @ (k2_relset_1 @ X44 @ X45 @ X43) @ 
% 0.39/0.57               (k1_relset_1 @ X45 @ X48 @ X47))
% 0.39/0.57          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X48)))
% 0.39/0.57          | ~ (v1_funct_1 @ X47)
% 0.39/0.57          | (v1_xboole_0 @ X45))),
% 0.39/0.57      inference('cnf', [status(esa)], [t185_funct_2])).
% 0.39/0.57  thf('18', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         ((v1_xboole_0 @ sk_A)
% 0.39/0.57          | ~ (v1_funct_1 @ X0)
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.39/0.57          | ~ (r1_tarski @ (k2_relset_1 @ sk_B @ sk_A @ sk_D) @ 
% 0.39/0.57               (k1_relset_1 @ sk_A @ X1 @ X0))
% 0.39/0.57          | ((sk_B) = (k1_xboole_0))
% 0.39/0.57          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0) @ X2)
% 0.39/0.57              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.39/0.57          | ~ (m1_subset_1 @ X2 @ sk_B)
% 0.39/0.57          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.39/0.57          | ~ (v1_funct_1 @ sk_D))),
% 0.39/0.57      inference('sup-', [status(thm)], ['16', '17'])).
% 0.39/0.57  thf('19', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(redefinition_k2_relset_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.57       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.39/0.57  thf('20', plain,
% 0.39/0.57      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.39/0.57         (((k2_relset_1 @ X17 @ X18 @ X16) = (k2_relat_1 @ X16))
% 0.39/0.57          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.39/0.57      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.39/0.57  thf('21', plain,
% 0.39/0.57      (((k2_relset_1 @ sk_B @ sk_A @ sk_D) = (k2_relat_1 @ sk_D))),
% 0.39/0.57      inference('sup-', [status(thm)], ['19', '20'])).
% 0.39/0.57  thf('22', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('23', plain, ((v1_funct_1 @ sk_D)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('24', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.57         ((v1_xboole_0 @ sk_A)
% 0.39/0.57          | ~ (v1_funct_1 @ X0)
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.39/0.57          | ~ (r1_tarski @ (k2_relat_1 @ sk_D) @ (k1_relset_1 @ sk_A @ X1 @ X0))
% 0.39/0.57          | ((sk_B) = (k1_xboole_0))
% 0.39/0.57          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0) @ X2)
% 0.39/0.57              = (k1_funct_1 @ X0 @ (k1_funct_1 @ sk_D @ X2)))
% 0.39/0.57          | ~ (m1_subset_1 @ X2 @ sk_B))),
% 0.39/0.57      inference('demod', [status(thm)], ['18', '21', '22', '23'])).
% 0.39/0.57  thf('25', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.39/0.57          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.39/0.57              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.39/0.57          | ((sk_B) = (k1_xboole_0))
% 0.39/0.57          | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))
% 0.39/0.57          | ~ (v1_funct_1 @ sk_E)
% 0.39/0.57          | (v1_xboole_0 @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['15', '24'])).
% 0.39/0.57  thf('26', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('27', plain,
% 0.39/0.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.39/0.57         ((v5_relat_1 @ X10 @ X12)
% 0.39/0.57          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.39/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.39/0.57  thf('28', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.39/0.57      inference('sup-', [status(thm)], ['26', '27'])).
% 0.39/0.57  thf(d19_relat_1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( v1_relat_1 @ B ) =>
% 0.39/0.57       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.39/0.57  thf('29', plain,
% 0.39/0.57      (![X2 : $i, X3 : $i]:
% 0.39/0.57         (~ (v5_relat_1 @ X2 @ X3)
% 0.39/0.57          | (r1_tarski @ (k2_relat_1 @ X2) @ X3)
% 0.39/0.57          | ~ (v1_relat_1 @ X2))),
% 0.39/0.57      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.39/0.57  thf('30', plain,
% 0.39/0.57      ((~ (v1_relat_1 @ sk_D) | (r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['28', '29'])).
% 0.39/0.57  thf('31', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('32', plain,
% 0.39/0.57      (![X7 : $i, X8 : $i, X9 : $i]:
% 0.39/0.57         ((v1_relat_1 @ X7)
% 0.39/0.57          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9))))),
% 0.39/0.57      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.39/0.57  thf('33', plain, ((v1_relat_1 @ sk_D)),
% 0.39/0.57      inference('sup-', [status(thm)], ['31', '32'])).
% 0.39/0.57  thf('34', plain, ((r1_tarski @ (k2_relat_1 @ sk_D) @ sk_A)),
% 0.39/0.57      inference('demod', [status(thm)], ['30', '33'])).
% 0.39/0.57  thf('35', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('37', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.39/0.57          | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.39/0.57              = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ X0)))
% 0.39/0.57          | ((sk_B) = (k1_xboole_0))
% 0.39/0.57          | (v1_xboole_0 @ sk_A))),
% 0.39/0.57      inference('demod', [status(thm)], ['25', '34', '35', '36'])).
% 0.39/0.57  thf('38', plain,
% 0.39/0.57      (((v1_xboole_0 @ sk_A)
% 0.39/0.57        | ((sk_B) = (k1_xboole_0))
% 0.39/0.57        | ((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.39/0.57            = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['1', '37'])).
% 0.39/0.57  thf('39', plain,
% 0.39/0.57      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.39/0.57         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.39/0.57         != (k7_partfun1 @ sk_C @ sk_E @ 
% 0.39/0.57             (k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('40', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('41', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(redefinition_k3_funct_2, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.57     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.39/0.57         ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.39/0.57         ( m1_subset_1 @ D @ A ) ) =>
% 0.39/0.57       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.39/0.57  thf('42', plain,
% 0.39/0.57      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.39/0.57          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 0.39/0.57          | ~ (v1_funct_1 @ X35)
% 0.39/0.57          | (v1_xboole_0 @ X36)
% 0.39/0.57          | ~ (m1_subset_1 @ X38 @ X36)
% 0.39/0.57          | ((k3_funct_2 @ X36 @ X37 @ X35 @ X38) = (k1_funct_1 @ X35 @ X38)))),
% 0.39/0.57      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.39/0.57  thf('43', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.39/0.57          | (v1_xboole_0 @ sk_B)
% 0.39/0.57          | ~ (v1_funct_1 @ sk_D)
% 0.39/0.57          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['41', '42'])).
% 0.39/0.57  thf('44', plain, ((v1_funct_1 @ sk_D)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('45', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('46', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0))
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.39/0.57          | (v1_xboole_0 @ sk_B))),
% 0.39/0.57      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.39/0.57  thf('47', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('48', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.39/0.57          | ((k3_funct_2 @ sk_B @ sk_A @ sk_D @ X0) = (k1_funct_1 @ sk_D @ X0)))),
% 0.39/0.57      inference('clc', [status(thm)], ['46', '47'])).
% 0.39/0.57  thf('49', plain,
% 0.39/0.57      (((k3_funct_2 @ sk_B @ sk_A @ sk_D @ sk_F) = (k1_funct_1 @ sk_D @ sk_F))),
% 0.39/0.57      inference('sup-', [status(thm)], ['40', '48'])).
% 0.39/0.57  thf('50', plain,
% 0.39/0.57      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.39/0.57         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.39/0.57         != (k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.39/0.57      inference('demod', [status(thm)], ['39', '49'])).
% 0.39/0.57  thf('51', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('52', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('53', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(dt_k8_funct_2, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.39/0.57     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.39/0.57         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.39/0.57         ( v1_funct_1 @ E ) & 
% 0.39/0.57         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.39/0.57       ( ( v1_funct_1 @ ( k8_funct_2 @ A @ B @ C @ D @ E ) ) & 
% 0.39/0.57         ( v1_funct_2 @ ( k8_funct_2 @ A @ B @ C @ D @ E ) @ A @ C ) & 
% 0.39/0.57         ( m1_subset_1 @
% 0.39/0.57           ( k8_funct_2 @ A @ B @ C @ D @ E ) @ 
% 0.39/0.57           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ))).
% 0.39/0.57  thf('54', plain,
% 0.39/0.57      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.39/0.57          | ~ (v1_funct_2 @ X30 @ X31 @ X32)
% 0.39/0.57          | ~ (v1_funct_1 @ X30)
% 0.39/0.57          | ~ (v1_funct_1 @ X33)
% 0.39/0.57          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X34)))
% 0.39/0.57          | (m1_subset_1 @ (k8_funct_2 @ X31 @ X32 @ X34 @ X30 @ X33) @ 
% 0.39/0.57             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X34))))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_k8_funct_2])).
% 0.39/0.57  thf('55', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((m1_subset_1 @ (k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1) @ 
% 0.39/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.39/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.39/0.57          | ~ (v1_funct_1 @ X1)
% 0.39/0.57          | ~ (v1_funct_1 @ sk_D)
% 0.39/0.57          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['53', '54'])).
% 0.39/0.57  thf('56', plain, ((v1_funct_1 @ sk_D)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('57', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('58', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((m1_subset_1 @ (k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1) @ 
% 0.39/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ X0)))
% 0.39/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.39/0.57          | ~ (v1_funct_1 @ X1))),
% 0.39/0.57      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.39/0.57  thf('59', plain,
% 0.39/0.57      ((~ (v1_funct_1 @ sk_E)
% 0.39/0.57        | (m1_subset_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.39/0.57           (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 0.39/0.57      inference('sup-', [status(thm)], ['52', '58'])).
% 0.39/0.57  thf('60', plain, ((v1_funct_1 @ sk_E)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('61', plain,
% 0.39/0.57      ((m1_subset_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.39/0.57        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.39/0.57      inference('demod', [status(thm)], ['59', '60'])).
% 0.39/0.57  thf('62', plain,
% 0.39/0.57      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.39/0.57          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 0.39/0.57          | ~ (v1_funct_1 @ X35)
% 0.39/0.57          | (v1_xboole_0 @ X36)
% 0.39/0.57          | ~ (m1_subset_1 @ X38 @ X36)
% 0.39/0.57          | ((k3_funct_2 @ X36 @ X37 @ X35 @ X38) = (k1_funct_1 @ X35 @ X38)))),
% 0.39/0.57      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.39/0.57  thf('63', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.39/0.57            (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.39/0.57            = (k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.39/0.57               X0))
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.39/0.57          | (v1_xboole_0 @ sk_B)
% 0.39/0.57          | ~ (v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E))
% 0.39/0.57          | ~ (v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.39/0.57               sk_B @ sk_C))),
% 0.39/0.57      inference('sup-', [status(thm)], ['61', '62'])).
% 0.39/0.57  thf('64', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('65', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('66', plain,
% 0.39/0.57      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.39/0.57          | ~ (v1_funct_2 @ X30 @ X31 @ X32)
% 0.39/0.57          | ~ (v1_funct_1 @ X30)
% 0.39/0.57          | ~ (v1_funct_1 @ X33)
% 0.39/0.57          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X34)))
% 0.39/0.57          | (v1_funct_1 @ (k8_funct_2 @ X31 @ X32 @ X34 @ X30 @ X33)))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_k8_funct_2])).
% 0.39/0.57  thf('67', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0))
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.39/0.57          | ~ (v1_funct_1 @ X0)
% 0.39/0.57          | ~ (v1_funct_1 @ sk_D)
% 0.39/0.57          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['65', '66'])).
% 0.39/0.57  thf('68', plain, ((v1_funct_1 @ sk_D)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('69', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('70', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ X1 @ sk_D @ X0))
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X1)))
% 0.39/0.57          | ~ (v1_funct_1 @ X0))),
% 0.39/0.57      inference('demod', [status(thm)], ['67', '68', '69'])).
% 0.39/0.57  thf('71', plain,
% 0.39/0.57      ((~ (v1_funct_1 @ sk_E)
% 0.39/0.57        | (v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['64', '70'])).
% 0.39/0.57  thf('72', plain, ((v1_funct_1 @ sk_E)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('73', plain,
% 0.39/0.57      ((v1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E))),
% 0.39/0.57      inference('demod', [status(thm)], ['71', '72'])).
% 0.39/0.57  thf('74', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('75', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('76', plain,
% 0.39/0.57      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.39/0.57          | ~ (v1_funct_2 @ X30 @ X31 @ X32)
% 0.39/0.57          | ~ (v1_funct_1 @ X30)
% 0.39/0.57          | ~ (v1_funct_1 @ X33)
% 0.39/0.57          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X34)))
% 0.39/0.57          | (v1_funct_2 @ (k8_funct_2 @ X31 @ X32 @ X34 @ X30 @ X33) @ X31 @ 
% 0.39/0.57             X34))),
% 0.39/0.57      inference('cnf', [status(esa)], [dt_k8_funct_2])).
% 0.39/0.57  thf('77', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1) @ sk_B @ X0)
% 0.39/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.39/0.57          | ~ (v1_funct_1 @ X1)
% 0.39/0.57          | ~ (v1_funct_1 @ sk_D)
% 0.39/0.57          | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['75', '76'])).
% 0.39/0.57  thf('78', plain, ((v1_funct_1 @ sk_D)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('79', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('80', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ X0 @ sk_D @ X1) @ sk_B @ X0)
% 0.39/0.57          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ X0)))
% 0.39/0.57          | ~ (v1_funct_1 @ X1))),
% 0.39/0.57      inference('demod', [status(thm)], ['77', '78', '79'])).
% 0.39/0.57  thf('81', plain,
% 0.39/0.57      ((~ (v1_funct_1 @ sk_E)
% 0.39/0.57        | (v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.39/0.57           sk_B @ sk_C))),
% 0.39/0.57      inference('sup-', [status(thm)], ['74', '80'])).
% 0.39/0.57  thf('82', plain, ((v1_funct_1 @ sk_E)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('83', plain,
% 0.39/0.57      ((v1_funct_2 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_B @ 
% 0.39/0.57        sk_C)),
% 0.39/0.57      inference('demod', [status(thm)], ['81', '82'])).
% 0.39/0.57  thf('84', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.39/0.57            (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.39/0.57            = (k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ 
% 0.39/0.57               X0))
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ sk_B)
% 0.39/0.57          | (v1_xboole_0 @ sk_B))),
% 0.39/0.57      inference('demod', [status(thm)], ['63', '73', '83'])).
% 0.39/0.57  thf('85', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('86', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X0 @ sk_B)
% 0.39/0.57          | ((k3_funct_2 @ sk_B @ sk_C @ 
% 0.39/0.57              (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)
% 0.39/0.57              = (k1_funct_1 @ 
% 0.39/0.57                 (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ X0)))),
% 0.39/0.57      inference('clc', [status(thm)], ['84', '85'])).
% 0.39/0.57  thf('87', plain,
% 0.39/0.57      (((k3_funct_2 @ sk_B @ sk_C @ 
% 0.39/0.57         (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.39/0.57         = (k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F))),
% 0.39/0.57      inference('sup-', [status(thm)], ['51', '86'])).
% 0.39/0.57  thf('88', plain,
% 0.39/0.57      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.39/0.57         != (k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.39/0.57      inference('demod', [status(thm)], ['50', '87'])).
% 0.39/0.57  thf('89', plain, ((v5_relat_1 @ sk_D @ sk_A)),
% 0.39/0.57      inference('sup-', [status(thm)], ['26', '27'])).
% 0.39/0.57  thf('90', plain, ((m1_subset_1 @ sk_F @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(t2_subset, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ A @ B ) =>
% 0.39/0.57       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.39/0.57  thf('91', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         ((r2_hidden @ X0 @ X1)
% 0.39/0.57          | (v1_xboole_0 @ X1)
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ X1))),
% 0.39/0.57      inference('cnf', [status(esa)], [t2_subset])).
% 0.39/0.57  thf('92', plain, (((v1_xboole_0 @ sk_B) | (r2_hidden @ sk_F @ sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['90', '91'])).
% 0.39/0.57  thf('93', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('94', plain, ((r2_hidden @ sk_F @ sk_B)),
% 0.39/0.57      inference('clc', [status(thm)], ['92', '93'])).
% 0.39/0.57  thf('95', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(cc5_funct_2, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.39/0.57       ( ![C:$i]:
% 0.39/0.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.57           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.39/0.57             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.39/0.57  thf('96', plain,
% 0.39/0.57      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27)))
% 0.39/0.57          | (v1_partfun1 @ X25 @ X26)
% 0.39/0.57          | ~ (v1_funct_2 @ X25 @ X26 @ X27)
% 0.39/0.57          | ~ (v1_funct_1 @ X25)
% 0.39/0.57          | (v1_xboole_0 @ X27))),
% 0.39/0.57      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.39/0.57  thf('97', plain,
% 0.39/0.57      (((v1_xboole_0 @ sk_A)
% 0.39/0.57        | ~ (v1_funct_1 @ sk_D)
% 0.39/0.57        | ~ (v1_funct_2 @ sk_D @ sk_B @ sk_A)
% 0.39/0.57        | (v1_partfun1 @ sk_D @ sk_B))),
% 0.39/0.57      inference('sup-', [status(thm)], ['95', '96'])).
% 0.39/0.57  thf('98', plain, ((v1_funct_1 @ sk_D)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('99', plain, ((v1_funct_2 @ sk_D @ sk_B @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('100', plain, (((v1_xboole_0 @ sk_A) | (v1_partfun1 @ sk_D @ sk_B))),
% 0.39/0.57      inference('demod', [status(thm)], ['97', '98', '99'])).
% 0.39/0.57  thf('101', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('102', plain, ((v1_partfun1 @ sk_D @ sk_B)),
% 0.39/0.57      inference('clc', [status(thm)], ['100', '101'])).
% 0.39/0.57  thf('103', plain,
% 0.39/0.57      (![X28 : $i, X29 : $i]:
% 0.39/0.57         (~ (v1_partfun1 @ X29 @ X28)
% 0.39/0.57          | ((k1_relat_1 @ X29) = (X28))
% 0.39/0.57          | ~ (v4_relat_1 @ X29 @ X28)
% 0.39/0.57          | ~ (v1_relat_1 @ X29))),
% 0.39/0.57      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.39/0.57  thf('104', plain,
% 0.39/0.57      ((~ (v1_relat_1 @ sk_D)
% 0.39/0.57        | ~ (v4_relat_1 @ sk_D @ sk_B)
% 0.39/0.57        | ((k1_relat_1 @ sk_D) = (sk_B)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['102', '103'])).
% 0.39/0.57  thf('105', plain, ((v1_relat_1 @ sk_D)),
% 0.39/0.57      inference('sup-', [status(thm)], ['31', '32'])).
% 0.39/0.57  thf('106', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B @ sk_A)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('107', plain,
% 0.39/0.57      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.39/0.57         ((v4_relat_1 @ X10 @ X11)
% 0.39/0.57          | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X11 @ X12))))),
% 0.39/0.57      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.39/0.57  thf('108', plain, ((v4_relat_1 @ sk_D @ sk_B)),
% 0.39/0.57      inference('sup-', [status(thm)], ['106', '107'])).
% 0.39/0.57  thf('109', plain, (((k1_relat_1 @ sk_D) = (sk_B))),
% 0.39/0.57      inference('demod', [status(thm)], ['104', '105', '108'])).
% 0.39/0.57  thf(t176_funct_1, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( ( v1_relat_1 @ C ) & ( v5_relat_1 @ C @ A ) & ( v1_funct_1 @ C ) ) =>
% 0.39/0.57       ( ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) =>
% 0.39/0.57         ( m1_subset_1 @ ( k1_funct_1 @ C @ B ) @ A ) ) ))).
% 0.39/0.57  thf('110', plain,
% 0.39/0.57      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X4 @ (k1_relat_1 @ X5))
% 0.39/0.57          | (m1_subset_1 @ (k1_funct_1 @ X5 @ X4) @ X6)
% 0.39/0.57          | ~ (v1_funct_1 @ X5)
% 0.39/0.57          | ~ (v5_relat_1 @ X5 @ X6)
% 0.39/0.57          | ~ (v1_relat_1 @ X5))),
% 0.39/0.57      inference('cnf', [status(esa)], [t176_funct_1])).
% 0.39/0.57  thf('111', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X0 @ sk_B)
% 0.39/0.57          | ~ (v1_relat_1 @ sk_D)
% 0.39/0.57          | ~ (v5_relat_1 @ sk_D @ X1)
% 0.39/0.57          | ~ (v1_funct_1 @ sk_D)
% 0.39/0.57          | (m1_subset_1 @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 0.39/0.57      inference('sup-', [status(thm)], ['109', '110'])).
% 0.39/0.57  thf('112', plain, ((v1_relat_1 @ sk_D)),
% 0.39/0.57      inference('sup-', [status(thm)], ['31', '32'])).
% 0.39/0.57  thf('113', plain, ((v1_funct_1 @ sk_D)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('114', plain,
% 0.39/0.57      (![X0 : $i, X1 : $i]:
% 0.39/0.57         (~ (r2_hidden @ X0 @ sk_B)
% 0.39/0.57          | ~ (v5_relat_1 @ sk_D @ X1)
% 0.39/0.57          | (m1_subset_1 @ (k1_funct_1 @ sk_D @ X0) @ X1))),
% 0.39/0.57      inference('demod', [status(thm)], ['111', '112', '113'])).
% 0.39/0.57  thf('115', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_F) @ X0)
% 0.39/0.57          | ~ (v5_relat_1 @ sk_D @ X0))),
% 0.39/0.57      inference('sup-', [status(thm)], ['94', '114'])).
% 0.39/0.57  thf('116', plain, ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_F) @ sk_A)),
% 0.39/0.57      inference('sup-', [status(thm)], ['89', '115'])).
% 0.39/0.57  thf('117', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(t176_funct_2, axiom,
% 0.39/0.57    (![A:$i]:
% 0.39/0.57     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.57       ( ![B:$i]:
% 0.39/0.57         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.39/0.57           ( ![C:$i]:
% 0.39/0.57             ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.39/0.57                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.57               ( ![D:$i]:
% 0.39/0.57                 ( ( m1_subset_1 @ D @ A ) =>
% 0.39/0.57                   ( ( k7_partfun1 @ B @ C @ D ) =
% 0.39/0.57                     ( k3_funct_2 @ A @ B @ C @ D ) ) ) ) ) ) ) ) ))).
% 0.39/0.57  thf('118', plain,
% 0.39/0.57      (![X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.39/0.57         ((v1_xboole_0 @ X39)
% 0.39/0.57          | ~ (m1_subset_1 @ X40 @ X41)
% 0.39/0.57          | ((k7_partfun1 @ X39 @ X42 @ X40)
% 0.39/0.57              = (k3_funct_2 @ X41 @ X39 @ X42 @ X40))
% 0.39/0.57          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X39)))
% 0.39/0.57          | ~ (v1_funct_2 @ X42 @ X41 @ X39)
% 0.39/0.57          | ~ (v1_funct_1 @ X42)
% 0.39/0.57          | (v1_xboole_0 @ X41))),
% 0.39/0.57      inference('cnf', [status(esa)], [t176_funct_2])).
% 0.39/0.57  thf('119', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v1_xboole_0 @ sk_A)
% 0.39/0.57          | ~ (v1_funct_1 @ sk_E)
% 0.39/0.57          | ~ (v1_funct_2 @ sk_E @ sk_A @ sk_C)
% 0.39/0.57          | ((k7_partfun1 @ sk_C @ sk_E @ X0)
% 0.39/0.57              = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0))
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.39/0.57          | (v1_xboole_0 @ sk_C))),
% 0.39/0.57      inference('sup-', [status(thm)], ['117', '118'])).
% 0.39/0.57  thf('120', plain, ((v1_funct_1 @ sk_E)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('121', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(cc1_funct_2, axiom,
% 0.39/0.57    (![A:$i,B:$i,C:$i]:
% 0.39/0.57     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.57       ( ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) =>
% 0.39/0.57         ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) ) ))).
% 0.39/0.57  thf('122', plain,
% 0.39/0.57      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.39/0.57         (~ (v1_funct_1 @ X19)
% 0.39/0.57          | ~ (v1_partfun1 @ X19 @ X20)
% 0.39/0.57          | (v1_funct_2 @ X19 @ X20 @ X21)
% 0.39/0.57          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21))))),
% 0.39/0.57      inference('cnf', [status(esa)], [cc1_funct_2])).
% 0.39/0.57  thf('123', plain,
% 0.39/0.57      (((v1_funct_2 @ sk_E @ sk_A @ sk_C)
% 0.39/0.57        | ~ (v1_partfun1 @ sk_E @ sk_A)
% 0.39/0.57        | ~ (v1_funct_1 @ sk_E))),
% 0.39/0.57      inference('sup-', [status(thm)], ['121', '122'])).
% 0.39/0.57  thf('124', plain, ((v1_partfun1 @ sk_E @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('125', plain, ((v1_funct_1 @ sk_E)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('126', plain, ((v1_funct_2 @ sk_E @ sk_A @ sk_C)),
% 0.39/0.57      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.39/0.57  thf('127', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         ((v1_xboole_0 @ sk_A)
% 0.39/0.57          | ((k7_partfun1 @ sk_C @ sk_E @ X0)
% 0.39/0.57              = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0))
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.39/0.57          | (v1_xboole_0 @ sk_C))),
% 0.39/0.57      inference('demod', [status(thm)], ['119', '120', '126'])).
% 0.39/0.57  thf('128', plain,
% 0.39/0.57      (((v1_xboole_0 @ sk_C)
% 0.39/0.57        | ((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.39/0.57            = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))
% 0.39/0.57        | (v1_xboole_0 @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['116', '127'])).
% 0.39/0.57  thf('129', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf(cc2_partfun1, axiom,
% 0.39/0.57    (![A:$i,B:$i]:
% 0.39/0.57     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_xboole_0 @ B ) ) =>
% 0.39/0.57       ( ![C:$i]:
% 0.39/0.57         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.57           ( ~( v1_partfun1 @ C @ A ) ) ) ) ))).
% 0.39/0.57  thf('130', plain,
% 0.39/0.57      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.39/0.57         ((v1_xboole_0 @ X22)
% 0.39/0.57          | ~ (v1_xboole_0 @ X23)
% 0.39/0.57          | ~ (v1_partfun1 @ X24 @ X22)
% 0.39/0.57          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23))))),
% 0.39/0.57      inference('cnf', [status(esa)], [cc2_partfun1])).
% 0.39/0.57  thf('131', plain,
% 0.39/0.57      ((~ (v1_partfun1 @ sk_E @ sk_A)
% 0.39/0.57        | ~ (v1_xboole_0 @ sk_C)
% 0.39/0.57        | (v1_xboole_0 @ sk_A))),
% 0.39/0.57      inference('sup-', [status(thm)], ['129', '130'])).
% 0.39/0.57  thf('132', plain, ((v1_partfun1 @ sk_E @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('133', plain, ((~ (v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_A))),
% 0.39/0.57      inference('demod', [status(thm)], ['131', '132'])).
% 0.39/0.57  thf('134', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('135', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.39/0.57      inference('clc', [status(thm)], ['133', '134'])).
% 0.39/0.57  thf('136', plain,
% 0.39/0.57      (((v1_xboole_0 @ sk_A)
% 0.39/0.57        | ((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.39/0.57            = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))))),
% 0.39/0.57      inference('clc', [status(thm)], ['128', '135'])).
% 0.39/0.57  thf('137', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('138', plain,
% 0.39/0.57      (((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.39/0.57         = (k3_funct_2 @ sk_A @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.39/0.57      inference('clc', [status(thm)], ['136', '137'])).
% 0.39/0.57  thf('139', plain, ((m1_subset_1 @ (k1_funct_1 @ sk_D @ sk_F) @ sk_A)),
% 0.39/0.57      inference('sup-', [status(thm)], ['89', '115'])).
% 0.39/0.57  thf('140', plain,
% 0.39/0.57      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('141', plain,
% 0.39/0.57      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.39/0.57          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 0.39/0.57          | ~ (v1_funct_1 @ X35)
% 0.39/0.57          | (v1_xboole_0 @ X36)
% 0.39/0.57          | ~ (m1_subset_1 @ X38 @ X36)
% 0.39/0.57          | ((k3_funct_2 @ X36 @ X37 @ X35 @ X38) = (k1_funct_1 @ X35 @ X38)))),
% 0.39/0.57      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.39/0.57  thf('142', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (((k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0) = (k1_funct_1 @ sk_E @ X0))
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.39/0.57          | (v1_xboole_0 @ sk_A)
% 0.39/0.57          | ~ (v1_funct_1 @ sk_E)
% 0.39/0.57          | ~ (v1_funct_2 @ sk_E @ sk_A @ sk_C))),
% 0.39/0.57      inference('sup-', [status(thm)], ['140', '141'])).
% 0.39/0.57  thf('143', plain, ((v1_funct_1 @ sk_E)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('144', plain, ((v1_funct_2 @ sk_E @ sk_A @ sk_C)),
% 0.39/0.57      inference('demod', [status(thm)], ['123', '124', '125'])).
% 0.39/0.57  thf('145', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (((k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0) = (k1_funct_1 @ sk_E @ X0))
% 0.39/0.57          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.39/0.57          | (v1_xboole_0 @ sk_A))),
% 0.39/0.57      inference('demod', [status(thm)], ['142', '143', '144'])).
% 0.39/0.57  thf('146', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('147', plain,
% 0.39/0.57      (![X0 : $i]:
% 0.39/0.57         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.39/0.57          | ((k3_funct_2 @ sk_A @ sk_C @ sk_E @ X0) = (k1_funct_1 @ sk_E @ X0)))),
% 0.39/0.57      inference('clc', [status(thm)], ['145', '146'])).
% 0.39/0.57  thf('148', plain,
% 0.39/0.57      (((k3_funct_2 @ sk_A @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.39/0.57         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.39/0.57      inference('sup-', [status(thm)], ['139', '147'])).
% 0.39/0.57  thf('149', plain,
% 0.39/0.57      (((k7_partfun1 @ sk_C @ sk_E @ (k1_funct_1 @ sk_D @ sk_F))
% 0.39/0.57         = (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.39/0.57      inference('sup+', [status(thm)], ['138', '148'])).
% 0.39/0.57  thf('150', plain,
% 0.39/0.57      (((k1_funct_1 @ (k8_funct_2 @ sk_B @ sk_A @ sk_C @ sk_D @ sk_E) @ sk_F)
% 0.39/0.57         != (k1_funct_1 @ sk_E @ (k1_funct_1 @ sk_D @ sk_F)))),
% 0.39/0.57      inference('demod', [status(thm)], ['88', '149'])).
% 0.39/0.57  thf('151', plain, (((v1_xboole_0 @ sk_A) | ((sk_B) = (k1_xboole_0)))),
% 0.39/0.57      inference('simplify_reflect-', [status(thm)], ['38', '150'])).
% 0.39/0.57  thf('152', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.39/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.57  thf('153', plain, (((sk_B) = (k1_xboole_0))),
% 0.39/0.57      inference('clc', [status(thm)], ['151', '152'])).
% 0.39/0.57  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.39/0.57  thf('154', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.39/0.57      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.39/0.57  thf('155', plain, ($false),
% 0.39/0.57      inference('demod', [status(thm)], ['0', '153', '154'])).
% 0.39/0.57  
% 0.39/0.57  % SZS output end Refutation
% 0.39/0.57  
% 0.39/0.58  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
