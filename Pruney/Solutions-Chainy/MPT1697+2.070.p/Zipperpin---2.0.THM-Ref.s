%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aSdtBgeXPi

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:04 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  316 (1365 expanded)
%              Number of leaves         :   43 ( 401 expanded)
%              Depth                    :   46
%              Number of atoms          : 4924 (56810 expanded)
%              Number of equality atoms :  159 (1739 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(t6_tmap_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( ~ ( v1_xboole_0 @ C )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
             => ! [D: $i] :
                  ( ( ~ ( v1_xboole_0 @ D )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) )
                 => ( ( r1_subset_1 @ C @ D )
                   => ! [E: $i] :
                        ( ( ( v1_funct_1 @ E )
                          & ( v1_funct_2 @ E @ C @ B )
                          & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) )
                       => ! [F: $i] :
                            ( ( ( v1_funct_1 @ F )
                              & ( v1_funct_2 @ F @ D @ B )
                              & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) )
                           => ( ( ( k2_partfun1 @ C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) )
                                = ( k2_partfun1 @ D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) )
                              & ( ( k2_partfun1 @ ( k4_subset_1 @ A @ C @ D ) @ B @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C )
                                = E )
                              & ( ( k2_partfun1 @ ( k4_subset_1 @ A @ C @ D ) @ B @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D )
                                = F ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( ~ ( v1_xboole_0 @ C )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
               => ! [D: $i] :
                    ( ( ~ ( v1_xboole_0 @ D )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) )
                   => ( ( r1_subset_1 @ C @ D )
                     => ! [E: $i] :
                          ( ( ( v1_funct_1 @ E )
                            & ( v1_funct_2 @ E @ C @ B )
                            & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) )
                         => ! [F: $i] :
                              ( ( ( v1_funct_1 @ F )
                                & ( v1_funct_2 @ F @ D @ B )
                                & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) )
                             => ( ( ( k2_partfun1 @ C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) )
                                  = ( k2_partfun1 @ D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) )
                                & ( ( k2_partfun1 @ ( k4_subset_1 @ A @ C @ D ) @ B @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C )
                                  = E )
                                & ( ( k2_partfun1 @ ( k4_subset_1 @ A @ C @ D ) @ B @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D )
                                  = F ) ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_tmap_1])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ( X10 != X11 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X19 ) @ X20 )
      | ( v4_relat_1 @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('4',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('5',plain,(
    ! [X24: $i,X25: $i] :
      ( ( X24
        = ( k7_relat_1 @ X24 @ X25 ) )
      | ~ ( v4_relat_1 @ X24 @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('6',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf(t3_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( ( r2_hidden @ C @ B )
              & ( r2_hidden @ C @ A ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( ( r2_hidden @ C @ A )
                & ( r2_hidden @ C @ B ) ) ) ) )).

thf('8',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf(t207_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_xboole_0 @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = k1_xboole_0 ) ) ) )).

thf('11',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_xboole_0 @ X21 @ X22 )
      | ~ ( v1_relat_1 @ X23 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X23 @ X21 ) @ X22 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t207_relat_1])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X2 @ X1 ) @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X2 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['7','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k1_tmap_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B )
        & ~ ( v1_xboole_0 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
        & ~ ( v1_xboole_0 @ D )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) )
        & ( v1_funct_1 @ E )
        & ( v1_funct_2 @ E @ C @ B )
        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) )
        & ( v1_funct_1 @ F )
        & ( v1_funct_2 @ F @ D @ B )
        & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) )
     => ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) )
        & ( v1_funct_2 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( k4_subset_1 @ A @ C @ D ) @ B )
        & ( m1_subset_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ) )).

thf('18',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X42 @ X43 @ X44 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X46 ) )
      | ( v1_xboole_0 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X46 ) )
      | ( v1_xboole_0 @ X43 )
      | ( v1_xboole_0 @ X44 )
      | ( v1_xboole_0 @ X46 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ X45 @ X44 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X46 @ X44 @ X43 @ X45 @ X42 @ X47 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('19',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_tmap_1 @ X2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_tmap_1 @ X2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B_1 )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['16','22'])).

thf('24',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['23','24','25'])).

thf('27',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['15','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('30',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X42 @ X43 @ X44 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X46 ) )
      | ( v1_xboole_0 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X46 ) )
      | ( v1_xboole_0 @ X43 )
      | ( v1_xboole_0 @ X44 )
      | ( v1_xboole_0 @ X46 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ X45 @ X44 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X46 @ X44 @ X43 @ X45 @ X42 @ X47 ) @ ( k4_subset_1 @ X46 @ X43 @ X45 ) @ X44 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ ( k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_1 @ X0 @ sk_E @ X2 ) @ ( k4_subset_1 @ X1 @ sk_C_1 @ X0 ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ ( k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_1 @ X0 @ sk_E @ X2 ) @ ( k4_subset_1 @ X1 @ sk_C_1 @ X0 ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B_1 )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_D ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['31','37'])).

thf('39',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_D ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['38','39','40'])).

thf('42',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['30','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X44 ) ) )
      | ~ ( v1_funct_2 @ X42 @ X43 @ X44 )
      | ~ ( v1_funct_1 @ X42 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X46 ) )
      | ( v1_xboole_0 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X46 ) )
      | ( v1_xboole_0 @ X43 )
      | ( v1_xboole_0 @ X44 )
      | ( v1_xboole_0 @ X46 )
      | ~ ( v1_funct_1 @ X47 )
      | ~ ( v1_funct_2 @ X47 @ X45 @ X44 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X44 ) ) )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X46 @ X44 @ X43 @ X45 @ X42 @ X47 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X46 @ X43 @ X45 ) @ X44 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_1 @ X0 @ sk_E @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X1 @ sk_C_1 @ X0 ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_1 @ X0 @ sk_E @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X1 @ sk_C_1 @ X0 ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B_1 )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_D ) @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['46','52'])).

thf('54',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_D ) @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['45','56'])).

thf('58',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['57','58'])).

thf(d1_tmap_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( ~ ( v1_xboole_0 @ C )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) )
             => ! [D: $i] :
                  ( ( ~ ( v1_xboole_0 @ D )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ C @ B )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) )
                     => ! [F: $i] :
                          ( ( ( v1_funct_1 @ F )
                            & ( v1_funct_2 @ F @ D @ B )
                            & ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) )
                         => ( ( ( k2_partfun1 @ C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) )
                              = ( k2_partfun1 @ D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) )
                           => ! [G: $i] :
                                ( ( ( v1_funct_1 @ G )
                                  & ( v1_funct_2 @ G @ ( k4_subset_1 @ A @ C @ D ) @ B )
                                  & ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) )
                               => ( ( G
                                    = ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) )
                                <=> ( ( ( k2_partfun1 @ ( k4_subset_1 @ A @ C @ D ) @ B @ G @ C )
                                      = E )
                                    & ( ( k2_partfun1 @ ( k4_subset_1 @ A @ C @ D ) @ B @ G @ D )
                                      = F ) ) ) ) ) ) ) ) ) ) ) )).

thf('60',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( v1_xboole_0 @ X35 )
      | ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ X36 @ X35 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ( X41
       != ( k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X37 @ X40 @ X36 ) @ X35 @ X41 @ X40 )
        = X39 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X37 @ X40 @ X36 ) @ X35 ) ) )
      | ~ ( v1_funct_2 @ X41 @ ( k4_subset_1 @ X37 @ X40 @ X36 ) @ X35 )
      | ~ ( v1_funct_1 @ X41 )
      | ( ( k2_partfun1 @ X40 @ X35 @ X39 @ ( k9_subset_1 @ X37 @ X40 @ X36 ) )
       != ( k2_partfun1 @ X36 @ X35 @ X38 @ ( k9_subset_1 @ X37 @ X40 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X35 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X37 ) )
      | ( v1_xboole_0 @ X40 )
      | ( v1_xboole_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('61',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v1_xboole_0 @ X37 )
      | ( v1_xboole_0 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X35 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X35 ) ) )
      | ( ( k2_partfun1 @ X40 @ X35 @ X39 @ ( k9_subset_1 @ X37 @ X40 @ X36 ) )
       != ( k2_partfun1 @ X36 @ X35 @ X38 @ ( k9_subset_1 @ X37 @ X40 @ X36 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38 ) @ ( k4_subset_1 @ X37 @ X40 @ X36 ) @ X35 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X37 @ X40 @ X36 ) @ X35 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X37 @ X40 @ X36 ) @ X35 @ ( k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38 ) @ X40 )
        = X39 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X36 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ( v1_xboole_0 @ X36 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(simplify,[status(thm)],['60'])).

thf('62',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['59','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('68',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k9_subset_1 @ X15 @ X13 @ X14 )
        = ( k3_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    r1_subset_1 @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r1_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ( ( r1_subset_1 @ A @ B )
      <=> ( r1_xboole_0 @ A @ B ) ) ) )).

thf('71',plain,(
    ! [X26: $i,X27: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ( v1_xboole_0 @ X27 )
      | ( r1_xboole_0 @ X26 @ X27 )
      | ~ ( r1_subset_1 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_subset_1])).

thf('72',plain,
    ( ( r1_xboole_0 @ sk_C_1 @ sk_D )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r1_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_D ),
    inference(clc,[status(thm)],['74','75'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('77',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('78',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('80',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ( ( k2_partfun1 @ X32 @ X33 @ X31 @ X34 )
        = ( k7_relat_1 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X11: $i] :
      ( r1_tarski @ X11 @ X11 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('85',plain,(
    ! [X16: $i,X18: $i] :
      ( ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X18 ) )
      | ~ ( r1_tarski @ X16 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('86',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_1 @ X0 @ sk_E @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X1 @ sk_C_1 @ X0 ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('89',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_C_1 ) @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_C_1 ) @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['89','90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_C_1 ) @ sk_B_1 ) ) )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['86','93'])).

thf('95',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['94'])).

thf('96',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B_1 ) ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf('98',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    m1_subset_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ( v1_xboole_0 @ X35 )
      | ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( v1_funct_2 @ X38 @ X36 @ X35 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ( X41
       != ( k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X37 @ X40 @ X36 ) @ X35 @ X41 @ X36 )
        = X38 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X37 @ X40 @ X36 ) @ X35 ) ) )
      | ~ ( v1_funct_2 @ X41 @ ( k4_subset_1 @ X37 @ X40 @ X36 ) @ X35 )
      | ~ ( v1_funct_1 @ X41 )
      | ( ( k2_partfun1 @ X40 @ X35 @ X39 @ ( k9_subset_1 @ X37 @ X40 @ X36 ) )
       != ( k2_partfun1 @ X36 @ X35 @ X38 @ ( k9_subset_1 @ X37 @ X40 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X35 )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X37 ) )
      | ( v1_xboole_0 @ X40 )
      | ( v1_xboole_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('101',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v1_xboole_0 @ X37 )
      | ( v1_xboole_0 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X35 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X35 ) ) )
      | ( ( k2_partfun1 @ X40 @ X35 @ X39 @ ( k9_subset_1 @ X37 @ X40 @ X36 ) )
       != ( k2_partfun1 @ X36 @ X35 @ X38 @ ( k9_subset_1 @ X37 @ X40 @ X36 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38 ) @ ( k4_subset_1 @ X37 @ X40 @ X36 ) @ X35 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X37 @ X40 @ X36 ) @ X35 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X37 @ X40 @ X36 ) @ X35 @ ( k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38 ) @ X36 )
        = X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X36 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ( v1_xboole_0 @ X36 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('102',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ sk_C_1 )
      = sk_E )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B_1 )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) )
    | ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
     != ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_C_1 ) )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['99','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('104',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('105',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('108',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ ( k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_1 @ X0 @ sk_E @ X2 ) @ ( k4_subset_1 @ X1 @ sk_C_1 @ X0 ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_C_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['108','109'])).

thf('111',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('112',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_C_1 ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['110','111','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_C_1 ) @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_funct_2 @ ( k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['107','114'])).

thf('116',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( v1_funct_2 @ ( k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference(clc,[status(thm)],['116','117'])).

thf('119',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    v1_funct_2 @ ( k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B_1 ),
    inference(clc,[status(thm)],['118','119'])).

thf('121',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('122',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('123',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_tmap_1 @ X2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('124',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['122','123'])).

thf('125',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['124','125','126'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['127'])).

thf('129',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_funct_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) ) ),
    inference('sup-',[status(thm)],['121','128'])).

thf('130',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( v1_funct_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) ) ),
    inference(clc,[status(thm)],['130','131'])).

thf('133',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v1_funct_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) ),
    inference(clc,[status(thm)],['132','133'])).

thf('135',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('136',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ( ( k9_subset_1 @ X15 @ X13 @ X14 )
        = ( k3_xboole_0 @ X13 @ X14 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('137',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('139',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['135','136'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('141',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('145',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ sk_C_1 )
      = sk_E )
    | ( ( k7_relat_1 @ sk_E @ ( k3_xboole_0 @ sk_C_1 @ sk_C_1 ) )
     != ( k7_relat_1 @ sk_E @ ( k3_xboole_0 @ sk_C_1 @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['102','103','104','105','106','120','134','137','138','139','140','141','142','143','144'])).

thf('146',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ sk_C_1 )
      = sk_E )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ sk_C_1 )
      = sk_E ) ),
    inference(clc,[status(thm)],['146','147'])).

thf('149',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ sk_C_1 )
    = sk_E ),
    inference(clc,[status(thm)],['148','149'])).

thf('151',plain,(
    m1_subset_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf('152',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ( ( k2_partfun1 @ X32 @ X33 @ X31 @ X34 )
        = ( k7_relat_1 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('153',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ X0 )
        = ( k7_relat_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,(
    v1_funct_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) ),
    inference(clc,[status(thm)],['132','133'])).

thf('155',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ X0 )
      = ( k7_relat_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ X0 ) ) ),
    inference(demod,[status(thm)],['153','154'])).

thf('156',plain,
    ( ( k7_relat_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ sk_C_1 )
    = sk_E ),
    inference(demod,[status(thm)],['150','155'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('157',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('158',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('159',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,(
    ! [X21: $i,X22: $i,X23: $i] :
      ( ~ ( r1_xboole_0 @ X21 @ X22 )
      | ~ ( v1_relat_1 @ X23 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X23 @ X21 ) @ X22 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t207_relat_1])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('162',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) ) ),
    inference('sup+',[status(thm)],['156','161'])).

thf('163',plain,(
    m1_subset_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B_1 ) ) ),
    inference(clc,[status(thm)],['97','98'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('164',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('165',plain,(
    v1_relat_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['162','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('168',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['76','77'])).

thf('169',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ( ( k2_partfun1 @ X32 @ X33 @ X31 @ X34 )
        = ( k7_relat_1 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('178',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( k1_xboole_0
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['62','63','64','65','66','69','78','83','166','167','168','173','174','175','176','177'])).

thf('179',plain,
    ( ( k1_xboole_0
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( k1_xboole_0
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['44','179'])).

thf('181',plain,
    ( ( k1_xboole_0
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E ) ),
    inference(split,[status(esa)],['182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('185',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['159','160'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['184','185'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['186'])).

thf('189',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('191',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(split,[status(esa)],['182'])).

thf('192',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k3_xboole_0 @ sk_C_1 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['190','191'])).

thf('193',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('194',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['76','77'])).

thf('195',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['76','77'])).

thf('196',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ k1_xboole_0 )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['192','193','194','195'])).

thf('197',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['189','196'])).

thf('198',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('199',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['197','198'])).

thf('200',plain,
    ( ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_F ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['188','199'])).

thf('201',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('203',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['201','202'])).

thf('204',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['200','203'])).

thf('205',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_E ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['187','204'])).

thf('206',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('207',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('208',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['206','207'])).

thf('209',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['205','208'])).

thf('210',plain,
    ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['209'])).

thf('211',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('212',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['27','28'])).

thf('213',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('214',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['57','58'])).

thf('215',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ( v1_xboole_0 @ X37 )
      | ( v1_xboole_0 @ X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X37 ) )
      | ~ ( v1_funct_1 @ X39 )
      | ~ ( v1_funct_2 @ X39 @ X40 @ X35 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X35 ) ) )
      | ( ( k2_partfun1 @ X40 @ X35 @ X39 @ ( k9_subset_1 @ X37 @ X40 @ X36 ) )
       != ( k2_partfun1 @ X36 @ X35 @ X38 @ ( k9_subset_1 @ X37 @ X40 @ X36 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38 ) @ ( k4_subset_1 @ X37 @ X40 @ X36 ) @ X35 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X37 @ X40 @ X36 ) @ X35 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X37 @ X40 @ X36 ) @ X35 @ ( k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38 ) @ X36 )
        = X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X35 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X36 @ X35 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X37 ) )
      | ( v1_xboole_0 @ X36 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(simplify,[status(thm)],['100'])).

thf('216',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['214','215'])).

thf('217',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('219',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('220',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('221',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('222',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['76','77'])).

thf('223',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('224',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['162','165'])).

thf('225',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('226',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['76','77'])).

thf('227',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('228',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('231',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('232',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( k1_xboole_0
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['216','217','218','219','220','221','222','223','224','225','226','227','228','229','230','231'])).

thf('233',plain,
    ( ( k1_xboole_0
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['232'])).

thf('234',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( k1_xboole_0
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['213','233'])).

thf('235',plain,
    ( ( k1_xboole_0
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['234'])).

thf('236',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( k1_xboole_0
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['212','235'])).

thf('237',plain,
    ( ( k1_xboole_0
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['236'])).

thf('238',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference('sup-',[status(thm)],['211','237'])).

thf('239',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['201','202'])).

thf('240',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('241',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference(demod,[status(thm)],['238','239','240'])).

thf('242',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['241'])).

thf('243',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['182'])).

thf('244',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['242','243'])).

thf('245',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['244'])).

thf('246',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['245','246'])).

thf('248',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['247','248'])).

thf('250',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('251',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['249','250'])).

thf('252',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('253',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['251','252'])).

thf('254',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(split,[status(esa)],['182'])).

thf('255',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['210','253','254'])).

thf('256',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['183','255'])).

thf('257',plain,
    ( ( k1_xboole_0
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['181','256'])).

thf('258',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( k1_xboole_0
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['29','257'])).

thf('259',plain,
    ( ( k1_xboole_0
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['258'])).

thf('260',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['14','259'])).

thf('261',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['201','202'])).

thf('262',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('263',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['260','261','262'])).

thf('264',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['263'])).

thf('265',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('266',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['264','265'])).

thf('267',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('268',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['266','267'])).

thf('269',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('270',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(clc,[status(thm)],['268','269'])).

thf('271',plain,(
    $false ),
    inference(demod,[status(thm)],['0','270'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.aSdtBgeXPi
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:59:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.35  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.59/0.77  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.77  % Solved by: fo/fo7.sh
% 0.59/0.77  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.77  % done 613 iterations in 0.315s
% 0.59/0.77  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.77  % SZS output start Refutation
% 0.59/0.77  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.77  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.59/0.77  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.59/0.77  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.59/0.77  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.77  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.59/0.77  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.59/0.77  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.59/0.77  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.77  thf(sk_E_type, type, sk_E: $i).
% 0.59/0.77  thf(sk_D_type, type, sk_D: $i).
% 0.59/0.77  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.77  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.59/0.77  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.77  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.59/0.77  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.59/0.77  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 0.59/0.77  thf(sk_F_type, type, sk_F: $i).
% 0.59/0.77  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.77  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.59/0.77  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.77  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.59/0.77  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.59/0.77  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.77  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.59/0.77  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.59/0.77  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.59/0.77  thf(t6_tmap_1, conjecture,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.59/0.77       ( ![B:$i]:
% 0.59/0.77         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.59/0.77           ( ![C:$i]:
% 0.59/0.77             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.59/0.77                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.59/0.77               ( ![D:$i]:
% 0.59/0.77                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.59/0.77                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.59/0.77                   ( ( r1_subset_1 @ C @ D ) =>
% 0.59/0.77                     ( ![E:$i]:
% 0.59/0.77                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.59/0.77                           ( m1_subset_1 @
% 0.59/0.77                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.59/0.77                         ( ![F:$i]:
% 0.59/0.77                           ( ( ( v1_funct_1 @ F ) & 
% 0.59/0.77                               ( v1_funct_2 @ F @ D @ B ) & 
% 0.59/0.77                               ( m1_subset_1 @
% 0.59/0.77                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.59/0.77                             ( ( ( k2_partfun1 @
% 0.59/0.77                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.59/0.77                                 ( k2_partfun1 @
% 0.59/0.77                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.59/0.77                               ( ( k2_partfun1 @
% 0.59/0.77                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.59/0.77                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.59/0.77                                 ( E ) ) & 
% 0.59/0.77                               ( ( k2_partfun1 @
% 0.59/0.77                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.59/0.77                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.59/0.77                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.59/0.77  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.77    (~( ![A:$i]:
% 0.59/0.77        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.59/0.77          ( ![B:$i]:
% 0.59/0.77            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.59/0.77              ( ![C:$i]:
% 0.59/0.77                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.59/0.77                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.59/0.77                  ( ![D:$i]:
% 0.59/0.77                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.59/0.77                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.59/0.77                      ( ( r1_subset_1 @ C @ D ) =>
% 0.59/0.77                        ( ![E:$i]:
% 0.59/0.77                          ( ( ( v1_funct_1 @ E ) & 
% 0.59/0.77                              ( v1_funct_2 @ E @ C @ B ) & 
% 0.59/0.77                              ( m1_subset_1 @
% 0.59/0.77                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.59/0.77                            ( ![F:$i]:
% 0.59/0.77                              ( ( ( v1_funct_1 @ F ) & 
% 0.59/0.77                                  ( v1_funct_2 @ F @ D @ B ) & 
% 0.59/0.77                                  ( m1_subset_1 @
% 0.59/0.77                                    F @ 
% 0.59/0.77                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.59/0.77                                ( ( ( k2_partfun1 @
% 0.59/0.77                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.59/0.77                                    ( k2_partfun1 @
% 0.59/0.77                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.59/0.77                                  ( ( k2_partfun1 @
% 0.59/0.77                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.59/0.77                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.59/0.77                                    ( E ) ) & 
% 0.59/0.77                                  ( ( k2_partfun1 @
% 0.59/0.77                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.59/0.77                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.59/0.77                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.59/0.77    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 0.59/0.77  thf('0', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(d10_xboole_0, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.59/0.77  thf('1', plain,
% 0.59/0.77      (![X10 : $i, X11 : $i]: ((r1_tarski @ X10 @ X11) | ((X10) != (X11)))),
% 0.59/0.77      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.59/0.77  thf('2', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.59/0.77      inference('simplify', [status(thm)], ['1'])).
% 0.59/0.77  thf(d18_relat_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( v1_relat_1 @ B ) =>
% 0.59/0.77       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.59/0.77  thf('3', plain,
% 0.59/0.77      (![X19 : $i, X20 : $i]:
% 0.59/0.77         (~ (r1_tarski @ (k1_relat_1 @ X19) @ X20)
% 0.59/0.77          | (v4_relat_1 @ X19 @ X20)
% 0.59/0.77          | ~ (v1_relat_1 @ X19))),
% 0.59/0.77      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.59/0.77  thf('4', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['2', '3'])).
% 0.59/0.77  thf(t209_relat_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.59/0.77       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.59/0.77  thf('5', plain,
% 0.59/0.77      (![X24 : $i, X25 : $i]:
% 0.59/0.77         (((X24) = (k7_relat_1 @ X24 @ X25))
% 0.59/0.77          | ~ (v4_relat_1 @ X24 @ X25)
% 0.59/0.77          | ~ (v1_relat_1 @ X24))),
% 0.59/0.77      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.59/0.77  thf('6', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (~ (v1_relat_1 @ X0)
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | ((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['4', '5'])).
% 0.59/0.77  thf('7', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))) | ~ (v1_relat_1 @ X0))),
% 0.59/0.77      inference('simplify', [status(thm)], ['6'])).
% 0.59/0.77  thf(t3_xboole_0, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.59/0.77            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.59/0.77       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.59/0.77            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.59/0.77  thf('8', plain,
% 0.59/0.77      (![X6 : $i, X7 : $i]:
% 0.59/0.77         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.59/0.77      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.59/0.77  thf(d1_xboole_0, axiom,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.59/0.77  thf('9', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.59/0.77      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.59/0.77  thf('10', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['8', '9'])).
% 0.59/0.77  thf(t207_relat_1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( v1_relat_1 @ C ) =>
% 0.59/0.77       ( ( r1_xboole_0 @ A @ B ) =>
% 0.59/0.77         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.59/0.77  thf('11', plain,
% 0.59/0.77      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.59/0.77         (~ (r1_xboole_0 @ X21 @ X22)
% 0.59/0.77          | ~ (v1_relat_1 @ X23)
% 0.59/0.77          | ((k7_relat_1 @ (k7_relat_1 @ X23 @ X21) @ X22) = (k1_xboole_0)))),
% 0.59/0.77      inference('cnf', [status(esa)], [t207_relat_1])).
% 0.59/0.77  thf('12', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         (~ (v1_xboole_0 @ X0)
% 0.59/0.77          | ((k7_relat_1 @ (k7_relat_1 @ X2 @ X1) @ X0) = (k1_xboole_0))
% 0.59/0.77          | ~ (v1_relat_1 @ X2))),
% 0.59/0.77      inference('sup-', [status(thm)], ['10', '11'])).
% 0.59/0.77  thf('13', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (((k7_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | ~ (v1_xboole_0 @ X1))),
% 0.59/0.77      inference('sup+', [status(thm)], ['7', '12'])).
% 0.59/0.77  thf('14', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i]:
% 0.59/0.77         (~ (v1_xboole_0 @ X1)
% 0.59/0.77          | ~ (v1_relat_1 @ X0)
% 0.59/0.77          | ((k7_relat_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.59/0.77      inference('simplify', [status(thm)], ['13'])).
% 0.59/0.77  thf('15', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('16', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('17', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(dt_k1_tmap_1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.59/0.77     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.59/0.77         ( ~( v1_xboole_0 @ C ) ) & 
% 0.59/0.77         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 0.59/0.77         ( ~( v1_xboole_0 @ D ) ) & 
% 0.59/0.77         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 0.59/0.77         ( v1_funct_2 @ E @ C @ B ) & 
% 0.59/0.77         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.59/0.77         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.59/0.77         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.59/0.77       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.59/0.77         ( v1_funct_2 @
% 0.59/0.77           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.59/0.77           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.59/0.77         ( m1_subset_1 @
% 0.59/0.77           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.59/0.77           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 0.59/0.77  thf('18', plain,
% 0.59/0.77      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 0.59/0.77          | ~ (v1_funct_2 @ X42 @ X43 @ X44)
% 0.59/0.77          | ~ (v1_funct_1 @ X42)
% 0.59/0.77          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46))
% 0.59/0.77          | (v1_xboole_0 @ X45)
% 0.59/0.77          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X46))
% 0.59/0.77          | (v1_xboole_0 @ X43)
% 0.59/0.77          | (v1_xboole_0 @ X44)
% 0.59/0.77          | (v1_xboole_0 @ X46)
% 0.59/0.77          | ~ (v1_funct_1 @ X47)
% 0.59/0.77          | ~ (v1_funct_2 @ X47 @ X45 @ X44)
% 0.59/0.77          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 0.59/0.77          | (v1_funct_1 @ (k1_tmap_1 @ X46 @ X44 @ X43 @ X45 @ X42 @ X47)))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.59/0.77  thf('19', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_E @ X0))
% 0.59/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 0.59/0.77          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 0.59/0.77          | ~ (v1_funct_1 @ X0)
% 0.59/0.77          | (v1_xboole_0 @ X2)
% 0.59/0.77          | (v1_xboole_0 @ sk_B_1)
% 0.59/0.77          | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X2))
% 0.59/0.77          | (v1_xboole_0 @ X1)
% 0.59/0.77          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.59/0.77          | ~ (v1_funct_1 @ sk_E)
% 0.59/0.77          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1))),
% 0.59/0.77      inference('sup-', [status(thm)], ['17', '18'])).
% 0.59/0.77  thf('20', plain, ((v1_funct_1 @ sk_E)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('21', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('22', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_E @ X0))
% 0.59/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 0.59/0.77          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 0.59/0.77          | ~ (v1_funct_1 @ X0)
% 0.59/0.77          | (v1_xboole_0 @ X2)
% 0.59/0.77          | (v1_xboole_0 @ sk_B_1)
% 0.59/0.77          | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X2))
% 0.59/0.77          | (v1_xboole_0 @ X1)
% 0.59/0.77          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.59/0.77      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.59/0.77  thf('23', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.59/0.77          | (v1_xboole_0 @ sk_D)
% 0.59/0.77          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.59/0.77          | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77          | (v1_xboole_0 @ sk_B_1)
% 0.59/0.77          | (v1_xboole_0 @ X0)
% 0.59/0.77          | ~ (v1_funct_1 @ sk_F)
% 0.59/0.77          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 0.59/0.77          | (v1_funct_1 @ 
% 0.59/0.77             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F)))),
% 0.59/0.77      inference('sup-', [status(thm)], ['16', '22'])).
% 0.59/0.77  thf('24', plain, ((v1_funct_1 @ sk_F)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('25', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('26', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.59/0.77          | (v1_xboole_0 @ sk_D)
% 0.59/0.77          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.59/0.77          | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77          | (v1_xboole_0 @ sk_B_1)
% 0.59/0.77          | (v1_xboole_0 @ X0)
% 0.59/0.77          | (v1_funct_1 @ 
% 0.59/0.77             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F)))),
% 0.59/0.77      inference('demod', [status(thm)], ['23', '24', '25'])).
% 0.59/0.77  thf('27', plain,
% 0.59/0.77      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.59/0.77        | (v1_xboole_0 @ sk_A)
% 0.59/0.77        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.77        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.59/0.77        | (v1_xboole_0 @ sk_D))),
% 0.59/0.77      inference('sup-', [status(thm)], ['15', '26'])).
% 0.59/0.77  thf('28', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('29', plain,
% 0.59/0.77      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.59/0.77        | (v1_xboole_0 @ sk_A)
% 0.59/0.77        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.77        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77        | (v1_xboole_0 @ sk_D))),
% 0.59/0.77      inference('demod', [status(thm)], ['27', '28'])).
% 0.59/0.77  thf('30', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('31', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('32', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('33', plain,
% 0.59/0.77      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 0.59/0.77          | ~ (v1_funct_2 @ X42 @ X43 @ X44)
% 0.59/0.77          | ~ (v1_funct_1 @ X42)
% 0.59/0.77          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46))
% 0.59/0.77          | (v1_xboole_0 @ X45)
% 0.59/0.77          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X46))
% 0.59/0.77          | (v1_xboole_0 @ X43)
% 0.59/0.77          | (v1_xboole_0 @ X44)
% 0.59/0.77          | (v1_xboole_0 @ X46)
% 0.59/0.77          | ~ (v1_funct_1 @ X47)
% 0.59/0.77          | ~ (v1_funct_2 @ X47 @ X45 @ X44)
% 0.59/0.77          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 0.59/0.77          | (v1_funct_2 @ (k1_tmap_1 @ X46 @ X44 @ X43 @ X45 @ X42 @ X47) @ 
% 0.59/0.77             (k4_subset_1 @ X46 @ X43 @ X45) @ X44))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.59/0.77  thf('34', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.59/0.77           (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B_1)
% 0.59/0.77          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.59/0.77          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 0.59/0.77          | ~ (v1_funct_1 @ X2)
% 0.59/0.77          | (v1_xboole_0 @ X1)
% 0.59/0.77          | (v1_xboole_0 @ sk_B_1)
% 0.59/0.77          | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.59/0.77          | (v1_xboole_0 @ X0)
% 0.59/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.59/0.77          | ~ (v1_funct_1 @ sk_E)
% 0.59/0.77          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1))),
% 0.59/0.77      inference('sup-', [status(thm)], ['32', '33'])).
% 0.59/0.77  thf('35', plain, ((v1_funct_1 @ sk_E)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('36', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('37', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.59/0.77           (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B_1)
% 0.59/0.77          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.59/0.77          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 0.59/0.77          | ~ (v1_funct_1 @ X2)
% 0.59/0.77          | (v1_xboole_0 @ X1)
% 0.59/0.77          | (v1_xboole_0 @ sk_B_1)
% 0.59/0.77          | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.59/0.77          | (v1_xboole_0 @ X0)
% 0.59/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.59/0.77      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.59/0.77  thf('38', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.59/0.77          | (v1_xboole_0 @ sk_D)
% 0.59/0.77          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.59/0.77          | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77          | (v1_xboole_0 @ sk_B_1)
% 0.59/0.77          | (v1_xboole_0 @ X0)
% 0.59/0.77          | ~ (v1_funct_1 @ sk_F)
% 0.59/0.77          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 0.59/0.77          | (v1_funct_2 @ 
% 0.59/0.77             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.77             (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B_1))),
% 0.59/0.77      inference('sup-', [status(thm)], ['31', '37'])).
% 0.59/0.77  thf('39', plain, ((v1_funct_1 @ sk_F)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('40', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('41', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.59/0.77          | (v1_xboole_0 @ sk_D)
% 0.59/0.77          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.59/0.77          | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77          | (v1_xboole_0 @ sk_B_1)
% 0.59/0.77          | (v1_xboole_0 @ X0)
% 0.59/0.77          | (v1_funct_2 @ 
% 0.59/0.77             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.77             (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B_1))),
% 0.59/0.77      inference('demod', [status(thm)], ['38', '39', '40'])).
% 0.59/0.77  thf('42', plain,
% 0.59/0.77      (((v1_funct_2 @ 
% 0.59/0.77         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.77         (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.59/0.77        | (v1_xboole_0 @ sk_A)
% 0.59/0.77        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.77        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.59/0.77        | (v1_xboole_0 @ sk_D))),
% 0.59/0.77      inference('sup-', [status(thm)], ['30', '41'])).
% 0.59/0.77  thf('43', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('44', plain,
% 0.59/0.77      (((v1_funct_2 @ 
% 0.59/0.77         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.77         (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.59/0.77        | (v1_xboole_0 @ sk_A)
% 0.59/0.77        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.77        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77        | (v1_xboole_0 @ sk_D))),
% 0.59/0.77      inference('demod', [status(thm)], ['42', '43'])).
% 0.59/0.77  thf('45', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('46', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('47', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('48', plain,
% 0.59/0.77      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X44)))
% 0.59/0.77          | ~ (v1_funct_2 @ X42 @ X43 @ X44)
% 0.59/0.77          | ~ (v1_funct_1 @ X42)
% 0.59/0.77          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X46))
% 0.59/0.77          | (v1_xboole_0 @ X45)
% 0.59/0.77          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X46))
% 0.59/0.77          | (v1_xboole_0 @ X43)
% 0.59/0.77          | (v1_xboole_0 @ X44)
% 0.59/0.77          | (v1_xboole_0 @ X46)
% 0.59/0.77          | ~ (v1_funct_1 @ X47)
% 0.59/0.77          | ~ (v1_funct_2 @ X47 @ X45 @ X44)
% 0.59/0.77          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X44)))
% 0.59/0.77          | (m1_subset_1 @ (k1_tmap_1 @ X46 @ X44 @ X43 @ X45 @ X42 @ X47) @ 
% 0.59/0.77             (k1_zfmisc_1 @ 
% 0.59/0.77              (k2_zfmisc_1 @ (k4_subset_1 @ X46 @ X43 @ X45) @ X44))))),
% 0.59/0.77      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.59/0.77  thf('49', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.59/0.77           (k1_zfmisc_1 @ 
% 0.59/0.77            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B_1)))
% 0.59/0.77          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.59/0.77          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 0.59/0.77          | ~ (v1_funct_1 @ X2)
% 0.59/0.77          | (v1_xboole_0 @ X1)
% 0.59/0.77          | (v1_xboole_0 @ sk_B_1)
% 0.59/0.77          | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.59/0.77          | (v1_xboole_0 @ X0)
% 0.59/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.59/0.77          | ~ (v1_funct_1 @ sk_E)
% 0.59/0.77          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1))),
% 0.59/0.77      inference('sup-', [status(thm)], ['47', '48'])).
% 0.59/0.77  thf('50', plain, ((v1_funct_1 @ sk_E)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('51', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('52', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.59/0.77           (k1_zfmisc_1 @ 
% 0.59/0.77            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B_1)))
% 0.59/0.77          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.59/0.77          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 0.59/0.77          | ~ (v1_funct_1 @ X2)
% 0.59/0.77          | (v1_xboole_0 @ X1)
% 0.59/0.77          | (v1_xboole_0 @ sk_B_1)
% 0.59/0.77          | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.59/0.77          | (v1_xboole_0 @ X0)
% 0.59/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.59/0.77      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.59/0.77  thf('53', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.59/0.77          | (v1_xboole_0 @ sk_D)
% 0.59/0.77          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.59/0.77          | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77          | (v1_xboole_0 @ sk_B_1)
% 0.59/0.77          | (v1_xboole_0 @ X0)
% 0.59/0.77          | ~ (v1_funct_1 @ sk_F)
% 0.59/0.77          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 0.59/0.77          | (m1_subset_1 @ 
% 0.59/0.77             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.77             (k1_zfmisc_1 @ 
% 0.59/0.77              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B_1))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['46', '52'])).
% 0.59/0.77  thf('54', plain, ((v1_funct_1 @ sk_F)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('55', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('56', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.59/0.77          | (v1_xboole_0 @ sk_D)
% 0.59/0.77          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.59/0.77          | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77          | (v1_xboole_0 @ sk_B_1)
% 0.59/0.77          | (v1_xboole_0 @ X0)
% 0.59/0.77          | (m1_subset_1 @ 
% 0.59/0.77             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.77             (k1_zfmisc_1 @ 
% 0.59/0.77              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B_1))))),
% 0.59/0.77      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.59/0.77  thf('57', plain,
% 0.59/0.77      (((m1_subset_1 @ 
% 0.59/0.77         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.77         (k1_zfmisc_1 @ 
% 0.59/0.77          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)))
% 0.59/0.77        | (v1_xboole_0 @ sk_A)
% 0.59/0.77        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.77        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.59/0.77        | (v1_xboole_0 @ sk_D))),
% 0.59/0.77      inference('sup-', [status(thm)], ['45', '56'])).
% 0.59/0.77  thf('58', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('59', plain,
% 0.59/0.77      (((m1_subset_1 @ 
% 0.59/0.77         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.77         (k1_zfmisc_1 @ 
% 0.59/0.77          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)))
% 0.59/0.77        | (v1_xboole_0 @ sk_A)
% 0.59/0.77        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.77        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77        | (v1_xboole_0 @ sk_D))),
% 0.59/0.77      inference('demod', [status(thm)], ['57', '58'])).
% 0.59/0.77  thf(d1_tmap_1, axiom,
% 0.59/0.77    (![A:$i]:
% 0.59/0.77     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.59/0.77       ( ![B:$i]:
% 0.59/0.77         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.59/0.77           ( ![C:$i]:
% 0.59/0.77             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.59/0.77                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.59/0.77               ( ![D:$i]:
% 0.59/0.77                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.59/0.77                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.59/0.77                   ( ![E:$i]:
% 0.59/0.77                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.59/0.77                         ( m1_subset_1 @
% 0.59/0.77                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.59/0.77                       ( ![F:$i]:
% 0.59/0.77                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.59/0.77                             ( m1_subset_1 @
% 0.59/0.77                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.59/0.77                           ( ( ( k2_partfun1 @
% 0.59/0.77                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.59/0.77                               ( k2_partfun1 @
% 0.59/0.77                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 0.59/0.77                             ( ![G:$i]:
% 0.59/0.77                               ( ( ( v1_funct_1 @ G ) & 
% 0.59/0.77                                   ( v1_funct_2 @
% 0.59/0.77                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.59/0.77                                   ( m1_subset_1 @
% 0.59/0.77                                     G @ 
% 0.59/0.77                                     ( k1_zfmisc_1 @
% 0.59/0.77                                       ( k2_zfmisc_1 @
% 0.59/0.77                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 0.59/0.77                                 ( ( ( G ) =
% 0.59/0.77                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.59/0.77                                   ( ( ( k2_partfun1 @
% 0.59/0.77                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.59/0.77                                         C ) =
% 0.59/0.77                                       ( E ) ) & 
% 0.59/0.77                                     ( ( k2_partfun1 @
% 0.59/0.77                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.59/0.77                                         D ) =
% 0.59/0.77                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.59/0.77  thf('60', plain,
% 0.59/0.77      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.59/0.77         ((v1_xboole_0 @ X35)
% 0.59/0.77          | (v1_xboole_0 @ X36)
% 0.59/0.77          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 0.59/0.77          | ~ (v1_funct_1 @ X38)
% 0.59/0.77          | ~ (v1_funct_2 @ X38 @ X36 @ X35)
% 0.59/0.77          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 0.59/0.77          | ((X41) != (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38))
% 0.59/0.77          | ((k2_partfun1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35 @ X41 @ X40)
% 0.59/0.77              = (X39))
% 0.59/0.77          | ~ (m1_subset_1 @ X41 @ 
% 0.59/0.77               (k1_zfmisc_1 @ 
% 0.59/0.77                (k2_zfmisc_1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35)))
% 0.59/0.77          | ~ (v1_funct_2 @ X41 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35)
% 0.59/0.77          | ~ (v1_funct_1 @ X41)
% 0.59/0.77          | ((k2_partfun1 @ X40 @ X35 @ X39 @ (k9_subset_1 @ X37 @ X40 @ X36))
% 0.59/0.77              != (k2_partfun1 @ X36 @ X35 @ X38 @ 
% 0.59/0.77                  (k9_subset_1 @ X37 @ X40 @ X36)))
% 0.59/0.77          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X35)))
% 0.59/0.77          | ~ (v1_funct_2 @ X39 @ X40 @ X35)
% 0.59/0.77          | ~ (v1_funct_1 @ X39)
% 0.59/0.77          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X37))
% 0.59/0.77          | (v1_xboole_0 @ X40)
% 0.59/0.77          | (v1_xboole_0 @ X37))),
% 0.59/0.77      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.59/0.77  thf('61', plain,
% 0.59/0.77      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.59/0.77         ((v1_xboole_0 @ X37)
% 0.59/0.77          | (v1_xboole_0 @ X40)
% 0.59/0.77          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X37))
% 0.59/0.77          | ~ (v1_funct_1 @ X39)
% 0.59/0.77          | ~ (v1_funct_2 @ X39 @ X40 @ X35)
% 0.59/0.77          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X35)))
% 0.59/0.77          | ((k2_partfun1 @ X40 @ X35 @ X39 @ (k9_subset_1 @ X37 @ X40 @ X36))
% 0.59/0.77              != (k2_partfun1 @ X36 @ X35 @ X38 @ 
% 0.59/0.77                  (k9_subset_1 @ X37 @ X40 @ X36)))
% 0.59/0.77          | ~ (v1_funct_1 @ (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38))
% 0.59/0.77          | ~ (v1_funct_2 @ (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38) @ 
% 0.59/0.77               (k4_subset_1 @ X37 @ X40 @ X36) @ X35)
% 0.59/0.77          | ~ (m1_subset_1 @ (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38) @ 
% 0.59/0.77               (k1_zfmisc_1 @ 
% 0.59/0.77                (k2_zfmisc_1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35)))
% 0.59/0.77          | ((k2_partfun1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35 @ 
% 0.59/0.77              (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38) @ X40) = (
% 0.59/0.77              X39))
% 0.59/0.77          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 0.59/0.77          | ~ (v1_funct_2 @ X38 @ X36 @ X35)
% 0.59/0.77          | ~ (v1_funct_1 @ X38)
% 0.59/0.77          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 0.59/0.77          | (v1_xboole_0 @ X36)
% 0.59/0.77          | (v1_xboole_0 @ X35))),
% 0.59/0.77      inference('simplify', [status(thm)], ['60'])).
% 0.59/0.77  thf('62', plain,
% 0.59/0.77      (((v1_xboole_0 @ sk_D)
% 0.59/0.77        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.77        | (v1_xboole_0 @ sk_A)
% 0.59/0.77        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.77        | (v1_xboole_0 @ sk_D)
% 0.59/0.77        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.59/0.77        | ~ (v1_funct_1 @ sk_F)
% 0.59/0.77        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 0.59/0.77        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))
% 0.59/0.77        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.59/0.77            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.59/0.77            = (sk_E))
% 0.59/0.77        | ~ (v1_funct_2 @ 
% 0.59/0.77             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.77             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.59/0.77        | ~ (v1_funct_1 @ 
% 0.59/0.77             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.59/0.77        | ((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.59/0.77            (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.59/0.77            != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.59/0.77                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))
% 0.59/0.77        | ~ (m1_subset_1 @ sk_E @ 
% 0.59/0.77             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))
% 0.59/0.77        | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)
% 0.59/0.77        | ~ (v1_funct_1 @ sk_E)
% 0.59/0.77        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.59/0.77        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77        | (v1_xboole_0 @ sk_A))),
% 0.59/0.77      inference('sup-', [status(thm)], ['59', '61'])).
% 0.59/0.77  thf('63', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('64', plain, ((v1_funct_1 @ sk_F)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('65', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('66', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('67', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(redefinition_k9_subset_1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i]:
% 0.59/0.77     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.59/0.77       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.59/0.77  thf('68', plain,
% 0.59/0.77      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.59/0.77         (((k9_subset_1 @ X15 @ X13 @ X14) = (k3_xboole_0 @ X13 @ X14))
% 0.59/0.77          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.59/0.77      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.59/0.77  thf('69', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.59/0.77      inference('sup-', [status(thm)], ['67', '68'])).
% 0.59/0.77  thf('70', plain, ((r1_subset_1 @ sk_C_1 @ sk_D)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(redefinition_r1_subset_1, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.59/0.77       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 0.59/0.77  thf('71', plain,
% 0.59/0.77      (![X26 : $i, X27 : $i]:
% 0.59/0.77         ((v1_xboole_0 @ X26)
% 0.59/0.77          | (v1_xboole_0 @ X27)
% 0.59/0.77          | (r1_xboole_0 @ X26 @ X27)
% 0.59/0.77          | ~ (r1_subset_1 @ X26 @ X27))),
% 0.59/0.77      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 0.59/0.77  thf('72', plain,
% 0.59/0.77      (((r1_xboole_0 @ sk_C_1 @ sk_D)
% 0.59/0.77        | (v1_xboole_0 @ sk_D)
% 0.59/0.77        | (v1_xboole_0 @ sk_C_1))),
% 0.59/0.77      inference('sup-', [status(thm)], ['70', '71'])).
% 0.59/0.77  thf('73', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('74', plain, (((v1_xboole_0 @ sk_C_1) | (r1_xboole_0 @ sk_C_1 @ sk_D))),
% 0.59/0.77      inference('clc', [status(thm)], ['72', '73'])).
% 0.59/0.77  thf('75', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('76', plain, ((r1_xboole_0 @ sk_C_1 @ sk_D)),
% 0.59/0.77      inference('clc', [status(thm)], ['74', '75'])).
% 0.59/0.77  thf(d7_xboole_0, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.59/0.77       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.59/0.77  thf('77', plain,
% 0.59/0.77      (![X3 : $i, X4 : $i]:
% 0.59/0.77         (((k3_xboole_0 @ X3 @ X4) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X3 @ X4))),
% 0.59/0.77      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.59/0.77  thf('78', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['76', '77'])).
% 0.59/0.77  thf('79', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf(redefinition_k2_partfun1, axiom,
% 0.59/0.77    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.77     ( ( ( v1_funct_1 @ C ) & 
% 0.59/0.77         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.59/0.77       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.59/0.77  thf('80', plain,
% 0.59/0.77      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.59/0.77          | ~ (v1_funct_1 @ X31)
% 0.59/0.77          | ((k2_partfun1 @ X32 @ X33 @ X31 @ X34) = (k7_relat_1 @ X31 @ X34)))),
% 0.59/0.77      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.59/0.77  thf('81', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0)
% 0.59/0.77            = (k7_relat_1 @ sk_E @ X0))
% 0.59/0.77          | ~ (v1_funct_1 @ sk_E))),
% 0.59/0.77      inference('sup-', [status(thm)], ['79', '80'])).
% 0.59/0.77  thf('82', plain, ((v1_funct_1 @ sk_E)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('83', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0)
% 0.59/0.77           = (k7_relat_1 @ sk_E @ X0))),
% 0.59/0.77      inference('demod', [status(thm)], ['81', '82'])).
% 0.59/0.77  thf('84', plain, (![X11 : $i]: (r1_tarski @ X11 @ X11)),
% 0.59/0.77      inference('simplify', [status(thm)], ['1'])).
% 0.59/0.77  thf(t3_subset, axiom,
% 0.59/0.77    (![A:$i,B:$i]:
% 0.59/0.77     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.59/0.77  thf('85', plain,
% 0.59/0.77      (![X16 : $i, X18 : $i]:
% 0.59/0.77         ((m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X18)) | ~ (r1_tarski @ X16 @ X18))),
% 0.59/0.77      inference('cnf', [status(esa)], [t3_subset])).
% 0.59/0.77  thf('86', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['84', '85'])).
% 0.59/0.77  thf('87', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('88', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.59/0.77           (k1_zfmisc_1 @ 
% 0.59/0.77            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B_1)))
% 0.59/0.77          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.59/0.77          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 0.59/0.77          | ~ (v1_funct_1 @ X2)
% 0.59/0.77          | (v1_xboole_0 @ X1)
% 0.59/0.77          | (v1_xboole_0 @ sk_B_1)
% 0.59/0.77          | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.59/0.77          | (v1_xboole_0 @ X0)
% 0.59/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.59/0.77      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.59/0.77  thf('89', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.59/0.77          | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.59/0.77          | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77          | (v1_xboole_0 @ sk_B_1)
% 0.59/0.77          | (v1_xboole_0 @ X0)
% 0.59/0.77          | ~ (v1_funct_1 @ sk_E)
% 0.59/0.77          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)
% 0.59/0.77          | (m1_subset_1 @ 
% 0.59/0.77             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.59/0.77             (k1_zfmisc_1 @ 
% 0.59/0.77              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C_1 @ sk_C_1) @ sk_B_1))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['87', '88'])).
% 0.59/0.77  thf('90', plain, ((v1_funct_1 @ sk_E)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('91', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('92', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.59/0.77          | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.59/0.77          | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77          | (v1_xboole_0 @ sk_B_1)
% 0.59/0.77          | (v1_xboole_0 @ X0)
% 0.59/0.77          | (m1_subset_1 @ 
% 0.59/0.77             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.59/0.77             (k1_zfmisc_1 @ 
% 0.59/0.77              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C_1 @ sk_C_1) @ sk_B_1))))),
% 0.59/0.77      inference('demod', [status(thm)], ['89', '90', '91'])).
% 0.59/0.77  thf('93', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((m1_subset_1 @ 
% 0.59/0.77           (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.59/0.77           (k1_zfmisc_1 @ 
% 0.59/0.77            (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C_1 @ sk_C_1) @ sk_B_1)))
% 0.59/0.77          | (v1_xboole_0 @ X0)
% 0.59/0.77          | (v1_xboole_0 @ sk_B_1)
% 0.59/0.77          | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0)))),
% 0.59/0.77      inference('simplify', [status(thm)], ['92'])).
% 0.59/0.77  thf('94', plain,
% 0.59/0.77      (((v1_xboole_0 @ sk_C_1)
% 0.59/0.77        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.77        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77        | (m1_subset_1 @ 
% 0.59/0.77           (k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.59/0.77           (k1_zfmisc_1 @ 
% 0.59/0.77            (k2_zfmisc_1 @ (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B_1))))),
% 0.59/0.77      inference('sup-', [status(thm)], ['86', '93'])).
% 0.59/0.77  thf('95', plain,
% 0.59/0.77      (((m1_subset_1 @ 
% 0.59/0.77         (k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.59/0.77         (k1_zfmisc_1 @ 
% 0.59/0.77          (k2_zfmisc_1 @ (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B_1)))
% 0.59/0.77        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.77        | (v1_xboole_0 @ sk_C_1))),
% 0.59/0.77      inference('simplify', [status(thm)], ['94'])).
% 0.59/0.77  thf('96', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('97', plain,
% 0.59/0.77      (((v1_xboole_0 @ sk_C_1)
% 0.59/0.77        | (m1_subset_1 @ 
% 0.59/0.77           (k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.59/0.77           (k1_zfmisc_1 @ 
% 0.59/0.77            (k2_zfmisc_1 @ (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B_1))))),
% 0.59/0.77      inference('clc', [status(thm)], ['95', '96'])).
% 0.59/0.77  thf('98', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('99', plain,
% 0.59/0.77      ((m1_subset_1 @ 
% 0.59/0.77        (k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.59/0.77        (k1_zfmisc_1 @ 
% 0.59/0.77         (k2_zfmisc_1 @ (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B_1)))),
% 0.59/0.77      inference('clc', [status(thm)], ['97', '98'])).
% 0.59/0.77  thf('100', plain,
% 0.59/0.77      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.59/0.77         ((v1_xboole_0 @ X35)
% 0.59/0.77          | (v1_xboole_0 @ X36)
% 0.59/0.77          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 0.59/0.77          | ~ (v1_funct_1 @ X38)
% 0.59/0.77          | ~ (v1_funct_2 @ X38 @ X36 @ X35)
% 0.59/0.77          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 0.59/0.77          | ((X41) != (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38))
% 0.59/0.77          | ((k2_partfun1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35 @ X41 @ X36)
% 0.59/0.77              = (X38))
% 0.59/0.77          | ~ (m1_subset_1 @ X41 @ 
% 0.59/0.77               (k1_zfmisc_1 @ 
% 0.59/0.77                (k2_zfmisc_1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35)))
% 0.59/0.77          | ~ (v1_funct_2 @ X41 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35)
% 0.59/0.77          | ~ (v1_funct_1 @ X41)
% 0.59/0.77          | ((k2_partfun1 @ X40 @ X35 @ X39 @ (k9_subset_1 @ X37 @ X40 @ X36))
% 0.59/0.77              != (k2_partfun1 @ X36 @ X35 @ X38 @ 
% 0.59/0.77                  (k9_subset_1 @ X37 @ X40 @ X36)))
% 0.59/0.77          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X35)))
% 0.59/0.77          | ~ (v1_funct_2 @ X39 @ X40 @ X35)
% 0.59/0.77          | ~ (v1_funct_1 @ X39)
% 0.59/0.77          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X37))
% 0.59/0.77          | (v1_xboole_0 @ X40)
% 0.59/0.77          | (v1_xboole_0 @ X37))),
% 0.59/0.77      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.59/0.77  thf('101', plain,
% 0.59/0.77      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.59/0.77         ((v1_xboole_0 @ X37)
% 0.59/0.77          | (v1_xboole_0 @ X40)
% 0.59/0.77          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X37))
% 0.59/0.77          | ~ (v1_funct_1 @ X39)
% 0.59/0.77          | ~ (v1_funct_2 @ X39 @ X40 @ X35)
% 0.59/0.77          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X35)))
% 0.59/0.77          | ((k2_partfun1 @ X40 @ X35 @ X39 @ (k9_subset_1 @ X37 @ X40 @ X36))
% 0.59/0.77              != (k2_partfun1 @ X36 @ X35 @ X38 @ 
% 0.59/0.77                  (k9_subset_1 @ X37 @ X40 @ X36)))
% 0.59/0.77          | ~ (v1_funct_1 @ (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38))
% 0.59/0.77          | ~ (v1_funct_2 @ (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38) @ 
% 0.59/0.77               (k4_subset_1 @ X37 @ X40 @ X36) @ X35)
% 0.59/0.77          | ~ (m1_subset_1 @ (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38) @ 
% 0.59/0.77               (k1_zfmisc_1 @ 
% 0.59/0.77                (k2_zfmisc_1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35)))
% 0.59/0.77          | ((k2_partfun1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35 @ 
% 0.59/0.77              (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38) @ X36) = (
% 0.59/0.77              X38))
% 0.59/0.77          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 0.59/0.77          | ~ (v1_funct_2 @ X38 @ X36 @ X35)
% 0.59/0.77          | ~ (v1_funct_1 @ X38)
% 0.59/0.77          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 0.59/0.77          | (v1_xboole_0 @ X36)
% 0.59/0.77          | (v1_xboole_0 @ X35))),
% 0.59/0.77      inference('simplify', [status(thm)], ['100'])).
% 0.59/0.77  thf('102', plain,
% 0.59/0.77      (((v1_xboole_0 @ sk_B_1)
% 0.59/0.77        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_C_1))
% 0.59/0.77        | ~ (v1_funct_1 @ sk_E)
% 0.59/0.77        | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)
% 0.59/0.77        | ~ (m1_subset_1 @ sk_E @ 
% 0.59/0.77             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))
% 0.59/0.77        | ((k2_partfun1 @ (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B_1 @ 
% 0.59/0.77            (k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.59/0.77            sk_C_1) = (sk_E))
% 0.59/0.77        | ~ (v1_funct_2 @ 
% 0.59/0.77             (k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.59/0.77             (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B_1)
% 0.59/0.77        | ~ (v1_funct_1 @ 
% 0.59/0.77             (k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E))
% 0.59/0.77        | ((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.59/0.77            (k9_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 0.59/0.77            != (k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.59/0.77                (k9_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))
% 0.59/0.77        | ~ (m1_subset_1 @ sk_E @ 
% 0.59/0.77             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))
% 0.59/0.77        | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)
% 0.59/0.77        | ~ (v1_funct_1 @ sk_E)
% 0.59/0.77        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_C_1))
% 0.59/0.77        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77        | (v1_xboole_0 @ sk_C_1))),
% 0.59/0.77      inference('sup-', [status(thm)], ['99', '101'])).
% 0.59/0.77  thf('103', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['84', '85'])).
% 0.59/0.77  thf('104', plain, ((v1_funct_1 @ sk_E)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('105', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('106', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('107', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.59/0.77      inference('sup-', [status(thm)], ['84', '85'])).
% 0.59/0.77  thf('108', plain,
% 0.59/0.77      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('109', plain,
% 0.59/0.77      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.77         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.59/0.77           (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B_1)
% 0.59/0.77          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.59/0.77          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 0.59/0.77          | ~ (v1_funct_1 @ X2)
% 0.59/0.77          | (v1_xboole_0 @ X1)
% 0.59/0.77          | (v1_xboole_0 @ sk_B_1)
% 0.59/0.77          | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.59/0.77          | (v1_xboole_0 @ X0)
% 0.59/0.77          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.59/0.77      inference('demod', [status(thm)], ['34', '35', '36'])).
% 0.59/0.77  thf('110', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.59/0.77          | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.59/0.77          | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77          | (v1_xboole_0 @ sk_B_1)
% 0.59/0.77          | (v1_xboole_0 @ X0)
% 0.59/0.77          | ~ (v1_funct_1 @ sk_E)
% 0.59/0.77          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)
% 0.59/0.77          | (v1_funct_2 @ 
% 0.59/0.77             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.59/0.77             (k4_subset_1 @ X0 @ sk_C_1 @ sk_C_1) @ sk_B_1))),
% 0.59/0.77      inference('sup-', [status(thm)], ['108', '109'])).
% 0.59/0.77  thf('111', plain, ((v1_funct_1 @ sk_E)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('112', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('113', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         (~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.59/0.77          | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.59/0.77          | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77          | (v1_xboole_0 @ sk_B_1)
% 0.59/0.77          | (v1_xboole_0 @ X0)
% 0.59/0.77          | (v1_funct_2 @ 
% 0.59/0.77             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.59/0.77             (k4_subset_1 @ X0 @ sk_C_1 @ sk_C_1) @ sk_B_1))),
% 0.59/0.77      inference('demod', [status(thm)], ['110', '111', '112'])).
% 0.59/0.77  thf('114', plain,
% 0.59/0.77      (![X0 : $i]:
% 0.59/0.77         ((v1_funct_2 @ 
% 0.59/0.77           (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.59/0.77           (k4_subset_1 @ X0 @ sk_C_1 @ sk_C_1) @ sk_B_1)
% 0.59/0.77          | (v1_xboole_0 @ X0)
% 0.59/0.77          | (v1_xboole_0 @ sk_B_1)
% 0.59/0.77          | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0)))),
% 0.59/0.77      inference('simplify', [status(thm)], ['113'])).
% 0.59/0.77  thf('115', plain,
% 0.59/0.77      (((v1_xboole_0 @ sk_C_1)
% 0.59/0.77        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.77        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.77        | (v1_funct_2 @ 
% 0.59/0.77           (k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.59/0.77           (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B_1))),
% 0.59/0.77      inference('sup-', [status(thm)], ['107', '114'])).
% 0.59/0.77  thf('116', plain,
% 0.59/0.77      (((v1_funct_2 @ 
% 0.59/0.77         (k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.59/0.77         (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B_1)
% 0.59/0.77        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.77        | (v1_xboole_0 @ sk_C_1))),
% 0.59/0.77      inference('simplify', [status(thm)], ['115'])).
% 0.59/0.77  thf('117', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('118', plain,
% 0.59/0.77      (((v1_xboole_0 @ sk_C_1)
% 0.59/0.77        | (v1_funct_2 @ 
% 0.59/0.77           (k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.59/0.77           (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B_1))),
% 0.59/0.77      inference('clc', [status(thm)], ['116', '117'])).
% 0.59/0.77  thf('119', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.59/0.77      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.77  thf('120', plain,
% 0.59/0.77      ((v1_funct_2 @ 
% 0.59/0.77        (k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.59/0.77        (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B_1)),
% 0.59/0.77      inference('clc', [status(thm)], ['118', '119'])).
% 0.59/0.77  thf('121', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['84', '85'])).
% 0.59/0.78  thf('122', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('123', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.78         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_E @ X0))
% 0.59/0.78          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 0.59/0.78          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 0.59/0.78          | ~ (v1_funct_1 @ X0)
% 0.59/0.78          | (v1_xboole_0 @ X2)
% 0.59/0.78          | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78          | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X2))
% 0.59/0.78          | (v1_xboole_0 @ X1)
% 0.59/0.78          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.59/0.78      inference('demod', [status(thm)], ['19', '20', '21'])).
% 0.59/0.78  thf('124', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.59/0.78          | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.59/0.78          | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78          | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78          | (v1_xboole_0 @ X0)
% 0.59/0.78          | ~ (v1_funct_1 @ sk_E)
% 0.59/0.78          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)
% 0.59/0.78          | (v1_funct_1 @ 
% 0.59/0.78             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['122', '123'])).
% 0.59/0.78  thf('125', plain, ((v1_funct_1 @ sk_E)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('126', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('127', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.59/0.78          | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.59/0.78          | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78          | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78          | (v1_xboole_0 @ X0)
% 0.59/0.78          | (v1_funct_1 @ 
% 0.59/0.78             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E)))),
% 0.59/0.78      inference('demod', [status(thm)], ['124', '125', '126'])).
% 0.59/0.78  thf('128', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((v1_funct_1 @ 
% 0.59/0.78           (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E))
% 0.59/0.78          | (v1_xboole_0 @ X0)
% 0.59/0.78          | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78          | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0)))),
% 0.59/0.78      inference('simplify', [status(thm)], ['127'])).
% 0.59/0.78  thf('129', plain,
% 0.59/0.78      (((v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_funct_1 @ 
% 0.59/0.78           (k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['121', '128'])).
% 0.59/0.78  thf('130', plain,
% 0.59/0.78      (((v1_funct_1 @ 
% 0.59/0.78         (k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E))
% 0.59/0.78        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1))),
% 0.59/0.78      inference('simplify', [status(thm)], ['129'])).
% 0.59/0.78  thf('131', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('132', plain,
% 0.59/0.78      (((v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_funct_1 @ 
% 0.59/0.78           (k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E)))),
% 0.59/0.78      inference('clc', [status(thm)], ['130', '131'])).
% 0.59/0.78  thf('133', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('134', plain,
% 0.59/0.78      ((v1_funct_1 @ 
% 0.59/0.78        (k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E))),
% 0.59/0.78      inference('clc', [status(thm)], ['132', '133'])).
% 0.59/0.78  thf('135', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['84', '85'])).
% 0.59/0.78  thf('136', plain,
% 0.59/0.78      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.59/0.78         (((k9_subset_1 @ X15 @ X13 @ X14) = (k3_xboole_0 @ X13 @ X14))
% 0.59/0.78          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.59/0.78      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.59/0.78  thf('137', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['135', '136'])).
% 0.59/0.78  thf('138', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0)
% 0.59/0.78           = (k7_relat_1 @ sk_E @ X0))),
% 0.59/0.78      inference('demod', [status(thm)], ['81', '82'])).
% 0.59/0.78  thf('139', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['135', '136'])).
% 0.59/0.78  thf('140', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0)
% 0.59/0.78           = (k7_relat_1 @ sk_E @ X0))),
% 0.59/0.78      inference('demod', [status(thm)], ['81', '82'])).
% 0.59/0.78  thf('141', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('142', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('143', plain, ((v1_funct_1 @ sk_E)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('144', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['84', '85'])).
% 0.59/0.78  thf('145', plain,
% 0.59/0.78      (((v1_xboole_0 @ sk_B_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | ((k2_partfun1 @ (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B_1 @ 
% 0.59/0.78            (k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.59/0.78            sk_C_1) = (sk_E))
% 0.59/0.78        | ((k7_relat_1 @ sk_E @ (k3_xboole_0 @ sk_C_1 @ sk_C_1))
% 0.59/0.78            != (k7_relat_1 @ sk_E @ (k3_xboole_0 @ sk_C_1 @ sk_C_1)))
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1))),
% 0.59/0.78      inference('demod', [status(thm)],
% 0.59/0.78                ['102', '103', '104', '105', '106', '120', '134', '137', 
% 0.59/0.78                 '138', '139', '140', '141', '142', '143', '144'])).
% 0.59/0.78  thf('146', plain,
% 0.59/0.78      ((((k2_partfun1 @ (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B_1 @ 
% 0.59/0.78          (k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.59/0.78          sk_C_1) = (sk_E))
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_B_1))),
% 0.59/0.78      inference('simplify', [status(thm)], ['145'])).
% 0.59/0.78  thf('147', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('148', plain,
% 0.59/0.78      (((v1_xboole_0 @ sk_B_1)
% 0.59/0.78        | ((k2_partfun1 @ (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B_1 @ 
% 0.59/0.78            (k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.59/0.78            sk_C_1) = (sk_E)))),
% 0.59/0.78      inference('clc', [status(thm)], ['146', '147'])).
% 0.59/0.78  thf('149', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('150', plain,
% 0.59/0.78      (((k2_partfun1 @ (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B_1 @ 
% 0.59/0.78         (k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ sk_C_1)
% 0.59/0.78         = (sk_E))),
% 0.59/0.78      inference('clc', [status(thm)], ['148', '149'])).
% 0.59/0.78  thf('151', plain,
% 0.59/0.78      ((m1_subset_1 @ 
% 0.59/0.78        (k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.59/0.78        (k1_zfmisc_1 @ 
% 0.59/0.78         (k2_zfmisc_1 @ (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B_1)))),
% 0.59/0.78      inference('clc', [status(thm)], ['97', '98'])).
% 0.59/0.78  thf('152', plain,
% 0.59/0.78      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.59/0.78         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.59/0.78          | ~ (v1_funct_1 @ X31)
% 0.59/0.78          | ((k2_partfun1 @ X32 @ X33 @ X31 @ X34) = (k7_relat_1 @ X31 @ X34)))),
% 0.59/0.78      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.59/0.78  thf('153', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (((k2_partfun1 @ (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B_1 @ 
% 0.59/0.78            (k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ X0)
% 0.59/0.78            = (k7_relat_1 @ 
% 0.59/0.78               (k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.59/0.78               X0))
% 0.59/0.78          | ~ (v1_funct_1 @ 
% 0.59/0.78               (k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['151', '152'])).
% 0.59/0.78  thf('154', plain,
% 0.59/0.78      ((v1_funct_1 @ 
% 0.59/0.78        (k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E))),
% 0.59/0.78      inference('clc', [status(thm)], ['132', '133'])).
% 0.59/0.78  thf('155', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((k2_partfun1 @ (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B_1 @ 
% 0.59/0.78           (k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ X0)
% 0.59/0.78           = (k7_relat_1 @ 
% 0.59/0.78              (k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.59/0.78              X0))),
% 0.59/0.78      inference('demod', [status(thm)], ['153', '154'])).
% 0.59/0.78  thf('156', plain,
% 0.59/0.78      (((k7_relat_1 @ 
% 0.59/0.78         (k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ sk_C_1)
% 0.59/0.78         = (sk_E))),
% 0.59/0.78      inference('demod', [status(thm)], ['150', '155'])).
% 0.59/0.78  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.59/0.78  thf('157', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.78      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.59/0.78  thf('158', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['8', '9'])).
% 0.59/0.78  thf('159', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.59/0.78      inference('sup-', [status(thm)], ['157', '158'])).
% 0.59/0.78  thf('160', plain,
% 0.59/0.78      (![X21 : $i, X22 : $i, X23 : $i]:
% 0.59/0.78         (~ (r1_xboole_0 @ X21 @ X22)
% 0.59/0.78          | ~ (v1_relat_1 @ X23)
% 0.59/0.78          | ((k7_relat_1 @ (k7_relat_1 @ X23 @ X21) @ X22) = (k1_xboole_0)))),
% 0.59/0.78      inference('cnf', [status(esa)], [t207_relat_1])).
% 0.59/0.78  thf('161', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 0.59/0.78          | ~ (v1_relat_1 @ X1))),
% 0.59/0.78      inference('sup-', [status(thm)], ['159', '160'])).
% 0.59/0.78  thf('162', plain,
% 0.59/0.78      ((((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))
% 0.59/0.78        | ~ (v1_relat_1 @ 
% 0.59/0.78             (k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E)))),
% 0.59/0.78      inference('sup+', [status(thm)], ['156', '161'])).
% 0.59/0.78  thf('163', plain,
% 0.59/0.78      ((m1_subset_1 @ 
% 0.59/0.78        (k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.59/0.78        (k1_zfmisc_1 @ 
% 0.59/0.78         (k2_zfmisc_1 @ (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B_1)))),
% 0.59/0.78      inference('clc', [status(thm)], ['97', '98'])).
% 0.59/0.78  thf(cc1_relset_1, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i]:
% 0.59/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.78       ( v1_relat_1 @ C ) ))).
% 0.59/0.78  thf('164', plain,
% 0.59/0.78      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.59/0.78         ((v1_relat_1 @ X28)
% 0.59/0.78          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.59/0.78      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.59/0.78  thf('165', plain,
% 0.59/0.78      ((v1_relat_1 @ 
% 0.59/0.78        (k1_tmap_1 @ sk_C_1 @ sk_B_1 @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E))),
% 0.59/0.78      inference('sup-', [status(thm)], ['163', '164'])).
% 0.59/0.78  thf('166', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.78      inference('demod', [status(thm)], ['162', '165'])).
% 0.59/0.78  thf('167', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.59/0.78      inference('sup-', [status(thm)], ['67', '68'])).
% 0.59/0.78  thf('168', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['76', '77'])).
% 0.59/0.78  thf('169', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('170', plain,
% 0.59/0.78      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.59/0.78         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.59/0.78          | ~ (v1_funct_1 @ X31)
% 0.59/0.78          | ((k2_partfun1 @ X32 @ X33 @ X31 @ X34) = (k7_relat_1 @ X31 @ X34)))),
% 0.59/0.78      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.59/0.78  thf('171', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 0.59/0.78          | ~ (v1_funct_1 @ sk_F))),
% 0.59/0.78      inference('sup-', [status(thm)], ['169', '170'])).
% 0.59/0.78  thf('172', plain, ((v1_funct_1 @ sk_F)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('173', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.59/0.78      inference('demod', [status(thm)], ['171', '172'])).
% 0.59/0.78  thf('174', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('175', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('176', plain, ((v1_funct_1 @ sk_E)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('177', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('178', plain,
% 0.59/0.78      (((v1_xboole_0 @ sk_D)
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_A)
% 0.59/0.78        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_D)
% 0.59/0.78        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.59/0.78            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.59/0.78            = (sk_E))
% 0.59/0.78        | ~ (v1_funct_2 @ 
% 0.59/0.78             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.78             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.59/0.78        | ~ (v1_funct_1 @ 
% 0.59/0.78             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.59/0.78        | ((k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_A))),
% 0.59/0.78      inference('demod', [status(thm)],
% 0.59/0.78                ['62', '63', '64', '65', '66', '69', '78', '83', '166', '167', 
% 0.59/0.78                 '168', '173', '174', '175', '176', '177'])).
% 0.59/0.78  thf('179', plain,
% 0.59/0.78      ((((k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.59/0.78        | ~ (v1_funct_1 @ 
% 0.59/0.78             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.59/0.78        | ~ (v1_funct_2 @ 
% 0.59/0.78             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.78             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.59/0.78        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.59/0.78            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.59/0.78            = (sk_E))
% 0.59/0.78        | (v1_xboole_0 @ sk_A)
% 0.59/0.78        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_D))),
% 0.59/0.78      inference('simplify', [status(thm)], ['178'])).
% 0.59/0.78  thf('180', plain,
% 0.59/0.78      (((v1_xboole_0 @ sk_D)
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_A)
% 0.59/0.78        | (v1_xboole_0 @ sk_D)
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_A)
% 0.59/0.78        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.59/0.78            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.59/0.78            = (sk_E))
% 0.59/0.78        | ~ (v1_funct_1 @ 
% 0.59/0.78             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.59/0.78        | ((k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['44', '179'])).
% 0.59/0.78  thf('181', plain,
% 0.59/0.78      ((((k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.59/0.78        | ~ (v1_funct_1 @ 
% 0.59/0.78             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.59/0.78        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.59/0.78            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.59/0.78            = (sk_E))
% 0.59/0.78        | (v1_xboole_0 @ sk_A)
% 0.59/0.78        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_D))),
% 0.59/0.78      inference('simplify', [status(thm)], ['180'])).
% 0.59/0.78  thf('182', plain,
% 0.59/0.78      ((((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.59/0.78          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.59/0.78          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.59/0.78              (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))
% 0.59/0.78        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.59/0.78            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.59/0.78            != (sk_E))
% 0.59/0.78        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.59/0.78            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.59/0.78            != (sk_F)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('183', plain,
% 0.59/0.78      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.59/0.78          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.59/0.78          != (sk_E)))
% 0.59/0.78         <= (~
% 0.59/0.78             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.59/0.78                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.78                sk_C_1) = (sk_E))))),
% 0.59/0.78      inference('split', [status(esa)], ['182'])).
% 0.59/0.78  thf('184', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))) | ~ (v1_relat_1 @ X0))),
% 0.59/0.78      inference('simplify', [status(thm)], ['6'])).
% 0.59/0.78  thf('185', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 0.59/0.78          | ~ (v1_relat_1 @ X1))),
% 0.59/0.78      inference('sup-', [status(thm)], ['159', '160'])).
% 0.59/0.78  thf('186', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.59/0.78          | ~ (v1_relat_1 @ X0)
% 0.59/0.78          | ~ (v1_relat_1 @ X0))),
% 0.59/0.78      inference('sup+', [status(thm)], ['184', '185'])).
% 0.59/0.78  thf('187', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (v1_relat_1 @ X0)
% 0.59/0.78          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.59/0.78      inference('simplify', [status(thm)], ['186'])).
% 0.59/0.78  thf('188', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (~ (v1_relat_1 @ X0)
% 0.59/0.78          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.59/0.78      inference('simplify', [status(thm)], ['186'])).
% 0.59/0.78  thf('189', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.59/0.78      inference('demod', [status(thm)], ['171', '172'])).
% 0.59/0.78  thf('190', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.59/0.78      inference('sup-', [status(thm)], ['67', '68'])).
% 0.59/0.78  thf('191', plain,
% 0.59/0.78      ((((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.59/0.78          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.59/0.78          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.59/0.78              (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))))
% 0.59/0.78         <= (~
% 0.59/0.78             (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.59/0.78                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.59/0.78                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.59/0.78                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.59/0.78      inference('split', [status(esa)], ['182'])).
% 0.59/0.78  thf('192', plain,
% 0.59/0.78      ((((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.59/0.78          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.59/0.78          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.59/0.78              (k3_xboole_0 @ sk_C_1 @ sk_D))))
% 0.59/0.78         <= (~
% 0.59/0.78             (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.59/0.78                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.59/0.78                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.59/0.78                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['190', '191'])).
% 0.59/0.78  thf('193', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.59/0.78      inference('sup-', [status(thm)], ['67', '68'])).
% 0.59/0.78  thf('194', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['76', '77'])).
% 0.59/0.78  thf('195', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['76', '77'])).
% 0.59/0.78  thf('196', plain,
% 0.59/0.78      ((((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ k1_xboole_0)
% 0.59/0.78          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ k1_xboole_0)))
% 0.59/0.78         <= (~
% 0.59/0.78             (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.59/0.78                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.59/0.78                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.59/0.78                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.59/0.78      inference('demod', [status(thm)], ['192', '193', '194', '195'])).
% 0.59/0.78  thf('197', plain,
% 0.59/0.78      ((((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ k1_xboole_0)
% 0.59/0.78          != (k7_relat_1 @ sk_F @ k1_xboole_0)))
% 0.59/0.78         <= (~
% 0.59/0.78             (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.59/0.78                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.59/0.78                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.59/0.78                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['189', '196'])).
% 0.59/0.78  thf('198', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0)
% 0.59/0.78           = (k7_relat_1 @ sk_E @ X0))),
% 0.59/0.78      inference('demod', [status(thm)], ['81', '82'])).
% 0.59/0.78  thf('199', plain,
% 0.59/0.78      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0)))
% 0.59/0.78         <= (~
% 0.59/0.78             (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.59/0.78                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.59/0.78                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.59/0.78                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.59/0.78      inference('demod', [status(thm)], ['197', '198'])).
% 0.59/0.78  thf('200', plain,
% 0.59/0.78      (((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.59/0.78         | ~ (v1_relat_1 @ sk_F)))
% 0.59/0.78         <= (~
% 0.59/0.78             (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.59/0.78                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.59/0.78                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.59/0.78                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['188', '199'])).
% 0.59/0.78  thf('201', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('202', plain,
% 0.59/0.78      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.59/0.78         ((v1_relat_1 @ X28)
% 0.59/0.78          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.59/0.78      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.59/0.78  thf('203', plain, ((v1_relat_1 @ sk_F)),
% 0.59/0.78      inference('sup-', [status(thm)], ['201', '202'])).
% 0.59/0.78  thf('204', plain,
% 0.59/0.78      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0)))
% 0.59/0.78         <= (~
% 0.59/0.78             (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.59/0.78                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.59/0.78                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.59/0.78                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.59/0.78      inference('demod', [status(thm)], ['200', '203'])).
% 0.59/0.78  thf('205', plain,
% 0.59/0.78      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_E)))
% 0.59/0.78         <= (~
% 0.59/0.78             (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.59/0.78                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.59/0.78                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.59/0.78                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['187', '204'])).
% 0.59/0.78  thf('206', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('207', plain,
% 0.59/0.78      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.59/0.78         ((v1_relat_1 @ X28)
% 0.59/0.78          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.59/0.78      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.59/0.78  thf('208', plain, ((v1_relat_1 @ sk_E)),
% 0.59/0.78      inference('sup-', [status(thm)], ['206', '207'])).
% 0.59/0.78  thf('209', plain,
% 0.59/0.78      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.59/0.78         <= (~
% 0.59/0.78             (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.59/0.78                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.59/0.78                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.59/0.78                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.59/0.78      inference('demod', [status(thm)], ['205', '208'])).
% 0.59/0.78  thf('210', plain,
% 0.59/0.78      ((((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.59/0.78          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.59/0.78          = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.59/0.78             (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))))),
% 0.59/0.78      inference('simplify', [status(thm)], ['209'])).
% 0.59/0.78  thf('211', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         (~ (v1_xboole_0 @ X1)
% 0.59/0.78          | ~ (v1_relat_1 @ X0)
% 0.59/0.78          | ((k7_relat_1 @ X0 @ X1) = (k1_xboole_0)))),
% 0.59/0.78      inference('simplify', [status(thm)], ['13'])).
% 0.59/0.78  thf('212', plain,
% 0.59/0.78      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.59/0.78        | (v1_xboole_0 @ sk_A)
% 0.59/0.78        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_D))),
% 0.59/0.78      inference('demod', [status(thm)], ['27', '28'])).
% 0.59/0.78  thf('213', plain,
% 0.59/0.78      (((v1_funct_2 @ 
% 0.59/0.78         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.78         (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_A)
% 0.59/0.78        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_D))),
% 0.59/0.78      inference('demod', [status(thm)], ['42', '43'])).
% 0.59/0.78  thf('214', plain,
% 0.59/0.78      (((m1_subset_1 @ 
% 0.59/0.78         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.78         (k1_zfmisc_1 @ 
% 0.59/0.78          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)))
% 0.59/0.78        | (v1_xboole_0 @ sk_A)
% 0.59/0.78        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_D))),
% 0.59/0.78      inference('demod', [status(thm)], ['57', '58'])).
% 0.59/0.78  thf('215', plain,
% 0.59/0.78      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.59/0.78         ((v1_xboole_0 @ X37)
% 0.59/0.78          | (v1_xboole_0 @ X40)
% 0.59/0.78          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ X37))
% 0.59/0.78          | ~ (v1_funct_1 @ X39)
% 0.59/0.78          | ~ (v1_funct_2 @ X39 @ X40 @ X35)
% 0.59/0.78          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X35)))
% 0.59/0.78          | ((k2_partfun1 @ X40 @ X35 @ X39 @ (k9_subset_1 @ X37 @ X40 @ X36))
% 0.59/0.78              != (k2_partfun1 @ X36 @ X35 @ X38 @ 
% 0.59/0.78                  (k9_subset_1 @ X37 @ X40 @ X36)))
% 0.59/0.78          | ~ (v1_funct_1 @ (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38))
% 0.59/0.78          | ~ (v1_funct_2 @ (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38) @ 
% 0.59/0.78               (k4_subset_1 @ X37 @ X40 @ X36) @ X35)
% 0.59/0.78          | ~ (m1_subset_1 @ (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38) @ 
% 0.59/0.78               (k1_zfmisc_1 @ 
% 0.59/0.78                (k2_zfmisc_1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35)))
% 0.59/0.78          | ((k2_partfun1 @ (k4_subset_1 @ X37 @ X40 @ X36) @ X35 @ 
% 0.59/0.78              (k1_tmap_1 @ X37 @ X35 @ X40 @ X36 @ X39 @ X38) @ X36) = (
% 0.59/0.78              X38))
% 0.59/0.78          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X35)))
% 0.59/0.78          | ~ (v1_funct_2 @ X38 @ X36 @ X35)
% 0.59/0.78          | ~ (v1_funct_1 @ X38)
% 0.59/0.78          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X37))
% 0.59/0.78          | (v1_xboole_0 @ X36)
% 0.59/0.78          | (v1_xboole_0 @ X35))),
% 0.59/0.78      inference('simplify', [status(thm)], ['100'])).
% 0.59/0.78  thf('216', plain,
% 0.59/0.78      (((v1_xboole_0 @ sk_D)
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_A)
% 0.59/0.78        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_D)
% 0.59/0.78        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.59/0.78        | ~ (v1_funct_1 @ sk_F)
% 0.59/0.78        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 0.59/0.78        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))
% 0.59/0.78        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.59/0.78            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.59/0.78            = (sk_F))
% 0.59/0.78        | ~ (v1_funct_2 @ 
% 0.59/0.78             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.78             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.59/0.78        | ~ (v1_funct_1 @ 
% 0.59/0.78             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.59/0.78        | ((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.59/0.78            (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.59/0.78            != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.59/0.78                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))
% 0.59/0.78        | ~ (m1_subset_1 @ sk_E @ 
% 0.59/0.78             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))
% 0.59/0.78        | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)
% 0.59/0.78        | ~ (v1_funct_1 @ sk_E)
% 0.59/0.78        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_A))),
% 0.59/0.78      inference('sup-', [status(thm)], ['214', '215'])).
% 0.59/0.78  thf('217', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('218', plain, ((v1_funct_1 @ sk_F)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('219', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('220', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('221', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.59/0.78      inference('sup-', [status(thm)], ['67', '68'])).
% 0.59/0.78  thf('222', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['76', '77'])).
% 0.59/0.78  thf('223', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0)
% 0.59/0.78           = (k7_relat_1 @ sk_E @ X0))),
% 0.59/0.78      inference('demod', [status(thm)], ['81', '82'])).
% 0.59/0.78  thf('224', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.78      inference('demod', [status(thm)], ['162', '165'])).
% 0.59/0.78  thf('225', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.59/0.78      inference('sup-', [status(thm)], ['67', '68'])).
% 0.59/0.78  thf('226', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['76', '77'])).
% 0.59/0.78  thf('227', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.59/0.78      inference('demod', [status(thm)], ['171', '172'])).
% 0.59/0.78  thf('228', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('229', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('230', plain, ((v1_funct_1 @ sk_E)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('231', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('232', plain,
% 0.59/0.78      (((v1_xboole_0 @ sk_D)
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_A)
% 0.59/0.78        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_D)
% 0.59/0.78        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.59/0.78            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.59/0.78            = (sk_F))
% 0.59/0.78        | ~ (v1_funct_2 @ 
% 0.59/0.78             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.78             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.59/0.78        | ~ (v1_funct_1 @ 
% 0.59/0.78             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.59/0.78        | ((k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_A))),
% 0.59/0.78      inference('demod', [status(thm)],
% 0.59/0.78                ['216', '217', '218', '219', '220', '221', '222', '223', 
% 0.59/0.78                 '224', '225', '226', '227', '228', '229', '230', '231'])).
% 0.59/0.78  thf('233', plain,
% 0.59/0.78      ((((k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.59/0.78        | ~ (v1_funct_1 @ 
% 0.59/0.78             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.59/0.78        | ~ (v1_funct_2 @ 
% 0.59/0.78             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.78             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.59/0.78        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.59/0.78            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.59/0.78            = (sk_F))
% 0.59/0.78        | (v1_xboole_0 @ sk_A)
% 0.59/0.78        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_D))),
% 0.59/0.78      inference('simplify', [status(thm)], ['232'])).
% 0.59/0.78  thf('234', plain,
% 0.59/0.78      (((v1_xboole_0 @ sk_D)
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_A)
% 0.59/0.78        | (v1_xboole_0 @ sk_D)
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_A)
% 0.59/0.78        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.59/0.78            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.59/0.78            = (sk_F))
% 0.59/0.78        | ~ (v1_funct_1 @ 
% 0.59/0.78             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.59/0.78        | ((k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['213', '233'])).
% 0.59/0.78  thf('235', plain,
% 0.59/0.78      ((((k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.59/0.78        | ~ (v1_funct_1 @ 
% 0.59/0.78             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.59/0.78        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.59/0.78            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.59/0.78            = (sk_F))
% 0.59/0.78        | (v1_xboole_0 @ sk_A)
% 0.59/0.78        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_D))),
% 0.59/0.78      inference('simplify', [status(thm)], ['234'])).
% 0.59/0.78  thf('236', plain,
% 0.59/0.78      (((v1_xboole_0 @ sk_D)
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_A)
% 0.59/0.78        | (v1_xboole_0 @ sk_D)
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_A)
% 0.59/0.78        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.59/0.78            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.59/0.78            = (sk_F))
% 0.59/0.78        | ((k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['212', '235'])).
% 0.59/0.78  thf('237', plain,
% 0.59/0.78      ((((k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.59/0.78        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.59/0.78            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.59/0.78            = (sk_F))
% 0.59/0.78        | (v1_xboole_0 @ sk_A)
% 0.59/0.78        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_D))),
% 0.59/0.78      inference('simplify', [status(thm)], ['236'])).
% 0.59/0.78  thf('238', plain,
% 0.59/0.78      ((((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.78        | ~ (v1_relat_1 @ sk_F)
% 0.59/0.78        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.59/0.78        | (v1_xboole_0 @ sk_D)
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_A)
% 0.59/0.78        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.59/0.78            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.59/0.78            = (sk_F)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['211', '237'])).
% 0.59/0.78  thf('239', plain, ((v1_relat_1 @ sk_F)),
% 0.59/0.78      inference('sup-', [status(thm)], ['201', '202'])).
% 0.59/0.78  thf('240', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.78      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.59/0.78  thf('241', plain,
% 0.59/0.78      ((((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.78        | (v1_xboole_0 @ sk_D)
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_A)
% 0.59/0.78        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.59/0.78            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.59/0.78            = (sk_F)))),
% 0.59/0.78      inference('demod', [status(thm)], ['238', '239', '240'])).
% 0.59/0.78  thf('242', plain,
% 0.59/0.78      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.59/0.78          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.59/0.78          = (sk_F))
% 0.59/0.78        | (v1_xboole_0 @ sk_A)
% 0.59/0.78        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_D))),
% 0.59/0.78      inference('simplify', [status(thm)], ['241'])).
% 0.59/0.78  thf('243', plain,
% 0.59/0.78      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.59/0.78          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.59/0.78          != (sk_F)))
% 0.59/0.78         <= (~
% 0.59/0.78             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.59/0.78                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.78                sk_D) = (sk_F))))),
% 0.59/0.78      inference('split', [status(esa)], ['182'])).
% 0.59/0.78  thf('244', plain,
% 0.59/0.78      (((((sk_F) != (sk_F))
% 0.59/0.78         | (v1_xboole_0 @ sk_D)
% 0.59/0.78         | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78         | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78         | (v1_xboole_0 @ sk_A)))
% 0.59/0.78         <= (~
% 0.59/0.78             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.59/0.78                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.78                sk_D) = (sk_F))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['242', '243'])).
% 0.59/0.78  thf('245', plain,
% 0.59/0.78      ((((v1_xboole_0 @ sk_A)
% 0.59/0.78         | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78         | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78         | (v1_xboole_0 @ sk_D)))
% 0.59/0.78         <= (~
% 0.59/0.78             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.59/0.78                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.78                sk_D) = (sk_F))))),
% 0.59/0.78      inference('simplify', [status(thm)], ['244'])).
% 0.59/0.78  thf('246', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('247', plain,
% 0.59/0.78      ((((v1_xboole_0 @ sk_C_1) | (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A)))
% 0.59/0.78         <= (~
% 0.59/0.78             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.59/0.78                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.78                sk_D) = (sk_F))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['245', '246'])).
% 0.59/0.78  thf('248', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('249', plain,
% 0.59/0.78      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B_1)))
% 0.59/0.78         <= (~
% 0.59/0.78             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.59/0.78                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.78                sk_D) = (sk_F))))),
% 0.59/0.78      inference('clc', [status(thm)], ['247', '248'])).
% 0.59/0.78  thf('250', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('251', plain,
% 0.59/0.78      (((v1_xboole_0 @ sk_B_1))
% 0.59/0.78         <= (~
% 0.59/0.78             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.59/0.78                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.59/0.78                sk_D) = (sk_F))))),
% 0.59/0.78      inference('clc', [status(thm)], ['249', '250'])).
% 0.59/0.78  thf('252', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('253', plain,
% 0.59/0.78      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.59/0.78          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.59/0.78          = (sk_F)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['251', '252'])).
% 0.59/0.78  thf('254', plain,
% 0.59/0.78      (~
% 0.59/0.78       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.59/0.78          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.59/0.78          = (sk_E))) | 
% 0.59/0.78       ~
% 0.59/0.78       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.59/0.78          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.59/0.78          = (sk_F))) | 
% 0.59/0.78       ~
% 0.59/0.78       (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.59/0.78          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.59/0.78          = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.59/0.78             (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))))),
% 0.59/0.78      inference('split', [status(esa)], ['182'])).
% 0.59/0.78  thf('255', plain,
% 0.59/0.78      (~
% 0.59/0.78       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.59/0.78          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.59/0.78          = (sk_E)))),
% 0.59/0.78      inference('sat_resolution*', [status(thm)], ['210', '253', '254'])).
% 0.59/0.78  thf('256', plain,
% 0.59/0.78      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.59/0.78         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.59/0.78         != (sk_E))),
% 0.59/0.78      inference('simpl_trail', [status(thm)], ['183', '255'])).
% 0.59/0.78  thf('257', plain,
% 0.59/0.78      ((((k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.59/0.78        | ~ (v1_funct_1 @ 
% 0.59/0.78             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.59/0.78        | (v1_xboole_0 @ sk_A)
% 0.59/0.78        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_D))),
% 0.59/0.78      inference('simplify_reflect-', [status(thm)], ['181', '256'])).
% 0.59/0.78  thf('258', plain,
% 0.59/0.78      (((v1_xboole_0 @ sk_D)
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_A)
% 0.59/0.78        | (v1_xboole_0 @ sk_D)
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_A)
% 0.59/0.78        | ((k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['29', '257'])).
% 0.59/0.78  thf('259', plain,
% 0.59/0.78      ((((k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.59/0.78        | (v1_xboole_0 @ sk_A)
% 0.59/0.78        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_D))),
% 0.59/0.78      inference('simplify', [status(thm)], ['258'])).
% 0.59/0.78  thf('260', plain,
% 0.59/0.78      ((((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.78        | ~ (v1_relat_1 @ sk_F)
% 0.59/0.78        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.59/0.78        | (v1_xboole_0 @ sk_D)
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_A))),
% 0.59/0.78      inference('sup-', [status(thm)], ['14', '259'])).
% 0.59/0.78  thf('261', plain, ((v1_relat_1 @ sk_F)),
% 0.59/0.78      inference('sup-', [status(thm)], ['201', '202'])).
% 0.59/0.78  thf('262', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.78      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.59/0.78  thf('263', plain,
% 0.59/0.78      ((((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.78        | (v1_xboole_0 @ sk_D)
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_A))),
% 0.59/0.78      inference('demod', [status(thm)], ['260', '261', '262'])).
% 0.59/0.78  thf('264', plain,
% 0.59/0.78      (((v1_xboole_0 @ sk_A)
% 0.59/0.78        | (v1_xboole_0 @ sk_B_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_C_1)
% 0.59/0.78        | (v1_xboole_0 @ sk_D))),
% 0.59/0.78      inference('simplify', [status(thm)], ['263'])).
% 0.59/0.78  thf('265', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('266', plain,
% 0.59/0.78      (((v1_xboole_0 @ sk_C_1) | (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A))),
% 0.59/0.78      inference('sup-', [status(thm)], ['264', '265'])).
% 0.59/0.78  thf('267', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('268', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B_1))),
% 0.59/0.78      inference('clc', [status(thm)], ['266', '267'])).
% 0.59/0.78  thf('269', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('270', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.59/0.78      inference('clc', [status(thm)], ['268', '269'])).
% 0.59/0.78  thf('271', plain, ($false), inference('demod', [status(thm)], ['0', '270'])).
% 0.59/0.78  
% 0.59/0.78  % SZS output end Refutation
% 0.59/0.78  
% 0.59/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
