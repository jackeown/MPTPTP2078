%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BMG1oR7H5g

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:59 EST 2020

% Result     : Theorem 1.01s
% Output     : Refutation 1.01s
% Verified   : 
% Statistics : Number of formulae       :  238 ( 766 expanded)
%              Number of leaves         :   40 ( 242 expanded)
%              Depth                    :   40
%              Number of atoms          : 3822 (28514 expanded)
%              Number of equality atoms :  145 ( 981 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k4_xboole_0_type,type,(
    k4_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

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
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

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

thf('1',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('2',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('3',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X1 @ k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf(t65_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_xboole_0 @ A @ k1_xboole_0 ) )).

thf('5',plain,(
    ! [X11: $i] :
      ( r1_xboole_0 @ X11 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('6',plain,(
    ! [X1: $i] :
      ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['1','6'])).

thf(t187_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
         => ( ( k7_relat_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('8',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_xboole_0 @ X20 @ ( k1_relat_1 @ X21 ) )
      | ( ( k7_relat_1 @ X21 @ X20 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_B ) ) ),
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

thf('14',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X40 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) )
      | ( v1_xboole_0 @ X41 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X42 ) )
      | ( v1_xboole_0 @ X39 )
      | ( v1_xboole_0 @ X40 )
      | ( v1_xboole_0 @ X42 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X41 @ X40 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X42 @ X40 @ X39 @ X41 @ X38 @ X43 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_tmap_1 @ X2 @ sk_B @ sk_C_2 @ X1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_2 )
      | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_2 @ sk_E @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_tmap_1 @ X2 @ sk_B @ sk_C_2 @ X1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_2 )
      | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_2 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['12','18'])).

thf('20',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_2 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['19','20','21'])).

thf('23',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X40 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) )
      | ( v1_xboole_0 @ X41 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X42 ) )
      | ( v1_xboole_0 @ X39 )
      | ( v1_xboole_0 @ X40 )
      | ( v1_xboole_0 @ X42 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X41 @ X40 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X42 @ X40 @ X39 @ X41 @ X38 @ X43 ) @ ( k4_subset_1 @ X42 @ X39 @ X41 ) @ X40 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ ( k1_tmap_1 @ X1 @ sk_B @ sk_C_2 @ X0 @ sk_E @ X2 ) @ ( k4_subset_1 @ X1 @ sk_C_2 @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_2 )
      | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_2 @ sk_E @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ ( k1_tmap_1 @ X1 @ sk_B @ sk_C_2 @ X0 @ sk_E @ X2 ) @ ( k4_subset_1 @ X1 @ sk_C_2 @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_2 )
      | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_2 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ X0 @ sk_C_2 @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['27','33'])).

thf('35',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_2 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ X0 @ sk_C_2 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['34','35','36'])).

thf('38',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['26','37'])).

thf('39',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_2 @ X38 @ X39 @ X40 )
      | ~ ( v1_funct_1 @ X38 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ X42 ) )
      | ( v1_xboole_0 @ X41 )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ X42 ) )
      | ( v1_xboole_0 @ X39 )
      | ( v1_xboole_0 @ X40 )
      | ( v1_xboole_0 @ X42 )
      | ~ ( v1_funct_1 @ X43 )
      | ~ ( v1_funct_2 @ X43 @ X41 @ X40 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X40 ) ) )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X42 @ X40 @ X39 @ X41 @ X38 @ X43 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X42 @ X39 @ X41 ) @ X40 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tmap_1 @ X1 @ sk_B @ sk_C_2 @ X0 @ sk_E @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X1 @ sk_C_2 @ X0 ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_2 )
      | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C_2 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_2 @ sk_E @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tmap_1 @ X1 @ sk_B @ sk_C_2 @ X0 @ sk_E @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X1 @ sk_C_2 @ X0 ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_2 )
      | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_2 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C_2 @ sk_D ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['42','48'])).

thf('50',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_2 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C_2 @ sk_D ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['41','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['53','54'])).

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

thf('56',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( v1_xboole_0 @ X31 )
      | ( v1_xboole_0 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ X32 @ X31 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ( X37
       != ( k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X33 @ X36 @ X32 ) @ X31 @ X37 @ X36 )
        = X35 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X33 @ X36 @ X32 ) @ X31 ) ) )
      | ~ ( v1_funct_2 @ X37 @ ( k4_subset_1 @ X33 @ X36 @ X32 ) @ X31 )
      | ~ ( v1_funct_1 @ X37 )
      | ( ( k2_partfun1 @ X36 @ X31 @ X35 @ ( k9_subset_1 @ X33 @ X36 @ X32 ) )
       != ( k2_partfun1 @ X32 @ X31 @ X34 @ ( k9_subset_1 @ X33 @ X36 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X31 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X33 ) )
      | ( v1_xboole_0 @ X36 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('57',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( v1_xboole_0 @ X33 )
      | ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X31 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X31 ) ) )
      | ( ( k2_partfun1 @ X36 @ X31 @ X35 @ ( k9_subset_1 @ X33 @ X36 @ X32 ) )
       != ( k2_partfun1 @ X32 @ X31 @ X34 @ ( k9_subset_1 @ X33 @ X36 @ X32 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34 ) @ ( k4_subset_1 @ X33 @ X36 @ X32 ) @ X31 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X33 @ X36 @ X32 ) @ X31 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X33 @ X36 @ X32 ) @ X31 @ ( k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34 ) @ X36 )
        = X35 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X32 @ X31 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) )
      | ( v1_xboole_0 @ X32 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(simplify,[status(thm)],['56'])).

thf('58',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_C_2 )
      = sk_E )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_E @ sk_C_2 @ sk_B )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['55','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('64',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k9_subset_1 @ X17 @ X15 @ X16 )
        = ( k3_xboole_0 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    r1_subset_1 @ sk_C_2 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r1_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ( ( r1_subset_1 @ A @ B )
      <=> ( r1_xboole_0 @ A @ B ) ) ) )).

thf('67',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ( v1_xboole_0 @ X23 )
      | ( r1_xboole_0 @ X22 @ X23 )
      | ~ ( r1_subset_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_subset_1])).

thf('68',plain,
    ( ( r1_xboole_0 @ sk_C_2 @ sk_D )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( r1_xboole_0 @ sk_C_2 @ sk_D ) ),
    inference(clc,[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_D ),
    inference(clc,[status(thm)],['70','71'])).

thf(t83_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k4_xboole_0 @ A @ B )
        = A ) ) )).

thf('73',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('74',plain,
    ( ( k4_xboole_0 @ sk_C_2 @ sk_D )
    = sk_C_2 ),
    inference('sup-',[status(thm)],['72','73'])).

thf(t48_xboole_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) )
      = ( k3_xboole_0 @ A @ B ) ) )).

thf('75',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('76',plain,
    ( ( k4_xboole_0 @ sk_C_2 @ sk_C_2 )
    = ( k3_xboole_0 @ sk_C_2 @ sk_D ) ),
    inference('sup+',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X11: $i] :
      ( r1_xboole_0 @ X11 @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t65_xboole_1])).

thf('78',plain,(
    ! [X12: $i,X13: $i] :
      ( ( ( k4_xboole_0 @ X12 @ X13 )
        = X12 )
      | ~ ( r1_xboole_0 @ X12 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t83_xboole_1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ k1_xboole_0 )
      = X0 ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X9: $i,X10: $i] :
      ( ( k4_xboole_0 @ X9 @ ( k4_xboole_0 @ X9 @ X10 ) )
      = ( k3_xboole_0 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t48_xboole_1])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X8: $i] :
      ( ( k3_xboole_0 @ X8 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k4_xboole_0 @ X0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['76','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('86',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ( ( k2_partfun1 @ X28 @ X29 @ X27 @ X30 )
        = ( k7_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('91',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['76','83'])).

thf('92',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ( ( k2_partfun1 @ X28 @ X29 @ X27 @ X30 )
        = ( k7_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,(
    v1_funct_2 @ sk_E @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('99',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_C_2 )
      = sk_E )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['58','59','60','61','62','65','84','89','90','91','96','97','98','99','100'])).

thf('102',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_C_2 )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['101'])).

thf('103',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_C_2 )
      = sk_E )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','102'])).

thf('104',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_C_2 )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['103'])).

thf('105',plain,
    ( ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_C_2 )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('106',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_C_2 )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_C_2 )
     != sk_E ) ),
    inference(split,[status(esa)],['105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('108',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('111',plain,
    ( ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) ) ),
    inference(split,[status(esa)],['105'])).

thf('112',plain,
    ( ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('114',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['76','83'])).

thf('115',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['76','83'])).

thf('116',plain,
    ( ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['112','113','114','115'])).

thf('117',plain,
    ( ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['109','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('119',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['117','118'])).

thf('120',plain,
    ( ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_F ) )
   <= ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['108','119'])).

thf('121',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('122',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('123',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['120','123'])).

thf('125',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_E ) )
   <= ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['107','124'])).

thf('126',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('128',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['125','128'])).

thf('130',plain,
    ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['129'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('133',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['23','24'])).

thf('134',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('135',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['53','54'])).

thf('136',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ( v1_xboole_0 @ X31 )
      | ( v1_xboole_0 @ X32 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( v1_funct_2 @ X34 @ X32 @ X31 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ( X37
       != ( k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X33 @ X36 @ X32 ) @ X31 @ X37 @ X32 )
        = X34 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X33 @ X36 @ X32 ) @ X31 ) ) )
      | ~ ( v1_funct_2 @ X37 @ ( k4_subset_1 @ X33 @ X36 @ X32 ) @ X31 )
      | ~ ( v1_funct_1 @ X37 )
      | ( ( k2_partfun1 @ X36 @ X31 @ X35 @ ( k9_subset_1 @ X33 @ X36 @ X32 ) )
       != ( k2_partfun1 @ X32 @ X31 @ X34 @ ( k9_subset_1 @ X33 @ X36 @ X32 ) ) )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X31 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X33 ) )
      | ( v1_xboole_0 @ X36 )
      | ( v1_xboole_0 @ X33 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('137',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ( v1_xboole_0 @ X33 )
      | ( v1_xboole_0 @ X36 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X33 ) )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X31 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X31 ) ) )
      | ( ( k2_partfun1 @ X36 @ X31 @ X35 @ ( k9_subset_1 @ X33 @ X36 @ X32 ) )
       != ( k2_partfun1 @ X32 @ X31 @ X34 @ ( k9_subset_1 @ X33 @ X36 @ X32 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34 ) @ ( k4_subset_1 @ X33 @ X36 @ X32 ) @ X31 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X33 @ X36 @ X32 ) @ X31 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X33 @ X36 @ X32 ) @ X31 @ ( k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34 ) @ X32 )
        = X34 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X31 ) ) )
      | ~ ( v1_funct_2 @ X34 @ X32 @ X31 )
      | ~ ( v1_funct_1 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X33 ) )
      | ( v1_xboole_0 @ X32 )
      | ( v1_xboole_0 @ X31 ) ) ),
    inference(simplify,[status(thm)],['136'])).

thf('138',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_E @ sk_C_2 @ sk_B )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['135','137'])).

thf('139',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('144',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['76','83'])).

thf('145',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('147',plain,
    ( k1_xboole_0
    = ( k3_xboole_0 @ sk_C_2 @ sk_D ) ),
    inference(demod,[status(thm)],['76','83'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('149',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('150',plain,(
    v1_funct_2 @ sk_E @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('151',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('153',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['138','139','140','141','142','143','144','145','146','147','148','149','150','151','152'])).

thf('154',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['134','154'])).

thf('156',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['155'])).

thf('157',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['133','156'])).

thf('158',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['157'])).

thf('159',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference('sup-',[status(thm)],['132','158'])).

thf('160',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['121','122'])).

thf('161',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference(demod,[status(thm)],['159','160'])).

thf('162',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['131','161'])).

thf('163',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['126','127'])).

thf('164',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['162','163'])).

thf('165',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference(simplify,[status(thm)],['164'])).

thf('166',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['105'])).

thf('167',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_2 )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['165','166'])).

thf('168',plain,
    ( ( ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C_2 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_2 ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['168','169'])).

thf('171',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( ( v1_xboole_0 @ sk_C_2 )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['170','171'])).

thf('173',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['172','173'])).

thf('175',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('176',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['174','175'])).

thf('177',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_C_2 )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) ) ),
    inference(split,[status(esa)],['105'])).

thf('178',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_C_2 )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['130','176','177'])).

thf('179',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_C_2 )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['106','178'])).

thf('180',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['104','179'])).

thf('181',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['25','180'])).

thf('182',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['10','182'])).

thf('184',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['121','122'])).

thf('185',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['183','184'])).

thf('186',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['9','185'])).

thf('187',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['126','127'])).

thf('188',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['186','187'])).

thf('189',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['188'])).

thf('190',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['189','190'])).

thf('192',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['191','192'])).

thf('194',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('195',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['193','194'])).

thf('196',plain,(
    $false ),
    inference(demod,[status(thm)],['0','195'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.BMG1oR7H5g
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:54:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 1.01/1.19  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 1.01/1.19  % Solved by: fo/fo7.sh
% 1.01/1.19  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 1.01/1.19  % done 349 iterations in 0.734s
% 1.01/1.19  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 1.01/1.19  % SZS output start Refutation
% 1.01/1.19  thf(sk_C_2_type, type, sk_C_2: $i).
% 1.01/1.19  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 1.01/1.19  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 1.01/1.19  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 1.01/1.19  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 1.01/1.19  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 1.01/1.19  thf(sk_A_type, type, sk_A: $i).
% 1.01/1.19  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 1.01/1.19  thf(sk_E_type, type, sk_E: $i).
% 1.01/1.19  thf(sk_B_type, type, sk_B: $i).
% 1.01/1.19  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 1.01/1.19  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 1.01/1.19  thf(sk_D_type, type, sk_D: $i).
% 1.01/1.19  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 1.01/1.19  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 1.01/1.19  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 1.01/1.19  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 1.01/1.19  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 1.01/1.19  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 1.01/1.19  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 1.01/1.19  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 1.01/1.19  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 1.01/1.19  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 1.01/1.19  thf(k4_xboole_0_type, type, k4_xboole_0: $i > $i > $i).
% 1.01/1.19  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 1.01/1.19  thf(sk_F_type, type, sk_F: $i).
% 1.01/1.19  thf(t6_tmap_1, conjecture,
% 1.01/1.19    (![A:$i]:
% 1.01/1.19     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.01/1.19       ( ![B:$i]:
% 1.01/1.19         ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.01/1.19           ( ![C:$i]:
% 1.01/1.19             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 1.01/1.19                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.01/1.19               ( ![D:$i]:
% 1.01/1.19                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 1.01/1.19                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.01/1.19                   ( ( r1_subset_1 @ C @ D ) =>
% 1.01/1.19                     ( ![E:$i]:
% 1.01/1.19                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 1.01/1.19                           ( m1_subset_1 @
% 1.01/1.19                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 1.01/1.19                         ( ![F:$i]:
% 1.01/1.19                           ( ( ( v1_funct_1 @ F ) & 
% 1.01/1.19                               ( v1_funct_2 @ F @ D @ B ) & 
% 1.01/1.19                               ( m1_subset_1 @
% 1.01/1.19                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 1.01/1.19                             ( ( ( k2_partfun1 @
% 1.01/1.19                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 1.01/1.19                                 ( k2_partfun1 @
% 1.01/1.19                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 1.01/1.19                               ( ( k2_partfun1 @
% 1.01/1.19                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 1.01/1.19                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 1.01/1.19                                 ( E ) ) & 
% 1.01/1.19                               ( ( k2_partfun1 @
% 1.01/1.19                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 1.01/1.19                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 1.01/1.19                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.01/1.19  thf(zf_stmt_0, negated_conjecture,
% 1.01/1.19    (~( ![A:$i]:
% 1.01/1.19        ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.01/1.19          ( ![B:$i]:
% 1.01/1.19            ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.01/1.19              ( ![C:$i]:
% 1.01/1.19                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 1.01/1.19                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.01/1.19                  ( ![D:$i]:
% 1.01/1.19                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 1.01/1.19                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.01/1.19                      ( ( r1_subset_1 @ C @ D ) =>
% 1.01/1.19                        ( ![E:$i]:
% 1.01/1.19                          ( ( ( v1_funct_1 @ E ) & 
% 1.01/1.19                              ( v1_funct_2 @ E @ C @ B ) & 
% 1.01/1.19                              ( m1_subset_1 @
% 1.01/1.19                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 1.01/1.19                            ( ![F:$i]:
% 1.01/1.19                              ( ( ( v1_funct_1 @ F ) & 
% 1.01/1.19                                  ( v1_funct_2 @ F @ D @ B ) & 
% 1.01/1.19                                  ( m1_subset_1 @
% 1.01/1.19                                    F @ 
% 1.01/1.19                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 1.01/1.19                                ( ( ( k2_partfun1 @
% 1.01/1.19                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 1.01/1.19                                    ( k2_partfun1 @
% 1.01/1.19                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 1.01/1.19                                  ( ( k2_partfun1 @
% 1.01/1.19                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 1.01/1.19                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 1.01/1.19                                    ( E ) ) & 
% 1.01/1.19                                  ( ( k2_partfun1 @
% 1.01/1.19                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 1.01/1.19                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 1.01/1.19                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 1.01/1.20    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 1.01/1.20  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf(t3_xboole_0, axiom,
% 1.01/1.20    (![A:$i,B:$i]:
% 1.01/1.20     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 1.01/1.20            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.01/1.20       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.01/1.20            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 1.01/1.20  thf('1', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i]:
% 1.01/1.20         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 1.01/1.20      inference('cnf', [status(esa)], [t3_xboole_0])).
% 1.01/1.20  thf(t2_boole, axiom,
% 1.01/1.20    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 1.01/1.20  thf('2', plain,
% 1.01/1.20      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 1.01/1.20      inference('cnf', [status(esa)], [t2_boole])).
% 1.01/1.20  thf(t4_xboole_0, axiom,
% 1.01/1.20    (![A:$i,B:$i]:
% 1.01/1.20     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 1.01/1.20            ( r1_xboole_0 @ A @ B ) ) ) & 
% 1.01/1.20       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 1.01/1.20            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 1.01/1.20  thf('3', plain,
% 1.01/1.20      (![X4 : $i, X6 : $i, X7 : $i]:
% 1.01/1.20         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 1.01/1.20          | ~ (r1_xboole_0 @ X4 @ X7))),
% 1.01/1.20      inference('cnf', [status(esa)], [t4_xboole_0])).
% 1.01/1.20  thf('4', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i]:
% 1.01/1.20         (~ (r2_hidden @ X1 @ k1_xboole_0) | ~ (r1_xboole_0 @ X0 @ k1_xboole_0))),
% 1.01/1.20      inference('sup-', [status(thm)], ['2', '3'])).
% 1.01/1.20  thf(t65_xboole_1, axiom, (![A:$i]: ( r1_xboole_0 @ A @ k1_xboole_0 ))).
% 1.01/1.20  thf('5', plain, (![X11 : $i]: (r1_xboole_0 @ X11 @ k1_xboole_0)),
% 1.01/1.20      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.01/1.20  thf('6', plain, (![X1 : $i]: ~ (r2_hidden @ X1 @ k1_xboole_0)),
% 1.01/1.20      inference('demod', [status(thm)], ['4', '5'])).
% 1.01/1.20  thf('7', plain, (![X0 : $i]: (r1_xboole_0 @ k1_xboole_0 @ X0)),
% 1.01/1.20      inference('sup-', [status(thm)], ['1', '6'])).
% 1.01/1.20  thf(t187_relat_1, axiom,
% 1.01/1.20    (![A:$i]:
% 1.01/1.20     ( ( v1_relat_1 @ A ) =>
% 1.01/1.20       ( ![B:$i]:
% 1.01/1.20         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 1.01/1.20           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 1.01/1.20  thf('8', plain,
% 1.01/1.20      (![X20 : $i, X21 : $i]:
% 1.01/1.20         (~ (r1_xboole_0 @ X20 @ (k1_relat_1 @ X21))
% 1.01/1.20          | ((k7_relat_1 @ X21 @ X20) = (k1_xboole_0))
% 1.01/1.20          | ~ (v1_relat_1 @ X21))),
% 1.01/1.20      inference('cnf', [status(esa)], [t187_relat_1])).
% 1.01/1.20  thf('9', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         (~ (v1_relat_1 @ X0)
% 1.01/1.20          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['7', '8'])).
% 1.01/1.20  thf('10', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         (~ (v1_relat_1 @ X0)
% 1.01/1.20          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['7', '8'])).
% 1.01/1.20  thf('11', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('12', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('13', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_B)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf(dt_k1_tmap_1, axiom,
% 1.01/1.20    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 1.01/1.20     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 1.01/1.20         ( ~( v1_xboole_0 @ C ) ) & 
% 1.01/1.20         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 1.01/1.20         ( ~( v1_xboole_0 @ D ) ) & 
% 1.01/1.20         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 1.01/1.20         ( v1_funct_2 @ E @ C @ B ) & 
% 1.01/1.20         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 1.01/1.20         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 1.01/1.20         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 1.01/1.20       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 1.01/1.20         ( v1_funct_2 @
% 1.01/1.20           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.01/1.20           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 1.01/1.20         ( m1_subset_1 @
% 1.01/1.20           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 1.01/1.20           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 1.01/1.20  thf('14', plain,
% 1.01/1.20      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.01/1.20         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 1.01/1.20          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 1.01/1.20          | ~ (v1_funct_1 @ X38)
% 1.01/1.20          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 1.01/1.20          | (v1_xboole_0 @ X41)
% 1.01/1.20          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X42))
% 1.01/1.20          | (v1_xboole_0 @ X39)
% 1.01/1.20          | (v1_xboole_0 @ X40)
% 1.01/1.20          | (v1_xboole_0 @ X42)
% 1.01/1.20          | ~ (v1_funct_1 @ X43)
% 1.01/1.20          | ~ (v1_funct_2 @ X43 @ X41 @ X40)
% 1.01/1.20          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 1.01/1.20          | (v1_funct_1 @ (k1_tmap_1 @ X42 @ X40 @ X39 @ X41 @ X38 @ X43)))),
% 1.01/1.20      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 1.01/1.20  thf('15', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.20         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C_2 @ X1 @ sk_E @ X0))
% 1.01/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.01/1.20          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.01/1.20          | ~ (v1_funct_1 @ X0)
% 1.01/1.20          | (v1_xboole_0 @ X2)
% 1.01/1.20          | (v1_xboole_0 @ sk_B)
% 1.01/1.20          | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X2))
% 1.01/1.20          | (v1_xboole_0 @ X1)
% 1.01/1.20          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 1.01/1.20          | ~ (v1_funct_1 @ sk_E)
% 1.01/1.20          | ~ (v1_funct_2 @ sk_E @ sk_C_2 @ sk_B))),
% 1.01/1.20      inference('sup-', [status(thm)], ['13', '14'])).
% 1.01/1.20  thf('16', plain, ((v1_funct_1 @ sk_E)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('17', plain, ((v1_funct_2 @ sk_E @ sk_C_2 @ sk_B)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('18', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.20         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C_2 @ X1 @ sk_E @ X0))
% 1.01/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 1.01/1.20          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 1.01/1.20          | ~ (v1_funct_1 @ X0)
% 1.01/1.20          | (v1_xboole_0 @ X2)
% 1.01/1.20          | (v1_xboole_0 @ sk_B)
% 1.01/1.20          | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X2))
% 1.01/1.20          | (v1_xboole_0 @ X1)
% 1.01/1.20          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 1.01/1.20      inference('demod', [status(thm)], ['15', '16', '17'])).
% 1.01/1.20  thf('19', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 1.01/1.20          | (v1_xboole_0 @ sk_D)
% 1.01/1.20          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X0))
% 1.01/1.20          | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20          | (v1_xboole_0 @ sk_B)
% 1.01/1.20          | (v1_xboole_0 @ X0)
% 1.01/1.20          | ~ (v1_funct_1 @ sk_F)
% 1.01/1.20          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 1.01/1.20          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['12', '18'])).
% 1.01/1.20  thf('20', plain, ((v1_funct_1 @ sk_F)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('21', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('22', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 1.01/1.20          | (v1_xboole_0 @ sk_D)
% 1.01/1.20          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X0))
% 1.01/1.20          | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20          | (v1_xboole_0 @ sk_B)
% 1.01/1.20          | (v1_xboole_0 @ X0)
% 1.01/1.20          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F)))),
% 1.01/1.20      inference('demod', [status(thm)], ['19', '20', '21'])).
% 1.01/1.20  thf('23', plain,
% 1.01/1.20      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))
% 1.01/1.20        | (v1_xboole_0 @ sk_D))),
% 1.01/1.20      inference('sup-', [status(thm)], ['11', '22'])).
% 1.01/1.20  thf('24', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('25', plain,
% 1.01/1.20      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_D))),
% 1.01/1.20      inference('demod', [status(thm)], ['23', '24'])).
% 1.01/1.20  thf('26', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('27', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('28', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_B)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('29', plain,
% 1.01/1.20      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.01/1.20         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 1.01/1.20          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 1.01/1.20          | ~ (v1_funct_1 @ X38)
% 1.01/1.20          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 1.01/1.20          | (v1_xboole_0 @ X41)
% 1.01/1.20          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X42))
% 1.01/1.20          | (v1_xboole_0 @ X39)
% 1.01/1.20          | (v1_xboole_0 @ X40)
% 1.01/1.20          | (v1_xboole_0 @ X42)
% 1.01/1.20          | ~ (v1_funct_1 @ X43)
% 1.01/1.20          | ~ (v1_funct_2 @ X43 @ X41 @ X40)
% 1.01/1.20          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 1.01/1.20          | (v1_funct_2 @ (k1_tmap_1 @ X42 @ X40 @ X39 @ X41 @ X38 @ X43) @ 
% 1.01/1.20             (k4_subset_1 @ X42 @ X39 @ X41) @ X40))),
% 1.01/1.20      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 1.01/1.20  thf('30', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.20         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C_2 @ X0 @ sk_E @ X2) @ 
% 1.01/1.20           (k4_subset_1 @ X1 @ sk_C_2 @ X0) @ sk_B)
% 1.01/1.20          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 1.01/1.20          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 1.01/1.20          | ~ (v1_funct_1 @ X2)
% 1.01/1.20          | (v1_xboole_0 @ X1)
% 1.01/1.20          | (v1_xboole_0 @ sk_B)
% 1.01/1.20          | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X1))
% 1.01/1.20          | (v1_xboole_0 @ X0)
% 1.01/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.01/1.20          | ~ (v1_funct_1 @ sk_E)
% 1.01/1.20          | ~ (v1_funct_2 @ sk_E @ sk_C_2 @ sk_B))),
% 1.01/1.20      inference('sup-', [status(thm)], ['28', '29'])).
% 1.01/1.20  thf('31', plain, ((v1_funct_1 @ sk_E)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('32', plain, ((v1_funct_2 @ sk_E @ sk_C_2 @ sk_B)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('33', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.20         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C_2 @ X0 @ sk_E @ X2) @ 
% 1.01/1.20           (k4_subset_1 @ X1 @ sk_C_2 @ X0) @ sk_B)
% 1.01/1.20          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 1.01/1.20          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 1.01/1.20          | ~ (v1_funct_1 @ X2)
% 1.01/1.20          | (v1_xboole_0 @ X1)
% 1.01/1.20          | (v1_xboole_0 @ sk_B)
% 1.01/1.20          | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X1))
% 1.01/1.20          | (v1_xboole_0 @ X0)
% 1.01/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 1.01/1.20      inference('demod', [status(thm)], ['30', '31', '32'])).
% 1.01/1.20  thf('34', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 1.01/1.20          | (v1_xboole_0 @ sk_D)
% 1.01/1.20          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X0))
% 1.01/1.20          | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20          | (v1_xboole_0 @ sk_B)
% 1.01/1.20          | (v1_xboole_0 @ X0)
% 1.01/1.20          | ~ (v1_funct_1 @ sk_F)
% 1.01/1.20          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 1.01/1.20          | (v1_funct_2 @ 
% 1.01/1.20             (k1_tmap_1 @ X0 @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 1.01/1.20             (k4_subset_1 @ X0 @ sk_C_2 @ sk_D) @ sk_B))),
% 1.01/1.20      inference('sup-', [status(thm)], ['27', '33'])).
% 1.01/1.20  thf('35', plain, ((v1_funct_1 @ sk_F)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('36', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('37', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 1.01/1.20          | (v1_xboole_0 @ sk_D)
% 1.01/1.20          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X0))
% 1.01/1.20          | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20          | (v1_xboole_0 @ sk_B)
% 1.01/1.20          | (v1_xboole_0 @ X0)
% 1.01/1.20          | (v1_funct_2 @ 
% 1.01/1.20             (k1_tmap_1 @ X0 @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 1.01/1.20             (k4_subset_1 @ X0 @ sk_C_2 @ sk_D) @ sk_B))),
% 1.01/1.20      inference('demod', [status(thm)], ['34', '35', '36'])).
% 1.01/1.20  thf('38', plain,
% 1.01/1.20      (((v1_funct_2 @ 
% 1.01/1.20         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 1.01/1.20         (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))
% 1.01/1.20        | (v1_xboole_0 @ sk_D))),
% 1.01/1.20      inference('sup-', [status(thm)], ['26', '37'])).
% 1.01/1.20  thf('39', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('40', plain,
% 1.01/1.20      (((v1_funct_2 @ 
% 1.01/1.20         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 1.01/1.20         (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_D))),
% 1.01/1.20      inference('demod', [status(thm)], ['38', '39'])).
% 1.01/1.20  thf('41', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('42', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('43', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_B)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('44', plain,
% 1.01/1.20      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 1.01/1.20         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 1.01/1.20          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 1.01/1.20          | ~ (v1_funct_1 @ X38)
% 1.01/1.20          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 1.01/1.20          | (v1_xboole_0 @ X41)
% 1.01/1.20          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X42))
% 1.01/1.20          | (v1_xboole_0 @ X39)
% 1.01/1.20          | (v1_xboole_0 @ X40)
% 1.01/1.20          | (v1_xboole_0 @ X42)
% 1.01/1.20          | ~ (v1_funct_1 @ X43)
% 1.01/1.20          | ~ (v1_funct_2 @ X43 @ X41 @ X40)
% 1.01/1.20          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 1.01/1.20          | (m1_subset_1 @ (k1_tmap_1 @ X42 @ X40 @ X39 @ X41 @ X38 @ X43) @ 
% 1.01/1.20             (k1_zfmisc_1 @ 
% 1.01/1.20              (k2_zfmisc_1 @ (k4_subset_1 @ X42 @ X39 @ X41) @ X40))))),
% 1.01/1.20      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 1.01/1.20  thf('45', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.20         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C_2 @ X0 @ sk_E @ X2) @ 
% 1.01/1.20           (k1_zfmisc_1 @ 
% 1.01/1.20            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C_2 @ X0) @ sk_B)))
% 1.01/1.20          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 1.01/1.20          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 1.01/1.20          | ~ (v1_funct_1 @ X2)
% 1.01/1.20          | (v1_xboole_0 @ X1)
% 1.01/1.20          | (v1_xboole_0 @ sk_B)
% 1.01/1.20          | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X1))
% 1.01/1.20          | (v1_xboole_0 @ X0)
% 1.01/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 1.01/1.20          | ~ (v1_funct_1 @ sk_E)
% 1.01/1.20          | ~ (v1_funct_2 @ sk_E @ sk_C_2 @ sk_B))),
% 1.01/1.20      inference('sup-', [status(thm)], ['43', '44'])).
% 1.01/1.20  thf('46', plain, ((v1_funct_1 @ sk_E)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('47', plain, ((v1_funct_2 @ sk_E @ sk_C_2 @ sk_B)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('48', plain,
% 1.01/1.20      (![X0 : $i, X1 : $i, X2 : $i]:
% 1.01/1.20         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C_2 @ X0 @ sk_E @ X2) @ 
% 1.01/1.20           (k1_zfmisc_1 @ 
% 1.01/1.20            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C_2 @ X0) @ sk_B)))
% 1.01/1.20          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 1.01/1.20          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 1.01/1.20          | ~ (v1_funct_1 @ X2)
% 1.01/1.20          | (v1_xboole_0 @ X1)
% 1.01/1.20          | (v1_xboole_0 @ sk_B)
% 1.01/1.20          | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X1))
% 1.01/1.20          | (v1_xboole_0 @ X0)
% 1.01/1.20          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 1.01/1.20      inference('demod', [status(thm)], ['45', '46', '47'])).
% 1.01/1.20  thf('49', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 1.01/1.20          | (v1_xboole_0 @ sk_D)
% 1.01/1.20          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X0))
% 1.01/1.20          | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20          | (v1_xboole_0 @ sk_B)
% 1.01/1.20          | (v1_xboole_0 @ X0)
% 1.01/1.20          | ~ (v1_funct_1 @ sk_F)
% 1.01/1.20          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 1.01/1.20          | (m1_subset_1 @ 
% 1.01/1.20             (k1_tmap_1 @ X0 @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 1.01/1.20             (k1_zfmisc_1 @ 
% 1.01/1.20              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C_2 @ sk_D) @ sk_B))))),
% 1.01/1.20      inference('sup-', [status(thm)], ['42', '48'])).
% 1.01/1.20  thf('50', plain, ((v1_funct_1 @ sk_F)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('51', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('52', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 1.01/1.20          | (v1_xboole_0 @ sk_D)
% 1.01/1.20          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X0))
% 1.01/1.20          | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20          | (v1_xboole_0 @ sk_B)
% 1.01/1.20          | (v1_xboole_0 @ X0)
% 1.01/1.20          | (m1_subset_1 @ 
% 1.01/1.20             (k1_tmap_1 @ X0 @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 1.01/1.20             (k1_zfmisc_1 @ 
% 1.01/1.20              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C_2 @ sk_D) @ sk_B))))),
% 1.01/1.20      inference('demod', [status(thm)], ['49', '50', '51'])).
% 1.01/1.20  thf('53', plain,
% 1.01/1.20      (((m1_subset_1 @ 
% 1.01/1.20         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 1.01/1.20         (k1_zfmisc_1 @ 
% 1.01/1.20          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B)))
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))
% 1.01/1.20        | (v1_xboole_0 @ sk_D))),
% 1.01/1.20      inference('sup-', [status(thm)], ['41', '52'])).
% 1.01/1.20  thf('54', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('55', plain,
% 1.01/1.20      (((m1_subset_1 @ 
% 1.01/1.20         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 1.01/1.20         (k1_zfmisc_1 @ 
% 1.01/1.20          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B)))
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_D))),
% 1.01/1.20      inference('demod', [status(thm)], ['53', '54'])).
% 1.01/1.20  thf(d1_tmap_1, axiom,
% 1.01/1.20    (![A:$i]:
% 1.01/1.20     ( ( ~( v1_xboole_0 @ A ) ) =>
% 1.01/1.20       ( ![B:$i]:
% 1.01/1.20         ( ( ~( v1_xboole_0 @ B ) ) =>
% 1.01/1.20           ( ![C:$i]:
% 1.01/1.20             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 1.01/1.20                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.01/1.20               ( ![D:$i]:
% 1.01/1.20                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 1.01/1.20                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 1.01/1.20                   ( ![E:$i]:
% 1.01/1.20                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 1.01/1.20                         ( m1_subset_1 @
% 1.01/1.20                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 1.01/1.20                       ( ![F:$i]:
% 1.01/1.20                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 1.01/1.20                             ( m1_subset_1 @
% 1.01/1.20                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 1.01/1.20                           ( ( ( k2_partfun1 @
% 1.01/1.20                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 1.01/1.20                               ( k2_partfun1 @
% 1.01/1.20                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 1.01/1.20                             ( ![G:$i]:
% 1.01/1.20                               ( ( ( v1_funct_1 @ G ) & 
% 1.01/1.20                                   ( v1_funct_2 @
% 1.01/1.20                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 1.01/1.20                                   ( m1_subset_1 @
% 1.01/1.20                                     G @ 
% 1.01/1.20                                     ( k1_zfmisc_1 @
% 1.01/1.20                                       ( k2_zfmisc_1 @
% 1.01/1.20                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 1.01/1.20                                 ( ( ( G ) =
% 1.01/1.20                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 1.01/1.20                                   ( ( ( k2_partfun1 @
% 1.01/1.20                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 1.01/1.20                                         C ) =
% 1.01/1.20                                       ( E ) ) & 
% 1.01/1.20                                     ( ( k2_partfun1 @
% 1.01/1.20                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 1.01/1.20                                         D ) =
% 1.01/1.20                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 1.01/1.20  thf('56', plain,
% 1.01/1.20      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 1.01/1.20         ((v1_xboole_0 @ X31)
% 1.01/1.20          | (v1_xboole_0 @ X32)
% 1.01/1.20          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 1.01/1.20          | ~ (v1_funct_1 @ X34)
% 1.01/1.20          | ~ (v1_funct_2 @ X34 @ X32 @ X31)
% 1.01/1.20          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 1.01/1.20          | ((X37) != (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34))
% 1.01/1.20          | ((k2_partfun1 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31 @ X37 @ X36)
% 1.01/1.20              = (X35))
% 1.01/1.20          | ~ (m1_subset_1 @ X37 @ 
% 1.01/1.20               (k1_zfmisc_1 @ 
% 1.01/1.20                (k2_zfmisc_1 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31)))
% 1.01/1.20          | ~ (v1_funct_2 @ X37 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31)
% 1.01/1.20          | ~ (v1_funct_1 @ X37)
% 1.01/1.20          | ((k2_partfun1 @ X36 @ X31 @ X35 @ (k9_subset_1 @ X33 @ X36 @ X32))
% 1.01/1.20              != (k2_partfun1 @ X32 @ X31 @ X34 @ 
% 1.01/1.20                  (k9_subset_1 @ X33 @ X36 @ X32)))
% 1.01/1.20          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X31)))
% 1.01/1.20          | ~ (v1_funct_2 @ X35 @ X36 @ X31)
% 1.01/1.20          | ~ (v1_funct_1 @ X35)
% 1.01/1.20          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X33))
% 1.01/1.20          | (v1_xboole_0 @ X36)
% 1.01/1.20          | (v1_xboole_0 @ X33))),
% 1.01/1.20      inference('cnf', [status(esa)], [d1_tmap_1])).
% 1.01/1.20  thf('57', plain,
% 1.01/1.20      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.01/1.20         ((v1_xboole_0 @ X33)
% 1.01/1.20          | (v1_xboole_0 @ X36)
% 1.01/1.20          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X33))
% 1.01/1.20          | ~ (v1_funct_1 @ X35)
% 1.01/1.20          | ~ (v1_funct_2 @ X35 @ X36 @ X31)
% 1.01/1.20          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X31)))
% 1.01/1.20          | ((k2_partfun1 @ X36 @ X31 @ X35 @ (k9_subset_1 @ X33 @ X36 @ X32))
% 1.01/1.20              != (k2_partfun1 @ X32 @ X31 @ X34 @ 
% 1.01/1.20                  (k9_subset_1 @ X33 @ X36 @ X32)))
% 1.01/1.20          | ~ (v1_funct_1 @ (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34))
% 1.01/1.20          | ~ (v1_funct_2 @ (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34) @ 
% 1.01/1.20               (k4_subset_1 @ X33 @ X36 @ X32) @ X31)
% 1.01/1.20          | ~ (m1_subset_1 @ (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34) @ 
% 1.01/1.20               (k1_zfmisc_1 @ 
% 1.01/1.20                (k2_zfmisc_1 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31)))
% 1.01/1.20          | ((k2_partfun1 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31 @ 
% 1.01/1.20              (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34) @ X36) = (
% 1.01/1.20              X35))
% 1.01/1.20          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 1.01/1.20          | ~ (v1_funct_2 @ X34 @ X32 @ X31)
% 1.01/1.20          | ~ (v1_funct_1 @ X34)
% 1.01/1.20          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 1.01/1.20          | (v1_xboole_0 @ X32)
% 1.01/1.20          | (v1_xboole_0 @ X31))),
% 1.01/1.20      inference('simplify', [status(thm)], ['56'])).
% 1.01/1.20  thf('58', plain,
% 1.01/1.20      (((v1_xboole_0 @ sk_D)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_D)
% 1.01/1.20        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 1.01/1.20        | ~ (v1_funct_1 @ sk_F)
% 1.01/1.20        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 1.01/1.20        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 1.01/1.20        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 1.01/1.20            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_C_2)
% 1.01/1.20            = (sk_E))
% 1.01/1.20        | ~ (v1_funct_2 @ 
% 1.01/1.20             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 1.01/1.20             (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B)
% 1.01/1.20        | ~ (v1_funct_1 @ 
% 1.01/1.20             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 1.01/1.20        | ((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ 
% 1.01/1.20            (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 1.01/1.20            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 1.01/1.20                (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))
% 1.01/1.20        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_B)))
% 1.01/1.20        | ~ (v1_funct_2 @ sk_E @ sk_C_2 @ sk_B)
% 1.01/1.20        | ~ (v1_funct_1 @ sk_E)
% 1.01/1.20        | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_A))),
% 1.01/1.20      inference('sup-', [status(thm)], ['55', '57'])).
% 1.01/1.20  thf('59', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('60', plain, ((v1_funct_1 @ sk_F)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('61', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('62', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('63', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf(redefinition_k9_subset_1, axiom,
% 1.01/1.20    (![A:$i,B:$i,C:$i]:
% 1.01/1.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 1.01/1.20       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 1.01/1.20  thf('64', plain,
% 1.01/1.20      (![X15 : $i, X16 : $i, X17 : $i]:
% 1.01/1.20         (((k9_subset_1 @ X17 @ X15 @ X16) = (k3_xboole_0 @ X15 @ X16))
% 1.01/1.20          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 1.01/1.20      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 1.01/1.20  thf('65', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 1.01/1.20      inference('sup-', [status(thm)], ['63', '64'])).
% 1.01/1.20  thf('66', plain, ((r1_subset_1 @ sk_C_2 @ sk_D)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf(redefinition_r1_subset_1, axiom,
% 1.01/1.20    (![A:$i,B:$i]:
% 1.01/1.20     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 1.01/1.20       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 1.01/1.20  thf('67', plain,
% 1.01/1.20      (![X22 : $i, X23 : $i]:
% 1.01/1.20         ((v1_xboole_0 @ X22)
% 1.01/1.20          | (v1_xboole_0 @ X23)
% 1.01/1.20          | (r1_xboole_0 @ X22 @ X23)
% 1.01/1.20          | ~ (r1_subset_1 @ X22 @ X23))),
% 1.01/1.20      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 1.01/1.20  thf('68', plain,
% 1.01/1.20      (((r1_xboole_0 @ sk_C_2 @ sk_D)
% 1.01/1.20        | (v1_xboole_0 @ sk_D)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2))),
% 1.01/1.20      inference('sup-', [status(thm)], ['66', '67'])).
% 1.01/1.20  thf('69', plain, (~ (v1_xboole_0 @ sk_D)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('70', plain, (((v1_xboole_0 @ sk_C_2) | (r1_xboole_0 @ sk_C_2 @ sk_D))),
% 1.01/1.20      inference('clc', [status(thm)], ['68', '69'])).
% 1.01/1.20  thf('71', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('72', plain, ((r1_xboole_0 @ sk_C_2 @ sk_D)),
% 1.01/1.20      inference('clc', [status(thm)], ['70', '71'])).
% 1.01/1.20  thf(t83_xboole_1, axiom,
% 1.01/1.20    (![A:$i,B:$i]:
% 1.01/1.20     ( ( r1_xboole_0 @ A @ B ) <=> ( ( k4_xboole_0 @ A @ B ) = ( A ) ) ))).
% 1.01/1.20  thf('73', plain,
% 1.01/1.20      (![X12 : $i, X13 : $i]:
% 1.01/1.20         (((k4_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_xboole_0 @ X12 @ X13))),
% 1.01/1.20      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.01/1.20  thf('74', plain, (((k4_xboole_0 @ sk_C_2 @ sk_D) = (sk_C_2))),
% 1.01/1.20      inference('sup-', [status(thm)], ['72', '73'])).
% 1.01/1.20  thf(t48_xboole_1, axiom,
% 1.01/1.20    (![A:$i,B:$i]:
% 1.01/1.20     ( ( k4_xboole_0 @ A @ ( k4_xboole_0 @ A @ B ) ) = ( k3_xboole_0 @ A @ B ) ))).
% 1.01/1.20  thf('75', plain,
% 1.01/1.20      (![X9 : $i, X10 : $i]:
% 1.01/1.20         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 1.01/1.20           = (k3_xboole_0 @ X9 @ X10))),
% 1.01/1.20      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.01/1.20  thf('76', plain,
% 1.01/1.20      (((k4_xboole_0 @ sk_C_2 @ sk_C_2) = (k3_xboole_0 @ sk_C_2 @ sk_D))),
% 1.01/1.20      inference('sup+', [status(thm)], ['74', '75'])).
% 1.01/1.20  thf('77', plain, (![X11 : $i]: (r1_xboole_0 @ X11 @ k1_xboole_0)),
% 1.01/1.20      inference('cnf', [status(esa)], [t65_xboole_1])).
% 1.01/1.20  thf('78', plain,
% 1.01/1.20      (![X12 : $i, X13 : $i]:
% 1.01/1.20         (((k4_xboole_0 @ X12 @ X13) = (X12)) | ~ (r1_xboole_0 @ X12 @ X13))),
% 1.01/1.20      inference('cnf', [status(esa)], [t83_xboole_1])).
% 1.01/1.20  thf('79', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ k1_xboole_0) = (X0))),
% 1.01/1.20      inference('sup-', [status(thm)], ['77', '78'])).
% 1.01/1.20  thf('80', plain,
% 1.01/1.20      (![X9 : $i, X10 : $i]:
% 1.01/1.20         ((k4_xboole_0 @ X9 @ (k4_xboole_0 @ X9 @ X10))
% 1.01/1.20           = (k3_xboole_0 @ X9 @ X10))),
% 1.01/1.20      inference('cnf', [status(esa)], [t48_xboole_1])).
% 1.01/1.20  thf('81', plain,
% 1.01/1.20      (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k3_xboole_0 @ X0 @ k1_xboole_0))),
% 1.01/1.20      inference('sup+', [status(thm)], ['79', '80'])).
% 1.01/1.20  thf('82', plain,
% 1.01/1.20      (![X8 : $i]: ((k3_xboole_0 @ X8 @ k1_xboole_0) = (k1_xboole_0))),
% 1.01/1.20      inference('cnf', [status(esa)], [t2_boole])).
% 1.01/1.20  thf('83', plain, (![X0 : $i]: ((k4_xboole_0 @ X0 @ X0) = (k1_xboole_0))),
% 1.01/1.20      inference('demod', [status(thm)], ['81', '82'])).
% 1.01/1.20  thf('84', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_C_2 @ sk_D))),
% 1.01/1.20      inference('demod', [status(thm)], ['76', '83'])).
% 1.01/1.20  thf('85', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_B)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf(redefinition_k2_partfun1, axiom,
% 1.01/1.20    (![A:$i,B:$i,C:$i,D:$i]:
% 1.01/1.20     ( ( ( v1_funct_1 @ C ) & 
% 1.01/1.20         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 1.01/1.20       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 1.01/1.20  thf('86', plain,
% 1.01/1.20      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.01/1.20         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 1.01/1.20          | ~ (v1_funct_1 @ X27)
% 1.01/1.20          | ((k2_partfun1 @ X28 @ X29 @ X27 @ X30) = (k7_relat_1 @ X27 @ X30)))),
% 1.01/1.20      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 1.01/1.20  thf('87', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         (((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 1.01/1.20          | ~ (v1_funct_1 @ sk_E))),
% 1.01/1.20      inference('sup-', [status(thm)], ['85', '86'])).
% 1.01/1.20  thf('88', plain, ((v1_funct_1 @ sk_E)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('89', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         ((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 1.01/1.20      inference('demod', [status(thm)], ['87', '88'])).
% 1.01/1.20  thf('90', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 1.01/1.20      inference('sup-', [status(thm)], ['63', '64'])).
% 1.01/1.20  thf('91', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_C_2 @ sk_D))),
% 1.01/1.20      inference('demod', [status(thm)], ['76', '83'])).
% 1.01/1.20  thf('92', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('93', plain,
% 1.01/1.20      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 1.01/1.20         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 1.01/1.20          | ~ (v1_funct_1 @ X27)
% 1.01/1.20          | ((k2_partfun1 @ X28 @ X29 @ X27 @ X30) = (k7_relat_1 @ X27 @ X30)))),
% 1.01/1.20      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 1.01/1.20  thf('94', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         (((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 1.01/1.20          | ~ (v1_funct_1 @ sk_F))),
% 1.01/1.20      inference('sup-', [status(thm)], ['92', '93'])).
% 1.01/1.20  thf('95', plain, ((v1_funct_1 @ sk_F)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('96', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 1.01/1.20      inference('demod', [status(thm)], ['94', '95'])).
% 1.01/1.20  thf('97', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_B)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('98', plain, ((v1_funct_2 @ sk_E @ sk_C_2 @ sk_B)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('99', plain, ((v1_funct_1 @ sk_E)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('100', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('101', plain,
% 1.01/1.20      (((v1_xboole_0 @ sk_D)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_D)
% 1.01/1.20        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 1.01/1.20            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_C_2)
% 1.01/1.20            = (sk_E))
% 1.01/1.20        | ~ (v1_funct_2 @ 
% 1.01/1.20             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 1.01/1.20             (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B)
% 1.01/1.20        | ~ (v1_funct_1 @ 
% 1.01/1.20             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 1.01/1.20        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 1.01/1.20            != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_A))),
% 1.01/1.20      inference('demod', [status(thm)],
% 1.01/1.20                ['58', '59', '60', '61', '62', '65', '84', '89', '90', '91', 
% 1.01/1.20                 '96', '97', '98', '99', '100'])).
% 1.01/1.20  thf('102', plain,
% 1.01/1.20      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 1.01/1.20        | ~ (v1_funct_1 @ 
% 1.01/1.20             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 1.01/1.20        | ~ (v1_funct_2 @ 
% 1.01/1.20             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 1.01/1.20             (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B)
% 1.01/1.20        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 1.01/1.20            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_C_2)
% 1.01/1.20            = (sk_E))
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_D))),
% 1.01/1.20      inference('simplify', [status(thm)], ['101'])).
% 1.01/1.20  thf('103', plain,
% 1.01/1.20      (((v1_xboole_0 @ sk_D)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | (v1_xboole_0 @ sk_D)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 1.01/1.20            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_C_2)
% 1.01/1.20            = (sk_E))
% 1.01/1.20        | ~ (v1_funct_1 @ 
% 1.01/1.20             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 1.01/1.20        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 1.01/1.20            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['40', '102'])).
% 1.01/1.20  thf('104', plain,
% 1.01/1.20      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 1.01/1.20        | ~ (v1_funct_1 @ 
% 1.01/1.20             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 1.01/1.20        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 1.01/1.20            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_C_2)
% 1.01/1.20            = (sk_E))
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_D))),
% 1.01/1.20      inference('simplify', [status(thm)], ['103'])).
% 1.01/1.20  thf('105', plain,
% 1.01/1.20      ((((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ 
% 1.01/1.20          (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 1.01/1.20          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 1.01/1.20              (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))
% 1.01/1.20        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 1.01/1.20            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_C_2)
% 1.01/1.20            != (sk_E))
% 1.01/1.20        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 1.01/1.20            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.01/1.20            != (sk_F)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('106', plain,
% 1.01/1.20      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 1.01/1.20          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_C_2)
% 1.01/1.20          != (sk_E)))
% 1.01/1.20         <= (~
% 1.01/1.20             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 1.01/1.20                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 1.01/1.20                sk_C_2) = (sk_E))))),
% 1.01/1.20      inference('split', [status(esa)], ['105'])).
% 1.01/1.20  thf('107', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         (~ (v1_relat_1 @ X0)
% 1.01/1.20          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['7', '8'])).
% 1.01/1.20  thf('108', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         (~ (v1_relat_1 @ X0)
% 1.01/1.20          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['7', '8'])).
% 1.01/1.20  thf('109', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 1.01/1.20      inference('demod', [status(thm)], ['94', '95'])).
% 1.01/1.20  thf('110', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 1.01/1.20      inference('sup-', [status(thm)], ['63', '64'])).
% 1.01/1.20  thf('111', plain,
% 1.01/1.20      ((((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ 
% 1.01/1.20          (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 1.01/1.20          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 1.01/1.20              (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))))
% 1.01/1.20         <= (~
% 1.01/1.20             (((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ 
% 1.01/1.20                (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 1.01/1.20                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 1.01/1.20                   (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))))),
% 1.01/1.20      inference('split', [status(esa)], ['105'])).
% 1.01/1.20  thf('112', plain,
% 1.01/1.20      ((((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ 
% 1.01/1.20          (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 1.01/1.20          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C_2 @ sk_D))))
% 1.01/1.20         <= (~
% 1.01/1.20             (((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ 
% 1.01/1.20                (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 1.01/1.20                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 1.01/1.20                   (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))))),
% 1.01/1.20      inference('sup-', [status(thm)], ['110', '111'])).
% 1.01/1.20  thf('113', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 1.01/1.20      inference('sup-', [status(thm)], ['63', '64'])).
% 1.01/1.20  thf('114', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_C_2 @ sk_D))),
% 1.01/1.20      inference('demod', [status(thm)], ['76', '83'])).
% 1.01/1.20  thf('115', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_C_2 @ sk_D))),
% 1.01/1.20      inference('demod', [status(thm)], ['76', '83'])).
% 1.01/1.20  thf('116', plain,
% 1.01/1.20      ((((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ k1_xboole_0)
% 1.01/1.20          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ k1_xboole_0)))
% 1.01/1.20         <= (~
% 1.01/1.20             (((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ 
% 1.01/1.20                (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 1.01/1.20                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 1.01/1.20                   (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))))),
% 1.01/1.20      inference('demod', [status(thm)], ['112', '113', '114', '115'])).
% 1.01/1.20  thf('117', plain,
% 1.01/1.20      ((((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ k1_xboole_0)
% 1.01/1.20          != (k7_relat_1 @ sk_F @ k1_xboole_0)))
% 1.01/1.20         <= (~
% 1.01/1.20             (((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ 
% 1.01/1.20                (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 1.01/1.20                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 1.01/1.20                   (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))))),
% 1.01/1.20      inference('sup-', [status(thm)], ['109', '116'])).
% 1.01/1.20  thf('118', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         ((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 1.01/1.20      inference('demod', [status(thm)], ['87', '88'])).
% 1.01/1.20  thf('119', plain,
% 1.01/1.20      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0)))
% 1.01/1.20         <= (~
% 1.01/1.20             (((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ 
% 1.01/1.20                (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 1.01/1.20                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 1.01/1.20                   (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))))),
% 1.01/1.20      inference('demod', [status(thm)], ['117', '118'])).
% 1.01/1.20  thf('120', plain,
% 1.01/1.20      (((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 1.01/1.20         | ~ (v1_relat_1 @ sk_F)))
% 1.01/1.20         <= (~
% 1.01/1.20             (((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ 
% 1.01/1.20                (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 1.01/1.20                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 1.01/1.20                   (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))))),
% 1.01/1.20      inference('sup-', [status(thm)], ['108', '119'])).
% 1.01/1.20  thf('121', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf(cc1_relset_1, axiom,
% 1.01/1.20    (![A:$i,B:$i,C:$i]:
% 1.01/1.20     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 1.01/1.20       ( v1_relat_1 @ C ) ))).
% 1.01/1.20  thf('122', plain,
% 1.01/1.20      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.01/1.20         ((v1_relat_1 @ X24)
% 1.01/1.20          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 1.01/1.20      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.01/1.20  thf('123', plain, ((v1_relat_1 @ sk_F)),
% 1.01/1.20      inference('sup-', [status(thm)], ['121', '122'])).
% 1.01/1.20  thf('124', plain,
% 1.01/1.20      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0)))
% 1.01/1.20         <= (~
% 1.01/1.20             (((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ 
% 1.01/1.20                (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 1.01/1.20                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 1.01/1.20                   (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))))),
% 1.01/1.20      inference('demod', [status(thm)], ['120', '123'])).
% 1.01/1.20  thf('125', plain,
% 1.01/1.20      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_E)))
% 1.01/1.20         <= (~
% 1.01/1.20             (((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ 
% 1.01/1.20                (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 1.01/1.20                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 1.01/1.20                   (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))))),
% 1.01/1.20      inference('sup-', [status(thm)], ['107', '124'])).
% 1.01/1.20  thf('126', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_B)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('127', plain,
% 1.01/1.20      (![X24 : $i, X25 : $i, X26 : $i]:
% 1.01/1.20         ((v1_relat_1 @ X24)
% 1.01/1.20          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 1.01/1.20      inference('cnf', [status(esa)], [cc1_relset_1])).
% 1.01/1.20  thf('128', plain, ((v1_relat_1 @ sk_E)),
% 1.01/1.20      inference('sup-', [status(thm)], ['126', '127'])).
% 1.01/1.20  thf('129', plain,
% 1.01/1.20      ((((k1_xboole_0) != (k1_xboole_0)))
% 1.01/1.20         <= (~
% 1.01/1.20             (((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ 
% 1.01/1.20                (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 1.01/1.20                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 1.01/1.20                   (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))))),
% 1.01/1.20      inference('demod', [status(thm)], ['125', '128'])).
% 1.01/1.20  thf('130', plain,
% 1.01/1.20      ((((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ 
% 1.01/1.20          (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 1.01/1.20          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 1.01/1.20             (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))))),
% 1.01/1.20      inference('simplify', [status(thm)], ['129'])).
% 1.01/1.20  thf('131', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         (~ (v1_relat_1 @ X0)
% 1.01/1.20          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['7', '8'])).
% 1.01/1.20  thf('132', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         (~ (v1_relat_1 @ X0)
% 1.01/1.20          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['7', '8'])).
% 1.01/1.20  thf('133', plain,
% 1.01/1.20      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_D))),
% 1.01/1.20      inference('demod', [status(thm)], ['23', '24'])).
% 1.01/1.20  thf('134', plain,
% 1.01/1.20      (((v1_funct_2 @ 
% 1.01/1.20         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 1.01/1.20         (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_D))),
% 1.01/1.20      inference('demod', [status(thm)], ['38', '39'])).
% 1.01/1.20  thf('135', plain,
% 1.01/1.20      (((m1_subset_1 @ 
% 1.01/1.20         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 1.01/1.20         (k1_zfmisc_1 @ 
% 1.01/1.20          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B)))
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_D))),
% 1.01/1.20      inference('demod', [status(thm)], ['53', '54'])).
% 1.01/1.20  thf('136', plain,
% 1.01/1.20      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 1.01/1.20         ((v1_xboole_0 @ X31)
% 1.01/1.20          | (v1_xboole_0 @ X32)
% 1.01/1.20          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 1.01/1.20          | ~ (v1_funct_1 @ X34)
% 1.01/1.20          | ~ (v1_funct_2 @ X34 @ X32 @ X31)
% 1.01/1.20          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 1.01/1.20          | ((X37) != (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34))
% 1.01/1.20          | ((k2_partfun1 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31 @ X37 @ X32)
% 1.01/1.20              = (X34))
% 1.01/1.20          | ~ (m1_subset_1 @ X37 @ 
% 1.01/1.20               (k1_zfmisc_1 @ 
% 1.01/1.20                (k2_zfmisc_1 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31)))
% 1.01/1.20          | ~ (v1_funct_2 @ X37 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31)
% 1.01/1.20          | ~ (v1_funct_1 @ X37)
% 1.01/1.20          | ((k2_partfun1 @ X36 @ X31 @ X35 @ (k9_subset_1 @ X33 @ X36 @ X32))
% 1.01/1.20              != (k2_partfun1 @ X32 @ X31 @ X34 @ 
% 1.01/1.20                  (k9_subset_1 @ X33 @ X36 @ X32)))
% 1.01/1.20          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X31)))
% 1.01/1.20          | ~ (v1_funct_2 @ X35 @ X36 @ X31)
% 1.01/1.20          | ~ (v1_funct_1 @ X35)
% 1.01/1.20          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X33))
% 1.01/1.20          | (v1_xboole_0 @ X36)
% 1.01/1.20          | (v1_xboole_0 @ X33))),
% 1.01/1.20      inference('cnf', [status(esa)], [d1_tmap_1])).
% 1.01/1.20  thf('137', plain,
% 1.01/1.20      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 1.01/1.20         ((v1_xboole_0 @ X33)
% 1.01/1.20          | (v1_xboole_0 @ X36)
% 1.01/1.20          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X33))
% 1.01/1.20          | ~ (v1_funct_1 @ X35)
% 1.01/1.20          | ~ (v1_funct_2 @ X35 @ X36 @ X31)
% 1.01/1.20          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X31)))
% 1.01/1.20          | ((k2_partfun1 @ X36 @ X31 @ X35 @ (k9_subset_1 @ X33 @ X36 @ X32))
% 1.01/1.20              != (k2_partfun1 @ X32 @ X31 @ X34 @ 
% 1.01/1.20                  (k9_subset_1 @ X33 @ X36 @ X32)))
% 1.01/1.20          | ~ (v1_funct_1 @ (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34))
% 1.01/1.20          | ~ (v1_funct_2 @ (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34) @ 
% 1.01/1.20               (k4_subset_1 @ X33 @ X36 @ X32) @ X31)
% 1.01/1.20          | ~ (m1_subset_1 @ (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34) @ 
% 1.01/1.20               (k1_zfmisc_1 @ 
% 1.01/1.20                (k2_zfmisc_1 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31)))
% 1.01/1.20          | ((k2_partfun1 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31 @ 
% 1.01/1.20              (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34) @ X32) = (
% 1.01/1.20              X34))
% 1.01/1.20          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 1.01/1.20          | ~ (v1_funct_2 @ X34 @ X32 @ X31)
% 1.01/1.20          | ~ (v1_funct_1 @ X34)
% 1.01/1.20          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 1.01/1.20          | (v1_xboole_0 @ X32)
% 1.01/1.20          | (v1_xboole_0 @ X31))),
% 1.01/1.20      inference('simplify', [status(thm)], ['136'])).
% 1.01/1.20  thf('138', plain,
% 1.01/1.20      (((v1_xboole_0 @ sk_D)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_D)
% 1.01/1.20        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 1.01/1.20        | ~ (v1_funct_1 @ sk_F)
% 1.01/1.20        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 1.01/1.20        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 1.01/1.20        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 1.01/1.20            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.01/1.20            = (sk_F))
% 1.01/1.20        | ~ (v1_funct_2 @ 
% 1.01/1.20             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 1.01/1.20             (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B)
% 1.01/1.20        | ~ (v1_funct_1 @ 
% 1.01/1.20             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 1.01/1.20        | ((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ 
% 1.01/1.20            (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 1.01/1.20            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 1.01/1.20                (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))
% 1.01/1.20        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_B)))
% 1.01/1.20        | ~ (v1_funct_2 @ sk_E @ sk_C_2 @ sk_B)
% 1.01/1.20        | ~ (v1_funct_1 @ sk_E)
% 1.01/1.20        | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_A))),
% 1.01/1.20      inference('sup-', [status(thm)], ['135', '137'])).
% 1.01/1.20  thf('139', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('140', plain, ((v1_funct_1 @ sk_F)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('141', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('142', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('143', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 1.01/1.20      inference('sup-', [status(thm)], ['63', '64'])).
% 1.01/1.20  thf('144', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_C_2 @ sk_D))),
% 1.01/1.20      inference('demod', [status(thm)], ['76', '83'])).
% 1.01/1.20  thf('145', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         ((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 1.01/1.20      inference('demod', [status(thm)], ['87', '88'])).
% 1.01/1.20  thf('146', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 1.01/1.20      inference('sup-', [status(thm)], ['63', '64'])).
% 1.01/1.20  thf('147', plain, (((k1_xboole_0) = (k3_xboole_0 @ sk_C_2 @ sk_D))),
% 1.01/1.20      inference('demod', [status(thm)], ['76', '83'])).
% 1.01/1.20  thf('148', plain,
% 1.01/1.20      (![X0 : $i]:
% 1.01/1.20         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 1.01/1.20      inference('demod', [status(thm)], ['94', '95'])).
% 1.01/1.20  thf('149', plain,
% 1.01/1.20      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_B)))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('150', plain, ((v1_funct_2 @ sk_E @ sk_C_2 @ sk_B)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('151', plain, ((v1_funct_1 @ sk_E)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('152', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('153', plain,
% 1.01/1.20      (((v1_xboole_0 @ sk_D)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_D)
% 1.01/1.20        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 1.01/1.20            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.01/1.20            = (sk_F))
% 1.01/1.20        | ~ (v1_funct_2 @ 
% 1.01/1.20             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 1.01/1.20             (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B)
% 1.01/1.20        | ~ (v1_funct_1 @ 
% 1.01/1.20             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 1.01/1.20        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 1.01/1.20            != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_A))),
% 1.01/1.20      inference('demod', [status(thm)],
% 1.01/1.20                ['138', '139', '140', '141', '142', '143', '144', '145', 
% 1.01/1.20                 '146', '147', '148', '149', '150', '151', '152'])).
% 1.01/1.20  thf('154', plain,
% 1.01/1.20      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 1.01/1.20        | ~ (v1_funct_1 @ 
% 1.01/1.20             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 1.01/1.20        | ~ (v1_funct_2 @ 
% 1.01/1.20             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 1.01/1.20             (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B)
% 1.01/1.20        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 1.01/1.20            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.01/1.20            = (sk_F))
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_D))),
% 1.01/1.20      inference('simplify', [status(thm)], ['153'])).
% 1.01/1.20  thf('155', plain,
% 1.01/1.20      (((v1_xboole_0 @ sk_D)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | (v1_xboole_0 @ sk_D)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 1.01/1.20            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.01/1.20            = (sk_F))
% 1.01/1.20        | ~ (v1_funct_1 @ 
% 1.01/1.20             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 1.01/1.20        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 1.01/1.20            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['134', '154'])).
% 1.01/1.20  thf('156', plain,
% 1.01/1.20      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 1.01/1.20        | ~ (v1_funct_1 @ 
% 1.01/1.20             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 1.01/1.20        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 1.01/1.20            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.01/1.20            = (sk_F))
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_D))),
% 1.01/1.20      inference('simplify', [status(thm)], ['155'])).
% 1.01/1.20  thf('157', plain,
% 1.01/1.20      (((v1_xboole_0 @ sk_D)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | (v1_xboole_0 @ sk_D)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 1.01/1.20            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.01/1.20            = (sk_F))
% 1.01/1.20        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 1.01/1.20            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['133', '156'])).
% 1.01/1.20  thf('158', plain,
% 1.01/1.20      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 1.01/1.20        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 1.01/1.20            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.01/1.20            = (sk_F))
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_D))),
% 1.01/1.20      inference('simplify', [status(thm)], ['157'])).
% 1.01/1.20  thf('159', plain,
% 1.01/1.20      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 1.01/1.20        | ~ (v1_relat_1 @ sk_F)
% 1.01/1.20        | (v1_xboole_0 @ sk_D)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 1.01/1.20            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.01/1.20            = (sk_F)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['132', '158'])).
% 1.01/1.20  thf('160', plain, ((v1_relat_1 @ sk_F)),
% 1.01/1.20      inference('sup-', [status(thm)], ['121', '122'])).
% 1.01/1.20  thf('161', plain,
% 1.01/1.20      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 1.01/1.20        | (v1_xboole_0 @ sk_D)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 1.01/1.20            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.01/1.20            = (sk_F)))),
% 1.01/1.20      inference('demod', [status(thm)], ['159', '160'])).
% 1.01/1.20  thf('162', plain,
% 1.01/1.20      ((((k1_xboole_0) != (k1_xboole_0))
% 1.01/1.20        | ~ (v1_relat_1 @ sk_E)
% 1.01/1.20        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 1.01/1.20            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.01/1.20            = (sk_F))
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_D))),
% 1.01/1.20      inference('sup-', [status(thm)], ['131', '161'])).
% 1.01/1.20  thf('163', plain, ((v1_relat_1 @ sk_E)),
% 1.01/1.20      inference('sup-', [status(thm)], ['126', '127'])).
% 1.01/1.20  thf('164', plain,
% 1.01/1.20      ((((k1_xboole_0) != (k1_xboole_0))
% 1.01/1.20        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 1.01/1.20            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.01/1.20            = (sk_F))
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_D))),
% 1.01/1.20      inference('demod', [status(thm)], ['162', '163'])).
% 1.01/1.20  thf('165', plain,
% 1.01/1.20      (((v1_xboole_0 @ sk_D)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 1.01/1.20            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.01/1.20            = (sk_F)))),
% 1.01/1.20      inference('simplify', [status(thm)], ['164'])).
% 1.01/1.20  thf('166', plain,
% 1.01/1.20      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 1.01/1.20          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.01/1.20          != (sk_F)))
% 1.01/1.20         <= (~
% 1.01/1.20             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 1.01/1.20                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.01/1.20                = (sk_F))))),
% 1.01/1.20      inference('split', [status(esa)], ['105'])).
% 1.01/1.20  thf('167', plain,
% 1.01/1.20      (((((sk_F) != (sk_F))
% 1.01/1.20         | (v1_xboole_0 @ sk_A)
% 1.01/1.20         | (v1_xboole_0 @ sk_B)
% 1.01/1.20         | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20         | (v1_xboole_0 @ sk_D)))
% 1.01/1.20         <= (~
% 1.01/1.20             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 1.01/1.20                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.01/1.20                = (sk_F))))),
% 1.01/1.20      inference('sup-', [status(thm)], ['165', '166'])).
% 1.01/1.20  thf('168', plain,
% 1.01/1.20      ((((v1_xboole_0 @ sk_D)
% 1.01/1.20         | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20         | (v1_xboole_0 @ sk_B)
% 1.01/1.20         | (v1_xboole_0 @ sk_A)))
% 1.01/1.20         <= (~
% 1.01/1.20             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 1.01/1.20                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.01/1.20                = (sk_F))))),
% 1.01/1.20      inference('simplify', [status(thm)], ['167'])).
% 1.01/1.20  thf('169', plain, (~ (v1_xboole_0 @ sk_D)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('170', plain,
% 1.01/1.20      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_C_2)))
% 1.01/1.20         <= (~
% 1.01/1.20             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 1.01/1.20                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.01/1.20                = (sk_F))))),
% 1.01/1.20      inference('sup-', [status(thm)], ['168', '169'])).
% 1.01/1.20  thf('171', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('172', plain,
% 1.01/1.20      ((((v1_xboole_0 @ sk_C_2) | (v1_xboole_0 @ sk_B)))
% 1.01/1.20         <= (~
% 1.01/1.20             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 1.01/1.20                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.01/1.20                = (sk_F))))),
% 1.01/1.20      inference('clc', [status(thm)], ['170', '171'])).
% 1.01/1.20  thf('173', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('174', plain,
% 1.01/1.20      (((v1_xboole_0 @ sk_B))
% 1.01/1.20         <= (~
% 1.01/1.20             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 1.01/1.20                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.01/1.20                = (sk_F))))),
% 1.01/1.20      inference('clc', [status(thm)], ['172', '173'])).
% 1.01/1.20  thf('175', plain, (~ (v1_xboole_0 @ sk_B)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('176', plain,
% 1.01/1.20      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 1.01/1.20          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.01/1.20          = (sk_F)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['174', '175'])).
% 1.01/1.20  thf('177', plain,
% 1.01/1.20      (~
% 1.01/1.20       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 1.01/1.20          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_C_2)
% 1.01/1.20          = (sk_E))) | 
% 1.01/1.20       ~
% 1.01/1.20       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 1.01/1.20          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 1.01/1.20          = (sk_F))) | 
% 1.01/1.20       ~
% 1.01/1.20       (((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ 
% 1.01/1.20          (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 1.01/1.20          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 1.01/1.20             (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))))),
% 1.01/1.20      inference('split', [status(esa)], ['105'])).
% 1.01/1.20  thf('178', plain,
% 1.01/1.20      (~
% 1.01/1.20       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 1.01/1.20          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_C_2)
% 1.01/1.20          = (sk_E)))),
% 1.01/1.20      inference('sat_resolution*', [status(thm)], ['130', '176', '177'])).
% 1.01/1.20  thf('179', plain,
% 1.01/1.20      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 1.01/1.20         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_C_2)
% 1.01/1.20         != (sk_E))),
% 1.01/1.20      inference('simpl_trail', [status(thm)], ['106', '178'])).
% 1.01/1.20  thf('180', plain,
% 1.01/1.20      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 1.01/1.20        | ~ (v1_funct_1 @ 
% 1.01/1.20             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_D))),
% 1.01/1.20      inference('simplify_reflect-', [status(thm)], ['104', '179'])).
% 1.01/1.20  thf('181', plain,
% 1.01/1.20      (((v1_xboole_0 @ sk_D)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | (v1_xboole_0 @ sk_D)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 1.01/1.20            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 1.01/1.20      inference('sup-', [status(thm)], ['25', '180'])).
% 1.01/1.20  thf('182', plain,
% 1.01/1.20      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_D))),
% 1.01/1.20      inference('simplify', [status(thm)], ['181'])).
% 1.01/1.20  thf('183', plain,
% 1.01/1.20      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 1.01/1.20        | ~ (v1_relat_1 @ sk_F)
% 1.01/1.20        | (v1_xboole_0 @ sk_D)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_A))),
% 1.01/1.20      inference('sup-', [status(thm)], ['10', '182'])).
% 1.01/1.20  thf('184', plain, ((v1_relat_1 @ sk_F)),
% 1.01/1.20      inference('sup-', [status(thm)], ['121', '122'])).
% 1.01/1.20  thf('185', plain,
% 1.01/1.20      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 1.01/1.20        | (v1_xboole_0 @ sk_D)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_A))),
% 1.01/1.20      inference('demod', [status(thm)], ['183', '184'])).
% 1.01/1.20  thf('186', plain,
% 1.01/1.20      ((((k1_xboole_0) != (k1_xboole_0))
% 1.01/1.20        | ~ (v1_relat_1 @ sk_E)
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_D))),
% 1.01/1.20      inference('sup-', [status(thm)], ['9', '185'])).
% 1.01/1.20  thf('187', plain, ((v1_relat_1 @ sk_E)),
% 1.01/1.20      inference('sup-', [status(thm)], ['126', '127'])).
% 1.01/1.20  thf('188', plain,
% 1.01/1.20      ((((k1_xboole_0) != (k1_xboole_0))
% 1.01/1.20        | (v1_xboole_0 @ sk_A)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_D))),
% 1.01/1.20      inference('demod', [status(thm)], ['186', '187'])).
% 1.01/1.20  thf('189', plain,
% 1.01/1.20      (((v1_xboole_0 @ sk_D)
% 1.01/1.20        | (v1_xboole_0 @ sk_C_2)
% 1.01/1.20        | (v1_xboole_0 @ sk_B)
% 1.01/1.20        | (v1_xboole_0 @ sk_A))),
% 1.01/1.20      inference('simplify', [status(thm)], ['188'])).
% 1.01/1.20  thf('190', plain, (~ (v1_xboole_0 @ sk_D)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('191', plain,
% 1.01/1.20      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_C_2))),
% 1.01/1.20      inference('sup-', [status(thm)], ['189', '190'])).
% 1.01/1.20  thf('192', plain, (~ (v1_xboole_0 @ sk_A)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('193', plain, (((v1_xboole_0 @ sk_C_2) | (v1_xboole_0 @ sk_B))),
% 1.01/1.20      inference('clc', [status(thm)], ['191', '192'])).
% 1.01/1.20  thf('194', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 1.01/1.20      inference('cnf', [status(esa)], [zf_stmt_0])).
% 1.01/1.20  thf('195', plain, ((v1_xboole_0 @ sk_B)),
% 1.01/1.20      inference('clc', [status(thm)], ['193', '194'])).
% 1.01/1.20  thf('196', plain, ($false), inference('demod', [status(thm)], ['0', '195'])).
% 1.01/1.20  
% 1.01/1.20  % SZS output end Refutation
% 1.01/1.20  
% 1.01/1.20  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
