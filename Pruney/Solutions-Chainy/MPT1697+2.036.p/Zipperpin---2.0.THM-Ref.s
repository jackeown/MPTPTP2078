%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.M7CGHqLMVj

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:58 EST 2020

% Result     : Theorem 7.88s
% Output     : Refutation 7.88s
% Verified   : 
% Statistics : Number of formulae       :  223 ( 658 expanded)
%              Number of leaves         :   37 ( 206 expanded)
%              Depth                    :   42
%              Number of atoms          : 3821 (27953 expanded)
%              Number of equality atoms :  123 ( 871 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

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
    ! [X5: $i,X6: $i] :
      ( ( r1_xboole_0 @ X5 @ X6 )
      | ( r2_hidden @ ( sk_C @ X6 @ X5 ) @ X5 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t187_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
         => ( ( k7_relat_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('4',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( r1_xboole_0 @ X20 @ ( k1_relat_1 @ X21 ) )
      | ( ( k7_relat_1 @ X21 @ X20 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_B_1 ) ) ),
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

thf('10',plain,(
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

thf('11',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_tmap_1 @ X2 @ sk_B_1 @ sk_C_2 @ X1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C_2 )
      | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_2 @ sk_E @ sk_C_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_tmap_1 @ X2 @ sk_B_1 @ sk_C_2 @ X1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C_2 )
      | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_2 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B_1 )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['8','14'])).

thf('16',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_2 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['7','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
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

thf('26',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ ( k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_2 @ X0 @ sk_E @ X2 ) @ ( k4_subset_1 @ X1 @ sk_C_2 @ X0 ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C_2 )
      | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_2 @ sk_E @ sk_C_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ ( k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_2 @ X0 @ sk_E @ X2 ) @ ( k4_subset_1 @ X1 @ sk_C_2 @ X0 ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C_2 )
      | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_2 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B_1 )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ X0 @ sk_C_2 @ sk_D ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','29'])).

thf('31',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_2 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ X0 @ sk_C_2 @ sk_D ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['22','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
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

thf('41',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_2 @ X0 @ sk_E @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X1 @ sk_C_2 @ X0 ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C_2 )
      | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C_2 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ sk_E @ sk_C_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_2 @ X0 @ sk_E @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X1 @ sk_C_2 @ X0 ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C_2 )
      | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_2 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B_1 )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C_2 @ sk_D ) @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['38','44'])).

thf('46',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_2 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C_2 @ sk_D ) @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['37','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['49','50'])).

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

thf('52',plain,(
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

thf('53',plain,(
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
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_C_2 )
      = sk_E )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_E @ sk_C_2 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['51','53'])).

thf('55',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('60',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( ( k9_subset_1 @ X17 @ X15 @ X16 )
        = ( k3_xboole_0 @ X15 @ X16 ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('63',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ( ( k2_partfun1 @ X28 @ X29 @ X27 @ X30 )
        = ( k7_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('68',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ( ( k2_partfun1 @ X28 @ X29 @ X27 @ X30 )
        = ( k7_relat_1 @ X27 @ X30 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('73',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ sk_E @ sk_C_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_C_2 )
      = sk_E )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k7_relat_1 @ sk_E @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) ) )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55','56','57','58','61','66','67','72','73','74','75','76'])).

thf('78',plain,
    ( ( ( k7_relat_1 @ sk_E @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_C_2 )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['77'])).

thf('79',plain,
    ( ( ( k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_C_2 )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_C_2 )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_C_2 )
     != sk_E ) ),
    inference(split,[status(esa)],['79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('84',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('85',plain,
    ( ( ( k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) ) ),
    inference(split,[status(esa)],['79'])).

thf('86',plain,
    ( ( ( k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('88',plain,
    ( ( ( k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,
    ( ( ( k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['83','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('91',plain,
    ( ( ( k7_relat_1 @ sk_E @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['89','90'])).

thf('92',plain,
    ( ( ( ( k7_relat_1 @ sk_E @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_F )
      | ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['82','91'])).

thf('93',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('94',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('95',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    r1_subset_1 @ sk_C_2 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r1_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ( ( r1_subset_1 @ A @ B )
      <=> ( r1_xboole_0 @ A @ B ) ) ) )).

thf('97',plain,(
    ! [X22: $i,X23: $i] :
      ( ( v1_xboole_0 @ X22 )
      | ( v1_xboole_0 @ X23 )
      | ( r1_xboole_0 @ X22 @ X23 )
      | ~ ( r1_subset_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_subset_1])).

thf('98',plain,
    ( ( r1_xboole_0 @ sk_C_2 @ sk_D )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( r1_xboole_0 @ sk_C_2 @ sk_D ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_D ),
    inference(clc,[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('104',plain,(
    ! [X9: $i,X11: $i,X12: $i] :
      ( ~ ( r2_hidden @ X11 @ ( k3_xboole_0 @ X9 @ X12 ) )
      | ~ ( r1_xboole_0 @ X9 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('105',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    v1_xboole_0 @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('107',plain,
    ( ( ( k7_relat_1 @ sk_E @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) )
     != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['92','95','106'])).

thf('108',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['81','107'])).

thf('109',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    ! [X24: $i,X25: $i,X26: $i] :
      ( ( v1_relat_1 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('111',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['109','110'])).

thf('112',plain,(
    v1_xboole_0 @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('113',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['108','111','112'])).

thf('114',plain,
    ( ( k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['113'])).

thf('115',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ X1 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('117',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('118',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('119',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('120',plain,(
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

thf('121',plain,(
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
    inference(simplify,[status(thm)],['120'])).

thf('122',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_E @ sk_C_2 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['119','121'])).

thf('123',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['64','65'])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['70','71'])).

thf('131',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    v1_funct_2 @ sk_E @ sk_C_2 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k7_relat_1 @ sk_E @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) ) )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['122','123','124','125','126','127','128','129','130','131','132','133','134'])).

thf('136',plain,
    ( ( ( k7_relat_1 @ sk_E @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['135'])).

thf('137',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k7_relat_1 @ sk_E @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['118','136'])).

thf('138',plain,
    ( ( ( k7_relat_1 @ sk_E @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['137'])).

thf('139',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( ( k7_relat_1 @ sk_E @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['117','138'])).

thf('140',plain,
    ( ( ( k7_relat_1 @ sk_E @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,
    ( ( ( k7_relat_1 @ sk_E @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F )
    | ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference('sup-',[status(thm)],['116','140'])).

thf('142',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['93','94'])).

thf('143',plain,(
    v1_xboole_0 @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('144',plain,
    ( ( ( k7_relat_1 @ sk_E @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) )
     != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference(demod,[status(thm)],['141','142','143'])).

thf('145',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['115','144'])).

thf('146',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['109','110'])).

thf('147',plain,(
    v1_xboole_0 @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('148',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['145','146','147'])).

thf('149',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference(simplify,[status(thm)],['148'])).

thf('150',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['79'])).

thf('151',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C_2 )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['149','150'])).

thf('152',plain,
    ( ( ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C_2 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C_2 ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( ( v1_xboole_0 @ sk_C_2 )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['154','155'])).

thf('157',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('159',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['158','159'])).

thf('161',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_C_2 )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) ) ),
    inference(split,[status(esa)],['79'])).

thf('162',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_C_2 )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['114','160','161'])).

thf('163',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_C_2 )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['80','162'])).

thf('164',plain,
    ( ( ( k7_relat_1 @ sk_E @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['78','163'])).

thf('165',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k7_relat_1 @ sk_E @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['36','164'])).

thf('166',plain,
    ( ( ( k7_relat_1 @ sk_E @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k7_relat_1 @ sk_E @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['21','166'])).

thf('168',plain,
    ( ( ( k7_relat_1 @ sk_E @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,
    ( ( ( k7_relat_1 @ sk_E @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F )
    | ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','168'])).

thf('170',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['93','94'])).

thf('171',plain,(
    v1_xboole_0 @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('172',plain,
    ( ( ( k7_relat_1 @ sk_E @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) )
     != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['169','170','171'])).

thf('173',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_xboole_0 @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','172'])).

thf('174',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['109','110'])).

thf('175',plain,(
    v1_xboole_0 @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) ),
    inference('sup-',[status(thm)],['102','105'])).

thf('176',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['173','174','175'])).

thf('177',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['176'])).

thf('178',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['177','178'])).

thf('180',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['179','180'])).

thf('182',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(clc,[status(thm)],['181','182'])).

thf('184',plain,(
    $false ),
    inference(demod,[status(thm)],['0','183'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.M7CGHqLMVj
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:46:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 7.88/8.08  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 7.88/8.08  % Solved by: fo/fo7.sh
% 7.88/8.08  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 7.88/8.08  % done 4528 iterations in 7.596s
% 7.88/8.08  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 7.88/8.08  % SZS output start Refutation
% 7.88/8.08  thf(sk_B_1_type, type, sk_B_1: $i).
% 7.88/8.08  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 7.88/8.08  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 7.88/8.08  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 7.88/8.08  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 7.88/8.08  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 7.88/8.08  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 7.88/8.08  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 7.88/8.08  thf(sk_D_type, type, sk_D: $i).
% 7.88/8.08  thf(sk_A_type, type, sk_A: $i).
% 7.88/8.08  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 7.88/8.08  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 7.88/8.08  thf(sk_B_type, type, sk_B: $i > $i).
% 7.88/8.08  thf(sk_C_2_type, type, sk_C_2: $i).
% 7.88/8.08  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 7.88/8.08  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 7.88/8.08  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 7.88/8.08  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 7.88/8.08  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 7.88/8.08  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 7.88/8.08  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 7.88/8.08  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 7.88/8.08  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 7.88/8.08  thf(sk_F_type, type, sk_F: $i).
% 7.88/8.08  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 7.88/8.08  thf(sk_E_type, type, sk_E: $i).
% 7.88/8.08  thf(t6_tmap_1, conjecture,
% 7.88/8.08    (![A:$i]:
% 7.88/8.08     ( ( ~( v1_xboole_0 @ A ) ) =>
% 7.88/8.08       ( ![B:$i]:
% 7.88/8.08         ( ( ~( v1_xboole_0 @ B ) ) =>
% 7.88/8.08           ( ![C:$i]:
% 7.88/8.08             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 7.88/8.08                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 7.88/8.08               ( ![D:$i]:
% 7.88/8.08                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 7.88/8.08                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 7.88/8.08                   ( ( r1_subset_1 @ C @ D ) =>
% 7.88/8.08                     ( ![E:$i]:
% 7.88/8.08                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 7.88/8.08                           ( m1_subset_1 @
% 7.88/8.08                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 7.88/8.08                         ( ![F:$i]:
% 7.88/8.08                           ( ( ( v1_funct_1 @ F ) & 
% 7.88/8.08                               ( v1_funct_2 @ F @ D @ B ) & 
% 7.88/8.08                               ( m1_subset_1 @
% 7.88/8.08                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 7.88/8.08                             ( ( ( k2_partfun1 @
% 7.88/8.08                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 7.88/8.08                                 ( k2_partfun1 @
% 7.88/8.08                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 7.88/8.08                               ( ( k2_partfun1 @
% 7.88/8.08                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 7.88/8.08                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 7.88/8.08                                 ( E ) ) & 
% 7.88/8.08                               ( ( k2_partfun1 @
% 7.88/8.08                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 7.88/8.08                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 7.88/8.08                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 7.88/8.08  thf(zf_stmt_0, negated_conjecture,
% 7.88/8.08    (~( ![A:$i]:
% 7.88/8.08        ( ( ~( v1_xboole_0 @ A ) ) =>
% 7.88/8.08          ( ![B:$i]:
% 7.88/8.08            ( ( ~( v1_xboole_0 @ B ) ) =>
% 7.88/8.08              ( ![C:$i]:
% 7.88/8.08                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 7.88/8.08                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 7.88/8.08                  ( ![D:$i]:
% 7.88/8.08                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 7.88/8.08                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 7.88/8.08                      ( ( r1_subset_1 @ C @ D ) =>
% 7.88/8.08                        ( ![E:$i]:
% 7.88/8.08                          ( ( ( v1_funct_1 @ E ) & 
% 7.88/8.08                              ( v1_funct_2 @ E @ C @ B ) & 
% 7.88/8.08                              ( m1_subset_1 @
% 7.88/8.08                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 7.88/8.08                            ( ![F:$i]:
% 7.88/8.08                              ( ( ( v1_funct_1 @ F ) & 
% 7.88/8.08                                  ( v1_funct_2 @ F @ D @ B ) & 
% 7.88/8.08                                  ( m1_subset_1 @
% 7.88/8.08                                    F @ 
% 7.88/8.08                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 7.88/8.08                                ( ( ( k2_partfun1 @
% 7.88/8.08                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 7.88/8.08                                    ( k2_partfun1 @
% 7.88/8.08                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 7.88/8.08                                  ( ( k2_partfun1 @
% 7.88/8.08                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 7.88/8.08                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 7.88/8.08                                    ( E ) ) & 
% 7.88/8.08                                  ( ( k2_partfun1 @
% 7.88/8.08                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 7.88/8.08                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 7.88/8.08                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 7.88/8.08    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 7.88/8.08  thf('0', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 7.88/8.08      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.08  thf(t3_xboole_0, axiom,
% 7.88/8.08    (![A:$i,B:$i]:
% 7.88/8.08     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 7.88/8.08            ( r1_xboole_0 @ A @ B ) ) ) & 
% 7.88/8.08       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 7.88/8.08            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 7.88/8.08  thf('1', plain,
% 7.88/8.08      (![X5 : $i, X6 : $i]:
% 7.88/8.08         ((r1_xboole_0 @ X5 @ X6) | (r2_hidden @ (sk_C @ X6 @ X5) @ X5))),
% 7.88/8.08      inference('cnf', [status(esa)], [t3_xboole_0])).
% 7.88/8.08  thf(d1_xboole_0, axiom,
% 7.88/8.08    (![A:$i]:
% 7.88/8.08     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 7.88/8.08  thf('2', plain,
% 7.88/8.08      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 7.88/8.08      inference('cnf', [status(esa)], [d1_xboole_0])).
% 7.88/8.08  thf('3', plain,
% 7.88/8.08      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X0 @ X1) | ~ (v1_xboole_0 @ X0))),
% 7.88/8.08      inference('sup-', [status(thm)], ['1', '2'])).
% 7.88/8.08  thf(t187_relat_1, axiom,
% 7.88/8.09    (![A:$i]:
% 7.88/8.09     ( ( v1_relat_1 @ A ) =>
% 7.88/8.09       ( ![B:$i]:
% 7.88/8.09         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 7.88/8.09           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 7.88/8.09  thf('4', plain,
% 7.88/8.09      (![X20 : $i, X21 : $i]:
% 7.88/8.09         (~ (r1_xboole_0 @ X20 @ (k1_relat_1 @ X21))
% 7.88/8.09          | ((k7_relat_1 @ X21 @ X20) = (k1_xboole_0))
% 7.88/8.09          | ~ (v1_relat_1 @ X21))),
% 7.88/8.09      inference('cnf', [status(esa)], [t187_relat_1])).
% 7.88/8.09  thf('5', plain,
% 7.88/8.09      (![X0 : $i, X1 : $i]:
% 7.88/8.09         (~ (v1_xboole_0 @ X1)
% 7.88/8.09          | ~ (v1_relat_1 @ X0)
% 7.88/8.09          | ((k7_relat_1 @ X0 @ X1) = (k1_xboole_0)))),
% 7.88/8.09      inference('sup-', [status(thm)], ['3', '4'])).
% 7.88/8.09  thf('6', plain,
% 7.88/8.09      (![X0 : $i, X1 : $i]:
% 7.88/8.09         (~ (v1_xboole_0 @ X1)
% 7.88/8.09          | ~ (v1_relat_1 @ X0)
% 7.88/8.09          | ((k7_relat_1 @ X0 @ X1) = (k1_xboole_0)))),
% 7.88/8.09      inference('sup-', [status(thm)], ['3', '4'])).
% 7.88/8.09  thf('7', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('8', plain,
% 7.88/8.09      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('9', plain,
% 7.88/8.09      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_B_1)))),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf(dt_k1_tmap_1, axiom,
% 7.88/8.09    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 7.88/8.09     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 7.88/8.09         ( ~( v1_xboole_0 @ C ) ) & 
% 7.88/8.09         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 7.88/8.09         ( ~( v1_xboole_0 @ D ) ) & 
% 7.88/8.09         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 7.88/8.09         ( v1_funct_2 @ E @ C @ B ) & 
% 7.88/8.09         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 7.88/8.09         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 7.88/8.09         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 7.88/8.09       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 7.88/8.09         ( v1_funct_2 @
% 7.88/8.09           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 7.88/8.09           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 7.88/8.09         ( m1_subset_1 @
% 7.88/8.09           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 7.88/8.09           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 7.88/8.09  thf('10', plain,
% 7.88/8.09      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 7.88/8.09         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 7.88/8.09          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 7.88/8.09          | ~ (v1_funct_1 @ X38)
% 7.88/8.09          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 7.88/8.09          | (v1_xboole_0 @ X41)
% 7.88/8.09          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X42))
% 7.88/8.09          | (v1_xboole_0 @ X39)
% 7.88/8.09          | (v1_xboole_0 @ X40)
% 7.88/8.09          | (v1_xboole_0 @ X42)
% 7.88/8.09          | ~ (v1_funct_1 @ X43)
% 7.88/8.09          | ~ (v1_funct_2 @ X43 @ X41 @ X40)
% 7.88/8.09          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 7.88/8.09          | (v1_funct_1 @ (k1_tmap_1 @ X42 @ X40 @ X39 @ X41 @ X38 @ X43)))),
% 7.88/8.09      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 7.88/8.09  thf('11', plain,
% 7.88/8.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.88/8.09         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B_1 @ sk_C_2 @ X1 @ sk_E @ X0))
% 7.88/8.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 7.88/8.09          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 7.88/8.09          | ~ (v1_funct_1 @ X0)
% 7.88/8.09          | (v1_xboole_0 @ X2)
% 7.88/8.09          | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09          | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X2))
% 7.88/8.09          | (v1_xboole_0 @ X1)
% 7.88/8.09          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 7.88/8.09          | ~ (v1_funct_1 @ sk_E)
% 7.88/8.09          | ~ (v1_funct_2 @ sk_E @ sk_C_2 @ sk_B_1))),
% 7.88/8.09      inference('sup-', [status(thm)], ['9', '10'])).
% 7.88/8.09  thf('12', plain, ((v1_funct_1 @ sk_E)),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('13', plain, ((v1_funct_2 @ sk_E @ sk_C_2 @ sk_B_1)),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('14', plain,
% 7.88/8.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.88/8.09         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B_1 @ sk_C_2 @ X1 @ sk_E @ X0))
% 7.88/8.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 7.88/8.09          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 7.88/8.09          | ~ (v1_funct_1 @ X0)
% 7.88/8.09          | (v1_xboole_0 @ X2)
% 7.88/8.09          | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09          | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X2))
% 7.88/8.09          | (v1_xboole_0 @ X1)
% 7.88/8.09          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 7.88/8.09      inference('demod', [status(thm)], ['11', '12', '13'])).
% 7.88/8.09  thf('15', plain,
% 7.88/8.09      (![X0 : $i]:
% 7.88/8.09         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 7.88/8.09          | (v1_xboole_0 @ sk_D)
% 7.88/8.09          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X0))
% 7.88/8.09          | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09          | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09          | (v1_xboole_0 @ X0)
% 7.88/8.09          | ~ (v1_funct_1 @ sk_F)
% 7.88/8.09          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 7.88/8.09          | (v1_funct_1 @ 
% 7.88/8.09             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F)))),
% 7.88/8.09      inference('sup-', [status(thm)], ['8', '14'])).
% 7.88/8.09  thf('16', plain, ((v1_funct_1 @ sk_F)),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('17', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('18', plain,
% 7.88/8.09      (![X0 : $i]:
% 7.88/8.09         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 7.88/8.09          | (v1_xboole_0 @ sk_D)
% 7.88/8.09          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X0))
% 7.88/8.09          | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09          | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09          | (v1_xboole_0 @ X0)
% 7.88/8.09          | (v1_funct_1 @ 
% 7.88/8.09             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F)))),
% 7.88/8.09      inference('demod', [status(thm)], ['15', '16', '17'])).
% 7.88/8.09  thf('19', plain,
% 7.88/8.09      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))
% 7.88/8.09        | (v1_xboole_0 @ sk_D))),
% 7.88/8.09      inference('sup-', [status(thm)], ['7', '18'])).
% 7.88/8.09  thf('20', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('21', plain,
% 7.88/8.09      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_D))),
% 7.88/8.09      inference('demod', [status(thm)], ['19', '20'])).
% 7.88/8.09  thf('22', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('23', plain,
% 7.88/8.09      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('24', plain,
% 7.88/8.09      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_B_1)))),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('25', plain,
% 7.88/8.09      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 7.88/8.09         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 7.88/8.09          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 7.88/8.09          | ~ (v1_funct_1 @ X38)
% 7.88/8.09          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 7.88/8.09          | (v1_xboole_0 @ X41)
% 7.88/8.09          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X42))
% 7.88/8.09          | (v1_xboole_0 @ X39)
% 7.88/8.09          | (v1_xboole_0 @ X40)
% 7.88/8.09          | (v1_xboole_0 @ X42)
% 7.88/8.09          | ~ (v1_funct_1 @ X43)
% 7.88/8.09          | ~ (v1_funct_2 @ X43 @ X41 @ X40)
% 7.88/8.09          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 7.88/8.09          | (v1_funct_2 @ (k1_tmap_1 @ X42 @ X40 @ X39 @ X41 @ X38 @ X43) @ 
% 7.88/8.09             (k4_subset_1 @ X42 @ X39 @ X41) @ X40))),
% 7.88/8.09      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 7.88/8.09  thf('26', plain,
% 7.88/8.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.88/8.09         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_2 @ X0 @ sk_E @ X2) @ 
% 7.88/8.09           (k4_subset_1 @ X1 @ sk_C_2 @ X0) @ sk_B_1)
% 7.88/8.09          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 7.88/8.09          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 7.88/8.09          | ~ (v1_funct_1 @ X2)
% 7.88/8.09          | (v1_xboole_0 @ X1)
% 7.88/8.09          | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09          | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X1))
% 7.88/8.09          | (v1_xboole_0 @ X0)
% 7.88/8.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 7.88/8.09          | ~ (v1_funct_1 @ sk_E)
% 7.88/8.09          | ~ (v1_funct_2 @ sk_E @ sk_C_2 @ sk_B_1))),
% 7.88/8.09      inference('sup-', [status(thm)], ['24', '25'])).
% 7.88/8.09  thf('27', plain, ((v1_funct_1 @ sk_E)),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('28', plain, ((v1_funct_2 @ sk_E @ sk_C_2 @ sk_B_1)),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('29', plain,
% 7.88/8.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.88/8.09         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_2 @ X0 @ sk_E @ X2) @ 
% 7.88/8.09           (k4_subset_1 @ X1 @ sk_C_2 @ X0) @ sk_B_1)
% 7.88/8.09          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 7.88/8.09          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 7.88/8.09          | ~ (v1_funct_1 @ X2)
% 7.88/8.09          | (v1_xboole_0 @ X1)
% 7.88/8.09          | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09          | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X1))
% 7.88/8.09          | (v1_xboole_0 @ X0)
% 7.88/8.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 7.88/8.09      inference('demod', [status(thm)], ['26', '27', '28'])).
% 7.88/8.09  thf('30', plain,
% 7.88/8.09      (![X0 : $i]:
% 7.88/8.09         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 7.88/8.09          | (v1_xboole_0 @ sk_D)
% 7.88/8.09          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X0))
% 7.88/8.09          | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09          | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09          | (v1_xboole_0 @ X0)
% 7.88/8.09          | ~ (v1_funct_1 @ sk_F)
% 7.88/8.09          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 7.88/8.09          | (v1_funct_2 @ 
% 7.88/8.09             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 7.88/8.09             (k4_subset_1 @ X0 @ sk_C_2 @ sk_D) @ sk_B_1))),
% 7.88/8.09      inference('sup-', [status(thm)], ['23', '29'])).
% 7.88/8.09  thf('31', plain, ((v1_funct_1 @ sk_F)),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('32', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('33', plain,
% 7.88/8.09      (![X0 : $i]:
% 7.88/8.09         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 7.88/8.09          | (v1_xboole_0 @ sk_D)
% 7.88/8.09          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X0))
% 7.88/8.09          | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09          | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09          | (v1_xboole_0 @ X0)
% 7.88/8.09          | (v1_funct_2 @ 
% 7.88/8.09             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 7.88/8.09             (k4_subset_1 @ X0 @ sk_C_2 @ sk_D) @ sk_B_1))),
% 7.88/8.09      inference('demod', [status(thm)], ['30', '31', '32'])).
% 7.88/8.09  thf('34', plain,
% 7.88/8.09      (((v1_funct_2 @ 
% 7.88/8.09         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 7.88/8.09         (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))
% 7.88/8.09        | (v1_xboole_0 @ sk_D))),
% 7.88/8.09      inference('sup-', [status(thm)], ['22', '33'])).
% 7.88/8.09  thf('35', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('36', plain,
% 7.88/8.09      (((v1_funct_2 @ 
% 7.88/8.09         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 7.88/8.09         (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_D))),
% 7.88/8.09      inference('demod', [status(thm)], ['34', '35'])).
% 7.88/8.09  thf('37', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('38', plain,
% 7.88/8.09      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('39', plain,
% 7.88/8.09      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_B_1)))),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('40', plain,
% 7.88/8.09      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 7.88/8.09         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 7.88/8.09          | ~ (v1_funct_2 @ X38 @ X39 @ X40)
% 7.88/8.09          | ~ (v1_funct_1 @ X38)
% 7.88/8.09          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ X42))
% 7.88/8.09          | (v1_xboole_0 @ X41)
% 7.88/8.09          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ X42))
% 7.88/8.09          | (v1_xboole_0 @ X39)
% 7.88/8.09          | (v1_xboole_0 @ X40)
% 7.88/8.09          | (v1_xboole_0 @ X42)
% 7.88/8.09          | ~ (v1_funct_1 @ X43)
% 7.88/8.09          | ~ (v1_funct_2 @ X43 @ X41 @ X40)
% 7.88/8.09          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X40)))
% 7.88/8.09          | (m1_subset_1 @ (k1_tmap_1 @ X42 @ X40 @ X39 @ X41 @ X38 @ X43) @ 
% 7.88/8.09             (k1_zfmisc_1 @ 
% 7.88/8.09              (k2_zfmisc_1 @ (k4_subset_1 @ X42 @ X39 @ X41) @ X40))))),
% 7.88/8.09      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 7.88/8.09  thf('41', plain,
% 7.88/8.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.88/8.09         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_2 @ X0 @ sk_E @ X2) @ 
% 7.88/8.09           (k1_zfmisc_1 @ 
% 7.88/8.09            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C_2 @ X0) @ sk_B_1)))
% 7.88/8.09          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 7.88/8.09          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 7.88/8.09          | ~ (v1_funct_1 @ X2)
% 7.88/8.09          | (v1_xboole_0 @ X1)
% 7.88/8.09          | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09          | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X1))
% 7.88/8.09          | (v1_xboole_0 @ X0)
% 7.88/8.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 7.88/8.09          | ~ (v1_funct_1 @ sk_E)
% 7.88/8.09          | ~ (v1_funct_2 @ sk_E @ sk_C_2 @ sk_B_1))),
% 7.88/8.09      inference('sup-', [status(thm)], ['39', '40'])).
% 7.88/8.09  thf('42', plain, ((v1_funct_1 @ sk_E)),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('43', plain, ((v1_funct_2 @ sk_E @ sk_C_2 @ sk_B_1)),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('44', plain,
% 7.88/8.09      (![X0 : $i, X1 : $i, X2 : $i]:
% 7.88/8.09         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_2 @ X0 @ sk_E @ X2) @ 
% 7.88/8.09           (k1_zfmisc_1 @ 
% 7.88/8.09            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C_2 @ X0) @ sk_B_1)))
% 7.88/8.09          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 7.88/8.09          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 7.88/8.09          | ~ (v1_funct_1 @ X2)
% 7.88/8.09          | (v1_xboole_0 @ X1)
% 7.88/8.09          | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09          | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X1))
% 7.88/8.09          | (v1_xboole_0 @ X0)
% 7.88/8.09          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 7.88/8.09      inference('demod', [status(thm)], ['41', '42', '43'])).
% 7.88/8.09  thf('45', plain,
% 7.88/8.09      (![X0 : $i]:
% 7.88/8.09         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 7.88/8.09          | (v1_xboole_0 @ sk_D)
% 7.88/8.09          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X0))
% 7.88/8.09          | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09          | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09          | (v1_xboole_0 @ X0)
% 7.88/8.09          | ~ (v1_funct_1 @ sk_F)
% 7.88/8.09          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 7.88/8.09          | (m1_subset_1 @ 
% 7.88/8.09             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 7.88/8.09             (k1_zfmisc_1 @ 
% 7.88/8.09              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C_2 @ sk_D) @ sk_B_1))))),
% 7.88/8.09      inference('sup-', [status(thm)], ['38', '44'])).
% 7.88/8.09  thf('46', plain, ((v1_funct_1 @ sk_F)),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('47', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('48', plain,
% 7.88/8.09      (![X0 : $i]:
% 7.88/8.09         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 7.88/8.09          | (v1_xboole_0 @ sk_D)
% 7.88/8.09          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X0))
% 7.88/8.09          | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09          | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09          | (v1_xboole_0 @ X0)
% 7.88/8.09          | (m1_subset_1 @ 
% 7.88/8.09             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 7.88/8.09             (k1_zfmisc_1 @ 
% 7.88/8.09              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C_2 @ sk_D) @ sk_B_1))))),
% 7.88/8.09      inference('demod', [status(thm)], ['45', '46', '47'])).
% 7.88/8.09  thf('49', plain,
% 7.88/8.09      (((m1_subset_1 @ 
% 7.88/8.09         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 7.88/8.09         (k1_zfmisc_1 @ 
% 7.88/8.09          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1)))
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))
% 7.88/8.09        | (v1_xboole_0 @ sk_D))),
% 7.88/8.09      inference('sup-', [status(thm)], ['37', '48'])).
% 7.88/8.09  thf('50', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('51', plain,
% 7.88/8.09      (((m1_subset_1 @ 
% 7.88/8.09         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 7.88/8.09         (k1_zfmisc_1 @ 
% 7.88/8.09          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1)))
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_D))),
% 7.88/8.09      inference('demod', [status(thm)], ['49', '50'])).
% 7.88/8.09  thf(d1_tmap_1, axiom,
% 7.88/8.09    (![A:$i]:
% 7.88/8.09     ( ( ~( v1_xboole_0 @ A ) ) =>
% 7.88/8.09       ( ![B:$i]:
% 7.88/8.09         ( ( ~( v1_xboole_0 @ B ) ) =>
% 7.88/8.09           ( ![C:$i]:
% 7.88/8.09             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 7.88/8.09                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 7.88/8.09               ( ![D:$i]:
% 7.88/8.09                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 7.88/8.09                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 7.88/8.09                   ( ![E:$i]:
% 7.88/8.09                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 7.88/8.09                         ( m1_subset_1 @
% 7.88/8.09                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 7.88/8.09                       ( ![F:$i]:
% 7.88/8.09                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 7.88/8.09                             ( m1_subset_1 @
% 7.88/8.09                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 7.88/8.09                           ( ( ( k2_partfun1 @
% 7.88/8.09                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 7.88/8.09                               ( k2_partfun1 @
% 7.88/8.09                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 7.88/8.09                             ( ![G:$i]:
% 7.88/8.09                               ( ( ( v1_funct_1 @ G ) & 
% 7.88/8.09                                   ( v1_funct_2 @
% 7.88/8.09                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 7.88/8.09                                   ( m1_subset_1 @
% 7.88/8.09                                     G @ 
% 7.88/8.09                                     ( k1_zfmisc_1 @
% 7.88/8.09                                       ( k2_zfmisc_1 @
% 7.88/8.09                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 7.88/8.09                                 ( ( ( G ) =
% 7.88/8.09                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 7.88/8.09                                   ( ( ( k2_partfun1 @
% 7.88/8.09                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 7.88/8.09                                         C ) =
% 7.88/8.09                                       ( E ) ) & 
% 7.88/8.09                                     ( ( k2_partfun1 @
% 7.88/8.09                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 7.88/8.09                                         D ) =
% 7.88/8.09                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 7.88/8.09  thf('52', plain,
% 7.88/8.09      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 7.88/8.09         ((v1_xboole_0 @ X31)
% 7.88/8.09          | (v1_xboole_0 @ X32)
% 7.88/8.09          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 7.88/8.09          | ~ (v1_funct_1 @ X34)
% 7.88/8.09          | ~ (v1_funct_2 @ X34 @ X32 @ X31)
% 7.88/8.09          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 7.88/8.09          | ((X37) != (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34))
% 7.88/8.09          | ((k2_partfun1 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31 @ X37 @ X36)
% 7.88/8.09              = (X35))
% 7.88/8.09          | ~ (m1_subset_1 @ X37 @ 
% 7.88/8.09               (k1_zfmisc_1 @ 
% 7.88/8.09                (k2_zfmisc_1 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31)))
% 7.88/8.09          | ~ (v1_funct_2 @ X37 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31)
% 7.88/8.09          | ~ (v1_funct_1 @ X37)
% 7.88/8.09          | ((k2_partfun1 @ X36 @ X31 @ X35 @ (k9_subset_1 @ X33 @ X36 @ X32))
% 7.88/8.09              != (k2_partfun1 @ X32 @ X31 @ X34 @ 
% 7.88/8.09                  (k9_subset_1 @ X33 @ X36 @ X32)))
% 7.88/8.09          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X31)))
% 7.88/8.09          | ~ (v1_funct_2 @ X35 @ X36 @ X31)
% 7.88/8.09          | ~ (v1_funct_1 @ X35)
% 7.88/8.09          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X33))
% 7.88/8.09          | (v1_xboole_0 @ X36)
% 7.88/8.09          | (v1_xboole_0 @ X33))),
% 7.88/8.09      inference('cnf', [status(esa)], [d1_tmap_1])).
% 7.88/8.09  thf('53', plain,
% 7.88/8.09      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 7.88/8.09         ((v1_xboole_0 @ X33)
% 7.88/8.09          | (v1_xboole_0 @ X36)
% 7.88/8.09          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X33))
% 7.88/8.09          | ~ (v1_funct_1 @ X35)
% 7.88/8.09          | ~ (v1_funct_2 @ X35 @ X36 @ X31)
% 7.88/8.09          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X31)))
% 7.88/8.09          | ((k2_partfun1 @ X36 @ X31 @ X35 @ (k9_subset_1 @ X33 @ X36 @ X32))
% 7.88/8.09              != (k2_partfun1 @ X32 @ X31 @ X34 @ 
% 7.88/8.09                  (k9_subset_1 @ X33 @ X36 @ X32)))
% 7.88/8.09          | ~ (v1_funct_1 @ (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34))
% 7.88/8.09          | ~ (v1_funct_2 @ (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34) @ 
% 7.88/8.09               (k4_subset_1 @ X33 @ X36 @ X32) @ X31)
% 7.88/8.09          | ~ (m1_subset_1 @ (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34) @ 
% 7.88/8.09               (k1_zfmisc_1 @ 
% 7.88/8.09                (k2_zfmisc_1 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31)))
% 7.88/8.09          | ((k2_partfun1 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31 @ 
% 7.88/8.09              (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34) @ X36) = (
% 7.88/8.09              X35))
% 7.88/8.09          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 7.88/8.09          | ~ (v1_funct_2 @ X34 @ X32 @ X31)
% 7.88/8.09          | ~ (v1_funct_1 @ X34)
% 7.88/8.09          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 7.88/8.09          | (v1_xboole_0 @ X32)
% 7.88/8.09          | (v1_xboole_0 @ X31))),
% 7.88/8.09      inference('simplify', [status(thm)], ['52'])).
% 7.88/8.09  thf('54', plain,
% 7.88/8.09      (((v1_xboole_0 @ sk_D)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_D)
% 7.88/8.09        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 7.88/8.09        | ~ (v1_funct_1 @ sk_F)
% 7.88/8.09        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 7.88/8.09        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))
% 7.88/8.09        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1 @ 
% 7.88/8.09            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_C_2)
% 7.88/8.09            = (sk_E))
% 7.88/8.09        | ~ (v1_funct_2 @ 
% 7.88/8.09             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 7.88/8.09             (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1)
% 7.88/8.09        | ~ (v1_funct_1 @ 
% 7.88/8.09             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 7.88/8.09        | ((k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ 
% 7.88/8.09            (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 7.88/8.09            != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 7.88/8.09                (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))
% 7.88/8.09        | ~ (m1_subset_1 @ sk_E @ 
% 7.88/8.09             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_B_1)))
% 7.88/8.09        | ~ (v1_funct_2 @ sk_E @ sk_C_2 @ sk_B_1)
% 7.88/8.09        | ~ (v1_funct_1 @ sk_E)
% 7.88/8.09        | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_A))),
% 7.88/8.09      inference('sup-', [status(thm)], ['51', '53'])).
% 7.88/8.09  thf('55', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('56', plain, ((v1_funct_1 @ sk_F)),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('57', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('58', plain,
% 7.88/8.09      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('59', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf(redefinition_k9_subset_1, axiom,
% 7.88/8.09    (![A:$i,B:$i,C:$i]:
% 7.88/8.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 7.88/8.09       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 7.88/8.09  thf('60', plain,
% 7.88/8.09      (![X15 : $i, X16 : $i, X17 : $i]:
% 7.88/8.09         (((k9_subset_1 @ X17 @ X15 @ X16) = (k3_xboole_0 @ X15 @ X16))
% 7.88/8.09          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ X17)))),
% 7.88/8.09      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 7.88/8.09  thf('61', plain,
% 7.88/8.09      (![X0 : $i]:
% 7.88/8.09         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 7.88/8.09      inference('sup-', [status(thm)], ['59', '60'])).
% 7.88/8.09  thf('62', plain,
% 7.88/8.09      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_B_1)))),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf(redefinition_k2_partfun1, axiom,
% 7.88/8.09    (![A:$i,B:$i,C:$i,D:$i]:
% 7.88/8.09     ( ( ( v1_funct_1 @ C ) & 
% 7.88/8.09         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 7.88/8.09       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 7.88/8.09  thf('63', plain,
% 7.88/8.09      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 7.88/8.09         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 7.88/8.09          | ~ (v1_funct_1 @ X27)
% 7.88/8.09          | ((k2_partfun1 @ X28 @ X29 @ X27 @ X30) = (k7_relat_1 @ X27 @ X30)))),
% 7.88/8.09      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 7.88/8.09  thf('64', plain,
% 7.88/8.09      (![X0 : $i]:
% 7.88/8.09         (((k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ X0)
% 7.88/8.09            = (k7_relat_1 @ sk_E @ X0))
% 7.88/8.09          | ~ (v1_funct_1 @ sk_E))),
% 7.88/8.09      inference('sup-', [status(thm)], ['62', '63'])).
% 7.88/8.09  thf('65', plain, ((v1_funct_1 @ sk_E)),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('66', plain,
% 7.88/8.09      (![X0 : $i]:
% 7.88/8.09         ((k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ X0)
% 7.88/8.09           = (k7_relat_1 @ sk_E @ X0))),
% 7.88/8.09      inference('demod', [status(thm)], ['64', '65'])).
% 7.88/8.09  thf('67', plain,
% 7.88/8.09      (![X0 : $i]:
% 7.88/8.09         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 7.88/8.09      inference('sup-', [status(thm)], ['59', '60'])).
% 7.88/8.09  thf('68', plain,
% 7.88/8.09      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('69', plain,
% 7.88/8.09      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 7.88/8.09         (~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X29)))
% 7.88/8.09          | ~ (v1_funct_1 @ X27)
% 7.88/8.09          | ((k2_partfun1 @ X28 @ X29 @ X27 @ X30) = (k7_relat_1 @ X27 @ X30)))),
% 7.88/8.09      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 7.88/8.09  thf('70', plain,
% 7.88/8.09      (![X0 : $i]:
% 7.88/8.09         (((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 7.88/8.09          | ~ (v1_funct_1 @ sk_F))),
% 7.88/8.09      inference('sup-', [status(thm)], ['68', '69'])).
% 7.88/8.09  thf('71', plain, ((v1_funct_1 @ sk_F)),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('72', plain,
% 7.88/8.09      (![X0 : $i]:
% 7.88/8.09         ((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 7.88/8.09      inference('demod', [status(thm)], ['70', '71'])).
% 7.88/8.09  thf('73', plain,
% 7.88/8.09      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_B_1)))),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('74', plain, ((v1_funct_2 @ sk_E @ sk_C_2 @ sk_B_1)),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('75', plain, ((v1_funct_1 @ sk_E)),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('76', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('77', plain,
% 7.88/8.09      (((v1_xboole_0 @ sk_D)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_D)
% 7.88/8.09        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1 @ 
% 7.88/8.09            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_C_2)
% 7.88/8.09            = (sk_E))
% 7.88/8.09        | ~ (v1_funct_2 @ 
% 7.88/8.09             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 7.88/8.09             (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1)
% 7.88/8.09        | ~ (v1_funct_1 @ 
% 7.88/8.09             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 7.88/8.09        | ((k7_relat_1 @ sk_E @ (k3_xboole_0 @ sk_C_2 @ sk_D))
% 7.88/8.09            != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C_2 @ sk_D)))
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_A))),
% 7.88/8.09      inference('demod', [status(thm)],
% 7.88/8.09                ['54', '55', '56', '57', '58', '61', '66', '67', '72', '73', 
% 7.88/8.09                 '74', '75', '76'])).
% 7.88/8.09  thf('78', plain,
% 7.88/8.09      ((((k7_relat_1 @ sk_E @ (k3_xboole_0 @ sk_C_2 @ sk_D))
% 7.88/8.09          != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C_2 @ sk_D)))
% 7.88/8.09        | ~ (v1_funct_1 @ 
% 7.88/8.09             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 7.88/8.09        | ~ (v1_funct_2 @ 
% 7.88/8.09             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 7.88/8.09             (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1)
% 7.88/8.09        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1 @ 
% 7.88/8.09            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_C_2)
% 7.88/8.09            = (sk_E))
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_D))),
% 7.88/8.09      inference('simplify', [status(thm)], ['77'])).
% 7.88/8.09  thf('79', plain,
% 7.88/8.09      ((((k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ 
% 7.88/8.09          (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 7.88/8.09          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 7.88/8.09              (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))
% 7.88/8.09        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1 @ 
% 7.88/8.09            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_C_2)
% 7.88/8.09            != (sk_E))
% 7.88/8.09        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1 @ 
% 7.88/8.09            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 7.88/8.09            != (sk_F)))),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('80', plain,
% 7.88/8.09      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1 @ 
% 7.88/8.09          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_C_2)
% 7.88/8.09          != (sk_E)))
% 7.88/8.09         <= (~
% 7.88/8.09             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1 @ 
% 7.88/8.09                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 7.88/8.09                sk_C_2) = (sk_E))))),
% 7.88/8.09      inference('split', [status(esa)], ['79'])).
% 7.88/8.09  thf('81', plain,
% 7.88/8.09      (![X0 : $i, X1 : $i]:
% 7.88/8.09         (~ (v1_xboole_0 @ X1)
% 7.88/8.09          | ~ (v1_relat_1 @ X0)
% 7.88/8.09          | ((k7_relat_1 @ X0 @ X1) = (k1_xboole_0)))),
% 7.88/8.09      inference('sup-', [status(thm)], ['3', '4'])).
% 7.88/8.09  thf('82', plain,
% 7.88/8.09      (![X0 : $i, X1 : $i]:
% 7.88/8.09         (~ (v1_xboole_0 @ X1)
% 7.88/8.09          | ~ (v1_relat_1 @ X0)
% 7.88/8.09          | ((k7_relat_1 @ X0 @ X1) = (k1_xboole_0)))),
% 7.88/8.09      inference('sup-', [status(thm)], ['3', '4'])).
% 7.88/8.09  thf('83', plain,
% 7.88/8.09      (![X0 : $i]:
% 7.88/8.09         ((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 7.88/8.09      inference('demod', [status(thm)], ['70', '71'])).
% 7.88/8.09  thf('84', plain,
% 7.88/8.09      (![X0 : $i]:
% 7.88/8.09         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 7.88/8.09      inference('sup-', [status(thm)], ['59', '60'])).
% 7.88/8.09  thf('85', plain,
% 7.88/8.09      ((((k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ 
% 7.88/8.09          (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 7.88/8.09          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 7.88/8.09              (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))))
% 7.88/8.09         <= (~
% 7.88/8.09             (((k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ 
% 7.88/8.09                (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 7.88/8.09                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 7.88/8.09                   (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))))),
% 7.88/8.09      inference('split', [status(esa)], ['79'])).
% 7.88/8.09  thf('86', plain,
% 7.88/8.09      ((((k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ 
% 7.88/8.09          (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 7.88/8.09          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 7.88/8.09              (k3_xboole_0 @ sk_C_2 @ sk_D))))
% 7.88/8.09         <= (~
% 7.88/8.09             (((k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ 
% 7.88/8.09                (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 7.88/8.09                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 7.88/8.09                   (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))))),
% 7.88/8.09      inference('sup-', [status(thm)], ['84', '85'])).
% 7.88/8.09  thf('87', plain,
% 7.88/8.09      (![X0 : $i]:
% 7.88/8.09         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 7.88/8.09      inference('sup-', [status(thm)], ['59', '60'])).
% 7.88/8.09  thf('88', plain,
% 7.88/8.09      ((((k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ (k3_xboole_0 @ sk_C_2 @ sk_D))
% 7.88/8.09          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 7.88/8.09              (k3_xboole_0 @ sk_C_2 @ sk_D))))
% 7.88/8.09         <= (~
% 7.88/8.09             (((k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ 
% 7.88/8.09                (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 7.88/8.09                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 7.88/8.09                   (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))))),
% 7.88/8.09      inference('demod', [status(thm)], ['86', '87'])).
% 7.88/8.09  thf('89', plain,
% 7.88/8.09      ((((k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ (k3_xboole_0 @ sk_C_2 @ sk_D))
% 7.88/8.09          != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C_2 @ sk_D))))
% 7.88/8.09         <= (~
% 7.88/8.09             (((k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ 
% 7.88/8.09                (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 7.88/8.09                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 7.88/8.09                   (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))))),
% 7.88/8.09      inference('sup-', [status(thm)], ['83', '88'])).
% 7.88/8.09  thf('90', plain,
% 7.88/8.09      (![X0 : $i]:
% 7.88/8.09         ((k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ X0)
% 7.88/8.09           = (k7_relat_1 @ sk_E @ X0))),
% 7.88/8.09      inference('demod', [status(thm)], ['64', '65'])).
% 7.88/8.09  thf('91', plain,
% 7.88/8.09      ((((k7_relat_1 @ sk_E @ (k3_xboole_0 @ sk_C_2 @ sk_D))
% 7.88/8.09          != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C_2 @ sk_D))))
% 7.88/8.09         <= (~
% 7.88/8.09             (((k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ 
% 7.88/8.09                (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 7.88/8.09                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 7.88/8.09                   (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))))),
% 7.88/8.09      inference('demod', [status(thm)], ['89', '90'])).
% 7.88/8.09  thf('92', plain,
% 7.88/8.09      (((((k7_relat_1 @ sk_E @ (k3_xboole_0 @ sk_C_2 @ sk_D)) != (k1_xboole_0))
% 7.88/8.09         | ~ (v1_relat_1 @ sk_F)
% 7.88/8.09         | ~ (v1_xboole_0 @ (k3_xboole_0 @ sk_C_2 @ sk_D))))
% 7.88/8.09         <= (~
% 7.88/8.09             (((k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ 
% 7.88/8.09                (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 7.88/8.09                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 7.88/8.09                   (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))))),
% 7.88/8.09      inference('sup-', [status(thm)], ['82', '91'])).
% 7.88/8.09  thf('93', plain,
% 7.88/8.09      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf(cc1_relset_1, axiom,
% 7.88/8.09    (![A:$i,B:$i,C:$i]:
% 7.88/8.09     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 7.88/8.09       ( v1_relat_1 @ C ) ))).
% 7.88/8.09  thf('94', plain,
% 7.88/8.09      (![X24 : $i, X25 : $i, X26 : $i]:
% 7.88/8.09         ((v1_relat_1 @ X24)
% 7.88/8.09          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 7.88/8.09      inference('cnf', [status(esa)], [cc1_relset_1])).
% 7.88/8.09  thf('95', plain, ((v1_relat_1 @ sk_F)),
% 7.88/8.09      inference('sup-', [status(thm)], ['93', '94'])).
% 7.88/8.09  thf('96', plain, ((r1_subset_1 @ sk_C_2 @ sk_D)),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf(redefinition_r1_subset_1, axiom,
% 7.88/8.09    (![A:$i,B:$i]:
% 7.88/8.09     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 7.88/8.09       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 7.88/8.09  thf('97', plain,
% 7.88/8.09      (![X22 : $i, X23 : $i]:
% 7.88/8.09         ((v1_xboole_0 @ X22)
% 7.88/8.09          | (v1_xboole_0 @ X23)
% 7.88/8.09          | (r1_xboole_0 @ X22 @ X23)
% 7.88/8.09          | ~ (r1_subset_1 @ X22 @ X23))),
% 7.88/8.09      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 7.88/8.09  thf('98', plain,
% 7.88/8.09      (((r1_xboole_0 @ sk_C_2 @ sk_D)
% 7.88/8.09        | (v1_xboole_0 @ sk_D)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2))),
% 7.88/8.09      inference('sup-', [status(thm)], ['96', '97'])).
% 7.88/8.09  thf('99', plain, (~ (v1_xboole_0 @ sk_D)),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('100', plain, (((v1_xboole_0 @ sk_C_2) | (r1_xboole_0 @ sk_C_2 @ sk_D))),
% 7.88/8.09      inference('clc', [status(thm)], ['98', '99'])).
% 7.88/8.09  thf('101', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('102', plain, ((r1_xboole_0 @ sk_C_2 @ sk_D)),
% 7.88/8.09      inference('clc', [status(thm)], ['100', '101'])).
% 7.88/8.09  thf('103', plain,
% 7.88/8.09      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 7.88/8.09      inference('cnf', [status(esa)], [d1_xboole_0])).
% 7.88/8.09  thf(t4_xboole_0, axiom,
% 7.88/8.09    (![A:$i,B:$i]:
% 7.88/8.09     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 7.88/8.09            ( r1_xboole_0 @ A @ B ) ) ) & 
% 7.88/8.09       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 7.88/8.09            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 7.88/8.09  thf('104', plain,
% 7.88/8.09      (![X9 : $i, X11 : $i, X12 : $i]:
% 7.88/8.09         (~ (r2_hidden @ X11 @ (k3_xboole_0 @ X9 @ X12))
% 7.88/8.09          | ~ (r1_xboole_0 @ X9 @ X12))),
% 7.88/8.09      inference('cnf', [status(esa)], [t4_xboole_0])).
% 7.88/8.09  thf('105', plain,
% 7.88/8.09      (![X0 : $i, X1 : $i]:
% 7.88/8.09         ((v1_xboole_0 @ (k3_xboole_0 @ X1 @ X0)) | ~ (r1_xboole_0 @ X1 @ X0))),
% 7.88/8.09      inference('sup-', [status(thm)], ['103', '104'])).
% 7.88/8.09  thf('106', plain, ((v1_xboole_0 @ (k3_xboole_0 @ sk_C_2 @ sk_D))),
% 7.88/8.09      inference('sup-', [status(thm)], ['102', '105'])).
% 7.88/8.09  thf('107', plain,
% 7.88/8.09      ((((k7_relat_1 @ sk_E @ (k3_xboole_0 @ sk_C_2 @ sk_D)) != (k1_xboole_0)))
% 7.88/8.09         <= (~
% 7.88/8.09             (((k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ 
% 7.88/8.09                (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 7.88/8.09                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 7.88/8.09                   (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))))),
% 7.88/8.09      inference('demod', [status(thm)], ['92', '95', '106'])).
% 7.88/8.09  thf('108', plain,
% 7.88/8.09      (((((k1_xboole_0) != (k1_xboole_0))
% 7.88/8.09         | ~ (v1_relat_1 @ sk_E)
% 7.88/8.09         | ~ (v1_xboole_0 @ (k3_xboole_0 @ sk_C_2 @ sk_D))))
% 7.88/8.09         <= (~
% 7.88/8.09             (((k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ 
% 7.88/8.09                (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 7.88/8.09                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 7.88/8.09                   (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))))),
% 7.88/8.09      inference('sup-', [status(thm)], ['81', '107'])).
% 7.88/8.09  thf('109', plain,
% 7.88/8.09      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_B_1)))),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('110', plain,
% 7.88/8.09      (![X24 : $i, X25 : $i, X26 : $i]:
% 7.88/8.09         ((v1_relat_1 @ X24)
% 7.88/8.09          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 7.88/8.09      inference('cnf', [status(esa)], [cc1_relset_1])).
% 7.88/8.09  thf('111', plain, ((v1_relat_1 @ sk_E)),
% 7.88/8.09      inference('sup-', [status(thm)], ['109', '110'])).
% 7.88/8.09  thf('112', plain, ((v1_xboole_0 @ (k3_xboole_0 @ sk_C_2 @ sk_D))),
% 7.88/8.09      inference('sup-', [status(thm)], ['102', '105'])).
% 7.88/8.09  thf('113', plain,
% 7.88/8.09      ((((k1_xboole_0) != (k1_xboole_0)))
% 7.88/8.09         <= (~
% 7.88/8.09             (((k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ 
% 7.88/8.09                (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 7.88/8.09                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 7.88/8.09                   (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))))),
% 7.88/8.09      inference('demod', [status(thm)], ['108', '111', '112'])).
% 7.88/8.09  thf('114', plain,
% 7.88/8.09      ((((k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ 
% 7.88/8.09          (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 7.88/8.09          = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 7.88/8.09             (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))))),
% 7.88/8.09      inference('simplify', [status(thm)], ['113'])).
% 7.88/8.09  thf('115', plain,
% 7.88/8.09      (![X0 : $i, X1 : $i]:
% 7.88/8.09         (~ (v1_xboole_0 @ X1)
% 7.88/8.09          | ~ (v1_relat_1 @ X0)
% 7.88/8.09          | ((k7_relat_1 @ X0 @ X1) = (k1_xboole_0)))),
% 7.88/8.09      inference('sup-', [status(thm)], ['3', '4'])).
% 7.88/8.09  thf('116', plain,
% 7.88/8.09      (![X0 : $i, X1 : $i]:
% 7.88/8.09         (~ (v1_xboole_0 @ X1)
% 7.88/8.09          | ~ (v1_relat_1 @ X0)
% 7.88/8.09          | ((k7_relat_1 @ X0 @ X1) = (k1_xboole_0)))),
% 7.88/8.09      inference('sup-', [status(thm)], ['3', '4'])).
% 7.88/8.09  thf('117', plain,
% 7.88/8.09      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_D))),
% 7.88/8.09      inference('demod', [status(thm)], ['19', '20'])).
% 7.88/8.09  thf('118', plain,
% 7.88/8.09      (((v1_funct_2 @ 
% 7.88/8.09         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 7.88/8.09         (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_D))),
% 7.88/8.09      inference('demod', [status(thm)], ['34', '35'])).
% 7.88/8.09  thf('119', plain,
% 7.88/8.09      (((m1_subset_1 @ 
% 7.88/8.09         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 7.88/8.09         (k1_zfmisc_1 @ 
% 7.88/8.09          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1)))
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_D))),
% 7.88/8.09      inference('demod', [status(thm)], ['49', '50'])).
% 7.88/8.09  thf('120', plain,
% 7.88/8.09      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 7.88/8.09         ((v1_xboole_0 @ X31)
% 7.88/8.09          | (v1_xboole_0 @ X32)
% 7.88/8.09          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 7.88/8.09          | ~ (v1_funct_1 @ X34)
% 7.88/8.09          | ~ (v1_funct_2 @ X34 @ X32 @ X31)
% 7.88/8.09          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 7.88/8.09          | ((X37) != (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34))
% 7.88/8.09          | ((k2_partfun1 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31 @ X37 @ X32)
% 7.88/8.09              = (X34))
% 7.88/8.09          | ~ (m1_subset_1 @ X37 @ 
% 7.88/8.09               (k1_zfmisc_1 @ 
% 7.88/8.09                (k2_zfmisc_1 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31)))
% 7.88/8.09          | ~ (v1_funct_2 @ X37 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31)
% 7.88/8.09          | ~ (v1_funct_1 @ X37)
% 7.88/8.09          | ((k2_partfun1 @ X36 @ X31 @ X35 @ (k9_subset_1 @ X33 @ X36 @ X32))
% 7.88/8.09              != (k2_partfun1 @ X32 @ X31 @ X34 @ 
% 7.88/8.09                  (k9_subset_1 @ X33 @ X36 @ X32)))
% 7.88/8.09          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X31)))
% 7.88/8.09          | ~ (v1_funct_2 @ X35 @ X36 @ X31)
% 7.88/8.09          | ~ (v1_funct_1 @ X35)
% 7.88/8.09          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X33))
% 7.88/8.09          | (v1_xboole_0 @ X36)
% 7.88/8.09          | (v1_xboole_0 @ X33))),
% 7.88/8.09      inference('cnf', [status(esa)], [d1_tmap_1])).
% 7.88/8.09  thf('121', plain,
% 7.88/8.09      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 7.88/8.09         ((v1_xboole_0 @ X33)
% 7.88/8.09          | (v1_xboole_0 @ X36)
% 7.88/8.09          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X33))
% 7.88/8.09          | ~ (v1_funct_1 @ X35)
% 7.88/8.09          | ~ (v1_funct_2 @ X35 @ X36 @ X31)
% 7.88/8.09          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X31)))
% 7.88/8.09          | ((k2_partfun1 @ X36 @ X31 @ X35 @ (k9_subset_1 @ X33 @ X36 @ X32))
% 7.88/8.09              != (k2_partfun1 @ X32 @ X31 @ X34 @ 
% 7.88/8.09                  (k9_subset_1 @ X33 @ X36 @ X32)))
% 7.88/8.09          | ~ (v1_funct_1 @ (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34))
% 7.88/8.09          | ~ (v1_funct_2 @ (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34) @ 
% 7.88/8.09               (k4_subset_1 @ X33 @ X36 @ X32) @ X31)
% 7.88/8.09          | ~ (m1_subset_1 @ (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34) @ 
% 7.88/8.09               (k1_zfmisc_1 @ 
% 7.88/8.09                (k2_zfmisc_1 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31)))
% 7.88/8.09          | ((k2_partfun1 @ (k4_subset_1 @ X33 @ X36 @ X32) @ X31 @ 
% 7.88/8.09              (k1_tmap_1 @ X33 @ X31 @ X36 @ X32 @ X35 @ X34) @ X32) = (
% 7.88/8.09              X34))
% 7.88/8.09          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X31)))
% 7.88/8.09          | ~ (v1_funct_2 @ X34 @ X32 @ X31)
% 7.88/8.09          | ~ (v1_funct_1 @ X34)
% 7.88/8.09          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X33))
% 7.88/8.09          | (v1_xboole_0 @ X32)
% 7.88/8.09          | (v1_xboole_0 @ X31))),
% 7.88/8.09      inference('simplify', [status(thm)], ['120'])).
% 7.88/8.09  thf('122', plain,
% 7.88/8.09      (((v1_xboole_0 @ sk_D)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_D)
% 7.88/8.09        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 7.88/8.09        | ~ (v1_funct_1 @ sk_F)
% 7.88/8.09        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 7.88/8.09        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))
% 7.88/8.09        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1 @ 
% 7.88/8.09            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 7.88/8.09            = (sk_F))
% 7.88/8.09        | ~ (v1_funct_2 @ 
% 7.88/8.09             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 7.88/8.09             (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1)
% 7.88/8.09        | ~ (v1_funct_1 @ 
% 7.88/8.09             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 7.88/8.09        | ((k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ 
% 7.88/8.09            (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 7.88/8.09            != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 7.88/8.09                (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))
% 7.88/8.09        | ~ (m1_subset_1 @ sk_E @ 
% 7.88/8.09             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_B_1)))
% 7.88/8.09        | ~ (v1_funct_2 @ sk_E @ sk_C_2 @ sk_B_1)
% 7.88/8.09        | ~ (v1_funct_1 @ sk_E)
% 7.88/8.09        | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_A))),
% 7.88/8.09      inference('sup-', [status(thm)], ['119', '121'])).
% 7.88/8.09  thf('123', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('124', plain, ((v1_funct_1 @ sk_F)),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('125', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('126', plain,
% 7.88/8.09      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('127', plain,
% 7.88/8.09      (![X0 : $i]:
% 7.88/8.09         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 7.88/8.09      inference('sup-', [status(thm)], ['59', '60'])).
% 7.88/8.09  thf('128', plain,
% 7.88/8.09      (![X0 : $i]:
% 7.88/8.09         ((k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ X0)
% 7.88/8.09           = (k7_relat_1 @ sk_E @ X0))),
% 7.88/8.09      inference('demod', [status(thm)], ['64', '65'])).
% 7.88/8.09  thf('129', plain,
% 7.88/8.09      (![X0 : $i]:
% 7.88/8.09         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 7.88/8.09      inference('sup-', [status(thm)], ['59', '60'])).
% 7.88/8.09  thf('130', plain,
% 7.88/8.09      (![X0 : $i]:
% 7.88/8.09         ((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 7.88/8.09      inference('demod', [status(thm)], ['70', '71'])).
% 7.88/8.09  thf('131', plain,
% 7.88/8.09      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_B_1)))),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('132', plain, ((v1_funct_2 @ sk_E @ sk_C_2 @ sk_B_1)),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('133', plain, ((v1_funct_1 @ sk_E)),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('134', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('135', plain,
% 7.88/8.09      (((v1_xboole_0 @ sk_D)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_D)
% 7.88/8.09        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1 @ 
% 7.88/8.09            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 7.88/8.09            = (sk_F))
% 7.88/8.09        | ~ (v1_funct_2 @ 
% 7.88/8.09             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 7.88/8.09             (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1)
% 7.88/8.09        | ~ (v1_funct_1 @ 
% 7.88/8.09             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 7.88/8.09        | ((k7_relat_1 @ sk_E @ (k3_xboole_0 @ sk_C_2 @ sk_D))
% 7.88/8.09            != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C_2 @ sk_D)))
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_A))),
% 7.88/8.09      inference('demod', [status(thm)],
% 7.88/8.09                ['122', '123', '124', '125', '126', '127', '128', '129', 
% 7.88/8.09                 '130', '131', '132', '133', '134'])).
% 7.88/8.09  thf('136', plain,
% 7.88/8.09      ((((k7_relat_1 @ sk_E @ (k3_xboole_0 @ sk_C_2 @ sk_D))
% 7.88/8.09          != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C_2 @ sk_D)))
% 7.88/8.09        | ~ (v1_funct_1 @ 
% 7.88/8.09             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 7.88/8.09        | ~ (v1_funct_2 @ 
% 7.88/8.09             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 7.88/8.09             (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1)
% 7.88/8.09        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1 @ 
% 7.88/8.09            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 7.88/8.09            = (sk_F))
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_D))),
% 7.88/8.09      inference('simplify', [status(thm)], ['135'])).
% 7.88/8.09  thf('137', plain,
% 7.88/8.09      (((v1_xboole_0 @ sk_D)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | (v1_xboole_0 @ sk_D)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1 @ 
% 7.88/8.09            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 7.88/8.09            = (sk_F))
% 7.88/8.09        | ~ (v1_funct_1 @ 
% 7.88/8.09             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 7.88/8.09        | ((k7_relat_1 @ sk_E @ (k3_xboole_0 @ sk_C_2 @ sk_D))
% 7.88/8.09            != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C_2 @ sk_D))))),
% 7.88/8.09      inference('sup-', [status(thm)], ['118', '136'])).
% 7.88/8.09  thf('138', plain,
% 7.88/8.09      ((((k7_relat_1 @ sk_E @ (k3_xboole_0 @ sk_C_2 @ sk_D))
% 7.88/8.09          != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C_2 @ sk_D)))
% 7.88/8.09        | ~ (v1_funct_1 @ 
% 7.88/8.09             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 7.88/8.09        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1 @ 
% 7.88/8.09            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 7.88/8.09            = (sk_F))
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_D))),
% 7.88/8.09      inference('simplify', [status(thm)], ['137'])).
% 7.88/8.09  thf('139', plain,
% 7.88/8.09      (((v1_xboole_0 @ sk_D)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | (v1_xboole_0 @ sk_D)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1 @ 
% 7.88/8.09            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 7.88/8.09            = (sk_F))
% 7.88/8.09        | ((k7_relat_1 @ sk_E @ (k3_xboole_0 @ sk_C_2 @ sk_D))
% 7.88/8.09            != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C_2 @ sk_D))))),
% 7.88/8.09      inference('sup-', [status(thm)], ['117', '138'])).
% 7.88/8.09  thf('140', plain,
% 7.88/8.09      ((((k7_relat_1 @ sk_E @ (k3_xboole_0 @ sk_C_2 @ sk_D))
% 7.88/8.09          != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C_2 @ sk_D)))
% 7.88/8.09        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1 @ 
% 7.88/8.09            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 7.88/8.09            = (sk_F))
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_D))),
% 7.88/8.09      inference('simplify', [status(thm)], ['139'])).
% 7.88/8.09  thf('141', plain,
% 7.88/8.09      ((((k7_relat_1 @ sk_E @ (k3_xboole_0 @ sk_C_2 @ sk_D)) != (k1_xboole_0))
% 7.88/8.09        | ~ (v1_relat_1 @ sk_F)
% 7.88/8.09        | ~ (v1_xboole_0 @ (k3_xboole_0 @ sk_C_2 @ sk_D))
% 7.88/8.09        | (v1_xboole_0 @ sk_D)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1 @ 
% 7.88/8.09            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 7.88/8.09            = (sk_F)))),
% 7.88/8.09      inference('sup-', [status(thm)], ['116', '140'])).
% 7.88/8.09  thf('142', plain, ((v1_relat_1 @ sk_F)),
% 7.88/8.09      inference('sup-', [status(thm)], ['93', '94'])).
% 7.88/8.09  thf('143', plain, ((v1_xboole_0 @ (k3_xboole_0 @ sk_C_2 @ sk_D))),
% 7.88/8.09      inference('sup-', [status(thm)], ['102', '105'])).
% 7.88/8.09  thf('144', plain,
% 7.88/8.09      ((((k7_relat_1 @ sk_E @ (k3_xboole_0 @ sk_C_2 @ sk_D)) != (k1_xboole_0))
% 7.88/8.09        | (v1_xboole_0 @ sk_D)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1 @ 
% 7.88/8.09            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 7.88/8.09            = (sk_F)))),
% 7.88/8.09      inference('demod', [status(thm)], ['141', '142', '143'])).
% 7.88/8.09  thf('145', plain,
% 7.88/8.09      ((((k1_xboole_0) != (k1_xboole_0))
% 7.88/8.09        | ~ (v1_relat_1 @ sk_E)
% 7.88/8.09        | ~ (v1_xboole_0 @ (k3_xboole_0 @ sk_C_2 @ sk_D))
% 7.88/8.09        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1 @ 
% 7.88/8.09            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 7.88/8.09            = (sk_F))
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_D))),
% 7.88/8.09      inference('sup-', [status(thm)], ['115', '144'])).
% 7.88/8.09  thf('146', plain, ((v1_relat_1 @ sk_E)),
% 7.88/8.09      inference('sup-', [status(thm)], ['109', '110'])).
% 7.88/8.09  thf('147', plain, ((v1_xboole_0 @ (k3_xboole_0 @ sk_C_2 @ sk_D))),
% 7.88/8.09      inference('sup-', [status(thm)], ['102', '105'])).
% 7.88/8.09  thf('148', plain,
% 7.88/8.09      ((((k1_xboole_0) != (k1_xboole_0))
% 7.88/8.09        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1 @ 
% 7.88/8.09            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 7.88/8.09            = (sk_F))
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_D))),
% 7.88/8.09      inference('demod', [status(thm)], ['145', '146', '147'])).
% 7.88/8.09  thf('149', plain,
% 7.88/8.09      (((v1_xboole_0 @ sk_D)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1 @ 
% 7.88/8.09            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 7.88/8.09            = (sk_F)))),
% 7.88/8.09      inference('simplify', [status(thm)], ['148'])).
% 7.88/8.09  thf('150', plain,
% 7.88/8.09      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1 @ 
% 7.88/8.09          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 7.88/8.09          != (sk_F)))
% 7.88/8.09         <= (~
% 7.88/8.09             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1 @ 
% 7.88/8.09                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 7.88/8.09                sk_D) = (sk_F))))),
% 7.88/8.09      inference('split', [status(esa)], ['79'])).
% 7.88/8.09  thf('151', plain,
% 7.88/8.09      (((((sk_F) != (sk_F))
% 7.88/8.09         | (v1_xboole_0 @ sk_A)
% 7.88/8.09         | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09         | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09         | (v1_xboole_0 @ sk_D)))
% 7.88/8.09         <= (~
% 7.88/8.09             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1 @ 
% 7.88/8.09                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 7.88/8.09                sk_D) = (sk_F))))),
% 7.88/8.09      inference('sup-', [status(thm)], ['149', '150'])).
% 7.88/8.09  thf('152', plain,
% 7.88/8.09      ((((v1_xboole_0 @ sk_D)
% 7.88/8.09         | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09         | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09         | (v1_xboole_0 @ sk_A)))
% 7.88/8.09         <= (~
% 7.88/8.09             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1 @ 
% 7.88/8.09                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 7.88/8.09                sk_D) = (sk_F))))),
% 7.88/8.09      inference('simplify', [status(thm)], ['151'])).
% 7.88/8.09  thf('153', plain, (~ (v1_xboole_0 @ sk_D)),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('154', plain,
% 7.88/8.09      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_C_2)))
% 7.88/8.09         <= (~
% 7.88/8.09             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1 @ 
% 7.88/8.09                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 7.88/8.09                sk_D) = (sk_F))))),
% 7.88/8.09      inference('sup-', [status(thm)], ['152', '153'])).
% 7.88/8.09  thf('155', plain, (~ (v1_xboole_0 @ sk_A)),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('156', plain,
% 7.88/8.09      ((((v1_xboole_0 @ sk_C_2) | (v1_xboole_0 @ sk_B_1)))
% 7.88/8.09         <= (~
% 7.88/8.09             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1 @ 
% 7.88/8.09                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 7.88/8.09                sk_D) = (sk_F))))),
% 7.88/8.09      inference('clc', [status(thm)], ['154', '155'])).
% 7.88/8.09  thf('157', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('158', plain,
% 7.88/8.09      (((v1_xboole_0 @ sk_B_1))
% 7.88/8.09         <= (~
% 7.88/8.09             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1 @ 
% 7.88/8.09                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 7.88/8.09                sk_D) = (sk_F))))),
% 7.88/8.09      inference('clc', [status(thm)], ['156', '157'])).
% 7.88/8.09  thf('159', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('160', plain,
% 7.88/8.09      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1 @ 
% 7.88/8.09          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 7.88/8.09          = (sk_F)))),
% 7.88/8.09      inference('sup-', [status(thm)], ['158', '159'])).
% 7.88/8.09  thf('161', plain,
% 7.88/8.09      (~
% 7.88/8.09       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1 @ 
% 7.88/8.09          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_C_2)
% 7.88/8.09          = (sk_E))) | 
% 7.88/8.09       ~
% 7.88/8.09       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1 @ 
% 7.88/8.09          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 7.88/8.09          = (sk_F))) | 
% 7.88/8.09       ~
% 7.88/8.09       (((k2_partfun1 @ sk_C_2 @ sk_B_1 @ sk_E @ 
% 7.88/8.09          (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 7.88/8.09          = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 7.88/8.09             (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))))),
% 7.88/8.09      inference('split', [status(esa)], ['79'])).
% 7.88/8.09  thf('162', plain,
% 7.88/8.09      (~
% 7.88/8.09       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1 @ 
% 7.88/8.09          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_C_2)
% 7.88/8.09          = (sk_E)))),
% 7.88/8.09      inference('sat_resolution*', [status(thm)], ['114', '160', '161'])).
% 7.88/8.09  thf('163', plain,
% 7.88/8.09      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1 @ 
% 7.88/8.09         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_C_2)
% 7.88/8.09         != (sk_E))),
% 7.88/8.09      inference('simpl_trail', [status(thm)], ['80', '162'])).
% 7.88/8.09  thf('164', plain,
% 7.88/8.09      ((((k7_relat_1 @ sk_E @ (k3_xboole_0 @ sk_C_2 @ sk_D))
% 7.88/8.09          != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C_2 @ sk_D)))
% 7.88/8.09        | ~ (v1_funct_1 @ 
% 7.88/8.09             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 7.88/8.09        | ~ (v1_funct_2 @ 
% 7.88/8.09             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 7.88/8.09             (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_D))),
% 7.88/8.09      inference('simplify_reflect-', [status(thm)], ['78', '163'])).
% 7.88/8.09  thf('165', plain,
% 7.88/8.09      (((v1_xboole_0 @ sk_D)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | (v1_xboole_0 @ sk_D)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | ~ (v1_funct_1 @ 
% 7.88/8.09             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 7.88/8.09        | ((k7_relat_1 @ sk_E @ (k3_xboole_0 @ sk_C_2 @ sk_D))
% 7.88/8.09            != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C_2 @ sk_D))))),
% 7.88/8.09      inference('sup-', [status(thm)], ['36', '164'])).
% 7.88/8.09  thf('166', plain,
% 7.88/8.09      ((((k7_relat_1 @ sk_E @ (k3_xboole_0 @ sk_C_2 @ sk_D))
% 7.88/8.09          != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C_2 @ sk_D)))
% 7.88/8.09        | ~ (v1_funct_1 @ 
% 7.88/8.09             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_D))),
% 7.88/8.09      inference('simplify', [status(thm)], ['165'])).
% 7.88/8.09  thf('167', plain,
% 7.88/8.09      (((v1_xboole_0 @ sk_D)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | (v1_xboole_0 @ sk_D)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | ((k7_relat_1 @ sk_E @ (k3_xboole_0 @ sk_C_2 @ sk_D))
% 7.88/8.09            != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C_2 @ sk_D))))),
% 7.88/8.09      inference('sup-', [status(thm)], ['21', '166'])).
% 7.88/8.09  thf('168', plain,
% 7.88/8.09      ((((k7_relat_1 @ sk_E @ (k3_xboole_0 @ sk_C_2 @ sk_D))
% 7.88/8.09          != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C_2 @ sk_D)))
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_D))),
% 7.88/8.09      inference('simplify', [status(thm)], ['167'])).
% 7.88/8.09  thf('169', plain,
% 7.88/8.09      ((((k7_relat_1 @ sk_E @ (k3_xboole_0 @ sk_C_2 @ sk_D)) != (k1_xboole_0))
% 7.88/8.09        | ~ (v1_relat_1 @ sk_F)
% 7.88/8.09        | ~ (v1_xboole_0 @ (k3_xboole_0 @ sk_C_2 @ sk_D))
% 7.88/8.09        | (v1_xboole_0 @ sk_D)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_A))),
% 7.88/8.09      inference('sup-', [status(thm)], ['6', '168'])).
% 7.88/8.09  thf('170', plain, ((v1_relat_1 @ sk_F)),
% 7.88/8.09      inference('sup-', [status(thm)], ['93', '94'])).
% 7.88/8.09  thf('171', plain, ((v1_xboole_0 @ (k3_xboole_0 @ sk_C_2 @ sk_D))),
% 7.88/8.09      inference('sup-', [status(thm)], ['102', '105'])).
% 7.88/8.09  thf('172', plain,
% 7.88/8.09      ((((k7_relat_1 @ sk_E @ (k3_xboole_0 @ sk_C_2 @ sk_D)) != (k1_xboole_0))
% 7.88/8.09        | (v1_xboole_0 @ sk_D)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_A))),
% 7.88/8.09      inference('demod', [status(thm)], ['169', '170', '171'])).
% 7.88/8.09  thf('173', plain,
% 7.88/8.09      ((((k1_xboole_0) != (k1_xboole_0))
% 7.88/8.09        | ~ (v1_relat_1 @ sk_E)
% 7.88/8.09        | ~ (v1_xboole_0 @ (k3_xboole_0 @ sk_C_2 @ sk_D))
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_D))),
% 7.88/8.09      inference('sup-', [status(thm)], ['5', '172'])).
% 7.88/8.09  thf('174', plain, ((v1_relat_1 @ sk_E)),
% 7.88/8.09      inference('sup-', [status(thm)], ['109', '110'])).
% 7.88/8.09  thf('175', plain, ((v1_xboole_0 @ (k3_xboole_0 @ sk_C_2 @ sk_D))),
% 7.88/8.09      inference('sup-', [status(thm)], ['102', '105'])).
% 7.88/8.09  thf('176', plain,
% 7.88/8.09      ((((k1_xboole_0) != (k1_xboole_0))
% 7.88/8.09        | (v1_xboole_0 @ sk_A)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_D))),
% 7.88/8.09      inference('demod', [status(thm)], ['173', '174', '175'])).
% 7.88/8.09  thf('177', plain,
% 7.88/8.09      (((v1_xboole_0 @ sk_D)
% 7.88/8.09        | (v1_xboole_0 @ sk_C_2)
% 7.88/8.09        | (v1_xboole_0 @ sk_B_1)
% 7.88/8.09        | (v1_xboole_0 @ sk_A))),
% 7.88/8.09      inference('simplify', [status(thm)], ['176'])).
% 7.88/8.09  thf('178', plain, (~ (v1_xboole_0 @ sk_D)),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('179', plain,
% 7.88/8.09      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_C_2))),
% 7.88/8.09      inference('sup-', [status(thm)], ['177', '178'])).
% 7.88/8.09  thf('180', plain, (~ (v1_xboole_0 @ sk_A)),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('181', plain, (((v1_xboole_0 @ sk_C_2) | (v1_xboole_0 @ sk_B_1))),
% 7.88/8.09      inference('clc', [status(thm)], ['179', '180'])).
% 7.88/8.09  thf('182', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 7.88/8.09      inference('cnf', [status(esa)], [zf_stmt_0])).
% 7.88/8.09  thf('183', plain, ((v1_xboole_0 @ sk_B_1)),
% 7.88/8.09      inference('clc', [status(thm)], ['181', '182'])).
% 7.88/8.09  thf('184', plain, ($false), inference('demod', [status(thm)], ['0', '183'])).
% 7.88/8.09  
% 7.88/8.09  % SZS output end Refutation
% 7.88/8.09  
% 7.88/8.09  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
