%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6mQcf1uxOK

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:53 EST 2020

% Result     : Theorem 2.31s
% Output     : Refutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :  234 ( 795 expanded)
%              Number of leaves         :   43 ( 249 expanded)
%              Depth                    :   32
%              Number of atoms          : 3501 (30478 expanded)
%              Number of equality atoms :  112 ( 977 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
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

thf('4',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) )
      | ~ ( v1_funct_2 @ X52 @ X53 @ X54 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ X56 ) )
      | ( v1_xboole_0 @ X55 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ X56 ) )
      | ( v1_xboole_0 @ X53 )
      | ( v1_xboole_0 @ X54 )
      | ( v1_xboole_0 @ X56 )
      | ~ ( v1_funct_1 @ X57 )
      | ~ ( v1_funct_2 @ X57 @ X55 @ X54 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X54 ) ) )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X56 @ X54 @ X53 @ X55 @ X52 @ X57 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_tmap_1 @ X2 @ sk_B @ sk_C_1 @ X1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_tmap_1 @ X2 @ sk_B @ sk_C_1 @ X1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) )
      | ~ ( v1_funct_2 @ X52 @ X53 @ X54 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ X56 ) )
      | ( v1_xboole_0 @ X55 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ X56 ) )
      | ( v1_xboole_0 @ X53 )
      | ( v1_xboole_0 @ X54 )
      | ( v1_xboole_0 @ X56 )
      | ~ ( v1_funct_1 @ X57 )
      | ~ ( v1_funct_2 @ X57 @ X55 @ X54 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X54 ) ) )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X56 @ X54 @ X53 @ X55 @ X52 @ X57 ) @ ( k4_subset_1 @ X56 @ X53 @ X55 ) @ X54 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ ( k1_tmap_1 @ X1 @ sk_B @ sk_C_1 @ X0 @ sk_E @ X2 ) @ ( k4_subset_1 @ X1 @ sk_C_1 @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ ( k1_tmap_1 @ X1 @ sk_B @ sk_C_1 @ X0 @ sk_E @ X2 ) @ ( k4_subset_1 @ X1 @ sk_C_1 @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['16','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X52: $i,X53: $i,X54: $i,X55: $i,X56: $i,X57: $i] :
      ( ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X53 @ X54 ) ) )
      | ~ ( v1_funct_2 @ X52 @ X53 @ X54 )
      | ~ ( v1_funct_1 @ X52 )
      | ~ ( m1_subset_1 @ X55 @ ( k1_zfmisc_1 @ X56 ) )
      | ( v1_xboole_0 @ X55 )
      | ~ ( m1_subset_1 @ X53 @ ( k1_zfmisc_1 @ X56 ) )
      | ( v1_xboole_0 @ X53 )
      | ( v1_xboole_0 @ X54 )
      | ( v1_xboole_0 @ X56 )
      | ~ ( v1_funct_1 @ X57 )
      | ~ ( v1_funct_2 @ X57 @ X55 @ X54 )
      | ~ ( m1_subset_1 @ X57 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X55 @ X54 ) ) )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X56 @ X54 @ X53 @ X55 @ X52 @ X57 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X56 @ X53 @ X55 ) @ X54 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tmap_1 @ X1 @ sk_B @ sk_C_1 @ X0 @ sk_E @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X1 @ sk_C_1 @ X0 ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tmap_1 @ X1 @ sk_B @ sk_C_1 @ X0 @ sk_E @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X1 @ sk_C_1 @ X0 ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_D ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_D ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['31','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

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

thf('46',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( v1_xboole_0 @ X45 )
      | ( v1_xboole_0 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_funct_2 @ X48 @ X46 @ X45 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) )
      | ( X51
       != ( k1_tmap_1 @ X47 @ X45 @ X50 @ X46 @ X49 @ X48 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X47 @ X50 @ X46 ) @ X45 @ X51 @ X50 )
        = X49 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X47 @ X50 @ X46 ) @ X45 ) ) )
      | ~ ( v1_funct_2 @ X51 @ ( k4_subset_1 @ X47 @ X50 @ X46 ) @ X45 )
      | ~ ( v1_funct_1 @ X51 )
      | ( ( k2_partfun1 @ X50 @ X45 @ X49 @ ( k9_subset_1 @ X47 @ X50 @ X46 ) )
       != ( k2_partfun1 @ X46 @ X45 @ X48 @ ( k9_subset_1 @ X47 @ X50 @ X46 ) ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X45 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X47 ) )
      | ( v1_xboole_0 @ X50 )
      | ( v1_xboole_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('47',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( v1_xboole_0 @ X47 )
      | ( v1_xboole_0 @ X50 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X47 ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X45 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X45 ) ) )
      | ( ( k2_partfun1 @ X50 @ X45 @ X49 @ ( k9_subset_1 @ X47 @ X50 @ X46 ) )
       != ( k2_partfun1 @ X46 @ X45 @ X48 @ ( k9_subset_1 @ X47 @ X50 @ X46 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X47 @ X45 @ X50 @ X46 @ X49 @ X48 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X47 @ X45 @ X50 @ X46 @ X49 @ X48 ) @ ( k4_subset_1 @ X47 @ X50 @ X46 ) @ X45 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X47 @ X45 @ X50 @ X46 @ X49 @ X48 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X47 @ X50 @ X46 ) @ X45 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X47 @ X50 @ X46 ) @ X45 @ ( k1_tmap_1 @ X47 @ X45 @ X50 @ X46 @ X49 @ X48 ) @ X50 )
        = X49 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X46 @ X45 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) )
      | ( v1_xboole_0 @ X46 )
      | ( v1_xboole_0 @ X45 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('54',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r1_subset_1 @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r1_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ( ( r1_subset_1 @ A @ B )
      <=> ( r1_xboole_0 @ A @ B ) ) ) )).

thf('57',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ( v1_xboole_0 @ X29 )
      | ( r1_xboole_0 @ X28 @ X29 )
      | ~ ( r1_subset_1 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_subset_1])).

thf('58',plain,
    ( ( r1_xboole_0 @ sk_C_1 @ sk_D )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r1_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_D ),
    inference(clc,[status(thm)],['60','61'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('63',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('64',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('66',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ( ( k2_partfun1 @ X42 @ X43 @ X41 @ X44 )
        = ( k7_relat_1 @ X41 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('71',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v4_relat_1 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('72',plain,(
    v4_relat_1 @ sk_E @ sk_C_1 ),
    inference('sup-',[status(thm)],['70','71'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('73',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X26
        = ( k7_relat_1 @ X26 @ X27 ) )
      | ~ ( v4_relat_1 @ X26 @ X27 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('74',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ( sk_E
      = ( k7_relat_1 @ sk_E @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('76',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_relat_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('77',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['75','76'])).

thf('78',plain,
    ( sk_E
    = ( k7_relat_1 @ sk_E @ sk_C_1 ) ),
    inference(demod,[status(thm)],['74','77'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('79',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

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

thf('80',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('81',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('82',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['81'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('83',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('84',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['82','83'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('85',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['80','86'])).

thf('88',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['79','87'])).

thf(t207_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_xboole_0 @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = k1_xboole_0 ) ) ) )).

thf('89',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_xboole_0 @ X23 @ X24 )
      | ~ ( v1_relat_1 @ X25 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X25 @ X23 ) @ X24 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t207_relat_1])).

thf('90',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['78','90'])).

thf('92',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['75','76'])).

thf('93',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['91','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('95',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('96',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,(
    ! [X41: $i,X42: $i,X43: $i,X44: $i] :
      ( ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X43 ) ) )
      | ~ ( v1_funct_1 @ X41 )
      | ( ( k2_partfun1 @ X42 @ X43 @ X41 @ X44 )
        = ( k7_relat_1 @ X41 @ X44 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('98',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('102',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v4_relat_1 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('103',plain,(
    v4_relat_1 @ sk_F @ sk_D ),
    inference('sup-',[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X26: $i,X27: $i] :
      ( ( X26
        = ( k7_relat_1 @ X26 @ X27 ) )
      | ~ ( v4_relat_1 @ X26 @ X27 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('105',plain,
    ( ~ ( v1_relat_1 @ sk_F )
    | ( sk_F
      = ( k7_relat_1 @ sk_F @ sk_D ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('107',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_relat_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('108',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( sk_F
    = ( k7_relat_1 @ sk_F @ sk_D ) ),
    inference(demod,[status(thm)],['105','108'])).

thf('110',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('111',plain,
    ( ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F ) ),
    inference('sup+',[status(thm)],['109','110'])).

thf('112',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['106','107'])).

thf('113',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['111','112'])).

thf('114',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('118',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49','50','51','52','55','64','69','93','94','95','100','113','114','115','116','117'])).

thf('119',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['118'])).

thf('120',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('121',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E ) ),
    inference(split,[status(esa)],['120'])).

thf('122',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('123',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('124',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(split,[status(esa)],['120'])).

thf('125',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C_1 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['123','124'])).

thf('126',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('127',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k3_xboole_0 @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C_1 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['125','126'])).

thf('128',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k3_xboole_0 @ sk_C_1 @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C_1 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['122','127'])).

thf('129',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('131',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['91','92'])).

thf('132',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('133',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['111','112'])).

thf('134',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['128','129','130','131','132','133'])).

thf('135',plain,
    ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['134'])).

thf('136',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('137',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('138',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('139',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i,X51: $i] :
      ( ( v1_xboole_0 @ X45 )
      | ( v1_xboole_0 @ X46 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( v1_funct_2 @ X48 @ X46 @ X45 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) )
      | ( X51
       != ( k1_tmap_1 @ X47 @ X45 @ X50 @ X46 @ X49 @ X48 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X47 @ X50 @ X46 ) @ X45 @ X51 @ X46 )
        = X48 )
      | ~ ( m1_subset_1 @ X51 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X47 @ X50 @ X46 ) @ X45 ) ) )
      | ~ ( v1_funct_2 @ X51 @ ( k4_subset_1 @ X47 @ X50 @ X46 ) @ X45 )
      | ~ ( v1_funct_1 @ X51 )
      | ( ( k2_partfun1 @ X50 @ X45 @ X49 @ ( k9_subset_1 @ X47 @ X50 @ X46 ) )
       != ( k2_partfun1 @ X46 @ X45 @ X48 @ ( k9_subset_1 @ X47 @ X50 @ X46 ) ) )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X45 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X47 ) )
      | ( v1_xboole_0 @ X50 )
      | ( v1_xboole_0 @ X47 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('140',plain,(
    ! [X45: $i,X46: $i,X47: $i,X48: $i,X49: $i,X50: $i] :
      ( ( v1_xboole_0 @ X47 )
      | ( v1_xboole_0 @ X50 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X47 ) )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X45 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X45 ) ) )
      | ( ( k2_partfun1 @ X50 @ X45 @ X49 @ ( k9_subset_1 @ X47 @ X50 @ X46 ) )
       != ( k2_partfun1 @ X46 @ X45 @ X48 @ ( k9_subset_1 @ X47 @ X50 @ X46 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X47 @ X45 @ X50 @ X46 @ X49 @ X48 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X47 @ X45 @ X50 @ X46 @ X49 @ X48 ) @ ( k4_subset_1 @ X47 @ X50 @ X46 ) @ X45 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X47 @ X45 @ X50 @ X46 @ X49 @ X48 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X47 @ X50 @ X46 ) @ X45 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X47 @ X50 @ X46 ) @ X45 @ ( k1_tmap_1 @ X47 @ X45 @ X50 @ X46 @ X49 @ X48 ) @ X46 )
        = X48 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X46 @ X45 ) ) )
      | ~ ( v1_funct_2 @ X48 @ X46 @ X45 )
      | ~ ( v1_funct_1 @ X48 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ X47 ) )
      | ( v1_xboole_0 @ X46 )
      | ( v1_xboole_0 @ X45 ) ) ),
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['138','140'])).

thf('142',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('147',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('148',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('149',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['91','92'])).

thf('150',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('151',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('152',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('153',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['111','112'])).

thf('154',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('155',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['141','142','143','144','145','146','147','148','149','150','151','152','153','154','155','156','157'])).

thf('159',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['158'])).

thf('160',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['137','159'])).

thf('161',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference('sup-',[status(thm)],['136','161'])).

thf('163',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['162'])).

thf('164',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['120'])).

thf('165',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['168','169'])).

thf('171',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['170','171'])).

thf('173',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('174',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['172','173'])).

thf('175',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(split,[status(esa)],['120'])).

thf('176',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['135','174','175'])).

thf('177',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['121','176'])).

thf('178',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['119','177'])).

thf('179',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['30','178'])).

thf('180',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['179'])).

thf('181',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','180'])).

thf('182',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['181'])).

thf('183',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['182','183'])).

thf('185',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('186',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['184','185'])).

thf('187',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('188',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['186','187'])).

thf('189',plain,(
    $false ),
    inference(demod,[status(thm)],['0','188'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6mQcf1uxOK
% 0.13/0.37  % Computer   : n002.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 17:39:07 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.37  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 2.31/2.55  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 2.31/2.55  % Solved by: fo/fo7.sh
% 2.31/2.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 2.31/2.55  % done 3770 iterations in 2.063s
% 2.31/2.55  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 2.31/2.55  % SZS output start Refutation
% 2.31/2.55  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 2.31/2.55  thf(sk_A_type, type, sk_A: $i).
% 2.31/2.55  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 2.31/2.55  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 2.31/2.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 2.31/2.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 2.31/2.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 2.31/2.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 2.31/2.55  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 2.31/2.55  thf(sk_C_1_type, type, sk_C_1: $i).
% 2.31/2.55  thf(sk_F_type, type, sk_F: $i).
% 2.31/2.55  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 2.31/2.55  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 2.31/2.55  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 2.31/2.55  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 2.31/2.55  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 2.31/2.55  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 2.31/2.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 2.31/2.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 2.31/2.55  thf(sk_B_type, type, sk_B: $i).
% 2.31/2.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 2.31/2.55  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 2.31/2.55  thf(sk_D_type, type, sk_D: $i).
% 2.31/2.55  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 2.31/2.55  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 2.31/2.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 2.31/2.55  thf(sk_E_type, type, sk_E: $i).
% 2.31/2.55  thf(t6_tmap_1, conjecture,
% 2.31/2.55    (![A:$i]:
% 2.31/2.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.31/2.55       ( ![B:$i]:
% 2.31/2.55         ( ( ~( v1_xboole_0 @ B ) ) =>
% 2.31/2.55           ( ![C:$i]:
% 2.31/2.55             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 2.31/2.55                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.31/2.55               ( ![D:$i]:
% 2.31/2.55                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 2.31/2.55                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.31/2.55                   ( ( r1_subset_1 @ C @ D ) =>
% 2.31/2.55                     ( ![E:$i]:
% 2.31/2.55                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 2.31/2.55                           ( m1_subset_1 @
% 2.31/2.55                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 2.31/2.55                         ( ![F:$i]:
% 2.31/2.55                           ( ( ( v1_funct_1 @ F ) & 
% 2.31/2.55                               ( v1_funct_2 @ F @ D @ B ) & 
% 2.31/2.55                               ( m1_subset_1 @
% 2.31/2.55                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 2.31/2.55                             ( ( ( k2_partfun1 @
% 2.31/2.55                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 2.31/2.55                                 ( k2_partfun1 @
% 2.31/2.55                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 2.31/2.55                               ( ( k2_partfun1 @
% 2.31/2.55                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 2.31/2.55                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 2.31/2.55                                 ( E ) ) & 
% 2.31/2.55                               ( ( k2_partfun1 @
% 2.31/2.55                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 2.31/2.55                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 2.31/2.55                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 2.31/2.55  thf(zf_stmt_0, negated_conjecture,
% 2.31/2.55    (~( ![A:$i]:
% 2.31/2.55        ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.31/2.55          ( ![B:$i]:
% 2.31/2.55            ( ( ~( v1_xboole_0 @ B ) ) =>
% 2.31/2.55              ( ![C:$i]:
% 2.31/2.55                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 2.31/2.55                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.31/2.55                  ( ![D:$i]:
% 2.31/2.55                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 2.31/2.55                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.31/2.55                      ( ( r1_subset_1 @ C @ D ) =>
% 2.31/2.55                        ( ![E:$i]:
% 2.31/2.55                          ( ( ( v1_funct_1 @ E ) & 
% 2.31/2.55                              ( v1_funct_2 @ E @ C @ B ) & 
% 2.31/2.55                              ( m1_subset_1 @
% 2.31/2.55                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 2.31/2.55                            ( ![F:$i]:
% 2.31/2.55                              ( ( ( v1_funct_1 @ F ) & 
% 2.31/2.55                                  ( v1_funct_2 @ F @ D @ B ) & 
% 2.31/2.55                                  ( m1_subset_1 @
% 2.31/2.55                                    F @ 
% 2.31/2.55                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 2.31/2.55                                ( ( ( k2_partfun1 @
% 2.31/2.55                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 2.31/2.55                                    ( k2_partfun1 @
% 2.31/2.55                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 2.31/2.55                                  ( ( k2_partfun1 @
% 2.31/2.55                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 2.31/2.55                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 2.31/2.55                                    ( E ) ) & 
% 2.31/2.55                                  ( ( k2_partfun1 @
% 2.31/2.55                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 2.31/2.55                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 2.31/2.55                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 2.31/2.55    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 2.31/2.55  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf('1', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf('2', plain,
% 2.31/2.55      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf('3', plain,
% 2.31/2.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf(dt_k1_tmap_1, axiom,
% 2.31/2.55    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 2.31/2.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 2.31/2.55         ( ~( v1_xboole_0 @ C ) ) & 
% 2.31/2.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 2.31/2.55         ( ~( v1_xboole_0 @ D ) ) & 
% 2.31/2.55         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 2.31/2.55         ( v1_funct_2 @ E @ C @ B ) & 
% 2.31/2.55         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 2.31/2.55         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 2.31/2.55         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 2.31/2.55       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 2.31/2.55         ( v1_funct_2 @
% 2.31/2.55           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.31/2.55           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 2.31/2.55         ( m1_subset_1 @
% 2.31/2.55           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 2.31/2.55           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 2.31/2.55  thf('4', plain,
% 2.31/2.55      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 2.31/2.55         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54)))
% 2.31/2.55          | ~ (v1_funct_2 @ X52 @ X53 @ X54)
% 2.31/2.55          | ~ (v1_funct_1 @ X52)
% 2.31/2.55          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ X56))
% 2.31/2.55          | (v1_xboole_0 @ X55)
% 2.31/2.55          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ X56))
% 2.31/2.55          | (v1_xboole_0 @ X53)
% 2.31/2.55          | (v1_xboole_0 @ X54)
% 2.31/2.55          | (v1_xboole_0 @ X56)
% 2.31/2.55          | ~ (v1_funct_1 @ X57)
% 2.31/2.55          | ~ (v1_funct_2 @ X57 @ X55 @ X54)
% 2.31/2.55          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X54)))
% 2.31/2.55          | (v1_funct_1 @ (k1_tmap_1 @ X56 @ X54 @ X53 @ X55 @ X52 @ X57)))),
% 2.31/2.55      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 2.31/2.55  thf('5', plain,
% 2.31/2.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.31/2.55         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C_1 @ X1 @ sk_E @ X0))
% 2.31/2.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.31/2.55          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.31/2.55          | ~ (v1_funct_1 @ X0)
% 2.31/2.55          | (v1_xboole_0 @ X2)
% 2.31/2.55          | (v1_xboole_0 @ sk_B)
% 2.31/2.55          | (v1_xboole_0 @ sk_C_1)
% 2.31/2.55          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X2))
% 2.31/2.55          | (v1_xboole_0 @ X1)
% 2.31/2.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 2.31/2.55          | ~ (v1_funct_1 @ sk_E)
% 2.31/2.55          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B))),
% 2.31/2.55      inference('sup-', [status(thm)], ['3', '4'])).
% 2.31/2.55  thf('6', plain, ((v1_funct_1 @ sk_E)),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf('7', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf('8', plain,
% 2.31/2.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.31/2.55         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C_1 @ X1 @ sk_E @ X0))
% 2.31/2.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 2.31/2.55          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 2.31/2.55          | ~ (v1_funct_1 @ X0)
% 2.31/2.55          | (v1_xboole_0 @ X2)
% 2.31/2.55          | (v1_xboole_0 @ sk_B)
% 2.31/2.55          | (v1_xboole_0 @ sk_C_1)
% 2.31/2.55          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X2))
% 2.31/2.55          | (v1_xboole_0 @ X1)
% 2.31/2.55          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 2.31/2.55      inference('demod', [status(thm)], ['5', '6', '7'])).
% 2.31/2.55  thf('9', plain,
% 2.31/2.55      (![X0 : $i]:
% 2.31/2.55         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 2.31/2.55          | (v1_xboole_0 @ sk_D)
% 2.31/2.55          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 2.31/2.55          | (v1_xboole_0 @ sk_C_1)
% 2.31/2.55          | (v1_xboole_0 @ sk_B)
% 2.31/2.55          | (v1_xboole_0 @ X0)
% 2.31/2.55          | ~ (v1_funct_1 @ sk_F)
% 2.31/2.55          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 2.31/2.55          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F)))),
% 2.31/2.55      inference('sup-', [status(thm)], ['2', '8'])).
% 2.31/2.55  thf('10', plain, ((v1_funct_1 @ sk_F)),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf('11', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf('12', plain,
% 2.31/2.55      (![X0 : $i]:
% 2.31/2.55         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 2.31/2.55          | (v1_xboole_0 @ sk_D)
% 2.31/2.55          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 2.31/2.55          | (v1_xboole_0 @ sk_C_1)
% 2.31/2.55          | (v1_xboole_0 @ sk_B)
% 2.31/2.55          | (v1_xboole_0 @ X0)
% 2.31/2.55          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F)))),
% 2.31/2.55      inference('demod', [status(thm)], ['9', '10', '11'])).
% 2.31/2.55  thf('13', plain,
% 2.31/2.55      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 2.31/2.55        | (v1_xboole_0 @ sk_A)
% 2.31/2.55        | (v1_xboole_0 @ sk_B)
% 2.31/2.55        | (v1_xboole_0 @ sk_C_1)
% 2.31/2.55        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 2.31/2.55        | (v1_xboole_0 @ sk_D))),
% 2.31/2.55      inference('sup-', [status(thm)], ['1', '12'])).
% 2.31/2.55  thf('14', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf('15', plain,
% 2.31/2.55      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 2.31/2.55        | (v1_xboole_0 @ sk_A)
% 2.31/2.55        | (v1_xboole_0 @ sk_B)
% 2.31/2.55        | (v1_xboole_0 @ sk_C_1)
% 2.31/2.55        | (v1_xboole_0 @ sk_D))),
% 2.31/2.55      inference('demod', [status(thm)], ['13', '14'])).
% 2.31/2.55  thf('16', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf('17', plain,
% 2.31/2.55      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf('18', plain,
% 2.31/2.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf('19', plain,
% 2.31/2.55      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 2.31/2.55         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54)))
% 2.31/2.55          | ~ (v1_funct_2 @ X52 @ X53 @ X54)
% 2.31/2.55          | ~ (v1_funct_1 @ X52)
% 2.31/2.55          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ X56))
% 2.31/2.55          | (v1_xboole_0 @ X55)
% 2.31/2.55          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ X56))
% 2.31/2.55          | (v1_xboole_0 @ X53)
% 2.31/2.55          | (v1_xboole_0 @ X54)
% 2.31/2.55          | (v1_xboole_0 @ X56)
% 2.31/2.55          | ~ (v1_funct_1 @ X57)
% 2.31/2.55          | ~ (v1_funct_2 @ X57 @ X55 @ X54)
% 2.31/2.55          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X54)))
% 2.31/2.55          | (v1_funct_2 @ (k1_tmap_1 @ X56 @ X54 @ X53 @ X55 @ X52 @ X57) @ 
% 2.31/2.55             (k4_subset_1 @ X56 @ X53 @ X55) @ X54))),
% 2.31/2.55      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 2.31/2.55  thf('20', plain,
% 2.31/2.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.31/2.55         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 2.31/2.55           (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B)
% 2.31/2.55          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 2.31/2.55          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 2.31/2.55          | ~ (v1_funct_1 @ X2)
% 2.31/2.55          | (v1_xboole_0 @ X1)
% 2.31/2.55          | (v1_xboole_0 @ sk_B)
% 2.31/2.55          | (v1_xboole_0 @ sk_C_1)
% 2.31/2.55          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 2.31/2.55          | (v1_xboole_0 @ X0)
% 2.31/2.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.31/2.55          | ~ (v1_funct_1 @ sk_E)
% 2.31/2.55          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B))),
% 2.31/2.55      inference('sup-', [status(thm)], ['18', '19'])).
% 2.31/2.55  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf('22', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf('23', plain,
% 2.31/2.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.31/2.55         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 2.31/2.55           (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B)
% 2.31/2.55          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 2.31/2.55          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 2.31/2.55          | ~ (v1_funct_1 @ X2)
% 2.31/2.55          | (v1_xboole_0 @ X1)
% 2.31/2.55          | (v1_xboole_0 @ sk_B)
% 2.31/2.55          | (v1_xboole_0 @ sk_C_1)
% 2.31/2.55          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 2.31/2.55          | (v1_xboole_0 @ X0)
% 2.31/2.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 2.31/2.55      inference('demod', [status(thm)], ['20', '21', '22'])).
% 2.31/2.55  thf('24', plain,
% 2.31/2.55      (![X0 : $i]:
% 2.31/2.55         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 2.31/2.55          | (v1_xboole_0 @ sk_D)
% 2.31/2.55          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 2.31/2.55          | (v1_xboole_0 @ sk_C_1)
% 2.31/2.55          | (v1_xboole_0 @ sk_B)
% 2.31/2.55          | (v1_xboole_0 @ X0)
% 2.31/2.55          | ~ (v1_funct_1 @ sk_F)
% 2.31/2.55          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 2.31/2.55          | (v1_funct_2 @ 
% 2.31/2.55             (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 2.31/2.55             (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B))),
% 2.31/2.55      inference('sup-', [status(thm)], ['17', '23'])).
% 2.31/2.55  thf('25', plain, ((v1_funct_1 @ sk_F)),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf('26', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf('27', plain,
% 2.31/2.55      (![X0 : $i]:
% 2.31/2.55         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 2.31/2.55          | (v1_xboole_0 @ sk_D)
% 2.31/2.55          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 2.31/2.55          | (v1_xboole_0 @ sk_C_1)
% 2.31/2.55          | (v1_xboole_0 @ sk_B)
% 2.31/2.55          | (v1_xboole_0 @ X0)
% 2.31/2.55          | (v1_funct_2 @ 
% 2.31/2.55             (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 2.31/2.55             (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B))),
% 2.31/2.55      inference('demod', [status(thm)], ['24', '25', '26'])).
% 2.31/2.55  thf('28', plain,
% 2.31/2.55      (((v1_funct_2 @ 
% 2.31/2.55         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 2.31/2.55         (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 2.31/2.55        | (v1_xboole_0 @ sk_A)
% 2.31/2.55        | (v1_xboole_0 @ sk_B)
% 2.31/2.55        | (v1_xboole_0 @ sk_C_1)
% 2.31/2.55        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 2.31/2.55        | (v1_xboole_0 @ sk_D))),
% 2.31/2.55      inference('sup-', [status(thm)], ['16', '27'])).
% 2.31/2.55  thf('29', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf('30', plain,
% 2.31/2.55      (((v1_funct_2 @ 
% 2.31/2.55         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 2.31/2.55         (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 2.31/2.55        | (v1_xboole_0 @ sk_A)
% 2.31/2.55        | (v1_xboole_0 @ sk_B)
% 2.31/2.55        | (v1_xboole_0 @ sk_C_1)
% 2.31/2.55        | (v1_xboole_0 @ sk_D))),
% 2.31/2.55      inference('demod', [status(thm)], ['28', '29'])).
% 2.31/2.55  thf('31', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf('32', plain,
% 2.31/2.55      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf('33', plain,
% 2.31/2.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf('34', plain,
% 2.31/2.55      (![X52 : $i, X53 : $i, X54 : $i, X55 : $i, X56 : $i, X57 : $i]:
% 2.31/2.55         (~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X53 @ X54)))
% 2.31/2.55          | ~ (v1_funct_2 @ X52 @ X53 @ X54)
% 2.31/2.55          | ~ (v1_funct_1 @ X52)
% 2.31/2.55          | ~ (m1_subset_1 @ X55 @ (k1_zfmisc_1 @ X56))
% 2.31/2.55          | (v1_xboole_0 @ X55)
% 2.31/2.55          | ~ (m1_subset_1 @ X53 @ (k1_zfmisc_1 @ X56))
% 2.31/2.55          | (v1_xboole_0 @ X53)
% 2.31/2.55          | (v1_xboole_0 @ X54)
% 2.31/2.55          | (v1_xboole_0 @ X56)
% 2.31/2.55          | ~ (v1_funct_1 @ X57)
% 2.31/2.55          | ~ (v1_funct_2 @ X57 @ X55 @ X54)
% 2.31/2.55          | ~ (m1_subset_1 @ X57 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X55 @ X54)))
% 2.31/2.55          | (m1_subset_1 @ (k1_tmap_1 @ X56 @ X54 @ X53 @ X55 @ X52 @ X57) @ 
% 2.31/2.55             (k1_zfmisc_1 @ 
% 2.31/2.55              (k2_zfmisc_1 @ (k4_subset_1 @ X56 @ X53 @ X55) @ X54))))),
% 2.31/2.55      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 2.31/2.55  thf('35', plain,
% 2.31/2.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.31/2.55         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 2.31/2.55           (k1_zfmisc_1 @ 
% 2.31/2.55            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B)))
% 2.31/2.55          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 2.31/2.55          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 2.31/2.55          | ~ (v1_funct_1 @ X2)
% 2.31/2.55          | (v1_xboole_0 @ X1)
% 2.31/2.55          | (v1_xboole_0 @ sk_B)
% 2.31/2.55          | (v1_xboole_0 @ sk_C_1)
% 2.31/2.55          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 2.31/2.55          | (v1_xboole_0 @ X0)
% 2.31/2.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 2.31/2.55          | ~ (v1_funct_1 @ sk_E)
% 2.31/2.55          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B))),
% 2.31/2.55      inference('sup-', [status(thm)], ['33', '34'])).
% 2.31/2.55  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf('37', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf('38', plain,
% 2.31/2.55      (![X0 : $i, X1 : $i, X2 : $i]:
% 2.31/2.55         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 2.31/2.55           (k1_zfmisc_1 @ 
% 2.31/2.55            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B)))
% 2.31/2.55          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 2.31/2.55          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 2.31/2.55          | ~ (v1_funct_1 @ X2)
% 2.31/2.55          | (v1_xboole_0 @ X1)
% 2.31/2.55          | (v1_xboole_0 @ sk_B)
% 2.31/2.55          | (v1_xboole_0 @ sk_C_1)
% 2.31/2.55          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 2.31/2.55          | (v1_xboole_0 @ X0)
% 2.31/2.55          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 2.31/2.55      inference('demod', [status(thm)], ['35', '36', '37'])).
% 2.31/2.55  thf('39', plain,
% 2.31/2.55      (![X0 : $i]:
% 2.31/2.55         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 2.31/2.55          | (v1_xboole_0 @ sk_D)
% 2.31/2.55          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 2.31/2.55          | (v1_xboole_0 @ sk_C_1)
% 2.31/2.55          | (v1_xboole_0 @ sk_B)
% 2.31/2.55          | (v1_xboole_0 @ X0)
% 2.31/2.55          | ~ (v1_funct_1 @ sk_F)
% 2.31/2.55          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 2.31/2.55          | (m1_subset_1 @ 
% 2.31/2.55             (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 2.31/2.55             (k1_zfmisc_1 @ 
% 2.31/2.55              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B))))),
% 2.31/2.55      inference('sup-', [status(thm)], ['32', '38'])).
% 2.31/2.55  thf('40', plain, ((v1_funct_1 @ sk_F)),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf('41', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf('42', plain,
% 2.31/2.55      (![X0 : $i]:
% 2.31/2.55         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 2.31/2.55          | (v1_xboole_0 @ sk_D)
% 2.31/2.55          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 2.31/2.55          | (v1_xboole_0 @ sk_C_1)
% 2.31/2.55          | (v1_xboole_0 @ sk_B)
% 2.31/2.55          | (v1_xboole_0 @ X0)
% 2.31/2.55          | (m1_subset_1 @ 
% 2.31/2.55             (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 2.31/2.55             (k1_zfmisc_1 @ 
% 2.31/2.55              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B))))),
% 2.31/2.55      inference('demod', [status(thm)], ['39', '40', '41'])).
% 2.31/2.55  thf('43', plain,
% 2.31/2.55      (((m1_subset_1 @ 
% 2.31/2.55         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 2.31/2.55         (k1_zfmisc_1 @ 
% 2.31/2.55          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)))
% 2.31/2.55        | (v1_xboole_0 @ sk_A)
% 2.31/2.55        | (v1_xboole_0 @ sk_B)
% 2.31/2.55        | (v1_xboole_0 @ sk_C_1)
% 2.31/2.55        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 2.31/2.55        | (v1_xboole_0 @ sk_D))),
% 2.31/2.55      inference('sup-', [status(thm)], ['31', '42'])).
% 2.31/2.55  thf('44', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf('45', plain,
% 2.31/2.55      (((m1_subset_1 @ 
% 2.31/2.55         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 2.31/2.55         (k1_zfmisc_1 @ 
% 2.31/2.55          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)))
% 2.31/2.55        | (v1_xboole_0 @ sk_A)
% 2.31/2.55        | (v1_xboole_0 @ sk_B)
% 2.31/2.55        | (v1_xboole_0 @ sk_C_1)
% 2.31/2.55        | (v1_xboole_0 @ sk_D))),
% 2.31/2.55      inference('demod', [status(thm)], ['43', '44'])).
% 2.31/2.55  thf(d1_tmap_1, axiom,
% 2.31/2.55    (![A:$i]:
% 2.31/2.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 2.31/2.55       ( ![B:$i]:
% 2.31/2.55         ( ( ~( v1_xboole_0 @ B ) ) =>
% 2.31/2.55           ( ![C:$i]:
% 2.31/2.55             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 2.31/2.55                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.31/2.55               ( ![D:$i]:
% 2.31/2.55                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 2.31/2.55                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 2.31/2.55                   ( ![E:$i]:
% 2.31/2.55                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 2.31/2.55                         ( m1_subset_1 @
% 2.31/2.55                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 2.31/2.55                       ( ![F:$i]:
% 2.31/2.55                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 2.31/2.55                             ( m1_subset_1 @
% 2.31/2.55                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 2.31/2.55                           ( ( ( k2_partfun1 @
% 2.31/2.55                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 2.31/2.55                               ( k2_partfun1 @
% 2.31/2.55                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 2.31/2.55                             ( ![G:$i]:
% 2.31/2.55                               ( ( ( v1_funct_1 @ G ) & 
% 2.31/2.55                                   ( v1_funct_2 @
% 2.31/2.55                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 2.31/2.55                                   ( m1_subset_1 @
% 2.31/2.55                                     G @ 
% 2.31/2.55                                     ( k1_zfmisc_1 @
% 2.31/2.55                                       ( k2_zfmisc_1 @
% 2.31/2.55                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 2.31/2.55                                 ( ( ( G ) =
% 2.31/2.55                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 2.31/2.55                                   ( ( ( k2_partfun1 @
% 2.31/2.55                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 2.31/2.55                                         C ) =
% 2.31/2.55                                       ( E ) ) & 
% 2.31/2.55                                     ( ( k2_partfun1 @
% 2.31/2.55                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 2.31/2.55                                         D ) =
% 2.31/2.55                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 2.31/2.55  thf('46', plain,
% 2.31/2.55      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 2.31/2.55         ((v1_xboole_0 @ X45)
% 2.31/2.55          | (v1_xboole_0 @ X46)
% 2.31/2.55          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47))
% 2.31/2.55          | ~ (v1_funct_1 @ X48)
% 2.31/2.55          | ~ (v1_funct_2 @ X48 @ X46 @ X45)
% 2.31/2.55          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45)))
% 2.31/2.55          | ((X51) != (k1_tmap_1 @ X47 @ X45 @ X50 @ X46 @ X49 @ X48))
% 2.31/2.55          | ((k2_partfun1 @ (k4_subset_1 @ X47 @ X50 @ X46) @ X45 @ X51 @ X50)
% 2.31/2.55              = (X49))
% 2.31/2.55          | ~ (m1_subset_1 @ X51 @ 
% 2.31/2.55               (k1_zfmisc_1 @ 
% 2.31/2.55                (k2_zfmisc_1 @ (k4_subset_1 @ X47 @ X50 @ X46) @ X45)))
% 2.31/2.55          | ~ (v1_funct_2 @ X51 @ (k4_subset_1 @ X47 @ X50 @ X46) @ X45)
% 2.31/2.55          | ~ (v1_funct_1 @ X51)
% 2.31/2.55          | ((k2_partfun1 @ X50 @ X45 @ X49 @ (k9_subset_1 @ X47 @ X50 @ X46))
% 2.31/2.55              != (k2_partfun1 @ X46 @ X45 @ X48 @ 
% 2.31/2.55                  (k9_subset_1 @ X47 @ X50 @ X46)))
% 2.31/2.55          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X45)))
% 2.31/2.55          | ~ (v1_funct_2 @ X49 @ X50 @ X45)
% 2.31/2.55          | ~ (v1_funct_1 @ X49)
% 2.31/2.55          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X47))
% 2.31/2.55          | (v1_xboole_0 @ X50)
% 2.31/2.55          | (v1_xboole_0 @ X47))),
% 2.31/2.55      inference('cnf', [status(esa)], [d1_tmap_1])).
% 2.31/2.55  thf('47', plain,
% 2.31/2.55      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 2.31/2.55         ((v1_xboole_0 @ X47)
% 2.31/2.55          | (v1_xboole_0 @ X50)
% 2.31/2.55          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X47))
% 2.31/2.55          | ~ (v1_funct_1 @ X49)
% 2.31/2.55          | ~ (v1_funct_2 @ X49 @ X50 @ X45)
% 2.31/2.55          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X45)))
% 2.31/2.55          | ((k2_partfun1 @ X50 @ X45 @ X49 @ (k9_subset_1 @ X47 @ X50 @ X46))
% 2.31/2.55              != (k2_partfun1 @ X46 @ X45 @ X48 @ 
% 2.31/2.55                  (k9_subset_1 @ X47 @ X50 @ X46)))
% 2.31/2.55          | ~ (v1_funct_1 @ (k1_tmap_1 @ X47 @ X45 @ X50 @ X46 @ X49 @ X48))
% 2.31/2.55          | ~ (v1_funct_2 @ (k1_tmap_1 @ X47 @ X45 @ X50 @ X46 @ X49 @ X48) @ 
% 2.31/2.55               (k4_subset_1 @ X47 @ X50 @ X46) @ X45)
% 2.31/2.55          | ~ (m1_subset_1 @ (k1_tmap_1 @ X47 @ X45 @ X50 @ X46 @ X49 @ X48) @ 
% 2.31/2.55               (k1_zfmisc_1 @ 
% 2.31/2.55                (k2_zfmisc_1 @ (k4_subset_1 @ X47 @ X50 @ X46) @ X45)))
% 2.31/2.55          | ((k2_partfun1 @ (k4_subset_1 @ X47 @ X50 @ X46) @ X45 @ 
% 2.31/2.55              (k1_tmap_1 @ X47 @ X45 @ X50 @ X46 @ X49 @ X48) @ X50) = (
% 2.31/2.55              X49))
% 2.31/2.55          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45)))
% 2.31/2.55          | ~ (v1_funct_2 @ X48 @ X46 @ X45)
% 2.31/2.55          | ~ (v1_funct_1 @ X48)
% 2.31/2.55          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47))
% 2.31/2.55          | (v1_xboole_0 @ X46)
% 2.31/2.55          | (v1_xboole_0 @ X45))),
% 2.31/2.55      inference('simplify', [status(thm)], ['46'])).
% 2.31/2.55  thf('48', plain,
% 2.31/2.55      (((v1_xboole_0 @ sk_D)
% 2.31/2.55        | (v1_xboole_0 @ sk_C_1)
% 2.31/2.55        | (v1_xboole_0 @ sk_B)
% 2.31/2.55        | (v1_xboole_0 @ sk_A)
% 2.31/2.55        | (v1_xboole_0 @ sk_B)
% 2.31/2.55        | (v1_xboole_0 @ sk_D)
% 2.31/2.55        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 2.31/2.55        | ~ (v1_funct_1 @ sk_F)
% 2.31/2.55        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 2.31/2.55        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 2.31/2.55        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 2.31/2.55            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 2.31/2.55            = (sk_E))
% 2.31/2.55        | ~ (v1_funct_2 @ 
% 2.31/2.55             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 2.31/2.55             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 2.31/2.55        | ~ (v1_funct_1 @ 
% 2.31/2.55             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 2.31/2.55        | ((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 2.31/2.55            (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 2.31/2.55            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 2.31/2.55                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))
% 2.31/2.55        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))
% 2.31/2.55        | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)
% 2.31/2.55        | ~ (v1_funct_1 @ sk_E)
% 2.31/2.55        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 2.31/2.55        | (v1_xboole_0 @ sk_C_1)
% 2.31/2.55        | (v1_xboole_0 @ sk_A))),
% 2.31/2.55      inference('sup-', [status(thm)], ['45', '47'])).
% 2.31/2.55  thf('49', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf('50', plain, ((v1_funct_1 @ sk_F)),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf('51', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf('52', plain,
% 2.31/2.55      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf('53', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf(redefinition_k9_subset_1, axiom,
% 2.31/2.55    (![A:$i,B:$i,C:$i]:
% 2.31/2.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 2.31/2.55       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 2.31/2.55  thf('54', plain,
% 2.31/2.55      (![X10 : $i, X11 : $i, X12 : $i]:
% 2.31/2.55         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 2.31/2.55          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 2.31/2.55      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 2.31/2.55  thf('55', plain,
% 2.31/2.55      (![X0 : $i]:
% 2.31/2.55         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 2.31/2.55      inference('sup-', [status(thm)], ['53', '54'])).
% 2.31/2.55  thf('56', plain, ((r1_subset_1 @ sk_C_1 @ sk_D)),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf(redefinition_r1_subset_1, axiom,
% 2.31/2.55    (![A:$i,B:$i]:
% 2.31/2.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 2.31/2.55       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 2.31/2.55  thf('57', plain,
% 2.31/2.55      (![X28 : $i, X29 : $i]:
% 2.31/2.55         ((v1_xboole_0 @ X28)
% 2.31/2.55          | (v1_xboole_0 @ X29)
% 2.31/2.55          | (r1_xboole_0 @ X28 @ X29)
% 2.31/2.55          | ~ (r1_subset_1 @ X28 @ X29))),
% 2.31/2.55      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 2.31/2.55  thf('58', plain,
% 2.31/2.55      (((r1_xboole_0 @ sk_C_1 @ sk_D)
% 2.31/2.55        | (v1_xboole_0 @ sk_D)
% 2.31/2.55        | (v1_xboole_0 @ sk_C_1))),
% 2.31/2.55      inference('sup-', [status(thm)], ['56', '57'])).
% 2.31/2.55  thf('59', plain, (~ (v1_xboole_0 @ sk_D)),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf('60', plain, (((v1_xboole_0 @ sk_C_1) | (r1_xboole_0 @ sk_C_1 @ sk_D))),
% 2.31/2.55      inference('clc', [status(thm)], ['58', '59'])).
% 2.31/2.55  thf('61', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf('62', plain, ((r1_xboole_0 @ sk_C_1 @ sk_D)),
% 2.31/2.55      inference('clc', [status(thm)], ['60', '61'])).
% 2.31/2.55  thf(d7_xboole_0, axiom,
% 2.31/2.55    (![A:$i,B:$i]:
% 2.31/2.55     ( ( r1_xboole_0 @ A @ B ) <=>
% 2.31/2.55       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 2.31/2.55  thf('63', plain,
% 2.31/2.55      (![X0 : $i, X1 : $i]:
% 2.31/2.55         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 2.31/2.55      inference('cnf', [status(esa)], [d7_xboole_0])).
% 2.31/2.55  thf('64', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 2.31/2.55      inference('sup-', [status(thm)], ['62', '63'])).
% 2.31/2.55  thf('65', plain,
% 2.31/2.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf(redefinition_k2_partfun1, axiom,
% 2.31/2.55    (![A:$i,B:$i,C:$i,D:$i]:
% 2.31/2.55     ( ( ( v1_funct_1 @ C ) & 
% 2.31/2.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 2.31/2.55       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 2.31/2.55  thf('66', plain,
% 2.31/2.55      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 2.31/2.55         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 2.31/2.55          | ~ (v1_funct_1 @ X41)
% 2.31/2.55          | ((k2_partfun1 @ X42 @ X43 @ X41 @ X44) = (k7_relat_1 @ X41 @ X44)))),
% 2.31/2.55      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 2.31/2.55  thf('67', plain,
% 2.31/2.55      (![X0 : $i]:
% 2.31/2.55         (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 2.31/2.55          | ~ (v1_funct_1 @ sk_E))),
% 2.31/2.55      inference('sup-', [status(thm)], ['65', '66'])).
% 2.31/2.55  thf('68', plain, ((v1_funct_1 @ sk_E)),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf('69', plain,
% 2.31/2.55      (![X0 : $i]:
% 2.31/2.55         ((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 2.31/2.55      inference('demod', [status(thm)], ['67', '68'])).
% 2.31/2.55  thf('70', plain,
% 2.31/2.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf(cc2_relset_1, axiom,
% 2.31/2.55    (![A:$i,B:$i,C:$i]:
% 2.31/2.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.31/2.55       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 2.31/2.55  thf('71', plain,
% 2.31/2.55      (![X33 : $i, X34 : $i, X35 : $i]:
% 2.31/2.55         ((v4_relat_1 @ X33 @ X34)
% 2.31/2.55          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 2.31/2.55      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.31/2.55  thf('72', plain, ((v4_relat_1 @ sk_E @ sk_C_1)),
% 2.31/2.55      inference('sup-', [status(thm)], ['70', '71'])).
% 2.31/2.55  thf(t209_relat_1, axiom,
% 2.31/2.55    (![A:$i,B:$i]:
% 2.31/2.55     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 2.31/2.55       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 2.31/2.55  thf('73', plain,
% 2.31/2.55      (![X26 : $i, X27 : $i]:
% 2.31/2.55         (((X26) = (k7_relat_1 @ X26 @ X27))
% 2.31/2.55          | ~ (v4_relat_1 @ X26 @ X27)
% 2.31/2.55          | ~ (v1_relat_1 @ X26))),
% 2.31/2.55      inference('cnf', [status(esa)], [t209_relat_1])).
% 2.31/2.55  thf('74', plain,
% 2.31/2.55      ((~ (v1_relat_1 @ sk_E) | ((sk_E) = (k7_relat_1 @ sk_E @ sk_C_1)))),
% 2.31/2.55      inference('sup-', [status(thm)], ['72', '73'])).
% 2.31/2.55  thf('75', plain,
% 2.31/2.55      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 2.31/2.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.55  thf(cc1_relset_1, axiom,
% 2.31/2.55    (![A:$i,B:$i,C:$i]:
% 2.31/2.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 2.31/2.55       ( v1_relat_1 @ C ) ))).
% 2.31/2.55  thf('76', plain,
% 2.31/2.55      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.31/2.55         ((v1_relat_1 @ X30)
% 2.31/2.55          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 2.31/2.55      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.31/2.55  thf('77', plain, ((v1_relat_1 @ sk_E)),
% 2.31/2.55      inference('sup-', [status(thm)], ['75', '76'])).
% 2.31/2.55  thf('78', plain, (((sk_E) = (k7_relat_1 @ sk_E @ sk_C_1))),
% 2.31/2.55      inference('demod', [status(thm)], ['74', '77'])).
% 2.31/2.55  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 2.31/2.55  thf('79', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 2.31/2.55      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 2.31/2.55  thf(t3_xboole_0, axiom,
% 2.31/2.55    (![A:$i,B:$i]:
% 2.31/2.55     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 2.31/2.55            ( r1_xboole_0 @ A @ B ) ) ) & 
% 2.31/2.55       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 2.31/2.55            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 2.31/2.55  thf('80', plain,
% 2.31/2.55      (![X3 : $i, X4 : $i]:
% 2.31/2.55         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 2.31/2.56      inference('cnf', [status(esa)], [t3_xboole_0])).
% 2.31/2.56  thf(d10_xboole_0, axiom,
% 2.31/2.56    (![A:$i,B:$i]:
% 2.31/2.56     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 2.31/2.56  thf('81', plain,
% 2.31/2.56      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 2.31/2.56      inference('cnf', [status(esa)], [d10_xboole_0])).
% 2.31/2.56  thf('82', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 2.31/2.56      inference('simplify', [status(thm)], ['81'])).
% 2.31/2.56  thf(t3_subset, axiom,
% 2.31/2.56    (![A:$i,B:$i]:
% 2.31/2.56     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 2.31/2.56  thf('83', plain,
% 2.31/2.56      (![X15 : $i, X17 : $i]:
% 2.31/2.56         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 2.31/2.56      inference('cnf', [status(esa)], [t3_subset])).
% 2.31/2.56  thf('84', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 2.31/2.56      inference('sup-', [status(thm)], ['82', '83'])).
% 2.31/2.56  thf(t5_subset, axiom,
% 2.31/2.56    (![A:$i,B:$i,C:$i]:
% 2.31/2.56     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 2.31/2.56          ( v1_xboole_0 @ C ) ) ))).
% 2.31/2.56  thf('85', plain,
% 2.31/2.56      (![X18 : $i, X19 : $i, X20 : $i]:
% 2.31/2.56         (~ (r2_hidden @ X18 @ X19)
% 2.31/2.56          | ~ (v1_xboole_0 @ X20)
% 2.31/2.56          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 2.31/2.56      inference('cnf', [status(esa)], [t5_subset])).
% 2.31/2.56  thf('86', plain,
% 2.31/2.56      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 2.31/2.56      inference('sup-', [status(thm)], ['84', '85'])).
% 2.31/2.56  thf('87', plain,
% 2.31/2.56      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 2.31/2.56      inference('sup-', [status(thm)], ['80', '86'])).
% 2.31/2.56  thf('88', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 2.31/2.56      inference('sup-', [status(thm)], ['79', '87'])).
% 2.31/2.56  thf(t207_relat_1, axiom,
% 2.31/2.56    (![A:$i,B:$i,C:$i]:
% 2.31/2.56     ( ( v1_relat_1 @ C ) =>
% 2.31/2.56       ( ( r1_xboole_0 @ A @ B ) =>
% 2.31/2.56         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ))).
% 2.31/2.56  thf('89', plain,
% 2.31/2.56      (![X23 : $i, X24 : $i, X25 : $i]:
% 2.31/2.56         (~ (r1_xboole_0 @ X23 @ X24)
% 2.31/2.56          | ~ (v1_relat_1 @ X25)
% 2.31/2.56          | ((k7_relat_1 @ (k7_relat_1 @ X25 @ X23) @ X24) = (k1_xboole_0)))),
% 2.31/2.56      inference('cnf', [status(esa)], [t207_relat_1])).
% 2.31/2.56  thf('90', plain,
% 2.31/2.56      (![X0 : $i, X1 : $i]:
% 2.31/2.56         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 2.31/2.56          | ~ (v1_relat_1 @ X1))),
% 2.31/2.56      inference('sup-', [status(thm)], ['88', '89'])).
% 2.31/2.56  thf('91', plain,
% 2.31/2.56      ((((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))
% 2.31/2.56        | ~ (v1_relat_1 @ sk_E))),
% 2.31/2.56      inference('sup+', [status(thm)], ['78', '90'])).
% 2.31/2.56  thf('92', plain, ((v1_relat_1 @ sk_E)),
% 2.31/2.56      inference('sup-', [status(thm)], ['75', '76'])).
% 2.31/2.56  thf('93', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 2.31/2.56      inference('demod', [status(thm)], ['91', '92'])).
% 2.31/2.56  thf('94', plain,
% 2.31/2.56      (![X0 : $i]:
% 2.31/2.56         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 2.31/2.56      inference('sup-', [status(thm)], ['53', '54'])).
% 2.31/2.56  thf('95', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 2.31/2.56      inference('sup-', [status(thm)], ['62', '63'])).
% 2.31/2.56  thf('96', plain,
% 2.31/2.56      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 2.31/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.56  thf('97', plain,
% 2.31/2.56      (![X41 : $i, X42 : $i, X43 : $i, X44 : $i]:
% 2.31/2.56         (~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X43)))
% 2.31/2.56          | ~ (v1_funct_1 @ X41)
% 2.31/2.56          | ((k2_partfun1 @ X42 @ X43 @ X41 @ X44) = (k7_relat_1 @ X41 @ X44)))),
% 2.31/2.56      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 2.31/2.56  thf('98', plain,
% 2.31/2.56      (![X0 : $i]:
% 2.31/2.56         (((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 2.31/2.56          | ~ (v1_funct_1 @ sk_F))),
% 2.31/2.56      inference('sup-', [status(thm)], ['96', '97'])).
% 2.31/2.56  thf('99', plain, ((v1_funct_1 @ sk_F)),
% 2.31/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.56  thf('100', plain,
% 2.31/2.56      (![X0 : $i]:
% 2.31/2.56         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 2.31/2.56      inference('demod', [status(thm)], ['98', '99'])).
% 2.31/2.56  thf('101', plain,
% 2.31/2.56      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 2.31/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.56  thf('102', plain,
% 2.31/2.56      (![X33 : $i, X34 : $i, X35 : $i]:
% 2.31/2.56         ((v4_relat_1 @ X33 @ X34)
% 2.31/2.56          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 2.31/2.56      inference('cnf', [status(esa)], [cc2_relset_1])).
% 2.31/2.56  thf('103', plain, ((v4_relat_1 @ sk_F @ sk_D)),
% 2.31/2.56      inference('sup-', [status(thm)], ['101', '102'])).
% 2.31/2.56  thf('104', plain,
% 2.31/2.56      (![X26 : $i, X27 : $i]:
% 2.31/2.56         (((X26) = (k7_relat_1 @ X26 @ X27))
% 2.31/2.56          | ~ (v4_relat_1 @ X26 @ X27)
% 2.31/2.56          | ~ (v1_relat_1 @ X26))),
% 2.31/2.56      inference('cnf', [status(esa)], [t209_relat_1])).
% 2.31/2.56  thf('105', plain,
% 2.31/2.56      ((~ (v1_relat_1 @ sk_F) | ((sk_F) = (k7_relat_1 @ sk_F @ sk_D)))),
% 2.31/2.56      inference('sup-', [status(thm)], ['103', '104'])).
% 2.31/2.56  thf('106', plain,
% 2.31/2.56      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 2.31/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.56  thf('107', plain,
% 2.31/2.56      (![X30 : $i, X31 : $i, X32 : $i]:
% 2.31/2.56         ((v1_relat_1 @ X30)
% 2.31/2.56          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 2.31/2.56      inference('cnf', [status(esa)], [cc1_relset_1])).
% 2.31/2.56  thf('108', plain, ((v1_relat_1 @ sk_F)),
% 2.31/2.56      inference('sup-', [status(thm)], ['106', '107'])).
% 2.31/2.56  thf('109', plain, (((sk_F) = (k7_relat_1 @ sk_F @ sk_D))),
% 2.31/2.56      inference('demod', [status(thm)], ['105', '108'])).
% 2.31/2.56  thf('110', plain,
% 2.31/2.56      (![X0 : $i, X1 : $i]:
% 2.31/2.56         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 2.31/2.56          | ~ (v1_relat_1 @ X1))),
% 2.31/2.56      inference('sup-', [status(thm)], ['88', '89'])).
% 2.31/2.56  thf('111', plain,
% 2.31/2.56      ((((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))
% 2.31/2.56        | ~ (v1_relat_1 @ sk_F))),
% 2.31/2.56      inference('sup+', [status(thm)], ['109', '110'])).
% 2.31/2.56  thf('112', plain, ((v1_relat_1 @ sk_F)),
% 2.31/2.56      inference('sup-', [status(thm)], ['106', '107'])).
% 2.31/2.56  thf('113', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 2.31/2.56      inference('demod', [status(thm)], ['111', '112'])).
% 2.31/2.56  thf('114', plain,
% 2.31/2.56      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 2.31/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.56  thf('115', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)),
% 2.31/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.56  thf('116', plain, ((v1_funct_1 @ sk_E)),
% 2.31/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.56  thf('117', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 2.31/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.56  thf('118', plain,
% 2.31/2.56      (((v1_xboole_0 @ sk_D)
% 2.31/2.56        | (v1_xboole_0 @ sk_C_1)
% 2.31/2.56        | (v1_xboole_0 @ sk_B)
% 2.31/2.56        | (v1_xboole_0 @ sk_A)
% 2.31/2.56        | (v1_xboole_0 @ sk_B)
% 2.31/2.56        | (v1_xboole_0 @ sk_D)
% 2.31/2.56        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 2.31/2.56            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 2.31/2.56            = (sk_E))
% 2.31/2.56        | ~ (v1_funct_2 @ 
% 2.31/2.56             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 2.31/2.56             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 2.31/2.56        | ~ (v1_funct_1 @ 
% 2.31/2.56             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 2.31/2.56        | ((k1_xboole_0) != (k1_xboole_0))
% 2.31/2.56        | (v1_xboole_0 @ sk_C_1)
% 2.31/2.56        | (v1_xboole_0 @ sk_A))),
% 2.31/2.56      inference('demod', [status(thm)],
% 2.31/2.56                ['48', '49', '50', '51', '52', '55', '64', '69', '93', '94', 
% 2.31/2.56                 '95', '100', '113', '114', '115', '116', '117'])).
% 2.31/2.56  thf('119', plain,
% 2.31/2.56      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 2.31/2.56        | ~ (v1_funct_2 @ 
% 2.31/2.56             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 2.31/2.56             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 2.31/2.56        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 2.31/2.56            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 2.31/2.56            = (sk_E))
% 2.31/2.56        | (v1_xboole_0 @ sk_A)
% 2.31/2.56        | (v1_xboole_0 @ sk_B)
% 2.31/2.56        | (v1_xboole_0 @ sk_C_1)
% 2.31/2.56        | (v1_xboole_0 @ sk_D))),
% 2.31/2.56      inference('simplify', [status(thm)], ['118'])).
% 2.31/2.56  thf('120', plain,
% 2.31/2.56      ((((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 2.31/2.56          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 2.31/2.56          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 2.31/2.56              (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))
% 2.31/2.56        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 2.31/2.56            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 2.31/2.56            != (sk_E))
% 2.31/2.56        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 2.31/2.56            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 2.31/2.56            != (sk_F)))),
% 2.31/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.56  thf('121', plain,
% 2.31/2.56      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 2.31/2.56          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 2.31/2.56          != (sk_E)))
% 2.31/2.56         <= (~
% 2.31/2.56             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 2.31/2.56                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 2.31/2.56                sk_C_1) = (sk_E))))),
% 2.31/2.56      inference('split', [status(esa)], ['120'])).
% 2.31/2.56  thf('122', plain,
% 2.31/2.56      (![X0 : $i]:
% 2.31/2.56         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 2.31/2.56      inference('demod', [status(thm)], ['98', '99'])).
% 2.31/2.56  thf('123', plain,
% 2.31/2.56      (![X0 : $i]:
% 2.31/2.56         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 2.31/2.56      inference('sup-', [status(thm)], ['53', '54'])).
% 2.31/2.56  thf('124', plain,
% 2.31/2.56      ((((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 2.31/2.56          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 2.31/2.56          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 2.31/2.56              (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))))
% 2.31/2.56         <= (~
% 2.31/2.56             (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 2.31/2.56                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 2.31/2.56                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 2.31/2.56                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 2.31/2.56      inference('split', [status(esa)], ['120'])).
% 2.31/2.56  thf('125', plain,
% 2.31/2.56      ((((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 2.31/2.56          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 2.31/2.56          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C_1 @ sk_D))))
% 2.31/2.56         <= (~
% 2.31/2.56             (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 2.31/2.56                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 2.31/2.56                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 2.31/2.56                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 2.31/2.56      inference('sup-', [status(thm)], ['123', '124'])).
% 2.31/2.56  thf('126', plain,
% 2.31/2.56      (![X0 : $i]:
% 2.31/2.56         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 2.31/2.56      inference('sup-', [status(thm)], ['53', '54'])).
% 2.31/2.56  thf('127', plain,
% 2.31/2.56      ((((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C_1 @ sk_D))
% 2.31/2.56          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C_1 @ sk_D))))
% 2.31/2.56         <= (~
% 2.31/2.56             (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 2.31/2.56                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 2.31/2.56                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 2.31/2.56                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 2.31/2.56      inference('demod', [status(thm)], ['125', '126'])).
% 2.31/2.56  thf('128', plain,
% 2.31/2.56      ((((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C_1 @ sk_D))
% 2.31/2.56          != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C_1 @ sk_D))))
% 2.31/2.56         <= (~
% 2.31/2.56             (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 2.31/2.56                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 2.31/2.56                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 2.31/2.56                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 2.31/2.56      inference('sup-', [status(thm)], ['122', '127'])).
% 2.31/2.56  thf('129', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 2.31/2.56      inference('sup-', [status(thm)], ['62', '63'])).
% 2.31/2.56  thf('130', plain,
% 2.31/2.56      (![X0 : $i]:
% 2.31/2.56         ((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 2.31/2.56      inference('demod', [status(thm)], ['67', '68'])).
% 2.31/2.56  thf('131', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 2.31/2.56      inference('demod', [status(thm)], ['91', '92'])).
% 2.31/2.56  thf('132', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 2.31/2.56      inference('sup-', [status(thm)], ['62', '63'])).
% 2.31/2.56  thf('133', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 2.31/2.56      inference('demod', [status(thm)], ['111', '112'])).
% 2.31/2.56  thf('134', plain,
% 2.31/2.56      ((((k1_xboole_0) != (k1_xboole_0)))
% 2.31/2.56         <= (~
% 2.31/2.56             (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 2.31/2.56                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 2.31/2.56                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 2.31/2.56                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 2.31/2.56      inference('demod', [status(thm)],
% 2.31/2.56                ['128', '129', '130', '131', '132', '133'])).
% 2.31/2.56  thf('135', plain,
% 2.31/2.56      ((((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 2.31/2.56          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 2.31/2.56          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 2.31/2.56             (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))))),
% 2.31/2.56      inference('simplify', [status(thm)], ['134'])).
% 2.31/2.56  thf('136', plain,
% 2.31/2.56      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 2.31/2.56        | (v1_xboole_0 @ sk_A)
% 2.31/2.56        | (v1_xboole_0 @ sk_B)
% 2.31/2.56        | (v1_xboole_0 @ sk_C_1)
% 2.31/2.56        | (v1_xboole_0 @ sk_D))),
% 2.31/2.56      inference('demod', [status(thm)], ['13', '14'])).
% 2.31/2.56  thf('137', plain,
% 2.31/2.56      (((v1_funct_2 @ 
% 2.31/2.56         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 2.31/2.56         (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 2.31/2.56        | (v1_xboole_0 @ sk_A)
% 2.31/2.56        | (v1_xboole_0 @ sk_B)
% 2.31/2.56        | (v1_xboole_0 @ sk_C_1)
% 2.31/2.56        | (v1_xboole_0 @ sk_D))),
% 2.31/2.56      inference('demod', [status(thm)], ['28', '29'])).
% 2.31/2.56  thf('138', plain,
% 2.31/2.56      (((m1_subset_1 @ 
% 2.31/2.56         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 2.31/2.56         (k1_zfmisc_1 @ 
% 2.31/2.56          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)))
% 2.31/2.56        | (v1_xboole_0 @ sk_A)
% 2.31/2.56        | (v1_xboole_0 @ sk_B)
% 2.31/2.56        | (v1_xboole_0 @ sk_C_1)
% 2.31/2.56        | (v1_xboole_0 @ sk_D))),
% 2.31/2.56      inference('demod', [status(thm)], ['43', '44'])).
% 2.31/2.56  thf('139', plain,
% 2.31/2.56      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i, X51 : $i]:
% 2.31/2.56         ((v1_xboole_0 @ X45)
% 2.31/2.56          | (v1_xboole_0 @ X46)
% 2.31/2.56          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47))
% 2.31/2.56          | ~ (v1_funct_1 @ X48)
% 2.31/2.56          | ~ (v1_funct_2 @ X48 @ X46 @ X45)
% 2.31/2.56          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45)))
% 2.31/2.56          | ((X51) != (k1_tmap_1 @ X47 @ X45 @ X50 @ X46 @ X49 @ X48))
% 2.31/2.56          | ((k2_partfun1 @ (k4_subset_1 @ X47 @ X50 @ X46) @ X45 @ X51 @ X46)
% 2.31/2.56              = (X48))
% 2.31/2.56          | ~ (m1_subset_1 @ X51 @ 
% 2.31/2.56               (k1_zfmisc_1 @ 
% 2.31/2.56                (k2_zfmisc_1 @ (k4_subset_1 @ X47 @ X50 @ X46) @ X45)))
% 2.31/2.56          | ~ (v1_funct_2 @ X51 @ (k4_subset_1 @ X47 @ X50 @ X46) @ X45)
% 2.31/2.56          | ~ (v1_funct_1 @ X51)
% 2.31/2.56          | ((k2_partfun1 @ X50 @ X45 @ X49 @ (k9_subset_1 @ X47 @ X50 @ X46))
% 2.31/2.56              != (k2_partfun1 @ X46 @ X45 @ X48 @ 
% 2.31/2.56                  (k9_subset_1 @ X47 @ X50 @ X46)))
% 2.31/2.56          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X45)))
% 2.31/2.56          | ~ (v1_funct_2 @ X49 @ X50 @ X45)
% 2.31/2.56          | ~ (v1_funct_1 @ X49)
% 2.31/2.56          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X47))
% 2.31/2.56          | (v1_xboole_0 @ X50)
% 2.31/2.56          | (v1_xboole_0 @ X47))),
% 2.31/2.56      inference('cnf', [status(esa)], [d1_tmap_1])).
% 2.31/2.56  thf('140', plain,
% 2.31/2.56      (![X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i, X50 : $i]:
% 2.31/2.56         ((v1_xboole_0 @ X47)
% 2.31/2.56          | (v1_xboole_0 @ X50)
% 2.31/2.56          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X47))
% 2.31/2.56          | ~ (v1_funct_1 @ X49)
% 2.31/2.56          | ~ (v1_funct_2 @ X49 @ X50 @ X45)
% 2.31/2.56          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X45)))
% 2.31/2.56          | ((k2_partfun1 @ X50 @ X45 @ X49 @ (k9_subset_1 @ X47 @ X50 @ X46))
% 2.31/2.56              != (k2_partfun1 @ X46 @ X45 @ X48 @ 
% 2.31/2.56                  (k9_subset_1 @ X47 @ X50 @ X46)))
% 2.31/2.56          | ~ (v1_funct_1 @ (k1_tmap_1 @ X47 @ X45 @ X50 @ X46 @ X49 @ X48))
% 2.31/2.56          | ~ (v1_funct_2 @ (k1_tmap_1 @ X47 @ X45 @ X50 @ X46 @ X49 @ X48) @ 
% 2.31/2.56               (k4_subset_1 @ X47 @ X50 @ X46) @ X45)
% 2.31/2.56          | ~ (m1_subset_1 @ (k1_tmap_1 @ X47 @ X45 @ X50 @ X46 @ X49 @ X48) @ 
% 2.31/2.56               (k1_zfmisc_1 @ 
% 2.31/2.56                (k2_zfmisc_1 @ (k4_subset_1 @ X47 @ X50 @ X46) @ X45)))
% 2.31/2.56          | ((k2_partfun1 @ (k4_subset_1 @ X47 @ X50 @ X46) @ X45 @ 
% 2.31/2.56              (k1_tmap_1 @ X47 @ X45 @ X50 @ X46 @ X49 @ X48) @ X46) = (
% 2.31/2.56              X48))
% 2.31/2.56          | ~ (m1_subset_1 @ X48 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X46 @ X45)))
% 2.31/2.56          | ~ (v1_funct_2 @ X48 @ X46 @ X45)
% 2.31/2.56          | ~ (v1_funct_1 @ X48)
% 2.31/2.56          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ X47))
% 2.31/2.56          | (v1_xboole_0 @ X46)
% 2.31/2.56          | (v1_xboole_0 @ X45))),
% 2.31/2.56      inference('simplify', [status(thm)], ['139'])).
% 2.31/2.56  thf('141', plain,
% 2.31/2.56      (((v1_xboole_0 @ sk_D)
% 2.31/2.56        | (v1_xboole_0 @ sk_C_1)
% 2.31/2.56        | (v1_xboole_0 @ sk_B)
% 2.31/2.56        | (v1_xboole_0 @ sk_A)
% 2.31/2.56        | (v1_xboole_0 @ sk_B)
% 2.31/2.56        | (v1_xboole_0 @ sk_D)
% 2.31/2.56        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 2.31/2.56        | ~ (v1_funct_1 @ sk_F)
% 2.31/2.56        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 2.31/2.56        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 2.31/2.56        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 2.31/2.56            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 2.31/2.56            = (sk_F))
% 2.31/2.56        | ~ (v1_funct_2 @ 
% 2.31/2.56             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 2.31/2.56             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 2.31/2.56        | ~ (v1_funct_1 @ 
% 2.31/2.56             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 2.31/2.56        | ((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 2.31/2.56            (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 2.31/2.56            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 2.31/2.56                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))
% 2.31/2.56        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))
% 2.31/2.56        | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)
% 2.31/2.56        | ~ (v1_funct_1 @ sk_E)
% 2.31/2.56        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 2.31/2.56        | (v1_xboole_0 @ sk_C_1)
% 2.31/2.56        | (v1_xboole_0 @ sk_A))),
% 2.31/2.56      inference('sup-', [status(thm)], ['138', '140'])).
% 2.31/2.56  thf('142', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 2.31/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.56  thf('143', plain, ((v1_funct_1 @ sk_F)),
% 2.31/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.56  thf('144', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 2.31/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.56  thf('145', plain,
% 2.31/2.56      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 2.31/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.56  thf('146', plain,
% 2.31/2.56      (![X0 : $i]:
% 2.31/2.56         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 2.31/2.56      inference('sup-', [status(thm)], ['53', '54'])).
% 2.31/2.56  thf('147', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 2.31/2.56      inference('sup-', [status(thm)], ['62', '63'])).
% 2.31/2.56  thf('148', plain,
% 2.31/2.56      (![X0 : $i]:
% 2.31/2.56         ((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 2.31/2.56      inference('demod', [status(thm)], ['67', '68'])).
% 2.31/2.56  thf('149', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 2.31/2.56      inference('demod', [status(thm)], ['91', '92'])).
% 2.31/2.56  thf('150', plain,
% 2.31/2.56      (![X0 : $i]:
% 2.31/2.56         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 2.31/2.56      inference('sup-', [status(thm)], ['53', '54'])).
% 2.31/2.56  thf('151', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 2.31/2.56      inference('sup-', [status(thm)], ['62', '63'])).
% 2.31/2.56  thf('152', plain,
% 2.31/2.56      (![X0 : $i]:
% 2.31/2.56         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 2.31/2.56      inference('demod', [status(thm)], ['98', '99'])).
% 2.31/2.56  thf('153', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 2.31/2.56      inference('demod', [status(thm)], ['111', '112'])).
% 2.31/2.56  thf('154', plain,
% 2.31/2.56      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 2.31/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.56  thf('155', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)),
% 2.31/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.56  thf('156', plain, ((v1_funct_1 @ sk_E)),
% 2.31/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.56  thf('157', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 2.31/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.56  thf('158', plain,
% 2.31/2.56      (((v1_xboole_0 @ sk_D)
% 2.31/2.56        | (v1_xboole_0 @ sk_C_1)
% 2.31/2.56        | (v1_xboole_0 @ sk_B)
% 2.31/2.56        | (v1_xboole_0 @ sk_A)
% 2.31/2.56        | (v1_xboole_0 @ sk_B)
% 2.31/2.56        | (v1_xboole_0 @ sk_D)
% 2.31/2.56        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 2.31/2.56            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 2.31/2.56            = (sk_F))
% 2.31/2.56        | ~ (v1_funct_2 @ 
% 2.31/2.56             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 2.31/2.56             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 2.31/2.56        | ~ (v1_funct_1 @ 
% 2.31/2.56             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 2.31/2.56        | ((k1_xboole_0) != (k1_xboole_0))
% 2.31/2.56        | (v1_xboole_0 @ sk_C_1)
% 2.31/2.56        | (v1_xboole_0 @ sk_A))),
% 2.31/2.56      inference('demod', [status(thm)],
% 2.31/2.56                ['141', '142', '143', '144', '145', '146', '147', '148', 
% 2.31/2.56                 '149', '150', '151', '152', '153', '154', '155', '156', '157'])).
% 2.31/2.56  thf('159', plain,
% 2.31/2.56      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 2.31/2.56        | ~ (v1_funct_2 @ 
% 2.31/2.56             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 2.31/2.56             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 2.31/2.56        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 2.31/2.56            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 2.31/2.56            = (sk_F))
% 2.31/2.56        | (v1_xboole_0 @ sk_A)
% 2.31/2.56        | (v1_xboole_0 @ sk_B)
% 2.31/2.56        | (v1_xboole_0 @ sk_C_1)
% 2.31/2.56        | (v1_xboole_0 @ sk_D))),
% 2.31/2.56      inference('simplify', [status(thm)], ['158'])).
% 2.31/2.56  thf('160', plain,
% 2.31/2.56      (((v1_xboole_0 @ sk_D)
% 2.31/2.56        | (v1_xboole_0 @ sk_C_1)
% 2.31/2.56        | (v1_xboole_0 @ sk_B)
% 2.31/2.56        | (v1_xboole_0 @ sk_A)
% 2.31/2.56        | (v1_xboole_0 @ sk_D)
% 2.31/2.56        | (v1_xboole_0 @ sk_C_1)
% 2.31/2.56        | (v1_xboole_0 @ sk_B)
% 2.31/2.56        | (v1_xboole_0 @ sk_A)
% 2.31/2.56        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 2.31/2.56            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 2.31/2.56            = (sk_F))
% 2.31/2.56        | ~ (v1_funct_1 @ 
% 2.31/2.56             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F)))),
% 2.31/2.56      inference('sup-', [status(thm)], ['137', '159'])).
% 2.31/2.56  thf('161', plain,
% 2.31/2.56      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 2.31/2.56        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 2.31/2.56            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 2.31/2.56            = (sk_F))
% 2.31/2.56        | (v1_xboole_0 @ sk_A)
% 2.31/2.56        | (v1_xboole_0 @ sk_B)
% 2.31/2.56        | (v1_xboole_0 @ sk_C_1)
% 2.31/2.56        | (v1_xboole_0 @ sk_D))),
% 2.31/2.56      inference('simplify', [status(thm)], ['160'])).
% 2.31/2.56  thf('162', plain,
% 2.31/2.56      (((v1_xboole_0 @ sk_D)
% 2.31/2.56        | (v1_xboole_0 @ sk_C_1)
% 2.31/2.56        | (v1_xboole_0 @ sk_B)
% 2.31/2.56        | (v1_xboole_0 @ sk_A)
% 2.31/2.56        | (v1_xboole_0 @ sk_D)
% 2.31/2.56        | (v1_xboole_0 @ sk_C_1)
% 2.31/2.56        | (v1_xboole_0 @ sk_B)
% 2.31/2.56        | (v1_xboole_0 @ sk_A)
% 2.31/2.56        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 2.31/2.56            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 2.31/2.56            = (sk_F)))),
% 2.31/2.56      inference('sup-', [status(thm)], ['136', '161'])).
% 2.31/2.56  thf('163', plain,
% 2.31/2.56      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 2.31/2.56          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 2.31/2.56          = (sk_F))
% 2.31/2.56        | (v1_xboole_0 @ sk_A)
% 2.31/2.56        | (v1_xboole_0 @ sk_B)
% 2.31/2.56        | (v1_xboole_0 @ sk_C_1)
% 2.31/2.56        | (v1_xboole_0 @ sk_D))),
% 2.31/2.56      inference('simplify', [status(thm)], ['162'])).
% 2.31/2.56  thf('164', plain,
% 2.31/2.56      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 2.31/2.56          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 2.31/2.56          != (sk_F)))
% 2.31/2.56         <= (~
% 2.31/2.56             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 2.31/2.56                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 2.31/2.56                = (sk_F))))),
% 2.31/2.56      inference('split', [status(esa)], ['120'])).
% 2.31/2.56  thf('165', plain,
% 2.31/2.56      (((((sk_F) != (sk_F))
% 2.31/2.56         | (v1_xboole_0 @ sk_D)
% 2.31/2.56         | (v1_xboole_0 @ sk_C_1)
% 2.31/2.56         | (v1_xboole_0 @ sk_B)
% 2.31/2.56         | (v1_xboole_0 @ sk_A)))
% 2.31/2.56         <= (~
% 2.31/2.56             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 2.31/2.56                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 2.31/2.56                = (sk_F))))),
% 2.31/2.56      inference('sup-', [status(thm)], ['163', '164'])).
% 2.31/2.56  thf('166', plain,
% 2.31/2.56      ((((v1_xboole_0 @ sk_A)
% 2.31/2.56         | (v1_xboole_0 @ sk_B)
% 2.31/2.56         | (v1_xboole_0 @ sk_C_1)
% 2.31/2.56         | (v1_xboole_0 @ sk_D)))
% 2.31/2.56         <= (~
% 2.31/2.56             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 2.31/2.56                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 2.31/2.56                = (sk_F))))),
% 2.31/2.56      inference('simplify', [status(thm)], ['165'])).
% 2.31/2.56  thf('167', plain, (~ (v1_xboole_0 @ sk_D)),
% 2.31/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.56  thf('168', plain,
% 2.31/2.56      ((((v1_xboole_0 @ sk_C_1) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A)))
% 2.31/2.56         <= (~
% 2.31/2.56             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 2.31/2.56                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 2.31/2.56                = (sk_F))))),
% 2.31/2.56      inference('sup-', [status(thm)], ['166', '167'])).
% 2.31/2.56  thf('169', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 2.31/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.56  thf('170', plain,
% 2.31/2.56      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B)))
% 2.31/2.56         <= (~
% 2.31/2.56             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 2.31/2.56                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 2.31/2.56                = (sk_F))))),
% 2.31/2.56      inference('clc', [status(thm)], ['168', '169'])).
% 2.31/2.56  thf('171', plain, (~ (v1_xboole_0 @ sk_A)),
% 2.31/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.56  thf('172', plain,
% 2.31/2.56      (((v1_xboole_0 @ sk_B))
% 2.31/2.56         <= (~
% 2.31/2.56             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 2.31/2.56                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 2.31/2.56                = (sk_F))))),
% 2.31/2.56      inference('clc', [status(thm)], ['170', '171'])).
% 2.31/2.56  thf('173', plain, (~ (v1_xboole_0 @ sk_B)),
% 2.31/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.56  thf('174', plain,
% 2.31/2.56      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 2.31/2.56          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 2.31/2.56          = (sk_F)))),
% 2.31/2.56      inference('sup-', [status(thm)], ['172', '173'])).
% 2.31/2.56  thf('175', plain,
% 2.31/2.56      (~
% 2.31/2.56       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 2.31/2.56          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 2.31/2.56          = (sk_E))) | 
% 2.31/2.56       ~
% 2.31/2.56       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 2.31/2.56          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 2.31/2.56          = (sk_F))) | 
% 2.31/2.56       ~
% 2.31/2.56       (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 2.31/2.56          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 2.31/2.56          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 2.31/2.56             (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))))),
% 2.31/2.56      inference('split', [status(esa)], ['120'])).
% 2.31/2.56  thf('176', plain,
% 2.31/2.56      (~
% 2.31/2.56       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 2.31/2.56          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 2.31/2.56          = (sk_E)))),
% 2.31/2.56      inference('sat_resolution*', [status(thm)], ['135', '174', '175'])).
% 2.31/2.56  thf('177', plain,
% 2.31/2.56      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 2.31/2.56         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 2.31/2.56         != (sk_E))),
% 2.31/2.56      inference('simpl_trail', [status(thm)], ['121', '176'])).
% 2.31/2.56  thf('178', plain,
% 2.31/2.56      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 2.31/2.56        | ~ (v1_funct_2 @ 
% 2.31/2.56             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 2.31/2.56             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 2.31/2.56        | (v1_xboole_0 @ sk_A)
% 2.31/2.56        | (v1_xboole_0 @ sk_B)
% 2.31/2.56        | (v1_xboole_0 @ sk_C_1)
% 2.31/2.56        | (v1_xboole_0 @ sk_D))),
% 2.31/2.56      inference('simplify_reflect-', [status(thm)], ['119', '177'])).
% 2.31/2.56  thf('179', plain,
% 2.31/2.56      (((v1_xboole_0 @ sk_D)
% 2.31/2.56        | (v1_xboole_0 @ sk_C_1)
% 2.31/2.56        | (v1_xboole_0 @ sk_B)
% 2.31/2.56        | (v1_xboole_0 @ sk_A)
% 2.31/2.56        | (v1_xboole_0 @ sk_D)
% 2.31/2.56        | (v1_xboole_0 @ sk_C_1)
% 2.31/2.56        | (v1_xboole_0 @ sk_B)
% 2.31/2.56        | (v1_xboole_0 @ sk_A)
% 2.31/2.56        | ~ (v1_funct_1 @ 
% 2.31/2.56             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F)))),
% 2.31/2.56      inference('sup-', [status(thm)], ['30', '178'])).
% 2.31/2.56  thf('180', plain,
% 2.31/2.56      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 2.31/2.56        | (v1_xboole_0 @ sk_A)
% 2.31/2.56        | (v1_xboole_0 @ sk_B)
% 2.31/2.56        | (v1_xboole_0 @ sk_C_1)
% 2.31/2.56        | (v1_xboole_0 @ sk_D))),
% 2.31/2.56      inference('simplify', [status(thm)], ['179'])).
% 2.31/2.56  thf('181', plain,
% 2.31/2.56      (((v1_xboole_0 @ sk_D)
% 2.31/2.56        | (v1_xboole_0 @ sk_C_1)
% 2.31/2.56        | (v1_xboole_0 @ sk_B)
% 2.31/2.56        | (v1_xboole_0 @ sk_A)
% 2.31/2.56        | (v1_xboole_0 @ sk_D)
% 2.31/2.56        | (v1_xboole_0 @ sk_C_1)
% 2.31/2.56        | (v1_xboole_0 @ sk_B)
% 2.31/2.56        | (v1_xboole_0 @ sk_A))),
% 2.31/2.56      inference('sup-', [status(thm)], ['15', '180'])).
% 2.31/2.56  thf('182', plain,
% 2.31/2.56      (((v1_xboole_0 @ sk_A)
% 2.31/2.56        | (v1_xboole_0 @ sk_B)
% 2.31/2.56        | (v1_xboole_0 @ sk_C_1)
% 2.31/2.56        | (v1_xboole_0 @ sk_D))),
% 2.31/2.56      inference('simplify', [status(thm)], ['181'])).
% 2.31/2.56  thf('183', plain, (~ (v1_xboole_0 @ sk_D)),
% 2.31/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.56  thf('184', plain,
% 2.31/2.56      (((v1_xboole_0 @ sk_C_1) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 2.31/2.56      inference('sup-', [status(thm)], ['182', '183'])).
% 2.31/2.56  thf('185', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 2.31/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.56  thf('186', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B))),
% 2.31/2.56      inference('clc', [status(thm)], ['184', '185'])).
% 2.31/2.56  thf('187', plain, (~ (v1_xboole_0 @ sk_A)),
% 2.31/2.56      inference('cnf', [status(esa)], [zf_stmt_0])).
% 2.31/2.56  thf('188', plain, ((v1_xboole_0 @ sk_B)),
% 2.31/2.56      inference('clc', [status(thm)], ['186', '187'])).
% 2.31/2.56  thf('189', plain, ($false), inference('demod', [status(thm)], ['0', '188'])).
% 2.31/2.56  
% 2.31/2.56  % SZS output end Refutation
% 2.31/2.56  
% 2.31/2.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
