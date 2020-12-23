%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FXWYCBx7yZ

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:55 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :  299 (1229 expanded)
%              Number of leaves         :   52 ( 377 expanded)
%              Depth                    :   39
%              Number of atoms          : 4068 (41064 expanded)
%              Number of equality atoms :  168 (1597 expanded)
%              Maximal formula depth    :   28 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

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

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B_1 ) ) ),
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
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X51 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X53 ) )
      | ( v1_xboole_0 @ X52 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X53 ) )
      | ( v1_xboole_0 @ X50 )
      | ( v1_xboole_0 @ X51 )
      | ( v1_xboole_0 @ X53 )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( v1_funct_2 @ X54 @ X52 @ X51 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X51 ) ) )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X53 @ X51 @ X50 @ X52 @ X49 @ X54 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_tmap_1 @ X2 @ sk_B_1 @ sk_C @ X1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_tmap_1 @ X2 @ sk_B_1 @ sk_C @ X1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B_1 )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['1','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X51 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X53 ) )
      | ( v1_xboole_0 @ X52 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X53 ) )
      | ( v1_xboole_0 @ X50 )
      | ( v1_xboole_0 @ X51 )
      | ( v1_xboole_0 @ X53 )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( v1_funct_2 @ X54 @ X52 @ X51 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X51 ) ) )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X53 @ X51 @ X50 @ X52 @ X49 @ X54 ) @ ( k4_subset_1 @ X53 @ X50 @ X52 ) @ X51 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ ( k1_tmap_1 @ X1 @ sk_B_1 @ sk_C @ X0 @ sk_E @ X2 ) @ ( k4_subset_1 @ X1 @ sk_C @ X0 ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ ( k1_tmap_1 @ X1 @ sk_B_1 @ sk_C @ X0 @ sk_E @ X2 ) @ ( k4_subset_1 @ X1 @ sk_C @ X0 ) @ sk_B_1 )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B_1 )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ X0 @ sk_C @ sk_D ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['17','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ X0 @ sk_C @ sk_D ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['16','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    ! [X49: $i,X50: $i,X51: $i,X52: $i,X53: $i,X54: $i] :
      ( ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X50 @ X51 ) ) )
      | ~ ( v1_funct_2 @ X49 @ X50 @ X51 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( m1_subset_1 @ X52 @ ( k1_zfmisc_1 @ X53 ) )
      | ( v1_xboole_0 @ X52 )
      | ~ ( m1_subset_1 @ X50 @ ( k1_zfmisc_1 @ X53 ) )
      | ( v1_xboole_0 @ X50 )
      | ( v1_xboole_0 @ X51 )
      | ( v1_xboole_0 @ X53 )
      | ~ ( v1_funct_1 @ X54 )
      | ~ ( v1_funct_2 @ X54 @ X52 @ X51 )
      | ~ ( m1_subset_1 @ X54 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X52 @ X51 ) ) )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X53 @ X51 @ X50 @ X52 @ X49 @ X54 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X53 @ X50 @ X52 ) @ X51 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tmap_1 @ X1 @ sk_B_1 @ sk_C @ X0 @ sk_E @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X1 @ sk_C @ X0 ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tmap_1 @ X1 @ sk_B_1 @ sk_C @ X0 @ sk_E @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X1 @ sk_C @ X0 ) @ sk_B_1 ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B_1 ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B_1 )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['35','36','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B_1 )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C @ sk_D ) @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['32','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C @ sk_D ) @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['31','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
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
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( v1_xboole_0 @ X42 )
      | ( v1_xboole_0 @ X43 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X43 @ X42 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) )
      | ( X48
       != ( k1_tmap_1 @ X44 @ X42 @ X47 @ X43 @ X46 @ X45 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X44 @ X47 @ X43 ) @ X42 @ X48 @ X47 )
        = X46 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X44 @ X47 @ X43 ) @ X42 ) ) )
      | ~ ( v1_funct_2 @ X48 @ ( k4_subset_1 @ X44 @ X47 @ X43 ) @ X42 )
      | ~ ( v1_funct_1 @ X48 )
      | ( ( k2_partfun1 @ X47 @ X42 @ X46 @ ( k9_subset_1 @ X44 @ X47 @ X43 ) )
       != ( k2_partfun1 @ X43 @ X42 @ X45 @ ( k9_subset_1 @ X44 @ X47 @ X43 ) ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X42 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X44 ) )
      | ( v1_xboole_0 @ X47 )
      | ( v1_xboole_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('47',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( v1_xboole_0 @ X44 )
      | ( v1_xboole_0 @ X47 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X44 ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X42 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X42 ) ) )
      | ( ( k2_partfun1 @ X47 @ X42 @ X46 @ ( k9_subset_1 @ X44 @ X47 @ X43 ) )
       != ( k2_partfun1 @ X43 @ X42 @ X45 @ ( k9_subset_1 @ X44 @ X47 @ X43 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X44 @ X42 @ X47 @ X43 @ X46 @ X45 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X44 @ X42 @ X47 @ X43 @ X46 @ X45 ) @ ( k4_subset_1 @ X44 @ X47 @ X43 ) @ X42 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X44 @ X42 @ X47 @ X43 @ X46 @ X45 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X44 @ X47 @ X43 ) @ X42 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X44 @ X47 @ X43 ) @ X42 @ ( k1_tmap_1 @ X44 @ X42 @ X47 @ X43 @ X46 @ X45 ) @ X47 )
        = X46 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X45 @ X43 @ X42 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ( v1_xboole_0 @ X43 )
      | ( v1_xboole_0 @ X42 ) ) ),
    inference(simplify,[status(thm)],['46'])).

thf('48',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['45','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
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
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k9_subset_1 @ X6 @ X4 @ X5 )
        = ( k3_xboole_0 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    r1_subset_1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r1_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ( ( r1_subset_1 @ A @ B )
      <=> ( r1_xboole_0 @ A @ B ) ) ) )).

thf('57',plain,(
    ! [X24: $i,X25: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ( v1_xboole_0 @ X25 )
      | ( r1_xboole_0 @ X24 @ X25 )
      | ~ ( r1_subset_1 @ X24 @ X25 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_subset_1])).

thf('58',plain,
    ( ( r1_xboole_0 @ sk_C @ sk_D )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r1_xboole_0 @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    r1_xboole_0 @ sk_C @ sk_D ),
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
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('66',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ( ( k2_partfun1 @ X39 @ X40 @ X38 @ X41 )
        = ( k7_relat_1 @ X38 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B_1 ) ) ),
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

thf('71',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( v1_partfun1 @ X33 @ X34 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( v1_funct_1 @ X33 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('72',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B_1 )
    | ( v1_partfun1 @ sk_E @ sk_C ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_partfun1 @ sk_E @ sk_C ) ),
    inference(demod,[status(thm)],['72','73','74'])).

thf('76',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    v1_partfun1 @ sk_E @ sk_C ),
    inference(clc,[status(thm)],['75','76'])).

thf(d4_partfun1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( ( v1_partfun1 @ B @ A )
      <=> ( ( k1_relat_1 @ B )
          = A ) ) ) )).

thf('78',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v1_partfun1 @ X37 @ X36 )
      | ( ( k1_relat_1 @ X37 )
        = X36 )
      | ~ ( v4_relat_1 @ X37 @ X36 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('79',plain,
    ( ~ ( v1_relat_1 @ sk_E )
    | ~ ( v4_relat_1 @ sk_E @ sk_C )
    | ( ( k1_relat_1 @ sk_E )
      = sk_C ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('81',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('82',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('84',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v4_relat_1 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('85',plain,(
    v4_relat_1 @ sk_E @ sk_C ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( k1_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['79','82','85'])).

thf(t1_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ( r1_xboole_0 @ B @ A ) ) ) )).

thf('87',plain,(
    ! [X32: $i] :
      ( ( X32 = k1_xboole_0 )
      | ( r1_xboole_0 @ ( sk_B @ X32 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[t1_mcart_1])).

thf(t187_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) )
         => ( ( k7_relat_1 @ A @ B )
            = k1_xboole_0 ) ) ) )).

thf('88',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( r1_xboole_0 @ X19 @ ( k1_relat_1 @ X20 ) )
      | ( ( k7_relat_1 @ X20 @ X19 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t187_relat_1])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('90',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(t162_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( r1_tarski @ B @ C )
         => ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B )
            = ( k9_relat_1 @ A @ B ) ) ) ) )).

thf('91',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ~ ( r1_tarski @ X16 @ X17 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X18 @ X17 ) @ X16 )
        = ( k9_relat_1 @ X18 @ X16 ) )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t162_relat_1])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k9_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ k1_xboole_0 )
        = ( k9_relat_1 @ X1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['90','91'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
        = ( k9_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['89','92'])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
        = ( k9_relat_1 @ X0 @ k1_xboole_0 ) ) ) ),
    inference(simplify,[status(thm)],['93'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('95',plain,(
    ! [X21: $i] :
      ( ( ( k1_relat_1 @ X21 )
       != k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
        = ( k9_relat_1 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(clc,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ ( sk_B @ ( k1_relat_1 @ X0 ) ) )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('98',plain,(
    ! [X11: $i,X12: $i] :
      ( ~ ( v1_relat_1 @ X11 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['97','98'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['99'])).

thf('101',plain,(
    ! [X21: $i] :
      ( ( ( k1_relat_1 @ X21 )
       != k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['102'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('104',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t146_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) )
        = ( k2_relat_1 @ A ) ) ) )).

thf('105',plain,(
    ! [X13: $i] :
      ( ( ( k9_relat_1 @ X13 @ ( k1_relat_1 @ X13 ) )
        = ( k2_relat_1 @ X13 ) )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t146_relat_1])).

thf('106',plain,
    ( ( ( k9_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['104','105'])).

thf('107',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('108',plain,
    ( ( ( k9_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('109',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['103','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ( v1_relat_1 @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['109'])).

thf('111',plain,
    ( ( ( k9_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['106','107'])).

thf('112',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k9_relat_1 @ k1_xboole_0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(clc,[status(thm)],['110','111'])).

thf('113',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k9_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup+',[status(thm)],['96','112'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(condensation,[status(thm)],['113'])).

thf(t151_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k9_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('115',plain,(
    ! [X14: $i,X15: $i] :
      ( ( ( k9_relat_1 @ X14 @ X15 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X14 ) @ X15 )
      | ~ ( v1_relat_1 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t151_relat_1])).

thf('116',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X0 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['114','115'])).

thf('117',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('118',plain,
    ( ( r1_xboole_0 @ sk_C @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E ) ),
    inference('sup+',[status(thm)],['86','117'])).

thf('119',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['80','81'])).

thf('120',plain,(
    r1_xboole_0 @ sk_C @ k1_xboole_0 ),
    inference(demod,[status(thm)],['118','119'])).

thf('121',plain,
    ( ( k1_relat_1 @ sk_E )
    = sk_C ),
    inference(demod,[status(thm)],['79','82','85'])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('122',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X22 ) @ X23 )
      | ( ( k7_relat_1 @ X22 @ X23 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('123',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C @ X0 )
      | ~ ( v1_relat_1 @ sk_E )
      | ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['121','122'])).

thf('124',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['80','81'])).

thf('125',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_C @ X0 )
      | ( ( k7_relat_1 @ sk_E @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['123','124'])).

thf('126',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['120','125'])).

thf('127',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('128',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('129',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    ! [X38: $i,X39: $i,X40: $i,X41: $i] :
      ( ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X39 @ X40 ) ) )
      | ~ ( v1_funct_1 @ X38 )
      | ( ( k2_partfun1 @ X39 @ X40 @ X38 @ X41 )
        = ( k7_relat_1 @ X38 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['129','130'])).

thf('132',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('134',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ( v1_partfun1 @ X33 @ X34 )
      | ~ ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( v1_funct_1 @ X33 )
      | ( v1_xboole_0 @ X35 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('136',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B_1 )
    | ( v1_partfun1 @ sk_F @ sk_D ) ),
    inference('sup-',[status(thm)],['134','135'])).

thf('137',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( v1_partfun1 @ sk_F @ sk_D ) ),
    inference(demod,[status(thm)],['136','137','138'])).

thf('140',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_partfun1 @ sk_F @ sk_D ),
    inference(clc,[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X36: $i,X37: $i] :
      ( ~ ( v1_partfun1 @ X37 @ X36 )
      | ( ( k1_relat_1 @ X37 )
        = X36 )
      | ~ ( v4_relat_1 @ X37 @ X36 )
      | ~ ( v1_relat_1 @ X37 ) ) ),
    inference(cnf,[status(esa)],[d4_partfun1])).

thf('143',plain,
    ( ~ ( v1_relat_1 @ sk_F )
    | ~ ( v4_relat_1 @ sk_F @ sk_D )
    | ( ( k1_relat_1 @ sk_F )
      = sk_D ) ),
    inference('sup-',[status(thm)],['141','142'])).

thf('144',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('146',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['144','145'])).

thf('147',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v4_relat_1 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('149',plain,(
    v4_relat_1 @ sk_F @ sk_D ),
    inference('sup-',[status(thm)],['147','148'])).

thf('150',plain,
    ( ( k1_relat_1 @ sk_F )
    = sk_D ),
    inference(demod,[status(thm)],['143','146','149'])).

thf('151',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('152',plain,
    ( ( r1_xboole_0 @ sk_D @ k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F ) ),
    inference('sup+',[status(thm)],['150','151'])).

thf('153',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['144','145'])).

thf('154',plain,(
    r1_xboole_0 @ sk_D @ k1_xboole_0 ),
    inference(demod,[status(thm)],['152','153'])).

thf('155',plain,
    ( ( k1_relat_1 @ sk_F )
    = sk_D ),
    inference(demod,[status(thm)],['143','146','149'])).

thf('156',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X22 ) @ X23 )
      | ( ( k7_relat_1 @ X22 @ X23 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('157',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_D @ X0 )
      | ~ ( v1_relat_1 @ sk_F )
      | ( ( k7_relat_1 @ sk_F @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['144','145'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ~ ( r1_xboole_0 @ sk_D @ X0 )
      | ( ( k7_relat_1 @ sk_F @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['154','159'])).

thf('161',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('165',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49','50','51','52','55','64','69','126','127','128','133','160','161','162','163','164'])).

thf('166',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['165'])).

thf('167',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E ) ),
    inference(split,[status(esa)],['167'])).

thf('169',plain,(
    ! [X0: $i] :
      ( ( r1_xboole_0 @ ( k1_relat_1 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['116'])).

thf('170',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X22 ) @ X23 )
      | ( ( k7_relat_1 @ X22 @ X23 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('171',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['171'])).

thf('174',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('175',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('176',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['167'])).

thf('177',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('179',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k3_xboole_0 @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['177','178'])).

thf('180',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k3_xboole_0 @ sk_C @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['174','179'])).

thf('181',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('182',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('183',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('184',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['180','181','182','183'])).

thf('185',plain,
    ( ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_F ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['173','184'])).

thf('186',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['144','145'])).

thf('187',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['185','186'])).

thf('188',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_E ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['172','187'])).

thf('189',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['80','81'])).

thf('190',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['188','189'])).

thf('191',plain,
    ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['190'])).

thf('192',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['13','14'])).

thf('193',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['28','29'])).

thf('194',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['43','44'])).

thf('195',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i,X48: $i] :
      ( ( v1_xboole_0 @ X42 )
      | ( v1_xboole_0 @ X43 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( v1_funct_2 @ X45 @ X43 @ X42 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) )
      | ( X48
       != ( k1_tmap_1 @ X44 @ X42 @ X47 @ X43 @ X46 @ X45 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X44 @ X47 @ X43 ) @ X42 @ X48 @ X43 )
        = X45 )
      | ~ ( m1_subset_1 @ X48 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X44 @ X47 @ X43 ) @ X42 ) ) )
      | ~ ( v1_funct_2 @ X48 @ ( k4_subset_1 @ X44 @ X47 @ X43 ) @ X42 )
      | ~ ( v1_funct_1 @ X48 )
      | ( ( k2_partfun1 @ X47 @ X42 @ X46 @ ( k9_subset_1 @ X44 @ X47 @ X43 ) )
       != ( k2_partfun1 @ X43 @ X42 @ X45 @ ( k9_subset_1 @ X44 @ X47 @ X43 ) ) )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X42 )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X44 ) )
      | ( v1_xboole_0 @ X47 )
      | ( v1_xboole_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('196',plain,(
    ! [X42: $i,X43: $i,X44: $i,X45: $i,X46: $i,X47: $i] :
      ( ( v1_xboole_0 @ X44 )
      | ( v1_xboole_0 @ X47 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X44 ) )
      | ~ ( v1_funct_1 @ X46 )
      | ~ ( v1_funct_2 @ X46 @ X47 @ X42 )
      | ~ ( m1_subset_1 @ X46 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X42 ) ) )
      | ( ( k2_partfun1 @ X47 @ X42 @ X46 @ ( k9_subset_1 @ X44 @ X47 @ X43 ) )
       != ( k2_partfun1 @ X43 @ X42 @ X45 @ ( k9_subset_1 @ X44 @ X47 @ X43 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X44 @ X42 @ X47 @ X43 @ X46 @ X45 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X44 @ X42 @ X47 @ X43 @ X46 @ X45 ) @ ( k4_subset_1 @ X44 @ X47 @ X43 ) @ X42 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X44 @ X42 @ X47 @ X43 @ X46 @ X45 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X44 @ X47 @ X43 ) @ X42 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X44 @ X47 @ X43 ) @ X42 @ ( k1_tmap_1 @ X44 @ X42 @ X47 @ X43 @ X46 @ X45 ) @ X43 )
        = X45 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X43 @ X42 ) ) )
      | ~ ( v1_funct_2 @ X45 @ X43 @ X42 )
      | ~ ( v1_funct_1 @ X45 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ X44 ) )
      | ( v1_xboole_0 @ X43 )
      | ( v1_xboole_0 @ X42 ) ) ),
    inference(simplify,[status(thm)],['195'])).

thf('197',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B_1 )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B_1 ) ) )
    | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B_1 )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['194','196'])).

thf('198',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('200',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('201',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('202',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('203',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('204',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['67','68'])).

thf('205',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['120','125'])).

thf('206',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('207',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','63'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['131','132'])).

thf('209',plain,
    ( ( k7_relat_1 @ sk_F @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['154','159'])).

thf('210',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('211',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('212',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('213',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('214',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_D )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['197','198','199','200','201','202','203','204','205','206','207','208','209','210','211','212','213'])).

thf('215',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['214'])).

thf('216',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['193','215'])).

thf('217',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['216'])).

thf('218',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference('sup-',[status(thm)],['192','217'])).

thf('219',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['218'])).

thf('220',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['167'])).

thf('221',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['219','220'])).

thf('222',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['221'])).

thf('223',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('224',plain,
    ( ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['222','223'])).

thf('225',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['224','225'])).

thf('227',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['226','227'])).

thf('229',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('230',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['228','229'])).

thf('231',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['167'])).

thf('232',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['191','230','231'])).

thf('233',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['168','232'])).

thf('234',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['166','233'])).

thf('235',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) ) ),
    inference('sup-',[status(thm)],['30','234'])).

thf('236',plain,
    ( ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['235'])).

thf('237',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['15','236'])).

thf('238',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['237'])).

thf('239',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('240',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['238','239'])).

thf('241',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('242',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['240','241'])).

thf('243',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('244',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(clc,[status(thm)],['242','243'])).

thf('245',plain,(
    $false ),
    inference(demod,[status(thm)],['0','244'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.FXWYCBx7yZ
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:32:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.75/0.98  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.75/0.98  % Solved by: fo/fo7.sh
% 0.75/0.98  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.75/0.98  % done 1365 iterations in 0.520s
% 0.75/0.98  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.75/0.98  % SZS output start Refutation
% 0.75/0.98  thf(sk_E_type, type, sk_E: $i).
% 0.75/0.98  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.75/0.98  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.75/0.98  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.75/0.98  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.75/0.98  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.75/0.98  thf(sk_F_type, type, sk_F: $i).
% 0.75/0.98  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.75/0.98  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.75/0.98  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.75/0.98  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.75/0.98  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.75/0.98  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.75/0.98  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.75/0.98  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.75/0.98  thf(sk_A_type, type, sk_A: $i).
% 0.75/0.98  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.75/0.98  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.75/0.98  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.75/0.98  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.75/0.98  thf(sk_D_type, type, sk_D: $i).
% 0.75/0.98  thf(sk_C_type, type, sk_C: $i).
% 0.75/0.98  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.75/0.98  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.75/0.98  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.75/0.98  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.75/0.98  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.75/0.98  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.75/0.98  thf(sk_B_type, type, sk_B: $i > $i).
% 0.75/0.98  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.75/0.98  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 0.75/0.98  thf(t6_tmap_1, conjecture,
% 0.75/0.98    (![A:$i]:
% 0.75/0.98     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.75/0.98       ( ![B:$i]:
% 0.75/0.98         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.75/0.98           ( ![C:$i]:
% 0.75/0.98             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.75/0.98                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.75/0.98               ( ![D:$i]:
% 0.75/0.98                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.75/0.98                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.75/0.98                   ( ( r1_subset_1 @ C @ D ) =>
% 0.75/0.98                     ( ![E:$i]:
% 0.75/0.98                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.75/0.98                           ( m1_subset_1 @
% 0.75/0.98                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.75/0.98                         ( ![F:$i]:
% 0.75/0.98                           ( ( ( v1_funct_1 @ F ) & 
% 0.75/0.98                               ( v1_funct_2 @ F @ D @ B ) & 
% 0.75/0.98                               ( m1_subset_1 @
% 0.75/0.98                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.75/0.98                             ( ( ( k2_partfun1 @
% 0.75/0.98                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.75/0.98                                 ( k2_partfun1 @
% 0.75/0.98                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.75/0.98                               ( ( k2_partfun1 @
% 0.75/0.98                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.75/0.98                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.75/0.98                                 ( E ) ) & 
% 0.75/0.98                               ( ( k2_partfun1 @
% 0.75/0.98                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.75/0.98                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.75/0.98                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.75/0.98  thf(zf_stmt_0, negated_conjecture,
% 0.75/0.98    (~( ![A:$i]:
% 0.75/0.98        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.75/0.98          ( ![B:$i]:
% 0.75/0.98            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.75/0.98              ( ![C:$i]:
% 0.75/0.98                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.75/0.98                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.75/0.98                  ( ![D:$i]:
% 0.75/0.98                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.75/0.98                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.75/0.98                      ( ( r1_subset_1 @ C @ D ) =>
% 0.75/0.98                        ( ![E:$i]:
% 0.75/0.98                          ( ( ( v1_funct_1 @ E ) & 
% 0.75/0.98                              ( v1_funct_2 @ E @ C @ B ) & 
% 0.75/0.98                              ( m1_subset_1 @
% 0.75/0.98                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.75/0.98                            ( ![F:$i]:
% 0.75/0.98                              ( ( ( v1_funct_1 @ F ) & 
% 0.75/0.98                                  ( v1_funct_2 @ F @ D @ B ) & 
% 0.75/0.98                                  ( m1_subset_1 @
% 0.75/0.98                                    F @ 
% 0.75/0.98                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.75/0.98                                ( ( ( k2_partfun1 @
% 0.75/0.98                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.75/0.98                                    ( k2_partfun1 @
% 0.75/0.98                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.75/0.98                                  ( ( k2_partfun1 @
% 0.75/0.98                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.75/0.98                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.75/0.98                                    ( E ) ) & 
% 0.75/0.98                                  ( ( k2_partfun1 @
% 0.75/0.98                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.75/0.98                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.75/0.98                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.75/0.98    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 0.75/0.98  thf('0', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('1', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('2', plain,
% 0.75/0.98      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('3', plain,
% 0.75/0.98      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf(dt_k1_tmap_1, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.75/0.98     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.75/0.98         ( ~( v1_xboole_0 @ C ) ) & 
% 0.75/0.98         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 0.75/0.98         ( ~( v1_xboole_0 @ D ) ) & 
% 0.75/0.98         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 0.75/0.98         ( v1_funct_2 @ E @ C @ B ) & 
% 0.75/0.98         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.75/0.98         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.75/0.98         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.75/0.98       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.75/0.98         ( v1_funct_2 @
% 0.75/0.98           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.75/0.98           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.75/0.98         ( m1_subset_1 @
% 0.75/0.98           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.75/0.98           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 0.75/0.98  thf('4', plain,
% 0.75/0.98      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.75/0.98         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 0.75/0.98          | ~ (v1_funct_2 @ X49 @ X50 @ X51)
% 0.75/0.98          | ~ (v1_funct_1 @ X49)
% 0.75/0.98          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X53))
% 0.75/0.98          | (v1_xboole_0 @ X52)
% 0.75/0.98          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X53))
% 0.75/0.98          | (v1_xboole_0 @ X50)
% 0.75/0.98          | (v1_xboole_0 @ X51)
% 0.75/0.98          | (v1_xboole_0 @ X53)
% 0.75/0.98          | ~ (v1_funct_1 @ X54)
% 0.75/0.98          | ~ (v1_funct_2 @ X54 @ X52 @ X51)
% 0.75/0.98          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X51)))
% 0.75/0.98          | (v1_funct_1 @ (k1_tmap_1 @ X53 @ X51 @ X50 @ X52 @ X49 @ X54)))),
% 0.75/0.98      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.75/0.98  thf('5', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.98         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B_1 @ sk_C @ X1 @ sk_E @ X0))
% 0.75/0.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 0.75/0.98          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 0.75/0.98          | ~ (v1_funct_1 @ X0)
% 0.75/0.98          | (v1_xboole_0 @ X2)
% 0.75/0.98          | (v1_xboole_0 @ sk_B_1)
% 0.75/0.98          | (v1_xboole_0 @ sk_C)
% 0.75/0.98          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.75/0.98          | (v1_xboole_0 @ X1)
% 0.75/0.98          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.75/0.98          | ~ (v1_funct_1 @ sk_E)
% 0.75/0.98          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B_1))),
% 0.75/0.98      inference('sup-', [status(thm)], ['3', '4'])).
% 0.75/0.98  thf('6', plain, ((v1_funct_1 @ sk_E)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('7', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B_1)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('8', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.98         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B_1 @ sk_C @ X1 @ sk_E @ X0))
% 0.75/0.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 0.75/0.98          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 0.75/0.98          | ~ (v1_funct_1 @ X0)
% 0.75/0.98          | (v1_xboole_0 @ X2)
% 0.75/0.98          | (v1_xboole_0 @ sk_B_1)
% 0.75/0.98          | (v1_xboole_0 @ sk_C)
% 0.75/0.98          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.75/0.98          | (v1_xboole_0 @ X1)
% 0.75/0.98          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.75/0.98      inference('demod', [status(thm)], ['5', '6', '7'])).
% 0.75/0.98  thf('9', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.75/0.98          | (v1_xboole_0 @ sk_D)
% 0.75/0.98          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.75/0.98          | (v1_xboole_0 @ sk_C)
% 0.75/0.98          | (v1_xboole_0 @ sk_B_1)
% 0.75/0.98          | (v1_xboole_0 @ X0)
% 0.75/0.98          | ~ (v1_funct_1 @ sk_F)
% 0.75/0.98          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 0.75/0.98          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['2', '8'])).
% 0.75/0.98  thf('10', plain, ((v1_funct_1 @ sk_F)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('11', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('12', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.75/0.98          | (v1_xboole_0 @ sk_D)
% 0.75/0.98          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.75/0.98          | (v1_xboole_0 @ sk_C)
% 0.75/0.98          | (v1_xboole_0 @ sk_B_1)
% 0.75/0.98          | (v1_xboole_0 @ X0)
% 0.75/0.98          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.75/0.98      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.75/0.98  thf('13', plain,
% 0.75/0.98      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.75/0.98        | (v1_xboole_0 @ sk_A)
% 0.75/0.98        | (v1_xboole_0 @ sk_B_1)
% 0.75/0.98        | (v1_xboole_0 @ sk_C)
% 0.75/0.98        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.75/0.98        | (v1_xboole_0 @ sk_D))),
% 0.75/0.98      inference('sup-', [status(thm)], ['1', '12'])).
% 0.75/0.98  thf('14', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('15', plain,
% 0.75/0.98      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.75/0.98        | (v1_xboole_0 @ sk_A)
% 0.75/0.98        | (v1_xboole_0 @ sk_B_1)
% 0.75/0.98        | (v1_xboole_0 @ sk_C)
% 0.75/0.98        | (v1_xboole_0 @ sk_D))),
% 0.75/0.98      inference('demod', [status(thm)], ['13', '14'])).
% 0.75/0.98  thf('16', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('17', plain,
% 0.75/0.98      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('18', plain,
% 0.75/0.98      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('19', plain,
% 0.75/0.98      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.75/0.98         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 0.75/0.98          | ~ (v1_funct_2 @ X49 @ X50 @ X51)
% 0.75/0.98          | ~ (v1_funct_1 @ X49)
% 0.75/0.98          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X53))
% 0.75/0.98          | (v1_xboole_0 @ X52)
% 0.75/0.98          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X53))
% 0.75/0.98          | (v1_xboole_0 @ X50)
% 0.75/0.98          | (v1_xboole_0 @ X51)
% 0.75/0.98          | (v1_xboole_0 @ X53)
% 0.75/0.98          | ~ (v1_funct_1 @ X54)
% 0.75/0.98          | ~ (v1_funct_2 @ X54 @ X52 @ X51)
% 0.75/0.98          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X51)))
% 0.75/0.98          | (v1_funct_2 @ (k1_tmap_1 @ X53 @ X51 @ X50 @ X52 @ X49 @ X54) @ 
% 0.75/0.98             (k4_subset_1 @ X53 @ X50 @ X52) @ X51))),
% 0.75/0.98      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.75/0.98  thf('20', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.98         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.75/0.98           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B_1)
% 0.75/0.98          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.75/0.98          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 0.75/0.98          | ~ (v1_funct_1 @ X2)
% 0.75/0.98          | (v1_xboole_0 @ X1)
% 0.75/0.98          | (v1_xboole_0 @ sk_B_1)
% 0.75/0.98          | (v1_xboole_0 @ sk_C)
% 0.75/0.98          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.75/0.98          | (v1_xboole_0 @ X0)
% 0.75/0.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.75/0.98          | ~ (v1_funct_1 @ sk_E)
% 0.75/0.98          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B_1))),
% 0.75/0.98      inference('sup-', [status(thm)], ['18', '19'])).
% 0.75/0.98  thf('21', plain, ((v1_funct_1 @ sk_E)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('22', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B_1)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('23', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.98         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.75/0.98           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B_1)
% 0.75/0.98          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.75/0.98          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 0.75/0.98          | ~ (v1_funct_1 @ X2)
% 0.75/0.98          | (v1_xboole_0 @ X1)
% 0.75/0.98          | (v1_xboole_0 @ sk_B_1)
% 0.75/0.98          | (v1_xboole_0 @ sk_C)
% 0.75/0.98          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.75/0.98          | (v1_xboole_0 @ X0)
% 0.75/0.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.75/0.98      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.75/0.98  thf('24', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.75/0.98          | (v1_xboole_0 @ sk_D)
% 0.75/0.98          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.75/0.98          | (v1_xboole_0 @ sk_C)
% 0.75/0.98          | (v1_xboole_0 @ sk_B_1)
% 0.75/0.98          | (v1_xboole_0 @ X0)
% 0.75/0.98          | ~ (v1_funct_1 @ sk_F)
% 0.75/0.98          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 0.75/0.98          | (v1_funct_2 @ 
% 0.75/0.98             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.75/0.98             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B_1))),
% 0.75/0.98      inference('sup-', [status(thm)], ['17', '23'])).
% 0.75/0.98  thf('25', plain, ((v1_funct_1 @ sk_F)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('26', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('27', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.75/0.98          | (v1_xboole_0 @ sk_D)
% 0.75/0.98          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.75/0.98          | (v1_xboole_0 @ sk_C)
% 0.75/0.98          | (v1_xboole_0 @ sk_B_1)
% 0.75/0.98          | (v1_xboole_0 @ X0)
% 0.75/0.98          | (v1_funct_2 @ 
% 0.75/0.98             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.75/0.98             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B_1))),
% 0.75/0.98      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.75/0.98  thf('28', plain,
% 0.75/0.98      (((v1_funct_2 @ 
% 0.75/0.98         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.75/0.98         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 0.75/0.98        | (v1_xboole_0 @ sk_A)
% 0.75/0.98        | (v1_xboole_0 @ sk_B_1)
% 0.75/0.98        | (v1_xboole_0 @ sk_C)
% 0.75/0.98        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.75/0.98        | (v1_xboole_0 @ sk_D))),
% 0.75/0.98      inference('sup-', [status(thm)], ['16', '27'])).
% 0.75/0.98  thf('29', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('30', plain,
% 0.75/0.98      (((v1_funct_2 @ 
% 0.75/0.98         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.75/0.98         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 0.75/0.98        | (v1_xboole_0 @ sk_A)
% 0.75/0.98        | (v1_xboole_0 @ sk_B_1)
% 0.75/0.98        | (v1_xboole_0 @ sk_C)
% 0.75/0.98        | (v1_xboole_0 @ sk_D))),
% 0.75/0.98      inference('demod', [status(thm)], ['28', '29'])).
% 0.75/0.98  thf('31', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('32', plain,
% 0.75/0.98      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('33', plain,
% 0.75/0.98      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('34', plain,
% 0.75/0.98      (![X49 : $i, X50 : $i, X51 : $i, X52 : $i, X53 : $i, X54 : $i]:
% 0.75/0.98         (~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X50 @ X51)))
% 0.75/0.98          | ~ (v1_funct_2 @ X49 @ X50 @ X51)
% 0.75/0.98          | ~ (v1_funct_1 @ X49)
% 0.75/0.98          | ~ (m1_subset_1 @ X52 @ (k1_zfmisc_1 @ X53))
% 0.75/0.98          | (v1_xboole_0 @ X52)
% 0.75/0.98          | ~ (m1_subset_1 @ X50 @ (k1_zfmisc_1 @ X53))
% 0.75/0.98          | (v1_xboole_0 @ X50)
% 0.75/0.98          | (v1_xboole_0 @ X51)
% 0.75/0.98          | (v1_xboole_0 @ X53)
% 0.75/0.98          | ~ (v1_funct_1 @ X54)
% 0.75/0.98          | ~ (v1_funct_2 @ X54 @ X52 @ X51)
% 0.75/0.98          | ~ (m1_subset_1 @ X54 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X52 @ X51)))
% 0.75/0.98          | (m1_subset_1 @ (k1_tmap_1 @ X53 @ X51 @ X50 @ X52 @ X49 @ X54) @ 
% 0.75/0.98             (k1_zfmisc_1 @ 
% 0.75/0.98              (k2_zfmisc_1 @ (k4_subset_1 @ X53 @ X50 @ X52) @ X51))))),
% 0.75/0.98      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.75/0.98  thf('35', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.98         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.75/0.98           (k1_zfmisc_1 @ 
% 0.75/0.98            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B_1)))
% 0.75/0.98          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.75/0.98          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 0.75/0.98          | ~ (v1_funct_1 @ X2)
% 0.75/0.98          | (v1_xboole_0 @ X1)
% 0.75/0.98          | (v1_xboole_0 @ sk_B_1)
% 0.75/0.98          | (v1_xboole_0 @ sk_C)
% 0.75/0.98          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.75/0.98          | (v1_xboole_0 @ X0)
% 0.75/0.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.75/0.98          | ~ (v1_funct_1 @ sk_E)
% 0.75/0.98          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B_1))),
% 0.75/0.98      inference('sup-', [status(thm)], ['33', '34'])).
% 0.75/0.98  thf('36', plain, ((v1_funct_1 @ sk_E)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('37', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B_1)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('38', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.75/0.98         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.75/0.98           (k1_zfmisc_1 @ 
% 0.75/0.98            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B_1)))
% 0.75/0.98          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.75/0.98          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 0.75/0.98          | ~ (v1_funct_1 @ X2)
% 0.75/0.98          | (v1_xboole_0 @ X1)
% 0.75/0.98          | (v1_xboole_0 @ sk_B_1)
% 0.75/0.98          | (v1_xboole_0 @ sk_C)
% 0.75/0.98          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.75/0.98          | (v1_xboole_0 @ X0)
% 0.75/0.98          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.75/0.98      inference('demod', [status(thm)], ['35', '36', '37'])).
% 0.75/0.98  thf('39', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.75/0.98          | (v1_xboole_0 @ sk_D)
% 0.75/0.98          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.75/0.98          | (v1_xboole_0 @ sk_C)
% 0.75/0.98          | (v1_xboole_0 @ sk_B_1)
% 0.75/0.98          | (v1_xboole_0 @ X0)
% 0.75/0.98          | ~ (v1_funct_1 @ sk_F)
% 0.75/0.98          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 0.75/0.98          | (m1_subset_1 @ 
% 0.75/0.98             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.75/0.98             (k1_zfmisc_1 @ 
% 0.75/0.98              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B_1))))),
% 0.75/0.98      inference('sup-', [status(thm)], ['32', '38'])).
% 0.75/0.98  thf('40', plain, ((v1_funct_1 @ sk_F)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('41', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('42', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.75/0.98          | (v1_xboole_0 @ sk_D)
% 0.75/0.98          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.75/0.98          | (v1_xboole_0 @ sk_C)
% 0.75/0.98          | (v1_xboole_0 @ sk_B_1)
% 0.75/0.98          | (v1_xboole_0 @ X0)
% 0.75/0.98          | (m1_subset_1 @ 
% 0.75/0.98             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.75/0.98             (k1_zfmisc_1 @ 
% 0.75/0.98              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B_1))))),
% 0.75/0.98      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.75/0.98  thf('43', plain,
% 0.75/0.98      (((m1_subset_1 @ 
% 0.75/0.98         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.75/0.98         (k1_zfmisc_1 @ 
% 0.75/0.98          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)))
% 0.75/0.98        | (v1_xboole_0 @ sk_A)
% 0.75/0.98        | (v1_xboole_0 @ sk_B_1)
% 0.75/0.98        | (v1_xboole_0 @ sk_C)
% 0.75/0.98        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.75/0.98        | (v1_xboole_0 @ sk_D))),
% 0.75/0.98      inference('sup-', [status(thm)], ['31', '42'])).
% 0.75/0.98  thf('44', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('45', plain,
% 0.75/0.98      (((m1_subset_1 @ 
% 0.75/0.98         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.75/0.98         (k1_zfmisc_1 @ 
% 0.75/0.98          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)))
% 0.75/0.98        | (v1_xboole_0 @ sk_A)
% 0.75/0.98        | (v1_xboole_0 @ sk_B_1)
% 0.75/0.98        | (v1_xboole_0 @ sk_C)
% 0.75/0.98        | (v1_xboole_0 @ sk_D))),
% 0.75/0.98      inference('demod', [status(thm)], ['43', '44'])).
% 0.75/0.98  thf(d1_tmap_1, axiom,
% 0.75/0.98    (![A:$i]:
% 0.75/0.98     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.75/0.98       ( ![B:$i]:
% 0.75/0.98         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.75/0.98           ( ![C:$i]:
% 0.75/0.98             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.75/0.98                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.75/0.98               ( ![D:$i]:
% 0.75/0.98                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.75/0.98                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.75/0.98                   ( ![E:$i]:
% 0.75/0.98                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.75/0.98                         ( m1_subset_1 @
% 0.75/0.98                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.75/0.98                       ( ![F:$i]:
% 0.75/0.98                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.75/0.98                             ( m1_subset_1 @
% 0.75/0.98                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.75/0.98                           ( ( ( k2_partfun1 @
% 0.75/0.98                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.75/0.98                               ( k2_partfun1 @
% 0.75/0.98                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 0.75/0.98                             ( ![G:$i]:
% 0.75/0.98                               ( ( ( v1_funct_1 @ G ) & 
% 0.75/0.98                                   ( v1_funct_2 @
% 0.75/0.98                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.75/0.98                                   ( m1_subset_1 @
% 0.75/0.98                                     G @ 
% 0.75/0.98                                     ( k1_zfmisc_1 @
% 0.75/0.98                                       ( k2_zfmisc_1 @
% 0.75/0.98                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 0.75/0.98                                 ( ( ( G ) =
% 0.75/0.98                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.75/0.98                                   ( ( ( k2_partfun1 @
% 0.75/0.98                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.75/0.98                                         C ) =
% 0.75/0.98                                       ( E ) ) & 
% 0.75/0.98                                     ( ( k2_partfun1 @
% 0.75/0.98                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.75/0.98                                         D ) =
% 0.75/0.98                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.75/0.98  thf('46', plain,
% 0.75/0.98      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.75/0.98         ((v1_xboole_0 @ X42)
% 0.75/0.98          | (v1_xboole_0 @ X43)
% 0.75/0.98          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 0.75/0.98          | ~ (v1_funct_1 @ X45)
% 0.75/0.98          | ~ (v1_funct_2 @ X45 @ X43 @ X42)
% 0.75/0.98          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))
% 0.75/0.98          | ((X48) != (k1_tmap_1 @ X44 @ X42 @ X47 @ X43 @ X46 @ X45))
% 0.75/0.98          | ((k2_partfun1 @ (k4_subset_1 @ X44 @ X47 @ X43) @ X42 @ X48 @ X47)
% 0.75/0.98              = (X46))
% 0.75/0.98          | ~ (m1_subset_1 @ X48 @ 
% 0.75/0.98               (k1_zfmisc_1 @ 
% 0.75/0.98                (k2_zfmisc_1 @ (k4_subset_1 @ X44 @ X47 @ X43) @ X42)))
% 0.75/0.98          | ~ (v1_funct_2 @ X48 @ (k4_subset_1 @ X44 @ X47 @ X43) @ X42)
% 0.75/0.98          | ~ (v1_funct_1 @ X48)
% 0.75/0.98          | ((k2_partfun1 @ X47 @ X42 @ X46 @ (k9_subset_1 @ X44 @ X47 @ X43))
% 0.75/0.98              != (k2_partfun1 @ X43 @ X42 @ X45 @ 
% 0.75/0.98                  (k9_subset_1 @ X44 @ X47 @ X43)))
% 0.75/0.98          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X42)))
% 0.75/0.98          | ~ (v1_funct_2 @ X46 @ X47 @ X42)
% 0.75/0.98          | ~ (v1_funct_1 @ X46)
% 0.75/0.98          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X44))
% 0.75/0.98          | (v1_xboole_0 @ X47)
% 0.75/0.98          | (v1_xboole_0 @ X44))),
% 0.75/0.98      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.75/0.98  thf('47', plain,
% 0.75/0.98      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.75/0.98         ((v1_xboole_0 @ X44)
% 0.75/0.98          | (v1_xboole_0 @ X47)
% 0.75/0.98          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X44))
% 0.75/0.98          | ~ (v1_funct_1 @ X46)
% 0.75/0.98          | ~ (v1_funct_2 @ X46 @ X47 @ X42)
% 0.75/0.98          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X42)))
% 0.75/0.98          | ((k2_partfun1 @ X47 @ X42 @ X46 @ (k9_subset_1 @ X44 @ X47 @ X43))
% 0.75/0.98              != (k2_partfun1 @ X43 @ X42 @ X45 @ 
% 0.75/0.98                  (k9_subset_1 @ X44 @ X47 @ X43)))
% 0.75/0.98          | ~ (v1_funct_1 @ (k1_tmap_1 @ X44 @ X42 @ X47 @ X43 @ X46 @ X45))
% 0.75/0.98          | ~ (v1_funct_2 @ (k1_tmap_1 @ X44 @ X42 @ X47 @ X43 @ X46 @ X45) @ 
% 0.75/0.98               (k4_subset_1 @ X44 @ X47 @ X43) @ X42)
% 0.75/0.98          | ~ (m1_subset_1 @ (k1_tmap_1 @ X44 @ X42 @ X47 @ X43 @ X46 @ X45) @ 
% 0.75/0.98               (k1_zfmisc_1 @ 
% 0.75/0.98                (k2_zfmisc_1 @ (k4_subset_1 @ X44 @ X47 @ X43) @ X42)))
% 0.75/0.98          | ((k2_partfun1 @ (k4_subset_1 @ X44 @ X47 @ X43) @ X42 @ 
% 0.75/0.98              (k1_tmap_1 @ X44 @ X42 @ X47 @ X43 @ X46 @ X45) @ X47) = (
% 0.75/0.98              X46))
% 0.75/0.98          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))
% 0.75/0.98          | ~ (v1_funct_2 @ X45 @ X43 @ X42)
% 0.75/0.98          | ~ (v1_funct_1 @ X45)
% 0.75/0.98          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 0.75/0.98          | (v1_xboole_0 @ X43)
% 0.75/0.98          | (v1_xboole_0 @ X42))),
% 0.75/0.98      inference('simplify', [status(thm)], ['46'])).
% 0.75/0.98  thf('48', plain,
% 0.75/0.98      (((v1_xboole_0 @ sk_D)
% 0.75/0.98        | (v1_xboole_0 @ sk_C)
% 0.75/0.98        | (v1_xboole_0 @ sk_B_1)
% 0.75/0.98        | (v1_xboole_0 @ sk_A)
% 0.75/0.98        | (v1_xboole_0 @ sk_B_1)
% 0.75/0.98        | (v1_xboole_0 @ sk_D)
% 0.75/0.98        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.75/0.98        | ~ (v1_funct_1 @ sk_F)
% 0.75/0.98        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 0.75/0.98        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))
% 0.75/0.98        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.75/0.98            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.75/0.98            = (sk_E))
% 0.75/0.98        | ~ (v1_funct_2 @ 
% 0.75/0.98             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.75/0.98             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 0.75/0.98        | ~ (v1_funct_1 @ 
% 0.75/0.98             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.75/0.98        | ((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 0.75/0.98            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.75/0.98            != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.75/0.98                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.75/0.98        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))
% 0.75/0.98        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B_1)
% 0.75/0.98        | ~ (v1_funct_1 @ sk_E)
% 0.75/0.98        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.75/0.98        | (v1_xboole_0 @ sk_C)
% 0.75/0.98        | (v1_xboole_0 @ sk_A))),
% 0.75/0.98      inference('sup-', [status(thm)], ['45', '47'])).
% 0.75/0.98  thf('49', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('50', plain, ((v1_funct_1 @ sk_F)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('51', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('52', plain,
% 0.75/0.98      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('53', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf(redefinition_k9_subset_1, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i]:
% 0.75/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.75/0.98       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.75/0.98  thf('54', plain,
% 0.75/0.98      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.75/0.98         (((k9_subset_1 @ X6 @ X4 @ X5) = (k3_xboole_0 @ X4 @ X5))
% 0.75/0.98          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.75/0.98      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.75/0.98  thf('55', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.75/0.98      inference('sup-', [status(thm)], ['53', '54'])).
% 0.75/0.98  thf('56', plain, ((r1_subset_1 @ sk_C @ sk_D)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf(redefinition_r1_subset_1, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.75/0.98       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 0.75/0.98  thf('57', plain,
% 0.75/0.98      (![X24 : $i, X25 : $i]:
% 0.75/0.98         ((v1_xboole_0 @ X24)
% 0.75/0.98          | (v1_xboole_0 @ X25)
% 0.75/0.98          | (r1_xboole_0 @ X24 @ X25)
% 0.75/0.98          | ~ (r1_subset_1 @ X24 @ X25))),
% 0.75/0.98      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 0.75/0.98  thf('58', plain,
% 0.75/0.98      (((r1_xboole_0 @ sk_C @ sk_D)
% 0.75/0.98        | (v1_xboole_0 @ sk_D)
% 0.75/0.98        | (v1_xboole_0 @ sk_C))),
% 0.75/0.98      inference('sup-', [status(thm)], ['56', '57'])).
% 0.75/0.98  thf('59', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('60', plain, (((v1_xboole_0 @ sk_C) | (r1_xboole_0 @ sk_C @ sk_D))),
% 0.75/0.98      inference('clc', [status(thm)], ['58', '59'])).
% 0.75/0.98  thf('61', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('62', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 0.75/0.98      inference('clc', [status(thm)], ['60', '61'])).
% 0.75/0.98  thf(d7_xboole_0, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.75/0.98       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.75/0.98  thf('63', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.75/0.98      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.75/0.98  thf('64', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.75/0.98      inference('sup-', [status(thm)], ['62', '63'])).
% 0.75/0.98  thf('65', plain,
% 0.75/0.98      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf(redefinition_k2_partfun1, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i,D:$i]:
% 0.75/0.98     ( ( ( v1_funct_1 @ C ) & 
% 0.75/0.98         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.75/0.98       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.75/0.98  thf('66', plain,
% 0.75/0.98      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.75/0.98         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.75/0.98          | ~ (v1_funct_1 @ X38)
% 0.75/0.98          | ((k2_partfun1 @ X39 @ X40 @ X38 @ X41) = (k7_relat_1 @ X38 @ X41)))),
% 0.75/0.98      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.75/0.98  thf('67', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 0.75/0.98          | ~ (v1_funct_1 @ sk_E))),
% 0.75/0.98      inference('sup-', [status(thm)], ['65', '66'])).
% 0.75/0.98  thf('68', plain, ((v1_funct_1 @ sk_E)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('69', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         ((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.75/0.98      inference('demod', [status(thm)], ['67', '68'])).
% 0.75/0.98  thf('70', plain,
% 0.75/0.98      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf(cc5_funct_2, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.75/0.98       ( ![C:$i]:
% 0.75/0.98         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.98           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.75/0.98             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.75/0.98  thf('71', plain,
% 0.75/0.98      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.75/0.98         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.75/0.98          | (v1_partfun1 @ X33 @ X34)
% 0.75/0.98          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 0.75/0.98          | ~ (v1_funct_1 @ X33)
% 0.75/0.98          | (v1_xboole_0 @ X35))),
% 0.75/0.98      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.75/0.98  thf('72', plain,
% 0.75/0.98      (((v1_xboole_0 @ sk_B_1)
% 0.75/0.98        | ~ (v1_funct_1 @ sk_E)
% 0.75/0.98        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B_1)
% 0.75/0.98        | (v1_partfun1 @ sk_E @ sk_C))),
% 0.75/0.98      inference('sup-', [status(thm)], ['70', '71'])).
% 0.75/0.98  thf('73', plain, ((v1_funct_1 @ sk_E)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('74', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B_1)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('75', plain, (((v1_xboole_0 @ sk_B_1) | (v1_partfun1 @ sk_E @ sk_C))),
% 0.75/0.98      inference('demod', [status(thm)], ['72', '73', '74'])).
% 0.75/0.98  thf('76', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf('77', plain, ((v1_partfun1 @ sk_E @ sk_C)),
% 0.75/0.98      inference('clc', [status(thm)], ['75', '76'])).
% 0.75/0.98  thf(d4_partfun1, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.75/0.98       ( ( v1_partfun1 @ B @ A ) <=> ( ( k1_relat_1 @ B ) = ( A ) ) ) ))).
% 0.75/0.98  thf('78', plain,
% 0.75/0.98      (![X36 : $i, X37 : $i]:
% 0.75/0.98         (~ (v1_partfun1 @ X37 @ X36)
% 0.75/0.98          | ((k1_relat_1 @ X37) = (X36))
% 0.75/0.98          | ~ (v4_relat_1 @ X37 @ X36)
% 0.75/0.98          | ~ (v1_relat_1 @ X37))),
% 0.75/0.98      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.75/0.98  thf('79', plain,
% 0.75/0.98      ((~ (v1_relat_1 @ sk_E)
% 0.75/0.98        | ~ (v4_relat_1 @ sk_E @ sk_C)
% 0.75/0.98        | ((k1_relat_1 @ sk_E) = (sk_C)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['77', '78'])).
% 0.75/0.98  thf('80', plain,
% 0.75/0.98      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf(cc1_relset_1, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i]:
% 0.75/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.98       ( v1_relat_1 @ C ) ))).
% 0.75/0.98  thf('81', plain,
% 0.75/0.98      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.75/0.98         ((v1_relat_1 @ X26)
% 0.75/0.98          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.75/0.98      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.75/0.98  thf('82', plain, ((v1_relat_1 @ sk_E)),
% 0.75/0.98      inference('sup-', [status(thm)], ['80', '81'])).
% 0.75/0.98  thf('83', plain,
% 0.75/0.98      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 0.75/0.98      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.98  thf(cc2_relset_1, axiom,
% 0.75/0.98    (![A:$i,B:$i,C:$i]:
% 0.75/0.98     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.75/0.98       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.75/0.98  thf('84', plain,
% 0.75/0.98      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.75/0.98         ((v4_relat_1 @ X29 @ X30)
% 0.75/0.98          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.75/0.98      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.75/0.98  thf('85', plain, ((v4_relat_1 @ sk_E @ sk_C)),
% 0.75/0.98      inference('sup-', [status(thm)], ['83', '84'])).
% 0.75/0.98  thf('86', plain, (((k1_relat_1 @ sk_E) = (sk_C))),
% 0.75/0.98      inference('demod', [status(thm)], ['79', '82', '85'])).
% 0.75/0.98  thf(t1_mcart_1, axiom,
% 0.75/0.98    (![A:$i]:
% 0.75/0.98     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.75/0.98          ( ![B:$i]: ( ~( ( r2_hidden @ B @ A ) & ( r1_xboole_0 @ B @ A ) ) ) ) ) ))).
% 0.75/0.98  thf('87', plain,
% 0.75/0.98      (![X32 : $i]:
% 0.75/0.98         (((X32) = (k1_xboole_0)) | (r1_xboole_0 @ (sk_B @ X32) @ X32))),
% 0.75/0.98      inference('cnf', [status(esa)], [t1_mcart_1])).
% 0.75/0.98  thf(t187_relat_1, axiom,
% 0.75/0.98    (![A:$i]:
% 0.75/0.98     ( ( v1_relat_1 @ A ) =>
% 0.75/0.98       ( ![B:$i]:
% 0.75/0.98         ( ( r1_xboole_0 @ B @ ( k1_relat_1 @ A ) ) =>
% 0.75/0.98           ( ( k7_relat_1 @ A @ B ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.75/0.98  thf('88', plain,
% 0.75/0.98      (![X19 : $i, X20 : $i]:
% 0.75/0.98         (~ (r1_xboole_0 @ X19 @ (k1_relat_1 @ X20))
% 0.75/0.98          | ((k7_relat_1 @ X20 @ X19) = (k1_xboole_0))
% 0.75/0.98          | ~ (v1_relat_1 @ X20))),
% 0.75/0.98      inference('cnf', [status(esa)], [t187_relat_1])).
% 0.75/0.98  thf('89', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (((k1_relat_1 @ X0) = (k1_xboole_0))
% 0.75/0.98          | ~ (v1_relat_1 @ X0)
% 0.75/0.98          | ((k7_relat_1 @ X0 @ (sk_B @ (k1_relat_1 @ X0))) = (k1_xboole_0)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['87', '88'])).
% 0.75/0.98  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.75/0.98  thf('90', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.75/0.98      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.75/0.98  thf(t162_relat_1, axiom,
% 0.75/0.98    (![A:$i]:
% 0.75/0.98     ( ( v1_relat_1 @ A ) =>
% 0.75/0.98       ( ![B:$i,C:$i]:
% 0.75/0.98         ( ( r1_tarski @ B @ C ) =>
% 0.75/0.98           ( ( k9_relat_1 @ ( k7_relat_1 @ A @ C ) @ B ) =
% 0.75/0.98             ( k9_relat_1 @ A @ B ) ) ) ) ))).
% 0.75/0.98  thf('91', plain,
% 0.75/0.98      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.75/0.98         (~ (r1_tarski @ X16 @ X17)
% 0.75/0.98          | ((k9_relat_1 @ (k7_relat_1 @ X18 @ X17) @ X16)
% 0.75/0.98              = (k9_relat_1 @ X18 @ X16))
% 0.75/0.98          | ~ (v1_relat_1 @ X18))),
% 0.75/0.98      inference('cnf', [status(esa)], [t162_relat_1])).
% 0.75/0.98  thf('92', plain,
% 0.75/0.98      (![X0 : $i, X1 : $i]:
% 0.75/0.98         (~ (v1_relat_1 @ X1)
% 0.75/0.98          | ((k9_relat_1 @ (k7_relat_1 @ X1 @ X0) @ k1_xboole_0)
% 0.75/0.98              = (k9_relat_1 @ X1 @ k1_xboole_0)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['90', '91'])).
% 0.75/0.98  thf('93', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (((k9_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.75/0.98            = (k9_relat_1 @ X0 @ k1_xboole_0))
% 0.75/0.98          | ~ (v1_relat_1 @ X0)
% 0.75/0.98          | ((k1_relat_1 @ X0) = (k1_xboole_0))
% 0.75/0.98          | ~ (v1_relat_1 @ X0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['89', '92'])).
% 0.75/0.98  thf('94', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (((k1_relat_1 @ X0) = (k1_xboole_0))
% 0.75/0.98          | ~ (v1_relat_1 @ X0)
% 0.75/0.98          | ((k9_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.75/0.98              = (k9_relat_1 @ X0 @ k1_xboole_0)))),
% 0.75/0.98      inference('simplify', [status(thm)], ['93'])).
% 0.75/0.98  thf(t64_relat_1, axiom,
% 0.75/0.98    (![A:$i]:
% 0.75/0.98     ( ( v1_relat_1 @ A ) =>
% 0.75/0.98       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.75/0.98           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.75/0.98         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.75/0.98  thf('95', plain,
% 0.75/0.98      (![X21 : $i]:
% 0.75/0.98         (((k1_relat_1 @ X21) != (k1_xboole_0))
% 0.75/0.98          | ((X21) = (k1_xboole_0))
% 0.75/0.98          | ~ (v1_relat_1 @ X21))),
% 0.75/0.98      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.75/0.98  thf('96', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (((k9_relat_1 @ k1_xboole_0 @ k1_xboole_0)
% 0.75/0.98            = (k9_relat_1 @ X0 @ k1_xboole_0))
% 0.75/0.98          | ~ (v1_relat_1 @ X0))),
% 0.75/0.98      inference('clc', [status(thm)], ['94', '95'])).
% 0.75/0.98  thf('97', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         (((k1_relat_1 @ X0) = (k1_xboole_0))
% 0.75/0.98          | ~ (v1_relat_1 @ X0)
% 0.75/0.98          | ((k7_relat_1 @ X0 @ (sk_B @ (k1_relat_1 @ X0))) = (k1_xboole_0)))),
% 0.75/0.98      inference('sup-', [status(thm)], ['87', '88'])).
% 0.75/0.98  thf(dt_k7_relat_1, axiom,
% 0.75/0.98    (![A:$i,B:$i]:
% 0.75/0.98     ( ( v1_relat_1 @ A ) => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ))).
% 0.75/0.98  thf('98', plain,
% 0.75/0.98      (![X11 : $i, X12 : $i]:
% 0.75/0.98         (~ (v1_relat_1 @ X11) | (v1_relat_1 @ (k7_relat_1 @ X11 @ X12)))),
% 0.75/0.98      inference('cnf', [status(esa)], [dt_k7_relat_1])).
% 0.75/0.98  thf('99', plain,
% 0.75/0.98      (![X0 : $i]:
% 0.75/0.98         ((v1_relat_1 @ k1_xboole_0)
% 0.75/0.98          | ~ (v1_relat_1 @ X0)
% 0.75/0.98          | ((k1_relat_1 @ X0) = (k1_xboole_0))
% 0.75/0.98          | ~ (v1_relat_1 @ X0))),
% 0.75/0.98      inference('sup+', [status(thm)], ['97', '98'])).
% 0.75/0.98  thf('100', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (((k1_relat_1 @ X0) = (k1_xboole_0))
% 0.75/0.99          | ~ (v1_relat_1 @ X0)
% 0.75/0.99          | (v1_relat_1 @ k1_xboole_0))),
% 0.75/0.99      inference('simplify', [status(thm)], ['99'])).
% 0.75/0.99  thf('101', plain,
% 0.75/0.99      (![X21 : $i]:
% 0.75/0.99         (((k1_relat_1 @ X21) != (k1_xboole_0))
% 0.75/0.99          | ((X21) = (k1_xboole_0))
% 0.75/0.99          | ~ (v1_relat_1 @ X21))),
% 0.75/0.99      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.75/0.99  thf('102', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (((k1_xboole_0) != (k1_xboole_0))
% 0.75/0.99          | (v1_relat_1 @ k1_xboole_0)
% 0.75/0.99          | ~ (v1_relat_1 @ X0)
% 0.75/0.99          | ~ (v1_relat_1 @ X0)
% 0.75/0.99          | ((X0) = (k1_xboole_0)))),
% 0.75/0.99      inference('sup-', [status(thm)], ['100', '101'])).
% 0.75/0.99  thf('103', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (((X0) = (k1_xboole_0))
% 0.75/0.99          | ~ (v1_relat_1 @ X0)
% 0.75/0.99          | (v1_relat_1 @ k1_xboole_0))),
% 0.75/0.99      inference('simplify', [status(thm)], ['102'])).
% 0.75/0.99  thf(t60_relat_1, axiom,
% 0.75/0.99    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.75/0.99     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.75/0.99  thf('104', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.99      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.75/0.99  thf(t146_relat_1, axiom,
% 0.75/0.99    (![A:$i]:
% 0.75/0.99     ( ( v1_relat_1 @ A ) =>
% 0.75/0.99       ( ( k9_relat_1 @ A @ ( k1_relat_1 @ A ) ) = ( k2_relat_1 @ A ) ) ))).
% 0.75/0.99  thf('105', plain,
% 0.75/0.99      (![X13 : $i]:
% 0.75/0.99         (((k9_relat_1 @ X13 @ (k1_relat_1 @ X13)) = (k2_relat_1 @ X13))
% 0.75/0.99          | ~ (v1_relat_1 @ X13))),
% 0.75/0.99      inference('cnf', [status(esa)], [t146_relat_1])).
% 0.75/0.99  thf('106', plain,
% 0.75/0.99      ((((k9_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))
% 0.75/0.99        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.75/0.99      inference('sup+', [status(thm)], ['104', '105'])).
% 0.75/0.99  thf('107', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.99      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.75/0.99  thf('108', plain,
% 0.75/0.99      ((((k9_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 0.75/0.99        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.75/0.99      inference('demod', [status(thm)], ['106', '107'])).
% 0.75/0.99  thf('109', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (~ (v1_relat_1 @ X0)
% 0.75/0.99          | (v1_relat_1 @ k1_xboole_0)
% 0.75/0.99          | ~ (v1_relat_1 @ X0)
% 0.75/0.99          | ((k9_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.75/0.99      inference('sup-', [status(thm)], ['103', '108'])).
% 0.75/0.99  thf('110', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (((k9_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 0.75/0.99          | (v1_relat_1 @ k1_xboole_0)
% 0.75/0.99          | ~ (v1_relat_1 @ X0))),
% 0.75/0.99      inference('simplify', [status(thm)], ['109'])).
% 0.75/0.99  thf('111', plain,
% 0.75/0.99      ((((k9_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0))
% 0.75/0.99        | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.75/0.99      inference('demod', [status(thm)], ['106', '107'])).
% 0.75/0.99  thf('112', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (~ (v1_relat_1 @ X0)
% 0.75/0.99          | ((k9_relat_1 @ k1_xboole_0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.75/0.99      inference('clc', [status(thm)], ['110', '111'])).
% 0.75/0.99  thf('113', plain,
% 0.75/0.99      (![X0 : $i, X1 : $i]:
% 0.75/0.99         (((k9_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.75/0.99          | ~ (v1_relat_1 @ X0)
% 0.75/0.99          | ~ (v1_relat_1 @ X1))),
% 0.75/0.99      inference('sup+', [status(thm)], ['96', '112'])).
% 0.75/0.99  thf('114', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (((k9_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.75/0.99          | ~ (v1_relat_1 @ X0))),
% 0.75/0.99      inference('condensation', [status(thm)], ['113'])).
% 0.75/0.99  thf(t151_relat_1, axiom,
% 0.75/0.99    (![A:$i,B:$i]:
% 0.75/0.99     ( ( v1_relat_1 @ B ) =>
% 0.75/0.99       ( ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.75/0.99         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.75/0.99  thf('115', plain,
% 0.75/0.99      (![X14 : $i, X15 : $i]:
% 0.75/0.99         (((k9_relat_1 @ X14 @ X15) != (k1_xboole_0))
% 0.75/0.99          | (r1_xboole_0 @ (k1_relat_1 @ X14) @ X15)
% 0.75/0.99          | ~ (v1_relat_1 @ X14))),
% 0.75/0.99      inference('cnf', [status(esa)], [t151_relat_1])).
% 0.75/0.99  thf('116', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (((k1_xboole_0) != (k1_xboole_0))
% 0.75/0.99          | ~ (v1_relat_1 @ X0)
% 0.75/0.99          | ~ (v1_relat_1 @ X0)
% 0.75/0.99          | (r1_xboole_0 @ (k1_relat_1 @ X0) @ k1_xboole_0))),
% 0.75/0.99      inference('sup-', [status(thm)], ['114', '115'])).
% 0.75/0.99  thf('117', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         ((r1_xboole_0 @ (k1_relat_1 @ X0) @ k1_xboole_0) | ~ (v1_relat_1 @ X0))),
% 0.75/0.99      inference('simplify', [status(thm)], ['116'])).
% 0.75/0.99  thf('118', plain,
% 0.75/0.99      (((r1_xboole_0 @ sk_C @ k1_xboole_0) | ~ (v1_relat_1 @ sk_E))),
% 0.75/0.99      inference('sup+', [status(thm)], ['86', '117'])).
% 0.75/0.99  thf('119', plain, ((v1_relat_1 @ sk_E)),
% 0.75/0.99      inference('sup-', [status(thm)], ['80', '81'])).
% 0.75/0.99  thf('120', plain, ((r1_xboole_0 @ sk_C @ k1_xboole_0)),
% 0.75/0.99      inference('demod', [status(thm)], ['118', '119'])).
% 0.75/0.99  thf('121', plain, (((k1_relat_1 @ sk_E) = (sk_C))),
% 0.75/0.99      inference('demod', [status(thm)], ['79', '82', '85'])).
% 0.75/0.99  thf(t95_relat_1, axiom,
% 0.75/0.99    (![A:$i,B:$i]:
% 0.75/0.99     ( ( v1_relat_1 @ B ) =>
% 0.75/0.99       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.75/0.99         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.75/0.99  thf('122', plain,
% 0.75/0.99      (![X22 : $i, X23 : $i]:
% 0.75/0.99         (~ (r1_xboole_0 @ (k1_relat_1 @ X22) @ X23)
% 0.75/0.99          | ((k7_relat_1 @ X22 @ X23) = (k1_xboole_0))
% 0.75/0.99          | ~ (v1_relat_1 @ X22))),
% 0.75/0.99      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.75/0.99  thf('123', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (~ (r1_xboole_0 @ sk_C @ X0)
% 0.75/0.99          | ~ (v1_relat_1 @ sk_E)
% 0.75/0.99          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 0.75/0.99      inference('sup-', [status(thm)], ['121', '122'])).
% 0.75/0.99  thf('124', plain, ((v1_relat_1 @ sk_E)),
% 0.75/0.99      inference('sup-', [status(thm)], ['80', '81'])).
% 0.75/0.99  thf('125', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (~ (r1_xboole_0 @ sk_C @ X0)
% 0.75/0.99          | ((k7_relat_1 @ sk_E @ X0) = (k1_xboole_0)))),
% 0.75/0.99      inference('demod', [status(thm)], ['123', '124'])).
% 0.75/0.99  thf('126', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.99      inference('sup-', [status(thm)], ['120', '125'])).
% 0.75/0.99  thf('127', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.75/0.99      inference('sup-', [status(thm)], ['53', '54'])).
% 0.75/0.99  thf('128', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.75/0.99      inference('sup-', [status(thm)], ['62', '63'])).
% 0.75/0.99  thf('129', plain,
% 0.75/0.99      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('130', plain,
% 0.75/0.99      (![X38 : $i, X39 : $i, X40 : $i, X41 : $i]:
% 0.75/0.99         (~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X39 @ X40)))
% 0.75/0.99          | ~ (v1_funct_1 @ X38)
% 0.75/0.99          | ((k2_partfun1 @ X39 @ X40 @ X38 @ X41) = (k7_relat_1 @ X38 @ X41)))),
% 0.75/0.99      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.75/0.99  thf('131', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 0.75/0.99          | ~ (v1_funct_1 @ sk_F))),
% 0.75/0.99      inference('sup-', [status(thm)], ['129', '130'])).
% 0.75/0.99  thf('132', plain, ((v1_funct_1 @ sk_F)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('133', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         ((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.75/0.99      inference('demod', [status(thm)], ['131', '132'])).
% 0.75/0.99  thf('134', plain,
% 0.75/0.99      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('135', plain,
% 0.75/0.99      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.75/0.99         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.75/0.99          | (v1_partfun1 @ X33 @ X34)
% 0.75/0.99          | ~ (v1_funct_2 @ X33 @ X34 @ X35)
% 0.75/0.99          | ~ (v1_funct_1 @ X33)
% 0.75/0.99          | (v1_xboole_0 @ X35))),
% 0.75/0.99      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.75/0.99  thf('136', plain,
% 0.75/0.99      (((v1_xboole_0 @ sk_B_1)
% 0.75/0.99        | ~ (v1_funct_1 @ sk_F)
% 0.75/0.99        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 0.75/0.99        | (v1_partfun1 @ sk_F @ sk_D))),
% 0.75/0.99      inference('sup-', [status(thm)], ['134', '135'])).
% 0.75/0.99  thf('137', plain, ((v1_funct_1 @ sk_F)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('138', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('139', plain, (((v1_xboole_0 @ sk_B_1) | (v1_partfun1 @ sk_F @ sk_D))),
% 0.75/0.99      inference('demod', [status(thm)], ['136', '137', '138'])).
% 0.75/0.99  thf('140', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('141', plain, ((v1_partfun1 @ sk_F @ sk_D)),
% 0.75/0.99      inference('clc', [status(thm)], ['139', '140'])).
% 0.75/0.99  thf('142', plain,
% 0.75/0.99      (![X36 : $i, X37 : $i]:
% 0.75/0.99         (~ (v1_partfun1 @ X37 @ X36)
% 0.75/0.99          | ((k1_relat_1 @ X37) = (X36))
% 0.75/0.99          | ~ (v4_relat_1 @ X37 @ X36)
% 0.75/0.99          | ~ (v1_relat_1 @ X37))),
% 0.75/0.99      inference('cnf', [status(esa)], [d4_partfun1])).
% 0.75/0.99  thf('143', plain,
% 0.75/0.99      ((~ (v1_relat_1 @ sk_F)
% 0.75/0.99        | ~ (v4_relat_1 @ sk_F @ sk_D)
% 0.75/0.99        | ((k1_relat_1 @ sk_F) = (sk_D)))),
% 0.75/0.99      inference('sup-', [status(thm)], ['141', '142'])).
% 0.75/0.99  thf('144', plain,
% 0.75/0.99      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('145', plain,
% 0.75/0.99      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.75/0.99         ((v1_relat_1 @ X26)
% 0.75/0.99          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.75/0.99      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.75/0.99  thf('146', plain, ((v1_relat_1 @ sk_F)),
% 0.75/0.99      inference('sup-', [status(thm)], ['144', '145'])).
% 0.75/0.99  thf('147', plain,
% 0.75/0.99      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('148', plain,
% 0.75/0.99      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.75/0.99         ((v4_relat_1 @ X29 @ X30)
% 0.75/0.99          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.75/0.99      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.75/0.99  thf('149', plain, ((v4_relat_1 @ sk_F @ sk_D)),
% 0.75/0.99      inference('sup-', [status(thm)], ['147', '148'])).
% 0.75/0.99  thf('150', plain, (((k1_relat_1 @ sk_F) = (sk_D))),
% 0.75/0.99      inference('demod', [status(thm)], ['143', '146', '149'])).
% 0.75/0.99  thf('151', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         ((r1_xboole_0 @ (k1_relat_1 @ X0) @ k1_xboole_0) | ~ (v1_relat_1 @ X0))),
% 0.75/0.99      inference('simplify', [status(thm)], ['116'])).
% 0.75/0.99  thf('152', plain,
% 0.75/0.99      (((r1_xboole_0 @ sk_D @ k1_xboole_0) | ~ (v1_relat_1 @ sk_F))),
% 0.75/0.99      inference('sup+', [status(thm)], ['150', '151'])).
% 0.75/0.99  thf('153', plain, ((v1_relat_1 @ sk_F)),
% 0.75/0.99      inference('sup-', [status(thm)], ['144', '145'])).
% 0.75/0.99  thf('154', plain, ((r1_xboole_0 @ sk_D @ k1_xboole_0)),
% 0.75/0.99      inference('demod', [status(thm)], ['152', '153'])).
% 0.75/0.99  thf('155', plain, (((k1_relat_1 @ sk_F) = (sk_D))),
% 0.75/0.99      inference('demod', [status(thm)], ['143', '146', '149'])).
% 0.75/0.99  thf('156', plain,
% 0.75/0.99      (![X22 : $i, X23 : $i]:
% 0.75/0.99         (~ (r1_xboole_0 @ (k1_relat_1 @ X22) @ X23)
% 0.75/0.99          | ((k7_relat_1 @ X22 @ X23) = (k1_xboole_0))
% 0.75/0.99          | ~ (v1_relat_1 @ X22))),
% 0.75/0.99      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.75/0.99  thf('157', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (~ (r1_xboole_0 @ sk_D @ X0)
% 0.75/0.99          | ~ (v1_relat_1 @ sk_F)
% 0.75/0.99          | ((k7_relat_1 @ sk_F @ X0) = (k1_xboole_0)))),
% 0.75/0.99      inference('sup-', [status(thm)], ['155', '156'])).
% 0.75/0.99  thf('158', plain, ((v1_relat_1 @ sk_F)),
% 0.75/0.99      inference('sup-', [status(thm)], ['144', '145'])).
% 0.75/0.99  thf('159', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (~ (r1_xboole_0 @ sk_D @ X0)
% 0.75/0.99          | ((k7_relat_1 @ sk_F @ X0) = (k1_xboole_0)))),
% 0.75/0.99      inference('demod', [status(thm)], ['157', '158'])).
% 0.75/0.99  thf('160', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.99      inference('sup-', [status(thm)], ['154', '159'])).
% 0.75/0.99  thf('161', plain,
% 0.75/0.99      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('162', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B_1)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('163', plain, ((v1_funct_1 @ sk_E)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('164', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('165', plain,
% 0.75/0.99      (((v1_xboole_0 @ sk_D)
% 0.75/0.99        | (v1_xboole_0 @ sk_C)
% 0.75/0.99        | (v1_xboole_0 @ sk_B_1)
% 0.75/0.99        | (v1_xboole_0 @ sk_A)
% 0.75/0.99        | (v1_xboole_0 @ sk_B_1)
% 0.75/0.99        | (v1_xboole_0 @ sk_D)
% 0.75/0.99        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.75/0.99            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.75/0.99            = (sk_E))
% 0.75/0.99        | ~ (v1_funct_2 @ 
% 0.75/0.99             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.75/0.99             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 0.75/0.99        | ~ (v1_funct_1 @ 
% 0.75/0.99             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.75/0.99        | ((k1_xboole_0) != (k1_xboole_0))
% 0.75/0.99        | (v1_xboole_0 @ sk_C)
% 0.75/0.99        | (v1_xboole_0 @ sk_A))),
% 0.75/0.99      inference('demod', [status(thm)],
% 0.75/0.99                ['48', '49', '50', '51', '52', '55', '64', '69', '126', '127', 
% 0.75/0.99                 '128', '133', '160', '161', '162', '163', '164'])).
% 0.75/0.99  thf('166', plain,
% 0.75/0.99      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.75/0.99        | ~ (v1_funct_2 @ 
% 0.75/0.99             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.75/0.99             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 0.75/0.99        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.75/0.99            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.75/0.99            = (sk_E))
% 0.75/0.99        | (v1_xboole_0 @ sk_A)
% 0.75/0.99        | (v1_xboole_0 @ sk_B_1)
% 0.75/0.99        | (v1_xboole_0 @ sk_C)
% 0.75/0.99        | (v1_xboole_0 @ sk_D))),
% 0.75/0.99      inference('simplify', [status(thm)], ['165'])).
% 0.75/0.99  thf('167', plain,
% 0.75/0.99      ((((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 0.75/0.99          (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.75/0.99          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.75/0.99              (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.75/0.99        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.75/0.99            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.75/0.99            != (sk_E))
% 0.75/0.99        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.75/0.99            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.75/0.99            != (sk_F)))),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('168', plain,
% 0.75/0.99      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.75/0.99          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.75/0.99          != (sk_E)))
% 0.75/0.99         <= (~
% 0.75/0.99             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.75/0.99                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.75/0.99                = (sk_E))))),
% 0.75/0.99      inference('split', [status(esa)], ['167'])).
% 0.75/0.99  thf('169', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         ((r1_xboole_0 @ (k1_relat_1 @ X0) @ k1_xboole_0) | ~ (v1_relat_1 @ X0))),
% 0.75/0.99      inference('simplify', [status(thm)], ['116'])).
% 0.75/0.99  thf('170', plain,
% 0.75/0.99      (![X22 : $i, X23 : $i]:
% 0.75/0.99         (~ (r1_xboole_0 @ (k1_relat_1 @ X22) @ X23)
% 0.75/0.99          | ((k7_relat_1 @ X22 @ X23) = (k1_xboole_0))
% 0.75/0.99          | ~ (v1_relat_1 @ X22))),
% 0.75/0.99      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.75/0.99  thf('171', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (~ (v1_relat_1 @ X0)
% 0.75/0.99          | ~ (v1_relat_1 @ X0)
% 0.75/0.99          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.75/0.99      inference('sup-', [status(thm)], ['169', '170'])).
% 0.75/0.99  thf('172', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.75/0.99          | ~ (v1_relat_1 @ X0))),
% 0.75/0.99      inference('simplify', [status(thm)], ['171'])).
% 0.75/0.99  thf('173', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         (((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.75/0.99          | ~ (v1_relat_1 @ X0))),
% 0.75/0.99      inference('simplify', [status(thm)], ['171'])).
% 0.75/0.99  thf('174', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         ((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.75/0.99      inference('demod', [status(thm)], ['131', '132'])).
% 0.75/0.99  thf('175', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.75/0.99      inference('sup-', [status(thm)], ['53', '54'])).
% 0.75/0.99  thf('176', plain,
% 0.75/0.99      ((((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 0.75/0.99          (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.75/0.99          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.75/0.99              (k9_subset_1 @ sk_A @ sk_C @ sk_D))))
% 0.75/0.99         <= (~
% 0.75/0.99             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 0.75/0.99                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.75/0.99                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.75/0.99                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.75/0.99      inference('split', [status(esa)], ['167'])).
% 0.75/0.99  thf('177', plain,
% 0.75/0.99      ((((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 0.75/0.99          (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.75/0.99          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.75/0.99         <= (~
% 0.75/0.99             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 0.75/0.99                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.75/0.99                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.75/0.99                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.75/0.99      inference('sup-', [status(thm)], ['175', '176'])).
% 0.75/0.99  thf('178', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.75/0.99      inference('sup-', [status(thm)], ['53', '54'])).
% 0.75/0.99  thf('179', plain,
% 0.75/0.99      ((((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 0.75/0.99          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.75/0.99         <= (~
% 0.75/0.99             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 0.75/0.99                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.75/0.99                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.75/0.99                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.75/0.99      inference('demod', [status(thm)], ['177', '178'])).
% 0.75/0.99  thf('180', plain,
% 0.75/0.99      ((((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 0.75/0.99          != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.75/0.99         <= (~
% 0.75/0.99             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 0.75/0.99                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.75/0.99                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.75/0.99                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.75/0.99      inference('sup-', [status(thm)], ['174', '179'])).
% 0.75/0.99  thf('181', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.75/0.99      inference('sup-', [status(thm)], ['62', '63'])).
% 0.75/0.99  thf('182', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         ((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.75/0.99      inference('demod', [status(thm)], ['67', '68'])).
% 0.75/0.99  thf('183', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.75/0.99      inference('sup-', [status(thm)], ['62', '63'])).
% 0.75/0.99  thf('184', plain,
% 0.75/0.99      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0)))
% 0.75/0.99         <= (~
% 0.75/0.99             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 0.75/0.99                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.75/0.99                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.75/0.99                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.75/0.99      inference('demod', [status(thm)], ['180', '181', '182', '183'])).
% 0.75/0.99  thf('185', plain,
% 0.75/0.99      (((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.75/0.99         | ~ (v1_relat_1 @ sk_F)))
% 0.75/0.99         <= (~
% 0.75/0.99             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 0.75/0.99                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.75/0.99                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.75/0.99                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.75/0.99      inference('sup-', [status(thm)], ['173', '184'])).
% 0.75/0.99  thf('186', plain, ((v1_relat_1 @ sk_F)),
% 0.75/0.99      inference('sup-', [status(thm)], ['144', '145'])).
% 0.75/0.99  thf('187', plain,
% 0.75/0.99      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0)))
% 0.75/0.99         <= (~
% 0.75/0.99             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 0.75/0.99                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.75/0.99                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.75/0.99                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.75/0.99      inference('demod', [status(thm)], ['185', '186'])).
% 0.75/0.99  thf('188', plain,
% 0.75/0.99      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_E)))
% 0.75/0.99         <= (~
% 0.75/0.99             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 0.75/0.99                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.75/0.99                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.75/0.99                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.75/0.99      inference('sup-', [status(thm)], ['172', '187'])).
% 0.75/0.99  thf('189', plain, ((v1_relat_1 @ sk_E)),
% 0.75/0.99      inference('sup-', [status(thm)], ['80', '81'])).
% 0.75/0.99  thf('190', plain,
% 0.75/0.99      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.75/0.99         <= (~
% 0.75/0.99             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 0.75/0.99                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.75/0.99                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.75/0.99                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.75/0.99      inference('demod', [status(thm)], ['188', '189'])).
% 0.75/0.99  thf('191', plain,
% 0.75/0.99      ((((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 0.75/0.99          (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.75/0.99          = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.75/0.99             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.75/0.99      inference('simplify', [status(thm)], ['190'])).
% 0.75/0.99  thf('192', plain,
% 0.75/0.99      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.75/0.99        | (v1_xboole_0 @ sk_A)
% 0.75/0.99        | (v1_xboole_0 @ sk_B_1)
% 0.75/0.99        | (v1_xboole_0 @ sk_C)
% 0.75/0.99        | (v1_xboole_0 @ sk_D))),
% 0.75/0.99      inference('demod', [status(thm)], ['13', '14'])).
% 0.75/0.99  thf('193', plain,
% 0.75/0.99      (((v1_funct_2 @ 
% 0.75/0.99         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.75/0.99         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 0.75/0.99        | (v1_xboole_0 @ sk_A)
% 0.75/0.99        | (v1_xboole_0 @ sk_B_1)
% 0.75/0.99        | (v1_xboole_0 @ sk_C)
% 0.75/0.99        | (v1_xboole_0 @ sk_D))),
% 0.75/0.99      inference('demod', [status(thm)], ['28', '29'])).
% 0.75/0.99  thf('194', plain,
% 0.75/0.99      (((m1_subset_1 @ 
% 0.75/0.99         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.75/0.99         (k1_zfmisc_1 @ 
% 0.75/0.99          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)))
% 0.75/0.99        | (v1_xboole_0 @ sk_A)
% 0.75/0.99        | (v1_xboole_0 @ sk_B_1)
% 0.75/0.99        | (v1_xboole_0 @ sk_C)
% 0.75/0.99        | (v1_xboole_0 @ sk_D))),
% 0.75/0.99      inference('demod', [status(thm)], ['43', '44'])).
% 0.75/0.99  thf('195', plain,
% 0.75/0.99      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i]:
% 0.75/0.99         ((v1_xboole_0 @ X42)
% 0.75/0.99          | (v1_xboole_0 @ X43)
% 0.75/0.99          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 0.75/0.99          | ~ (v1_funct_1 @ X45)
% 0.75/0.99          | ~ (v1_funct_2 @ X45 @ X43 @ X42)
% 0.75/0.99          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))
% 0.75/0.99          | ((X48) != (k1_tmap_1 @ X44 @ X42 @ X47 @ X43 @ X46 @ X45))
% 0.75/0.99          | ((k2_partfun1 @ (k4_subset_1 @ X44 @ X47 @ X43) @ X42 @ X48 @ X43)
% 0.75/0.99              = (X45))
% 0.75/0.99          | ~ (m1_subset_1 @ X48 @ 
% 0.75/0.99               (k1_zfmisc_1 @ 
% 0.75/0.99                (k2_zfmisc_1 @ (k4_subset_1 @ X44 @ X47 @ X43) @ X42)))
% 0.75/0.99          | ~ (v1_funct_2 @ X48 @ (k4_subset_1 @ X44 @ X47 @ X43) @ X42)
% 0.75/0.99          | ~ (v1_funct_1 @ X48)
% 0.75/0.99          | ((k2_partfun1 @ X47 @ X42 @ X46 @ (k9_subset_1 @ X44 @ X47 @ X43))
% 0.75/0.99              != (k2_partfun1 @ X43 @ X42 @ X45 @ 
% 0.75/0.99                  (k9_subset_1 @ X44 @ X47 @ X43)))
% 0.75/0.99          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X42)))
% 0.75/0.99          | ~ (v1_funct_2 @ X46 @ X47 @ X42)
% 0.75/0.99          | ~ (v1_funct_1 @ X46)
% 0.75/0.99          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X44))
% 0.75/0.99          | (v1_xboole_0 @ X47)
% 0.75/0.99          | (v1_xboole_0 @ X44))),
% 0.75/0.99      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.75/0.99  thf('196', plain,
% 0.75/0.99      (![X42 : $i, X43 : $i, X44 : $i, X45 : $i, X46 : $i, X47 : $i]:
% 0.75/0.99         ((v1_xboole_0 @ X44)
% 0.75/0.99          | (v1_xboole_0 @ X47)
% 0.75/0.99          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X44))
% 0.75/0.99          | ~ (v1_funct_1 @ X46)
% 0.75/0.99          | ~ (v1_funct_2 @ X46 @ X47 @ X42)
% 0.75/0.99          | ~ (m1_subset_1 @ X46 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X42)))
% 0.75/0.99          | ((k2_partfun1 @ X47 @ X42 @ X46 @ (k9_subset_1 @ X44 @ X47 @ X43))
% 0.75/0.99              != (k2_partfun1 @ X43 @ X42 @ X45 @ 
% 0.75/0.99                  (k9_subset_1 @ X44 @ X47 @ X43)))
% 0.75/0.99          | ~ (v1_funct_1 @ (k1_tmap_1 @ X44 @ X42 @ X47 @ X43 @ X46 @ X45))
% 0.75/0.99          | ~ (v1_funct_2 @ (k1_tmap_1 @ X44 @ X42 @ X47 @ X43 @ X46 @ X45) @ 
% 0.75/0.99               (k4_subset_1 @ X44 @ X47 @ X43) @ X42)
% 0.75/0.99          | ~ (m1_subset_1 @ (k1_tmap_1 @ X44 @ X42 @ X47 @ X43 @ X46 @ X45) @ 
% 0.75/0.99               (k1_zfmisc_1 @ 
% 0.75/0.99                (k2_zfmisc_1 @ (k4_subset_1 @ X44 @ X47 @ X43) @ X42)))
% 0.75/0.99          | ((k2_partfun1 @ (k4_subset_1 @ X44 @ X47 @ X43) @ X42 @ 
% 0.75/0.99              (k1_tmap_1 @ X44 @ X42 @ X47 @ X43 @ X46 @ X45) @ X43) = (
% 0.75/0.99              X45))
% 0.75/0.99          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X43 @ X42)))
% 0.75/0.99          | ~ (v1_funct_2 @ X45 @ X43 @ X42)
% 0.75/0.99          | ~ (v1_funct_1 @ X45)
% 0.75/0.99          | ~ (m1_subset_1 @ X43 @ (k1_zfmisc_1 @ X44))
% 0.75/0.99          | (v1_xboole_0 @ X43)
% 0.75/0.99          | (v1_xboole_0 @ X42))),
% 0.75/0.99      inference('simplify', [status(thm)], ['195'])).
% 0.75/0.99  thf('197', plain,
% 0.75/0.99      (((v1_xboole_0 @ sk_D)
% 0.75/0.99        | (v1_xboole_0 @ sk_C)
% 0.75/0.99        | (v1_xboole_0 @ sk_B_1)
% 0.75/0.99        | (v1_xboole_0 @ sk_A)
% 0.75/0.99        | (v1_xboole_0 @ sk_B_1)
% 0.75/0.99        | (v1_xboole_0 @ sk_D)
% 0.75/0.99        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.75/0.99        | ~ (v1_funct_1 @ sk_F)
% 0.75/0.99        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 0.75/0.99        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))
% 0.75/0.99        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.75/0.99            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.75/0.99            = (sk_F))
% 0.75/0.99        | ~ (v1_funct_2 @ 
% 0.75/0.99             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.75/0.99             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 0.75/0.99        | ~ (v1_funct_1 @ 
% 0.75/0.99             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.75/0.99        | ((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 0.75/0.99            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.75/0.99            != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.75/0.99                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.75/0.99        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))
% 0.75/0.99        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B_1)
% 0.75/0.99        | ~ (v1_funct_1 @ sk_E)
% 0.75/0.99        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.75/0.99        | (v1_xboole_0 @ sk_C)
% 0.75/0.99        | (v1_xboole_0 @ sk_A))),
% 0.75/0.99      inference('sup-', [status(thm)], ['194', '196'])).
% 0.75/0.99  thf('198', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('199', plain, ((v1_funct_1 @ sk_F)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('200', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('201', plain,
% 0.75/0.99      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('202', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.75/0.99      inference('sup-', [status(thm)], ['53', '54'])).
% 0.75/0.99  thf('203', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.75/0.99      inference('sup-', [status(thm)], ['62', '63'])).
% 0.75/0.99  thf('204', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         ((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.75/0.99      inference('demod', [status(thm)], ['67', '68'])).
% 0.75/0.99  thf('205', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.99      inference('sup-', [status(thm)], ['120', '125'])).
% 0.75/0.99  thf('206', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.75/0.99      inference('sup-', [status(thm)], ['53', '54'])).
% 0.75/0.99  thf('207', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.75/0.99      inference('sup-', [status(thm)], ['62', '63'])).
% 0.75/0.99  thf('208', plain,
% 0.75/0.99      (![X0 : $i]:
% 0.75/0.99         ((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.75/0.99      inference('demod', [status(thm)], ['131', '132'])).
% 0.75/0.99  thf('209', plain, (((k7_relat_1 @ sk_F @ k1_xboole_0) = (k1_xboole_0))),
% 0.75/0.99      inference('sup-', [status(thm)], ['154', '159'])).
% 0.75/0.99  thf('210', plain,
% 0.75/0.99      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('211', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B_1)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('212', plain, ((v1_funct_1 @ sk_E)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('213', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('214', plain,
% 0.75/0.99      (((v1_xboole_0 @ sk_D)
% 0.75/0.99        | (v1_xboole_0 @ sk_C)
% 0.75/0.99        | (v1_xboole_0 @ sk_B_1)
% 0.75/0.99        | (v1_xboole_0 @ sk_A)
% 0.75/0.99        | (v1_xboole_0 @ sk_B_1)
% 0.75/0.99        | (v1_xboole_0 @ sk_D)
% 0.75/0.99        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.75/0.99            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.75/0.99            = (sk_F))
% 0.75/0.99        | ~ (v1_funct_2 @ 
% 0.75/0.99             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.75/0.99             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 0.75/0.99        | ~ (v1_funct_1 @ 
% 0.75/0.99             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.75/0.99        | ((k1_xboole_0) != (k1_xboole_0))
% 0.75/0.99        | (v1_xboole_0 @ sk_C)
% 0.75/0.99        | (v1_xboole_0 @ sk_A))),
% 0.75/0.99      inference('demod', [status(thm)],
% 0.75/0.99                ['197', '198', '199', '200', '201', '202', '203', '204', 
% 0.75/0.99                 '205', '206', '207', '208', '209', '210', '211', '212', '213'])).
% 0.75/0.99  thf('215', plain,
% 0.75/0.99      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.75/0.99        | ~ (v1_funct_2 @ 
% 0.75/0.99             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.75/0.99             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 0.75/0.99        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.75/0.99            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.75/0.99            = (sk_F))
% 0.75/0.99        | (v1_xboole_0 @ sk_A)
% 0.75/0.99        | (v1_xboole_0 @ sk_B_1)
% 0.75/0.99        | (v1_xboole_0 @ sk_C)
% 0.75/0.99        | (v1_xboole_0 @ sk_D))),
% 0.75/0.99      inference('simplify', [status(thm)], ['214'])).
% 0.75/0.99  thf('216', plain,
% 0.75/0.99      (((v1_xboole_0 @ sk_D)
% 0.75/0.99        | (v1_xboole_0 @ sk_C)
% 0.75/0.99        | (v1_xboole_0 @ sk_B_1)
% 0.75/0.99        | (v1_xboole_0 @ sk_A)
% 0.75/0.99        | (v1_xboole_0 @ sk_D)
% 0.75/0.99        | (v1_xboole_0 @ sk_C)
% 0.75/0.99        | (v1_xboole_0 @ sk_B_1)
% 0.75/0.99        | (v1_xboole_0 @ sk_A)
% 0.75/0.99        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.75/0.99            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.75/0.99            = (sk_F))
% 0.75/0.99        | ~ (v1_funct_1 @ 
% 0.75/0.99             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.75/0.99      inference('sup-', [status(thm)], ['193', '215'])).
% 0.75/0.99  thf('217', plain,
% 0.75/0.99      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.75/0.99        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.75/0.99            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.75/0.99            = (sk_F))
% 0.75/0.99        | (v1_xboole_0 @ sk_A)
% 0.75/0.99        | (v1_xboole_0 @ sk_B_1)
% 0.75/0.99        | (v1_xboole_0 @ sk_C)
% 0.75/0.99        | (v1_xboole_0 @ sk_D))),
% 0.75/0.99      inference('simplify', [status(thm)], ['216'])).
% 0.75/0.99  thf('218', plain,
% 0.75/0.99      (((v1_xboole_0 @ sk_D)
% 0.75/0.99        | (v1_xboole_0 @ sk_C)
% 0.75/0.99        | (v1_xboole_0 @ sk_B_1)
% 0.75/0.99        | (v1_xboole_0 @ sk_A)
% 0.75/0.99        | (v1_xboole_0 @ sk_D)
% 0.75/0.99        | (v1_xboole_0 @ sk_C)
% 0.75/0.99        | (v1_xboole_0 @ sk_B_1)
% 0.75/0.99        | (v1_xboole_0 @ sk_A)
% 0.75/0.99        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.75/0.99            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.75/0.99            = (sk_F)))),
% 0.75/0.99      inference('sup-', [status(thm)], ['192', '217'])).
% 0.75/0.99  thf('219', plain,
% 0.75/0.99      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.75/0.99          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.75/0.99          = (sk_F))
% 0.75/0.99        | (v1_xboole_0 @ sk_A)
% 0.75/0.99        | (v1_xboole_0 @ sk_B_1)
% 0.75/0.99        | (v1_xboole_0 @ sk_C)
% 0.75/0.99        | (v1_xboole_0 @ sk_D))),
% 0.75/0.99      inference('simplify', [status(thm)], ['218'])).
% 0.75/0.99  thf('220', plain,
% 0.75/0.99      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.75/0.99          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.75/0.99          != (sk_F)))
% 0.75/0.99         <= (~
% 0.75/0.99             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.75/0.99                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.75/0.99                = (sk_F))))),
% 0.75/0.99      inference('split', [status(esa)], ['167'])).
% 0.75/0.99  thf('221', plain,
% 0.75/0.99      (((((sk_F) != (sk_F))
% 0.75/0.99         | (v1_xboole_0 @ sk_D)
% 0.75/0.99         | (v1_xboole_0 @ sk_C)
% 0.75/0.99         | (v1_xboole_0 @ sk_B_1)
% 0.75/0.99         | (v1_xboole_0 @ sk_A)))
% 0.75/0.99         <= (~
% 0.75/0.99             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.75/0.99                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.75/0.99                = (sk_F))))),
% 0.75/0.99      inference('sup-', [status(thm)], ['219', '220'])).
% 0.75/0.99  thf('222', plain,
% 0.75/0.99      ((((v1_xboole_0 @ sk_A)
% 0.75/0.99         | (v1_xboole_0 @ sk_B_1)
% 0.75/0.99         | (v1_xboole_0 @ sk_C)
% 0.75/0.99         | (v1_xboole_0 @ sk_D)))
% 0.75/0.99         <= (~
% 0.75/0.99             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.75/0.99                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.75/0.99                = (sk_F))))),
% 0.75/0.99      inference('simplify', [status(thm)], ['221'])).
% 0.75/0.99  thf('223', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('224', plain,
% 0.75/0.99      ((((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A)))
% 0.75/0.99         <= (~
% 0.75/0.99             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.75/0.99                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.75/0.99                = (sk_F))))),
% 0.75/0.99      inference('sup-', [status(thm)], ['222', '223'])).
% 0.75/0.99  thf('225', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('226', plain,
% 0.75/0.99      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B_1)))
% 0.75/0.99         <= (~
% 0.75/0.99             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.75/0.99                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.75/0.99                = (sk_F))))),
% 0.75/0.99      inference('clc', [status(thm)], ['224', '225'])).
% 0.75/0.99  thf('227', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('228', plain,
% 0.75/0.99      (((v1_xboole_0 @ sk_B_1))
% 0.75/0.99         <= (~
% 0.75/0.99             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.75/0.99                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.75/0.99                = (sk_F))))),
% 0.75/0.99      inference('clc', [status(thm)], ['226', '227'])).
% 0.75/0.99  thf('229', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('230', plain,
% 0.75/0.99      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.75/0.99          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.75/0.99          = (sk_F)))),
% 0.75/0.99      inference('sup-', [status(thm)], ['228', '229'])).
% 0.75/0.99  thf('231', plain,
% 0.75/0.99      (~
% 0.75/0.99       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.75/0.99          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.75/0.99          = (sk_E))) | 
% 0.75/0.99       ~
% 0.75/0.99       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.75/0.99          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.75/0.99          = (sk_F))) | 
% 0.75/0.99       ~
% 0.75/0.99       (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 0.75/0.99          (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.75/0.99          = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.75/0.99             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.75/0.99      inference('split', [status(esa)], ['167'])).
% 0.75/0.99  thf('232', plain,
% 0.75/0.99      (~
% 0.75/0.99       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.75/0.99          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.75/0.99          = (sk_E)))),
% 0.75/0.99      inference('sat_resolution*', [status(thm)], ['191', '230', '231'])).
% 0.75/0.99  thf('233', plain,
% 0.75/0.99      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.75/0.99         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.75/0.99         != (sk_E))),
% 0.75/0.99      inference('simpl_trail', [status(thm)], ['168', '232'])).
% 0.75/0.99  thf('234', plain,
% 0.75/0.99      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.75/0.99        | ~ (v1_funct_2 @ 
% 0.75/0.99             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.75/0.99             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 0.75/0.99        | (v1_xboole_0 @ sk_A)
% 0.75/0.99        | (v1_xboole_0 @ sk_B_1)
% 0.75/0.99        | (v1_xboole_0 @ sk_C)
% 0.75/0.99        | (v1_xboole_0 @ sk_D))),
% 0.75/0.99      inference('simplify_reflect-', [status(thm)], ['166', '233'])).
% 0.75/0.99  thf('235', plain,
% 0.75/0.99      (((v1_xboole_0 @ sk_D)
% 0.75/0.99        | (v1_xboole_0 @ sk_C)
% 0.75/0.99        | (v1_xboole_0 @ sk_B_1)
% 0.75/0.99        | (v1_xboole_0 @ sk_A)
% 0.75/0.99        | (v1_xboole_0 @ sk_D)
% 0.75/0.99        | (v1_xboole_0 @ sk_C)
% 0.75/0.99        | (v1_xboole_0 @ sk_B_1)
% 0.75/0.99        | (v1_xboole_0 @ sk_A)
% 0.75/0.99        | ~ (v1_funct_1 @ 
% 0.75/0.99             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.75/0.99      inference('sup-', [status(thm)], ['30', '234'])).
% 0.75/0.99  thf('236', plain,
% 0.75/0.99      ((~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.75/0.99        | (v1_xboole_0 @ sk_A)
% 0.75/0.99        | (v1_xboole_0 @ sk_B_1)
% 0.75/0.99        | (v1_xboole_0 @ sk_C)
% 0.75/0.99        | (v1_xboole_0 @ sk_D))),
% 0.75/0.99      inference('simplify', [status(thm)], ['235'])).
% 0.75/0.99  thf('237', plain,
% 0.75/0.99      (((v1_xboole_0 @ sk_D)
% 0.75/0.99        | (v1_xboole_0 @ sk_C)
% 0.75/0.99        | (v1_xboole_0 @ sk_B_1)
% 0.75/0.99        | (v1_xboole_0 @ sk_A)
% 0.75/0.99        | (v1_xboole_0 @ sk_D)
% 0.75/0.99        | (v1_xboole_0 @ sk_C)
% 0.75/0.99        | (v1_xboole_0 @ sk_B_1)
% 0.75/0.99        | (v1_xboole_0 @ sk_A))),
% 0.75/0.99      inference('sup-', [status(thm)], ['15', '236'])).
% 0.75/0.99  thf('238', plain,
% 0.75/0.99      (((v1_xboole_0 @ sk_A)
% 0.75/0.99        | (v1_xboole_0 @ sk_B_1)
% 0.75/0.99        | (v1_xboole_0 @ sk_C)
% 0.75/0.99        | (v1_xboole_0 @ sk_D))),
% 0.75/0.99      inference('simplify', [status(thm)], ['237'])).
% 0.75/0.99  thf('239', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('240', plain,
% 0.75/0.99      (((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A))),
% 0.75/0.99      inference('sup-', [status(thm)], ['238', '239'])).
% 0.75/0.99  thf('241', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('242', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B_1))),
% 0.75/0.99      inference('clc', [status(thm)], ['240', '241'])).
% 0.75/0.99  thf('243', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.75/0.99      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.75/0.99  thf('244', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.75/0.99      inference('clc', [status(thm)], ['242', '243'])).
% 0.75/0.99  thf('245', plain, ($false), inference('demod', [status(thm)], ['0', '244'])).
% 0.75/0.99  
% 0.75/0.99  % SZS output end Refutation
% 0.75/0.99  
% 0.75/0.99  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
