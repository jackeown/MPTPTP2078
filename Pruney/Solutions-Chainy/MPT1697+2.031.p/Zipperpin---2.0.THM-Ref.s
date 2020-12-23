%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3gbbJTgZfk

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:57 EST 2020

% Result     : Theorem 0.42s
% Output     : Refutation 0.42s
% Verified   : 
% Statistics : Number of formulae       :  220 ( 629 expanded)
%              Number of leaves         :   33 ( 196 expanded)
%              Depth                    :   40
%              Number of atoms          : 3693 (27535 expanded)
%              Number of equality atoms :  131 ( 889 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

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

thf(fc16_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ A )
        & ( v1_xboole_0 @ B ) )
     => ( ( v1_xboole_0 @ ( k7_relat_1 @ A @ B ) )
        & ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) ) )).

thf('1',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( v1_relat_1 @ X9 )
      | ~ ( v1_xboole_0 @ X10 )
      | ( v1_xboole_0 @ ( k7_relat_1 @ X9 @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[fc16_relat_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('5',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
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

thf('8',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ( v1_xboole_0 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X39 ) )
      | ( v1_xboole_0 @ X36 )
      | ( v1_xboole_0 @ X37 )
      | ( v1_xboole_0 @ X39 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X38 @ X37 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X39 @ X37 @ X36 @ X38 @ X35 @ X40 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_1 @ ( k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X0 @ X1 @ sk_B )
      | ~ ( v1_funct_1 @ X0 )
      | ( v1_xboole_0 @ X2 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X2 ) )
      | ( v1_xboole_0 @ X1 )
      | ~ ( m1_subset_1 @ X1 @ ( k1_zfmisc_1 @ X2 ) ) ) ),
    inference(demod,[status(thm)],['9','10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ( v1_xboole_0 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X39 ) )
      | ( v1_xboole_0 @ X36 )
      | ( v1_xboole_0 @ X37 )
      | ( v1_xboole_0 @ X39 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X38 @ X37 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X39 @ X37 @ X36 @ X38 @ X35 @ X40 ) @ ( k4_subset_1 @ X39 @ X36 @ X38 ) @ X37 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('24',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ ( k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2 ) @ ( k4_subset_1 @ X1 @ sk_C @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_funct_2 @ ( k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2 ) @ ( k4_subset_1 @ X1 @ sk_C @ X0 ) @ sk_B )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ X0 @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf('29',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ X0 @ sk_C @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['20','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i,X39: $i,X40: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X35 @ X36 @ X37 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ( v1_xboole_0 @ X38 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ X39 ) )
      | ( v1_xboole_0 @ X36 )
      | ( v1_xboole_0 @ X37 )
      | ( v1_xboole_0 @ X39 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X38 @ X37 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X39 @ X37 @ X36 @ X38 @ X35 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X39 @ X36 @ X38 ) @ X37 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X1 @ sk_C @ X0 ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X1 @ sk_C @ X0 ) @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_B ) ) )
      | ~ ( v1_funct_2 @ X2 @ X0 @ sk_B )
      | ~ ( v1_funct_1 @ X2 )
      | ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X1 ) )
      | ( v1_xboole_0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X1 ) ) ) ),
    inference(demod,[status(thm)],['39','40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_F )
      | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C @ sk_D ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['36','42'])).

thf('44',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C @ sk_D ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['43','44','45'])).

thf('47',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['35','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['47','48'])).

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

thf('50',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ( v1_xboole_0 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ( X34
       != ( k1_tmap_1 @ X30 @ X28 @ X33 @ X29 @ X32 @ X31 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X30 @ X33 @ X29 ) @ X28 @ X34 @ X33 )
        = X32 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X30 @ X33 @ X29 ) @ X28 ) ) )
      | ~ ( v1_funct_2 @ X34 @ ( k4_subset_1 @ X30 @ X33 @ X29 ) @ X28 )
      | ~ ( v1_funct_1 @ X34 )
      | ( ( k2_partfun1 @ X33 @ X28 @ X32 @ ( k9_subset_1 @ X30 @ X33 @ X29 ) )
       != ( k2_partfun1 @ X29 @ X28 @ X31 @ ( k9_subset_1 @ X30 @ X33 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X28 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X30 ) )
      | ( v1_xboole_0 @ X33 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('51',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ( v1_xboole_0 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X28 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X28 ) ) )
      | ( ( k2_partfun1 @ X33 @ X28 @ X32 @ ( k9_subset_1 @ X30 @ X33 @ X29 ) )
       != ( k2_partfun1 @ X29 @ X28 @ X31 @ ( k9_subset_1 @ X30 @ X33 @ X29 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X30 @ X28 @ X33 @ X29 @ X32 @ X31 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X30 @ X28 @ X33 @ X29 @ X32 @ X31 ) @ ( k4_subset_1 @ X30 @ X33 @ X29 ) @ X28 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X30 @ X28 @ X33 @ X29 @ X32 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X30 @ X33 @ X29 ) @ X28 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X30 @ X33 @ X29 ) @ X28 @ ( k1_tmap_1 @ X30 @ X28 @ X33 @ X29 @ X32 @ X31 ) @ X33 )
        = X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ( v1_xboole_0 @ X29 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['49','51'])).

thf('53',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('58',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( ( k9_subset_1 @ X6 @ X4 @ X5 )
        = ( k3_xboole_0 @ X4 @ X5 ) )
      | ~ ( m1_subset_1 @ X5 @ ( k1_zfmisc_1 @ X6 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    r1_subset_1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r1_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ( ( r1_subset_1 @ A @ B )
      <=> ( r1_xboole_0 @ A @ B ) ) ) )).

thf('61',plain,(
    ! [X16: $i,X17: $i] :
      ( ( v1_xboole_0 @ X16 )
      | ( v1_xboole_0 @ X17 )
      | ( r1_xboole_0 @ X16 @ X17 )
      | ~ ( r1_subset_1 @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_subset_1])).

thf('62',plain,
    ( ( r1_xboole_0 @ sk_C @ sk_D )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r1_xboole_0 @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    r1_xboole_0 @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['64','65'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('68',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('70',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ( ( k2_partfun1 @ X25 @ X26 @ X24 @ X27 )
        = ( k7_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('75',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['66','67'])).

thf('76',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('77',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X24 )
      | ( ( k2_partfun1 @ X25 @ X26 @ X24 @ X27 )
        = ( k7_relat_1 @ X24 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('83',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['52','53','54','55','56','59','68','73','74','75','80','81','82','83','84'])).

thf('86',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['34','86'])).

thf('88',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E ) ),
    inference(split,[status(esa)],['89'])).

thf('91',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('92',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('94',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['89'])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('97',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k3_xboole_0 @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['94','95','96'])).

thf('98',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k3_xboole_0 @ sk_C @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['93','97'])).

thf('99',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['66','67'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('101',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['66','67'])).

thf('102',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['98','99','100','101'])).

thf('103',plain,
    ( ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_F )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['92','102'])).

thf('104',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('105',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('106',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['104','105'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('107',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('108',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['103','106','107'])).

thf('109',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['91','108'])).

thf('110',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( v1_relat_1 @ X18 )
      | ~ ( m1_subset_1 @ X18 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X19 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('112',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['110','111'])).

thf('113',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('114',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['109','112','113'])).

thf('115',plain,
    ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['114'])).

thf('116',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('117',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('118',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['17','18'])).

thf('119',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['32','33'])).

thf('120',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('121',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ( v1_xboole_0 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_funct_2 @ X31 @ X29 @ X28 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ( X34
       != ( k1_tmap_1 @ X30 @ X28 @ X33 @ X29 @ X32 @ X31 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X30 @ X33 @ X29 ) @ X28 @ X34 @ X29 )
        = X31 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X30 @ X33 @ X29 ) @ X28 ) ) )
      | ~ ( v1_funct_2 @ X34 @ ( k4_subset_1 @ X30 @ X33 @ X29 ) @ X28 )
      | ~ ( v1_funct_1 @ X34 )
      | ( ( k2_partfun1 @ X33 @ X28 @ X32 @ ( k9_subset_1 @ X30 @ X33 @ X29 ) )
       != ( k2_partfun1 @ X29 @ X28 @ X31 @ ( k9_subset_1 @ X30 @ X33 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X28 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X30 ) )
      | ( v1_xboole_0 @ X33 )
      | ( v1_xboole_0 @ X30 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('122',plain,(
    ! [X28: $i,X29: $i,X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ( v1_xboole_0 @ X30 )
      | ( v1_xboole_0 @ X33 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X30 ) )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X28 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X28 ) ) )
      | ( ( k2_partfun1 @ X33 @ X28 @ X32 @ ( k9_subset_1 @ X30 @ X33 @ X29 ) )
       != ( k2_partfun1 @ X29 @ X28 @ X31 @ ( k9_subset_1 @ X30 @ X33 @ X29 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X30 @ X28 @ X33 @ X29 @ X32 @ X31 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X30 @ X28 @ X33 @ X29 @ X32 @ X31 ) @ ( k4_subset_1 @ X30 @ X33 @ X29 ) @ X28 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X30 @ X28 @ X33 @ X29 @ X32 @ X31 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X30 @ X33 @ X29 ) @ X28 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X30 @ X33 @ X29 ) @ X28 @ ( k1_tmap_1 @ X30 @ X28 @ X33 @ X29 @ X32 @ X31 ) @ X29 )
        = X31 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X29 @ X28 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X30 ) )
      | ( v1_xboole_0 @ X29 )
      | ( v1_xboole_0 @ X28 ) ) ),
    inference(simplify,[status(thm)],['121'])).

thf('123',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D )
    | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) )
    | ~ ( v1_funct_1 @ sk_F )
    | ~ ( v1_funct_2 @ sk_F @ sk_D @ sk_B )
    | ~ ( m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_E @ sk_C @ sk_B )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['120','122'])).

thf('124',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('125',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('129',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['66','67'])).

thf('130',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('132',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['66','67'])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('134',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['123','124','125','126','127','128','129','130','131','132','133','134','135','136','137'])).

thf('139',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['138'])).

thf('140',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['119','139'])).

thf('141',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['140'])).

thf('142',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['118','141'])).

thf('143',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['142'])).

thf('144',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference('sup-',[status(thm)],['117','143'])).

thf('145',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['104','105'])).

thf('146',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('147',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference(demod,[status(thm)],['144','145','146'])).

thf('148',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['116','147'])).

thf('149',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['110','111'])).

thf('150',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('151',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['148','149','150'])).

thf('152',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['89'])).

thf('154',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['152','153'])).

thf('155',plain,
    ( ( ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['154'])).

thf('156',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('157',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('159',plain,
    ( ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['157','158'])).

thf('160',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('161',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['159','160'])).

thf('162',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('163',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['89'])).

thf('165',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['115','163','164'])).

thf('166',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['90','165'])).

thf('167',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['88','166'])).

thf('168',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['19','167'])).

thf('169',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['168'])).

thf('170',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['4','169'])).

thf('171',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['104','105'])).

thf('172',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('173',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['170','171','172'])).

thf('174',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','173'])).

thf('175',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['110','111'])).

thf('176',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('177',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['174','175','176'])).

thf('178',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('180',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['178','179'])).

thf('181',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('182',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['180','181'])).

thf('183',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('184',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['182','183'])).

thf('185',plain,(
    $false ),
    inference(demod,[status(thm)],['0','184'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3gbbJTgZfk
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:47:11 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running portfolio for 600 s
% 0.12/0.33  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.12/0.33  % Number of cores: 8
% 0.12/0.34  % Python version: Python 3.6.8
% 0.12/0.34  % Running in FO mode
% 0.42/0.61  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.42/0.61  % Solved by: fo/fo7.sh
% 0.42/0.61  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.42/0.61  % done 179 iterations in 0.161s
% 0.42/0.61  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.42/0.61  % SZS output start Refutation
% 0.42/0.61  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.42/0.61  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.42/0.61  thf(sk_B_type, type, sk_B: $i).
% 0.42/0.61  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.42/0.61  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.42/0.61  thf(sk_E_type, type, sk_E: $i).
% 0.42/0.61  thf(sk_A_type, type, sk_A: $i).
% 0.42/0.61  thf(sk_D_type, type, sk_D: $i).
% 0.42/0.61  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.42/0.61  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.42/0.61  thf(sk_F_type, type, sk_F: $i).
% 0.42/0.61  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.42/0.61  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.42/0.61  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.42/0.61  thf(sk_C_type, type, sk_C: $i).
% 0.42/0.61  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.42/0.61  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.42/0.61  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.42/0.61  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.42/0.61  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 0.42/0.61  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.42/0.61  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.42/0.61  thf(t6_tmap_1, conjecture,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.42/0.61       ( ![B:$i]:
% 0.42/0.61         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.42/0.61           ( ![C:$i]:
% 0.42/0.61             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.42/0.61                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.61               ( ![D:$i]:
% 0.42/0.61                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.42/0.61                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.61                   ( ( r1_subset_1 @ C @ D ) =>
% 0.42/0.61                     ( ![E:$i]:
% 0.42/0.61                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.42/0.61                           ( m1_subset_1 @
% 0.42/0.61                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.42/0.61                         ( ![F:$i]:
% 0.42/0.61                           ( ( ( v1_funct_1 @ F ) & 
% 0.42/0.61                               ( v1_funct_2 @ F @ D @ B ) & 
% 0.42/0.61                               ( m1_subset_1 @
% 0.42/0.61                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.42/0.61                             ( ( ( k2_partfun1 @
% 0.42/0.61                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.42/0.61                                 ( k2_partfun1 @
% 0.42/0.61                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.42/0.61                               ( ( k2_partfun1 @
% 0.42/0.61                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.42/0.61                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.42/0.61                                 ( E ) ) & 
% 0.42/0.61                               ( ( k2_partfun1 @
% 0.42/0.61                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.42/0.61                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.42/0.61                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.42/0.61  thf(zf_stmt_0, negated_conjecture,
% 0.42/0.61    (~( ![A:$i]:
% 0.42/0.61        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.42/0.61          ( ![B:$i]:
% 0.42/0.61            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.42/0.61              ( ![C:$i]:
% 0.42/0.61                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.42/0.61                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.61                  ( ![D:$i]:
% 0.42/0.61                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.42/0.61                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.61                      ( ( r1_subset_1 @ C @ D ) =>
% 0.42/0.61                        ( ![E:$i]:
% 0.42/0.61                          ( ( ( v1_funct_1 @ E ) & 
% 0.42/0.61                              ( v1_funct_2 @ E @ C @ B ) & 
% 0.42/0.61                              ( m1_subset_1 @
% 0.42/0.61                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.42/0.61                            ( ![F:$i]:
% 0.42/0.61                              ( ( ( v1_funct_1 @ F ) & 
% 0.42/0.61                                  ( v1_funct_2 @ F @ D @ B ) & 
% 0.42/0.61                                  ( m1_subset_1 @
% 0.42/0.61                                    F @ 
% 0.42/0.61                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.42/0.61                                ( ( ( k2_partfun1 @
% 0.42/0.61                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.42/0.61                                    ( k2_partfun1 @
% 0.42/0.61                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.42/0.61                                  ( ( k2_partfun1 @
% 0.42/0.61                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.42/0.61                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.42/0.61                                    ( E ) ) & 
% 0.42/0.61                                  ( ( k2_partfun1 @
% 0.42/0.61                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.42/0.61                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.42/0.61                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.42/0.61    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 0.42/0.61  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(fc16_relat_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( ( v1_relat_1 @ A ) & ( v1_xboole_0 @ B ) ) =>
% 0.42/0.61       ( ( v1_xboole_0 @ ( k7_relat_1 @ A @ B ) ) & 
% 0.42/0.61         ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) ))).
% 0.42/0.61  thf('1', plain,
% 0.42/0.61      (![X9 : $i, X10 : $i]:
% 0.42/0.61         (~ (v1_relat_1 @ X9)
% 0.42/0.61          | ~ (v1_xboole_0 @ X10)
% 0.42/0.61          | (v1_xboole_0 @ (k7_relat_1 @ X9 @ X10)))),
% 0.42/0.61      inference('cnf', [status(esa)], [fc16_relat_1])).
% 0.42/0.61  thf(l13_xboole_0, axiom,
% 0.42/0.61    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.42/0.61  thf('2', plain,
% 0.42/0.61      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.42/0.61      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.42/0.61  thf('3', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (~ (v1_xboole_0 @ X0)
% 0.42/0.61          | ~ (v1_relat_1 @ X1)
% 0.42/0.61          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.61  thf('4', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (~ (v1_xboole_0 @ X0)
% 0.42/0.61          | ~ (v1_relat_1 @ X1)
% 0.42/0.61          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.61  thf('5', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('6', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('7', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(dt_k1_tmap_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.42/0.61     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.42/0.61         ( ~( v1_xboole_0 @ C ) ) & 
% 0.42/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 0.42/0.61         ( ~( v1_xboole_0 @ D ) ) & 
% 0.42/0.61         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 0.42/0.61         ( v1_funct_2 @ E @ C @ B ) & 
% 0.42/0.61         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.42/0.61         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.42/0.61         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.42/0.61       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.42/0.61         ( v1_funct_2 @
% 0.42/0.61           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.42/0.61           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.42/0.61         ( m1_subset_1 @
% 0.42/0.61           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.42/0.61           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 0.42/0.61  thf('8', plain,
% 0.42/0.61      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.42/0.61          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 0.42/0.61          | ~ (v1_funct_1 @ X35)
% 0.42/0.61          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 0.42/0.61          | (v1_xboole_0 @ X38)
% 0.42/0.61          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X39))
% 0.42/0.61          | (v1_xboole_0 @ X36)
% 0.42/0.61          | (v1_xboole_0 @ X37)
% 0.42/0.61          | (v1_xboole_0 @ X39)
% 0.42/0.61          | ~ (v1_funct_1 @ X40)
% 0.42/0.61          | ~ (v1_funct_2 @ X40 @ X38 @ X37)
% 0.42/0.61          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 0.42/0.61          | (v1_funct_1 @ (k1_tmap_1 @ X39 @ X37 @ X36 @ X38 @ X35 @ X40)))),
% 0.42/0.61      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.42/0.61  thf('9', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.61         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.42/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.42/0.61          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.42/0.61          | ~ (v1_funct_1 @ X0)
% 0.42/0.61          | (v1_xboole_0 @ X2)
% 0.42/0.61          | (v1_xboole_0 @ sk_B)
% 0.42/0.61          | (v1_xboole_0 @ sk_C)
% 0.42/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.42/0.61          | (v1_xboole_0 @ X1)
% 0.42/0.61          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.42/0.61          | ~ (v1_funct_1 @ sk_E)
% 0.42/0.61          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.42/0.61      inference('sup-', [status(thm)], ['7', '8'])).
% 0.42/0.61  thf('10', plain, ((v1_funct_1 @ sk_E)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('11', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('12', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.61         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C @ X1 @ sk_E @ X0))
% 0.42/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.42/0.61          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.42/0.61          | ~ (v1_funct_1 @ X0)
% 0.42/0.61          | (v1_xboole_0 @ X2)
% 0.42/0.61          | (v1_xboole_0 @ sk_B)
% 0.42/0.61          | (v1_xboole_0 @ sk_C)
% 0.42/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.42/0.61          | (v1_xboole_0 @ X1)
% 0.42/0.61          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.42/0.61      inference('demod', [status(thm)], ['9', '10', '11'])).
% 0.42/0.61  thf('13', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.42/0.61          | (v1_xboole_0 @ sk_D)
% 0.42/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.42/0.61          | (v1_xboole_0 @ sk_C)
% 0.42/0.61          | (v1_xboole_0 @ sk_B)
% 0.42/0.61          | (v1_xboole_0 @ X0)
% 0.42/0.61          | ~ (v1_funct_1 @ sk_F)
% 0.42/0.61          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.42/0.61          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['6', '12'])).
% 0.42/0.61  thf('14', plain, ((v1_funct_1 @ sk_F)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('15', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('16', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.42/0.61          | (v1_xboole_0 @ sk_D)
% 0.42/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.42/0.61          | (v1_xboole_0 @ sk_C)
% 0.42/0.61          | (v1_xboole_0 @ sk_B)
% 0.42/0.61          | (v1_xboole_0 @ X0)
% 0.42/0.61          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.42/0.61      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.42/0.61  thf('17', plain,
% 0.42/0.61      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('sup-', [status(thm)], ['5', '16'])).
% 0.42/0.61  thf('18', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('19', plain,
% 0.42/0.61      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('demod', [status(thm)], ['17', '18'])).
% 0.42/0.61  thf('20', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('21', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('22', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('23', plain,
% 0.42/0.61      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.42/0.61          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 0.42/0.61          | ~ (v1_funct_1 @ X35)
% 0.42/0.61          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 0.42/0.61          | (v1_xboole_0 @ X38)
% 0.42/0.61          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X39))
% 0.42/0.61          | (v1_xboole_0 @ X36)
% 0.42/0.61          | (v1_xboole_0 @ X37)
% 0.42/0.61          | (v1_xboole_0 @ X39)
% 0.42/0.61          | ~ (v1_funct_1 @ X40)
% 0.42/0.61          | ~ (v1_funct_2 @ X40 @ X38 @ X37)
% 0.42/0.61          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 0.42/0.61          | (v1_funct_2 @ (k1_tmap_1 @ X39 @ X37 @ X36 @ X38 @ X35 @ X40) @ 
% 0.42/0.61             (k4_subset_1 @ X39 @ X36 @ X38) @ X37))),
% 0.42/0.61      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.42/0.61  thf('24', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.61         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.42/0.61           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.42/0.61          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.42/0.61          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.42/0.61          | ~ (v1_funct_1 @ X2)
% 0.42/0.61          | (v1_xboole_0 @ X1)
% 0.42/0.61          | (v1_xboole_0 @ sk_B)
% 0.42/0.61          | (v1_xboole_0 @ sk_C)
% 0.42/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.42/0.61          | (v1_xboole_0 @ X0)
% 0.42/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.42/0.61          | ~ (v1_funct_1 @ sk_E)
% 0.42/0.61          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.42/0.61      inference('sup-', [status(thm)], ['22', '23'])).
% 0.42/0.61  thf('25', plain, ((v1_funct_1 @ sk_E)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('26', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('27', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.61         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.42/0.61           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)
% 0.42/0.61          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.42/0.61          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.42/0.61          | ~ (v1_funct_1 @ X2)
% 0.42/0.61          | (v1_xboole_0 @ X1)
% 0.42/0.61          | (v1_xboole_0 @ sk_B)
% 0.42/0.61          | (v1_xboole_0 @ sk_C)
% 0.42/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.42/0.61          | (v1_xboole_0 @ X0)
% 0.42/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.42/0.61      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.42/0.61  thf('28', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.42/0.61          | (v1_xboole_0 @ sk_D)
% 0.42/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.42/0.61          | (v1_xboole_0 @ sk_C)
% 0.42/0.61          | (v1_xboole_0 @ sk_B)
% 0.42/0.61          | (v1_xboole_0 @ X0)
% 0.42/0.61          | ~ (v1_funct_1 @ sk_F)
% 0.42/0.61          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.42/0.61          | (v1_funct_2 @ 
% 0.42/0.61             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 0.42/0.61      inference('sup-', [status(thm)], ['21', '27'])).
% 0.42/0.61  thf('29', plain, ((v1_funct_1 @ sk_F)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('30', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('31', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.42/0.61          | (v1_xboole_0 @ sk_D)
% 0.42/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.42/0.61          | (v1_xboole_0 @ sk_C)
% 0.42/0.61          | (v1_xboole_0 @ sk_B)
% 0.42/0.61          | (v1_xboole_0 @ X0)
% 0.42/0.61          | (v1_funct_2 @ 
% 0.42/0.61             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))),
% 0.42/0.61      inference('demod', [status(thm)], ['28', '29', '30'])).
% 0.42/0.61  thf('32', plain,
% 0.42/0.61      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('sup-', [status(thm)], ['20', '31'])).
% 0.42/0.61  thf('33', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('34', plain,
% 0.42/0.61      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('demod', [status(thm)], ['32', '33'])).
% 0.42/0.61  thf('35', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('36', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('37', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('38', plain,
% 0.42/0.61      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i, X39 : $i, X40 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.42/0.61          | ~ (v1_funct_2 @ X35 @ X36 @ X37)
% 0.42/0.61          | ~ (v1_funct_1 @ X35)
% 0.42/0.61          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 0.42/0.61          | (v1_xboole_0 @ X38)
% 0.42/0.61          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ X39))
% 0.42/0.61          | (v1_xboole_0 @ X36)
% 0.42/0.61          | (v1_xboole_0 @ X37)
% 0.42/0.61          | (v1_xboole_0 @ X39)
% 0.42/0.61          | ~ (v1_funct_1 @ X40)
% 0.42/0.61          | ~ (v1_funct_2 @ X40 @ X38 @ X37)
% 0.42/0.61          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 0.42/0.61          | (m1_subset_1 @ (k1_tmap_1 @ X39 @ X37 @ X36 @ X38 @ X35 @ X40) @ 
% 0.42/0.61             (k1_zfmisc_1 @ 
% 0.42/0.61              (k2_zfmisc_1 @ (k4_subset_1 @ X39 @ X36 @ X38) @ X37))))),
% 0.42/0.61      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.42/0.61  thf('39', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.61         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.42/0.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 0.42/0.61          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.42/0.61          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.42/0.61          | ~ (v1_funct_1 @ X2)
% 0.42/0.61          | (v1_xboole_0 @ X1)
% 0.42/0.61          | (v1_xboole_0 @ sk_B)
% 0.42/0.61          | (v1_xboole_0 @ sk_C)
% 0.42/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.42/0.61          | (v1_xboole_0 @ X0)
% 0.42/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.42/0.61          | ~ (v1_funct_1 @ sk_E)
% 0.42/0.61          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B))),
% 0.42/0.61      inference('sup-', [status(thm)], ['37', '38'])).
% 0.42/0.61  thf('40', plain, ((v1_funct_1 @ sk_E)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('41', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('42', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.42/0.61         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.42/0.61           (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B)))
% 0.42/0.61          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.42/0.61          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.42/0.61          | ~ (v1_funct_1 @ X2)
% 0.42/0.61          | (v1_xboole_0 @ X1)
% 0.42/0.61          | (v1_xboole_0 @ sk_B)
% 0.42/0.61          | (v1_xboole_0 @ sk_C)
% 0.42/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.42/0.61          | (v1_xboole_0 @ X0)
% 0.42/0.61          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.42/0.61      inference('demod', [status(thm)], ['39', '40', '41'])).
% 0.42/0.61  thf('43', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.42/0.61          | (v1_xboole_0 @ sk_D)
% 0.42/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.42/0.61          | (v1_xboole_0 @ sk_C)
% 0.42/0.61          | (v1_xboole_0 @ sk_B)
% 0.42/0.61          | (v1_xboole_0 @ X0)
% 0.42/0.61          | ~ (v1_funct_1 @ sk_F)
% 0.42/0.61          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.42/0.61          | (m1_subset_1 @ 
% 0.42/0.61             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61             (k1_zfmisc_1 @ 
% 0.42/0.61              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['36', '42'])).
% 0.42/0.61  thf('44', plain, ((v1_funct_1 @ sk_F)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('45', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('46', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.42/0.61          | (v1_xboole_0 @ sk_D)
% 0.42/0.61          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.42/0.61          | (v1_xboole_0 @ sk_C)
% 0.42/0.61          | (v1_xboole_0 @ sk_B)
% 0.42/0.61          | (v1_xboole_0 @ X0)
% 0.42/0.61          | (m1_subset_1 @ 
% 0.42/0.61             (k1_tmap_1 @ X0 @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61             (k1_zfmisc_1 @ 
% 0.42/0.61              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B))))),
% 0.42/0.61      inference('demod', [status(thm)], ['43', '44', '45'])).
% 0.42/0.61  thf('47', plain,
% 0.42/0.61      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61         (k1_zfmisc_1 @ 
% 0.42/0.61          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('sup-', [status(thm)], ['35', '46'])).
% 0.42/0.61  thf('48', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('49', plain,
% 0.42/0.61      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61         (k1_zfmisc_1 @ 
% 0.42/0.61          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('demod', [status(thm)], ['47', '48'])).
% 0.42/0.61  thf(d1_tmap_1, axiom,
% 0.42/0.61    (![A:$i]:
% 0.42/0.61     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.42/0.61       ( ![B:$i]:
% 0.42/0.61         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.42/0.61           ( ![C:$i]:
% 0.42/0.61             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.42/0.61                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.61               ( ![D:$i]:
% 0.42/0.61                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.42/0.61                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.42/0.61                   ( ![E:$i]:
% 0.42/0.61                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.42/0.61                         ( m1_subset_1 @
% 0.42/0.61                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.42/0.61                       ( ![F:$i]:
% 0.42/0.61                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.42/0.61                             ( m1_subset_1 @
% 0.42/0.61                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.42/0.61                           ( ( ( k2_partfun1 @
% 0.42/0.61                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.42/0.61                               ( k2_partfun1 @
% 0.42/0.61                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 0.42/0.61                             ( ![G:$i]:
% 0.42/0.61                               ( ( ( v1_funct_1 @ G ) & 
% 0.42/0.61                                   ( v1_funct_2 @
% 0.42/0.61                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.42/0.61                                   ( m1_subset_1 @
% 0.42/0.61                                     G @ 
% 0.42/0.61                                     ( k1_zfmisc_1 @
% 0.42/0.61                                       ( k2_zfmisc_1 @
% 0.42/0.61                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 0.42/0.61                                 ( ( ( G ) =
% 0.42/0.61                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.42/0.61                                   ( ( ( k2_partfun1 @
% 0.42/0.61                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.42/0.61                                         C ) =
% 0.42/0.61                                       ( E ) ) & 
% 0.42/0.61                                     ( ( k2_partfun1 @
% 0.42/0.61                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.42/0.61                                         D ) =
% 0.42/0.61                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.42/0.61  thf('50', plain,
% 0.42/0.61      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.42/0.61         ((v1_xboole_0 @ X28)
% 0.42/0.61          | (v1_xboole_0 @ X29)
% 0.42/0.61          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 0.42/0.61          | ~ (v1_funct_1 @ X31)
% 0.42/0.61          | ~ (v1_funct_2 @ X31 @ X29 @ X28)
% 0.42/0.61          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.42/0.61          | ((X34) != (k1_tmap_1 @ X30 @ X28 @ X33 @ X29 @ X32 @ X31))
% 0.42/0.61          | ((k2_partfun1 @ (k4_subset_1 @ X30 @ X33 @ X29) @ X28 @ X34 @ X33)
% 0.42/0.61              = (X32))
% 0.42/0.61          | ~ (m1_subset_1 @ X34 @ 
% 0.42/0.61               (k1_zfmisc_1 @ 
% 0.42/0.61                (k2_zfmisc_1 @ (k4_subset_1 @ X30 @ X33 @ X29) @ X28)))
% 0.42/0.61          | ~ (v1_funct_2 @ X34 @ (k4_subset_1 @ X30 @ X33 @ X29) @ X28)
% 0.42/0.61          | ~ (v1_funct_1 @ X34)
% 0.42/0.61          | ((k2_partfun1 @ X33 @ X28 @ X32 @ (k9_subset_1 @ X30 @ X33 @ X29))
% 0.42/0.61              != (k2_partfun1 @ X29 @ X28 @ X31 @ 
% 0.42/0.61                  (k9_subset_1 @ X30 @ X33 @ X29)))
% 0.42/0.61          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X28)))
% 0.42/0.61          | ~ (v1_funct_2 @ X32 @ X33 @ X28)
% 0.42/0.61          | ~ (v1_funct_1 @ X32)
% 0.42/0.61          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X30))
% 0.42/0.61          | (v1_xboole_0 @ X33)
% 0.42/0.61          | (v1_xboole_0 @ X30))),
% 0.42/0.61      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.42/0.61  thf('51', plain,
% 0.42/0.61      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.42/0.61         ((v1_xboole_0 @ X30)
% 0.42/0.61          | (v1_xboole_0 @ X33)
% 0.42/0.61          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X30))
% 0.42/0.61          | ~ (v1_funct_1 @ X32)
% 0.42/0.61          | ~ (v1_funct_2 @ X32 @ X33 @ X28)
% 0.42/0.61          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X28)))
% 0.42/0.61          | ((k2_partfun1 @ X33 @ X28 @ X32 @ (k9_subset_1 @ X30 @ X33 @ X29))
% 0.42/0.61              != (k2_partfun1 @ X29 @ X28 @ X31 @ 
% 0.42/0.61                  (k9_subset_1 @ X30 @ X33 @ X29)))
% 0.42/0.61          | ~ (v1_funct_1 @ (k1_tmap_1 @ X30 @ X28 @ X33 @ X29 @ X32 @ X31))
% 0.42/0.61          | ~ (v1_funct_2 @ (k1_tmap_1 @ X30 @ X28 @ X33 @ X29 @ X32 @ X31) @ 
% 0.42/0.61               (k4_subset_1 @ X30 @ X33 @ X29) @ X28)
% 0.42/0.61          | ~ (m1_subset_1 @ (k1_tmap_1 @ X30 @ X28 @ X33 @ X29 @ X32 @ X31) @ 
% 0.42/0.61               (k1_zfmisc_1 @ 
% 0.42/0.61                (k2_zfmisc_1 @ (k4_subset_1 @ X30 @ X33 @ X29) @ X28)))
% 0.42/0.61          | ((k2_partfun1 @ (k4_subset_1 @ X30 @ X33 @ X29) @ X28 @ 
% 0.42/0.61              (k1_tmap_1 @ X30 @ X28 @ X33 @ X29 @ X32 @ X31) @ X33) = (
% 0.42/0.61              X32))
% 0.42/0.61          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.42/0.61          | ~ (v1_funct_2 @ X31 @ X29 @ X28)
% 0.42/0.61          | ~ (v1_funct_1 @ X31)
% 0.42/0.61          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 0.42/0.61          | (v1_xboole_0 @ X29)
% 0.42/0.61          | (v1_xboole_0 @ X28))),
% 0.42/0.61      inference('simplify', [status(thm)], ['50'])).
% 0.42/0.61  thf('52', plain,
% 0.42/0.61      (((v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_D)
% 0.42/0.61        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.42/0.61        | ~ (v1_funct_1 @ sk_F)
% 0.42/0.61        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.42/0.61        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.42/0.61            = (sk_E))
% 0.42/0.61        | ~ (v1_funct_2 @ 
% 0.42/0.61             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.42/0.61        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.42/0.61        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.42/0.61            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.42/0.61        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 0.42/0.61        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.42/0.61        | ~ (v1_funct_1 @ sk_E)
% 0.42/0.61        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['49', '51'])).
% 0.42/0.61  thf('53', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('54', plain, ((v1_funct_1 @ sk_F)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('55', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('56', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('57', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(redefinition_k9_subset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.42/0.61       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.42/0.61  thf('58', plain,
% 0.42/0.61      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.42/0.61         (((k9_subset_1 @ X6 @ X4 @ X5) = (k3_xboole_0 @ X4 @ X5))
% 0.42/0.61          | ~ (m1_subset_1 @ X5 @ (k1_zfmisc_1 @ X6)))),
% 0.42/0.61      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.42/0.61  thf('59', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.42/0.61      inference('sup-', [status(thm)], ['57', '58'])).
% 0.42/0.61  thf('60', plain, ((r1_subset_1 @ sk_C @ sk_D)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(redefinition_r1_subset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.42/0.61       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 0.42/0.61  thf('61', plain,
% 0.42/0.61      (![X16 : $i, X17 : $i]:
% 0.42/0.61         ((v1_xboole_0 @ X16)
% 0.42/0.61          | (v1_xboole_0 @ X17)
% 0.42/0.61          | (r1_xboole_0 @ X16 @ X17)
% 0.42/0.61          | ~ (r1_subset_1 @ X16 @ X17))),
% 0.42/0.61      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 0.42/0.61  thf('62', plain,
% 0.42/0.61      (((r1_xboole_0 @ sk_C @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C))),
% 0.42/0.61      inference('sup-', [status(thm)], ['60', '61'])).
% 0.42/0.61  thf('63', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('64', plain, (((v1_xboole_0 @ sk_C) | (r1_xboole_0 @ sk_C @ sk_D))),
% 0.42/0.61      inference('clc', [status(thm)], ['62', '63'])).
% 0.42/0.61  thf('65', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('66', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 0.42/0.61      inference('clc', [status(thm)], ['64', '65'])).
% 0.42/0.61  thf(d7_xboole_0, axiom,
% 0.42/0.61    (![A:$i,B:$i]:
% 0.42/0.61     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.42/0.61       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.42/0.61  thf('67', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.42/0.61      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.42/0.61  thf('68', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['66', '67'])).
% 0.42/0.61  thf('69', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(redefinition_k2_partfun1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i,D:$i]:
% 0.42/0.61     ( ( ( v1_funct_1 @ C ) & 
% 0.42/0.61         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.42/0.61       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.42/0.61  thf('70', plain,
% 0.42/0.61      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.42/0.61          | ~ (v1_funct_1 @ X24)
% 0.42/0.61          | ((k2_partfun1 @ X25 @ X26 @ X24 @ X27) = (k7_relat_1 @ X24 @ X27)))),
% 0.42/0.61      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.42/0.61  thf('71', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 0.42/0.61          | ~ (v1_funct_1 @ sk_E))),
% 0.42/0.61      inference('sup-', [status(thm)], ['69', '70'])).
% 0.42/0.61  thf('72', plain, ((v1_funct_1 @ sk_E)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('73', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.42/0.61      inference('demod', [status(thm)], ['71', '72'])).
% 0.42/0.61  thf('74', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.42/0.61      inference('sup-', [status(thm)], ['57', '58'])).
% 0.42/0.61  thf('75', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['66', '67'])).
% 0.42/0.61  thf('76', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('77', plain,
% 0.42/0.61      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.42/0.61         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.42/0.61          | ~ (v1_funct_1 @ X24)
% 0.42/0.61          | ((k2_partfun1 @ X25 @ X26 @ X24 @ X27) = (k7_relat_1 @ X24 @ X27)))),
% 0.42/0.61      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.42/0.61  thf('78', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         (((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 0.42/0.61          | ~ (v1_funct_1 @ sk_F))),
% 0.42/0.61      inference('sup-', [status(thm)], ['76', '77'])).
% 0.42/0.61  thf('79', plain, ((v1_funct_1 @ sk_F)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('80', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.42/0.61      inference('demod', [status(thm)], ['78', '79'])).
% 0.42/0.61  thf('81', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('82', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('83', plain, ((v1_funct_1 @ sk_E)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('84', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('85', plain,
% 0.42/0.61      (((v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_D)
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.42/0.61            = (sk_E))
% 0.42/0.61        | ~ (v1_funct_2 @ 
% 0.42/0.61             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.42/0.61        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.42/0.61        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.42/0.61            != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_A))),
% 0.42/0.61      inference('demod', [status(thm)],
% 0.42/0.61                ['52', '53', '54', '55', '56', '59', '68', '73', '74', '75', 
% 0.42/0.61                 '80', '81', '82', '83', '84'])).
% 0.42/0.61  thf('86', plain,
% 0.42/0.61      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.42/0.61        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.42/0.61        | ~ (v1_funct_2 @ 
% 0.42/0.61             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.42/0.61            = (sk_E))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('simplify', [status(thm)], ['85'])).
% 0.42/0.61  thf('87', plain,
% 0.42/0.61      (((v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.42/0.61            = (sk_E))
% 0.42/0.61        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.42/0.61        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.42/0.61            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['34', '86'])).
% 0.42/0.61  thf('88', plain,
% 0.42/0.61      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.42/0.61        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.42/0.61            = (sk_E))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('simplify', [status(thm)], ['87'])).
% 0.42/0.61  thf('89', plain,
% 0.42/0.61      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61              (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.42/0.61            != (sk_E))
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61            != (sk_F)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('90', plain,
% 0.42/0.61      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.42/0.61          != (sk_E)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.42/0.61                = (sk_E))))),
% 0.42/0.61      inference('split', [status(esa)], ['89'])).
% 0.42/0.61  thf('91', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (~ (v1_xboole_0 @ X0)
% 0.42/0.61          | ~ (v1_relat_1 @ X1)
% 0.42/0.61          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.61  thf('92', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (~ (v1_xboole_0 @ X0)
% 0.42/0.61          | ~ (v1_relat_1 @ X1)
% 0.42/0.61          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.61  thf('93', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.42/0.61      inference('demod', [status(thm)], ['78', '79'])).
% 0.42/0.61  thf('94', plain,
% 0.42/0.61      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61              (k9_subset_1 @ sk_A @ sk_C @ sk_D))))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.42/0.61                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.42/0.61      inference('split', [status(esa)], ['89'])).
% 0.42/0.61  thf('95', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.42/0.61      inference('sup-', [status(thm)], ['57', '58'])).
% 0.42/0.61  thf('96', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.42/0.61      inference('sup-', [status(thm)], ['57', '58'])).
% 0.42/0.61  thf('97', plain,
% 0.42/0.61      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 0.42/0.61          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.42/0.61                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.42/0.61      inference('demod', [status(thm)], ['94', '95', '96'])).
% 0.42/0.61  thf('98', plain,
% 0.42/0.61      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C @ sk_D))
% 0.42/0.61          != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.42/0.61                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['93', '97'])).
% 0.42/0.61  thf('99', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['66', '67'])).
% 0.42/0.61  thf('100', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.42/0.61      inference('demod', [status(thm)], ['71', '72'])).
% 0.42/0.61  thf('101', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['66', '67'])).
% 0.42/0.61  thf('102', plain,
% 0.42/0.61      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.42/0.61                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.42/0.61      inference('demod', [status(thm)], ['98', '99', '100', '101'])).
% 0.42/0.61  thf('103', plain,
% 0.42/0.61      (((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.42/0.61         | ~ (v1_relat_1 @ sk_F)
% 0.42/0.61         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.42/0.61                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['92', '102'])).
% 0.42/0.61  thf('104', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf(cc1_relset_1, axiom,
% 0.42/0.61    (![A:$i,B:$i,C:$i]:
% 0.42/0.61     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.42/0.61       ( v1_relat_1 @ C ) ))).
% 0.42/0.61  thf('105', plain,
% 0.42/0.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.42/0.61         ((v1_relat_1 @ X18)
% 0.42/0.61          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.42/0.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.42/0.61  thf('106', plain, ((v1_relat_1 @ sk_F)),
% 0.42/0.61      inference('sup-', [status(thm)], ['104', '105'])).
% 0.42/0.61  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.42/0.61  thf('107', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.42/0.61  thf('108', plain,
% 0.42/0.61      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.42/0.61                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.42/0.61      inference('demod', [status(thm)], ['103', '106', '107'])).
% 0.42/0.61  thf('109', plain,
% 0.42/0.61      (((((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.61         | ~ (v1_relat_1 @ sk_E)
% 0.42/0.61         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.42/0.61                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['91', '108'])).
% 0.42/0.61  thf('110', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('111', plain,
% 0.42/0.61      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.42/0.61         ((v1_relat_1 @ X18)
% 0.42/0.61          | ~ (m1_subset_1 @ X18 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X19 @ X20))))),
% 0.42/0.61      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.42/0.61  thf('112', plain, ((v1_relat_1 @ sk_E)),
% 0.42/0.61      inference('sup-', [status(thm)], ['110', '111'])).
% 0.42/0.61  thf('113', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.42/0.61  thf('114', plain,
% 0.42/0.61      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.42/0.61                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.42/0.61      inference('demod', [status(thm)], ['109', '112', '113'])).
% 0.42/0.61  thf('115', plain,
% 0.42/0.61      ((((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.42/0.61      inference('simplify', [status(thm)], ['114'])).
% 0.42/0.61  thf('116', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (~ (v1_xboole_0 @ X0)
% 0.42/0.61          | ~ (v1_relat_1 @ X1)
% 0.42/0.61          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.61  thf('117', plain,
% 0.42/0.61      (![X0 : $i, X1 : $i]:
% 0.42/0.61         (~ (v1_xboole_0 @ X0)
% 0.42/0.61          | ~ (v1_relat_1 @ X1)
% 0.42/0.61          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['1', '2'])).
% 0.42/0.61  thf('118', plain,
% 0.42/0.61      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('demod', [status(thm)], ['17', '18'])).
% 0.42/0.61  thf('119', plain,
% 0.42/0.61      (((v1_funct_2 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('demod', [status(thm)], ['32', '33'])).
% 0.42/0.61  thf('120', plain,
% 0.42/0.61      (((m1_subset_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61         (k1_zfmisc_1 @ 
% 0.42/0.61          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('demod', [status(thm)], ['47', '48'])).
% 0.42/0.61  thf('121', plain,
% 0.42/0.61      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.42/0.61         ((v1_xboole_0 @ X28)
% 0.42/0.61          | (v1_xboole_0 @ X29)
% 0.42/0.61          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 0.42/0.61          | ~ (v1_funct_1 @ X31)
% 0.42/0.61          | ~ (v1_funct_2 @ X31 @ X29 @ X28)
% 0.42/0.61          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.42/0.61          | ((X34) != (k1_tmap_1 @ X30 @ X28 @ X33 @ X29 @ X32 @ X31))
% 0.42/0.61          | ((k2_partfun1 @ (k4_subset_1 @ X30 @ X33 @ X29) @ X28 @ X34 @ X29)
% 0.42/0.61              = (X31))
% 0.42/0.61          | ~ (m1_subset_1 @ X34 @ 
% 0.42/0.61               (k1_zfmisc_1 @ 
% 0.42/0.61                (k2_zfmisc_1 @ (k4_subset_1 @ X30 @ X33 @ X29) @ X28)))
% 0.42/0.61          | ~ (v1_funct_2 @ X34 @ (k4_subset_1 @ X30 @ X33 @ X29) @ X28)
% 0.42/0.61          | ~ (v1_funct_1 @ X34)
% 0.42/0.61          | ((k2_partfun1 @ X33 @ X28 @ X32 @ (k9_subset_1 @ X30 @ X33 @ X29))
% 0.42/0.61              != (k2_partfun1 @ X29 @ X28 @ X31 @ 
% 0.42/0.61                  (k9_subset_1 @ X30 @ X33 @ X29)))
% 0.42/0.61          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X28)))
% 0.42/0.61          | ~ (v1_funct_2 @ X32 @ X33 @ X28)
% 0.42/0.61          | ~ (v1_funct_1 @ X32)
% 0.42/0.61          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X30))
% 0.42/0.61          | (v1_xboole_0 @ X33)
% 0.42/0.61          | (v1_xboole_0 @ X30))),
% 0.42/0.61      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.42/0.61  thf('122', plain,
% 0.42/0.61      (![X28 : $i, X29 : $i, X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.42/0.61         ((v1_xboole_0 @ X30)
% 0.42/0.61          | (v1_xboole_0 @ X33)
% 0.42/0.61          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X30))
% 0.42/0.61          | ~ (v1_funct_1 @ X32)
% 0.42/0.61          | ~ (v1_funct_2 @ X32 @ X33 @ X28)
% 0.42/0.61          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X28)))
% 0.42/0.61          | ((k2_partfun1 @ X33 @ X28 @ X32 @ (k9_subset_1 @ X30 @ X33 @ X29))
% 0.42/0.61              != (k2_partfun1 @ X29 @ X28 @ X31 @ 
% 0.42/0.61                  (k9_subset_1 @ X30 @ X33 @ X29)))
% 0.42/0.61          | ~ (v1_funct_1 @ (k1_tmap_1 @ X30 @ X28 @ X33 @ X29 @ X32 @ X31))
% 0.42/0.61          | ~ (v1_funct_2 @ (k1_tmap_1 @ X30 @ X28 @ X33 @ X29 @ X32 @ X31) @ 
% 0.42/0.61               (k4_subset_1 @ X30 @ X33 @ X29) @ X28)
% 0.42/0.61          | ~ (m1_subset_1 @ (k1_tmap_1 @ X30 @ X28 @ X33 @ X29 @ X32 @ X31) @ 
% 0.42/0.61               (k1_zfmisc_1 @ 
% 0.42/0.61                (k2_zfmisc_1 @ (k4_subset_1 @ X30 @ X33 @ X29) @ X28)))
% 0.42/0.61          | ((k2_partfun1 @ (k4_subset_1 @ X30 @ X33 @ X29) @ X28 @ 
% 0.42/0.61              (k1_tmap_1 @ X30 @ X28 @ X33 @ X29 @ X32 @ X31) @ X29) = (
% 0.42/0.61              X31))
% 0.42/0.61          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28)))
% 0.42/0.61          | ~ (v1_funct_2 @ X31 @ X29 @ X28)
% 0.42/0.61          | ~ (v1_funct_1 @ X31)
% 0.42/0.61          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X30))
% 0.42/0.61          | (v1_xboole_0 @ X29)
% 0.42/0.61          | (v1_xboole_0 @ X28))),
% 0.42/0.61      inference('simplify', [status(thm)], ['121'])).
% 0.42/0.61  thf('123', plain,
% 0.42/0.61      (((v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_D)
% 0.42/0.61        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.42/0.61        | ~ (v1_funct_1 @ sk_F)
% 0.42/0.61        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.42/0.61        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61            = (sk_F))
% 0.42/0.61        | ~ (v1_funct_2 @ 
% 0.42/0.61             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.42/0.61        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.42/0.61        | ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ 
% 0.42/0.61            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.42/0.61        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))
% 0.42/0.61        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B)
% 0.42/0.61        | ~ (v1_funct_1 @ sk_E)
% 0.42/0.61        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['120', '122'])).
% 0.42/0.61  thf('124', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('125', plain, ((v1_funct_1 @ sk_F)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('126', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('127', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('128', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.42/0.61      inference('sup-', [status(thm)], ['57', '58'])).
% 0.42/0.61  thf('129', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['66', '67'])).
% 0.42/0.61  thf('130', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k2_partfun1 @ sk_C @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.42/0.61      inference('demod', [status(thm)], ['71', '72'])).
% 0.42/0.61  thf('131', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.42/0.61      inference('sup-', [status(thm)], ['57', '58'])).
% 0.42/0.61  thf('132', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.42/0.61      inference('sup-', [status(thm)], ['66', '67'])).
% 0.42/0.61  thf('133', plain,
% 0.42/0.61      (![X0 : $i]:
% 0.42/0.61         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.42/0.61      inference('demod', [status(thm)], ['78', '79'])).
% 0.42/0.61  thf('134', plain,
% 0.42/0.61      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B)))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('135', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('136', plain, ((v1_funct_1 @ sk_E)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('137', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('138', plain,
% 0.42/0.61      (((v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_D)
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61            = (sk_F))
% 0.42/0.61        | ~ (v1_funct_2 @ 
% 0.42/0.61             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.42/0.61        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.42/0.61        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.42/0.61            != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_A))),
% 0.42/0.61      inference('demod', [status(thm)],
% 0.42/0.61                ['123', '124', '125', '126', '127', '128', '129', '130', 
% 0.42/0.61                 '131', '132', '133', '134', '135', '136', '137'])).
% 0.42/0.61  thf('139', plain,
% 0.42/0.61      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.42/0.61        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.42/0.61        | ~ (v1_funct_2 @ 
% 0.42/0.61             (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.42/0.61             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B)
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61            = (sk_F))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('simplify', [status(thm)], ['138'])).
% 0.42/0.61  thf('140', plain,
% 0.42/0.61      (((v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61            = (sk_F))
% 0.42/0.61        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.42/0.61        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.42/0.61            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['119', '139'])).
% 0.42/0.61  thf('141', plain,
% 0.42/0.61      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.42/0.61        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61            = (sk_F))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('simplify', [status(thm)], ['140'])).
% 0.42/0.61  thf('142', plain,
% 0.42/0.61      (((v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61            = (sk_F))
% 0.42/0.61        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.42/0.61            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['118', '141'])).
% 0.42/0.61  thf('143', plain,
% 0.42/0.61      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61            = (sk_F))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('simplify', [status(thm)], ['142'])).
% 0.42/0.61  thf('144', plain,
% 0.42/0.61      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.42/0.61        | ~ (v1_relat_1 @ sk_F)
% 0.42/0.61        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.42/0.61        | (v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61            = (sk_F)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['117', '143'])).
% 0.42/0.61  thf('145', plain, ((v1_relat_1 @ sk_F)),
% 0.42/0.61      inference('sup-', [status(thm)], ['104', '105'])).
% 0.42/0.61  thf('146', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.42/0.61  thf('147', plain,
% 0.42/0.61      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.42/0.61        | (v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61            = (sk_F)))),
% 0.42/0.61      inference('demod', [status(thm)], ['144', '145', '146'])).
% 0.42/0.61  thf('148', plain,
% 0.42/0.61      ((((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.61        | ~ (v1_relat_1 @ sk_E)
% 0.42/0.61        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61            = (sk_F))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('sup-', [status(thm)], ['116', '147'])).
% 0.42/0.61  thf('149', plain, ((v1_relat_1 @ sk_E)),
% 0.42/0.61      inference('sup-', [status(thm)], ['110', '111'])).
% 0.42/0.61  thf('150', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.42/0.61  thf('151', plain,
% 0.42/0.61      ((((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61            = (sk_F))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('demod', [status(thm)], ['148', '149', '150'])).
% 0.42/0.61  thf('152', plain,
% 0.42/0.61      (((v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61            (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61            = (sk_F)))),
% 0.42/0.61      inference('simplify', [status(thm)], ['151'])).
% 0.42/0.61  thf('153', plain,
% 0.42/0.61      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61          != (sk_F)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61                = (sk_F))))),
% 0.42/0.61      inference('split', [status(esa)], ['89'])).
% 0.42/0.61  thf('154', plain,
% 0.42/0.61      (((((sk_F) != (sk_F))
% 0.42/0.61         | (v1_xboole_0 @ sk_A)
% 0.42/0.61         | (v1_xboole_0 @ sk_B)
% 0.42/0.61         | (v1_xboole_0 @ sk_C)
% 0.42/0.61         | (v1_xboole_0 @ sk_D)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61                = (sk_F))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['152', '153'])).
% 0.42/0.61  thf('155', plain,
% 0.42/0.61      ((((v1_xboole_0 @ sk_D)
% 0.42/0.61         | (v1_xboole_0 @ sk_C)
% 0.42/0.61         | (v1_xboole_0 @ sk_B)
% 0.42/0.61         | (v1_xboole_0 @ sk_A)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61                = (sk_F))))),
% 0.42/0.61      inference('simplify', [status(thm)], ['154'])).
% 0.42/0.61  thf('156', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('157', plain,
% 0.42/0.61      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_C)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61                = (sk_F))))),
% 0.42/0.61      inference('sup-', [status(thm)], ['155', '156'])).
% 0.42/0.61  thf('158', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('159', plain,
% 0.42/0.61      ((((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B)))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61                = (sk_F))))),
% 0.42/0.61      inference('clc', [status(thm)], ['157', '158'])).
% 0.42/0.61  thf('160', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('161', plain,
% 0.42/0.61      (((v1_xboole_0 @ sk_B))
% 0.42/0.61         <= (~
% 0.42/0.61             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61                (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61                = (sk_F))))),
% 0.42/0.61      inference('clc', [status(thm)], ['159', '160'])).
% 0.42/0.61  thf('162', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('163', plain,
% 0.42/0.61      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61          = (sk_F)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['161', '162'])).
% 0.42/0.61  thf('164', plain,
% 0.42/0.61      (~
% 0.42/0.61       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.42/0.61          = (sk_E))) | 
% 0.42/0.61       ~
% 0.42/0.61       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.42/0.61          = (sk_F))) | 
% 0.42/0.61       ~
% 0.42/0.61       (((k2_partfun1 @ sk_C @ sk_B @ sk_E @ (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.42/0.61          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.42/0.61             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.42/0.61      inference('split', [status(esa)], ['89'])).
% 0.42/0.61  thf('165', plain,
% 0.42/0.61      (~
% 0.42/0.61       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61          (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.42/0.61          = (sk_E)))),
% 0.42/0.61      inference('sat_resolution*', [status(thm)], ['115', '163', '164'])).
% 0.42/0.61  thf('166', plain,
% 0.42/0.61      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B @ 
% 0.42/0.61         (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.42/0.61         != (sk_E))),
% 0.42/0.61      inference('simpl_trail', [status(thm)], ['90', '165'])).
% 0.42/0.61  thf('167', plain,
% 0.42/0.61      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.42/0.61        | ~ (v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('simplify_reflect-', [status(thm)], ['88', '166'])).
% 0.42/0.61  thf('168', plain,
% 0.42/0.61      (((v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.42/0.61            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.42/0.61      inference('sup-', [status(thm)], ['19', '167'])).
% 0.42/0.61  thf('169', plain,
% 0.42/0.61      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('simplify', [status(thm)], ['168'])).
% 0.42/0.61  thf('170', plain,
% 0.42/0.61      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.42/0.61        | ~ (v1_relat_1 @ sk_F)
% 0.42/0.61        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.42/0.61        | (v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A))),
% 0.42/0.61      inference('sup-', [status(thm)], ['4', '169'])).
% 0.42/0.61  thf('171', plain, ((v1_relat_1 @ sk_F)),
% 0.42/0.61      inference('sup-', [status(thm)], ['104', '105'])).
% 0.42/0.61  thf('172', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.42/0.61  thf('173', plain,
% 0.42/0.61      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.42/0.61        | (v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A))),
% 0.42/0.61      inference('demod', [status(thm)], ['170', '171', '172'])).
% 0.42/0.61  thf('174', plain,
% 0.42/0.61      ((((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.61        | ~ (v1_relat_1 @ sk_E)
% 0.42/0.61        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('sup-', [status(thm)], ['3', '173'])).
% 0.42/0.61  thf('175', plain, ((v1_relat_1 @ sk_E)),
% 0.42/0.61      inference('sup-', [status(thm)], ['110', '111'])).
% 0.42/0.61  thf('176', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.42/0.61      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.42/0.61  thf('177', plain,
% 0.42/0.61      ((((k1_xboole_0) != (k1_xboole_0))
% 0.42/0.61        | (v1_xboole_0 @ sk_A)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_D))),
% 0.42/0.61      inference('demod', [status(thm)], ['174', '175', '176'])).
% 0.42/0.61  thf('178', plain,
% 0.42/0.61      (((v1_xboole_0 @ sk_D)
% 0.42/0.61        | (v1_xboole_0 @ sk_C)
% 0.42/0.61        | (v1_xboole_0 @ sk_B)
% 0.42/0.61        | (v1_xboole_0 @ sk_A))),
% 0.42/0.61      inference('simplify', [status(thm)], ['177'])).
% 0.42/0.61  thf('179', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('180', plain,
% 0.42/0.61      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_C))),
% 0.42/0.61      inference('sup-', [status(thm)], ['178', '179'])).
% 0.42/0.61  thf('181', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('182', plain, (((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B))),
% 0.42/0.61      inference('clc', [status(thm)], ['180', '181'])).
% 0.42/0.61  thf('183', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.42/0.61      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.42/0.61  thf('184', plain, ((v1_xboole_0 @ sk_B)),
% 0.42/0.61      inference('clc', [status(thm)], ['182', '183'])).
% 0.42/0.61  thf('185', plain, ($false), inference('demod', [status(thm)], ['0', '184'])).
% 0.42/0.61  
% 0.42/0.61  % SZS output end Refutation
% 0.42/0.61  
% 0.42/0.62  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
