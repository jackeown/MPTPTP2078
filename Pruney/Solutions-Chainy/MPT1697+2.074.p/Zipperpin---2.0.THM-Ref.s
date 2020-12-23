%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.j7xaLeGwdi

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:05 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :  219 ( 638 expanded)
%              Number of leaves         :   35 ( 198 expanded)
%              Depth                    :   40
%              Number of atoms          : 3730 (27772 expanded)
%              Number of equality atoms :  133 ( 891 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

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

thf(t110_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k7_relat_1 @ A @ k1_xboole_0 )
        = k1_xboole_0 ) ) )).

thf('1',plain,(
    ! [X13: $i] :
      ( ( ( k7_relat_1 @ X13 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('2',plain,(
    ! [X13: $i] :
      ( ( ( k7_relat_1 @ X13 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('3',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
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

thf('6',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X32 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ( v1_xboole_0 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X34 ) )
      | ( v1_xboole_0 @ X31 )
      | ( v1_xboole_0 @ X32 )
      | ( v1_xboole_0 @ X34 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X33 @ X32 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X34 @ X32 @ X31 @ X33 @ X30 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('7',plain,(
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
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    v1_funct_2 @ sk_E @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
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
    inference(demod,[status(thm)],['7','8','9'])).

thf('11',plain,(
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
    inference('sup-',[status(thm)],['4','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_2 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['3','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X32 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ( v1_xboole_0 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X34 ) )
      | ( v1_xboole_0 @ X31 )
      | ( v1_xboole_0 @ X32 )
      | ( v1_xboole_0 @ X34 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X33 @ X32 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X34 @ X32 @ X31 @ X33 @ X30 @ X35 ) @ ( k4_subset_1 @ X34 @ X31 @ X33 ) @ X32 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('22',plain,(
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
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_2 @ sk_E @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
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
    inference(demod,[status(thm)],['22','23','24'])).

thf('26',plain,(
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
    inference('sup-',[status(thm)],['19','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_2 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ X0 @ sk_C_2 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['18','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_2 @ X30 @ X31 @ X32 )
      | ~ ( v1_funct_1 @ X30 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) )
      | ( v1_xboole_0 @ X33 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X34 ) )
      | ( v1_xboole_0 @ X31 )
      | ( v1_xboole_0 @ X32 )
      | ( v1_xboole_0 @ X34 )
      | ~ ( v1_funct_1 @ X35 )
      | ~ ( v1_funct_2 @ X35 @ X33 @ X32 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X32 ) ) )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X34 @ X32 @ X31 @ X33 @ X30 @ X35 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X34 @ X31 @ X33 ) @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('37',plain,(
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
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_funct_2 @ sk_E @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
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
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
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
    inference('sup-',[status(thm)],['34','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_2 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C_2 @ sk_D ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ~ ( m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['33','44'])).

thf('46',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['45','46'])).

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

thf('48',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) )
      | ( X29
       != ( k1_tmap_1 @ X25 @ X23 @ X28 @ X24 @ X27 @ X26 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X25 @ X28 @ X24 ) @ X23 @ X29 @ X28 )
        = X27 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X25 @ X28 @ X24 ) @ X23 ) ) )
      | ~ ( v1_funct_2 @ X29 @ ( k4_subset_1 @ X25 @ X28 @ X24 ) @ X23 )
      | ~ ( v1_funct_1 @ X29 )
      | ( ( k2_partfun1 @ X28 @ X23 @ X27 @ ( k9_subset_1 @ X25 @ X28 @ X24 ) )
       != ( k2_partfun1 @ X24 @ X23 @ X26 @ ( k9_subset_1 @ X25 @ X28 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X23 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X25 ) )
      | ( v1_xboole_0 @ X28 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('49',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X23 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X23 ) ) )
      | ( ( k2_partfun1 @ X28 @ X23 @ X27 @ ( k9_subset_1 @ X25 @ X28 @ X24 ) )
       != ( k2_partfun1 @ X24 @ X23 @ X26 @ ( k9_subset_1 @ X25 @ X28 @ X24 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X25 @ X23 @ X28 @ X24 @ X27 @ X26 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X25 @ X23 @ X28 @ X24 @ X27 @ X26 ) @ ( k4_subset_1 @ X25 @ X28 @ X24 ) @ X23 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X25 @ X23 @ X28 @ X24 @ X27 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X25 @ X28 @ X24 ) @ X23 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X25 @ X28 @ X24 ) @ X23 @ ( k1_tmap_1 @ X25 @ X23 @ X28 @ X24 @ X27 @ X26 ) @ X28 )
        = X27 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ( v1_xboole_0 @ X24 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
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
    inference('sup-',[status(thm)],['47','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('56',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    r1_subset_1 @ sk_C_2 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r1_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ( ( r1_subset_1 @ A @ B )
      <=> ( r1_xboole_0 @ A @ B ) ) ) )).

thf('59',plain,(
    ! [X14: $i,X15: $i] :
      ( ( v1_xboole_0 @ X14 )
      | ( v1_xboole_0 @ X15 )
      | ( r1_xboole_0 @ X14 @ X15 )
      | ~ ( r1_subset_1 @ X14 @ X15 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_subset_1])).

thf('60',plain,
    ( ( r1_xboole_0 @ sk_C_2 @ sk_D )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( r1_xboole_0 @ sk_C_2 @ sk_D ) ),
    inference(clc,[status(thm)],['60','61'])).

thf('63',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    r1_xboole_0 @ sk_C_2 @ sk_D ),
    inference(clc,[status(thm)],['62','63'])).

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

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X0 @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf(t4_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( ? [C: $i] :
              ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) )
          & ( r1_xboole_0 @ A @ B ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ B )
          & ! [C: $i] :
              ~ ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) )).

thf('66',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ ( k3_xboole_0 @ X4 @ X7 ) )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t4_xboole_0])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_xboole_0 @ ( k3_xboole_0 @ X1 @ X0 ) @ X2 )
      | ~ ( r1_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) @ X0 ) ),
    inference('sup-',[status(thm)],['64','67'])).

thf(t66_xboole_1,axiom,(
    ! [A: $i] :
      ( ~ ( ( A != k1_xboole_0 )
          & ( r1_xboole_0 @ A @ A ) )
      & ~ ( ~ ( r1_xboole_0 @ A @ A )
          & ( A = k1_xboole_0 ) ) ) )).

thf('69',plain,(
    ! [X9: $i] :
      ( ( X9 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X9 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t66_xboole_1])).

thf('70',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('72',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ( ( k2_partfun1 @ X20 @ X21 @ X19 @ X22 )
        = ( k7_relat_1 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('77',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['68','69'])).

thf('78',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_1 @ X19 )
      | ( ( k2_partfun1 @ X20 @ X21 @ X19 @ X22 )
        = ( k7_relat_1 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_2 @ sk_E @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
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
    inference(demod,[status(thm)],['50','51','52','53','54','57','70','75','76','77','82','83','84','85','86'])).

thf('88',plain,
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
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
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
    inference('sup-',[status(thm)],['32','88'])).

thf('90',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_C_2 )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_C_2 )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_C_2 )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_C_2 )
     != sk_E ) ),
    inference(split,[status(esa)],['91'])).

thf('93',plain,(
    ! [X13: $i] :
      ( ( ( k7_relat_1 @ X13 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('94',plain,(
    ! [X13: $i] :
      ( ( ( k7_relat_1 @ X13 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('95',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('97',plain,
    ( ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) ) ),
    inference(split,[status(esa)],['91'])).

thf('98',plain,
    ( ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['96','97'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('100',plain,
    ( ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['98','99'])).

thf('101',plain,
    ( ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C_2 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['95','100'])).

thf('102',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['68','69'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('104',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['68','69'])).

thf('105',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['101','102','103','104'])).

thf('106',plain,
    ( ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_F ) )
   <= ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['94','105'])).

thf('107',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('108',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('109',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['107','108'])).

thf('110',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['106','109'])).

thf('111',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_E ) )
   <= ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['93','110'])).

thf('112',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( v1_relat_1 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('114',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['111','114'])).

thf('116',plain,
    ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['115'])).

thf('117',plain,(
    ! [X13: $i] :
      ( ( ( k7_relat_1 @ X13 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('118',plain,(
    ! [X13: $i] :
      ( ( ( k7_relat_1 @ X13 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t110_relat_1])).

thf('119',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['15','16'])).

thf('120',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('121',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('122',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ( v1_xboole_0 @ X24 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ X24 @ X23 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) )
      | ( X29
       != ( k1_tmap_1 @ X25 @ X23 @ X28 @ X24 @ X27 @ X26 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X25 @ X28 @ X24 ) @ X23 @ X29 @ X24 )
        = X26 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X25 @ X28 @ X24 ) @ X23 ) ) )
      | ~ ( v1_funct_2 @ X29 @ ( k4_subset_1 @ X25 @ X28 @ X24 ) @ X23 )
      | ~ ( v1_funct_1 @ X29 )
      | ( ( k2_partfun1 @ X28 @ X23 @ X27 @ ( k9_subset_1 @ X25 @ X28 @ X24 ) )
       != ( k2_partfun1 @ X24 @ X23 @ X26 @ ( k9_subset_1 @ X25 @ X28 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X23 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X25 ) )
      | ( v1_xboole_0 @ X28 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('123',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ( v1_xboole_0 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X25 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X28 @ X23 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ X23 ) ) )
      | ( ( k2_partfun1 @ X28 @ X23 @ X27 @ ( k9_subset_1 @ X25 @ X28 @ X24 ) )
       != ( k2_partfun1 @ X24 @ X23 @ X26 @ ( k9_subset_1 @ X25 @ X28 @ X24 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X25 @ X23 @ X28 @ X24 @ X27 @ X26 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X25 @ X23 @ X28 @ X24 @ X27 @ X26 ) @ ( k4_subset_1 @ X25 @ X28 @ X24 ) @ X23 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X25 @ X23 @ X28 @ X24 @ X27 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X25 @ X28 @ X24 ) @ X23 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X25 @ X28 @ X24 ) @ X23 @ ( k1_tmap_1 @ X25 @ X23 @ X28 @ X24 @ X27 @ X26 ) @ X24 )
        = X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) )
      | ~ ( v1_funct_2 @ X26 @ X24 @ X23 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ( v1_xboole_0 @ X24 )
      | ( v1_xboole_0 @ X23 ) ) ),
    inference(simplify,[status(thm)],['122'])).

thf('124',plain,
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
    inference('sup-',[status(thm)],['121','123'])).

thf('125',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('126',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('128',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('129',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('130',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['68','69'])).

thf('131',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('133',plain,
    ( ( k3_xboole_0 @ sk_C_2 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['68','69'])).

thf('134',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('135',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_2 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    v1_funct_2 @ sk_E @ sk_C_2 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('139',plain,
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
    inference(demod,[status(thm)],['124','125','126','127','128','129','130','131','132','133','134','135','136','137','138'])).

thf('140',plain,
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
    inference(simplify,[status(thm)],['139'])).

thf('141',plain,
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
    inference('sup-',[status(thm)],['120','140'])).

thf('142',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['141'])).

thf('143',plain,
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
    inference('sup-',[status(thm)],['119','142'])).

thf('144',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference('sup-',[status(thm)],['118','144'])).

thf('146',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['107','108'])).

thf('147',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference(demod,[status(thm)],['145','146'])).

thf('148',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['117','147'])).

thf('149',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['112','113'])).

thf('150',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['148','149'])).

thf('151',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference(simplify,[status(thm)],['150'])).

thf('152',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['91'])).

thf('153',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_2 )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['151','152'])).

thf('154',plain,
    ( ( ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C_2 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['153'])).

thf('155',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('156',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_2 ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['154','155'])).

thf('157',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('158',plain,
    ( ( ( v1_xboole_0 @ sk_C_2 )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['156','157'])).

thf('159',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('160',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['158','159'])).

thf('161',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_C_2 )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_2 @ sk_D ) ) ) ),
    inference(split,[status(esa)],['91'])).

thf('164',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_C_2 )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['116','162','163'])).

thf('165',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_2 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) @ sk_C_2 )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['92','164'])).

thf('166',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['90','165'])).

thf('167',plain,
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
    inference('sup-',[status(thm)],['17','166'])).

thf('168',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['167'])).

thf('169',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['2','168'])).

thf('170',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['107','108'])).

thf('171',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['169','170'])).

thf('172',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['1','171'])).

thf('173',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['112','113'])).

thf('174',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['172','173'])).

thf('175',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['174'])).

thf('176',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('177',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['175','176'])).

thf('178',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('179',plain,
    ( ( v1_xboole_0 @ sk_C_2 )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['177','178'])).

thf('180',plain,(
    ~ ( v1_xboole_0 @ sk_C_2 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('181',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['179','180'])).

thf('182',plain,(
    $false ),
    inference(demod,[status(thm)],['0','181'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.15  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.j7xaLeGwdi
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:30:51 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.39/0.62  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.39/0.62  % Solved by: fo/fo7.sh
% 0.39/0.62  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.39/0.62  % done 164 iterations in 0.147s
% 0.39/0.62  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.39/0.62  % SZS output start Refutation
% 0.39/0.62  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.39/0.62  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.39/0.62  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.39/0.62  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.39/0.62  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.39/0.62  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.39/0.62  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.39/0.62  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.39/0.62  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.39/0.62  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.39/0.62  thf(sk_D_type, type, sk_D: $i).
% 0.39/0.62  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.39/0.62  thf(sk_E_type, type, sk_E: $i).
% 0.39/0.62  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.39/0.62  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.39/0.62  thf(sk_F_type, type, sk_F: $i).
% 0.39/0.62  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 0.39/0.62  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.39/0.62  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.39/0.62  thf(sk_A_type, type, sk_A: $i).
% 0.39/0.62  thf(sk_B_type, type, sk_B: $i).
% 0.39/0.62  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.39/0.62  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.39/0.62  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.39/0.62  thf(t6_tmap_1, conjecture,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.62       ( ![B:$i]:
% 0.39/0.62         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.39/0.62           ( ![C:$i]:
% 0.39/0.62             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.39/0.62                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.39/0.62               ( ![D:$i]:
% 0.39/0.62                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.39/0.62                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.39/0.62                   ( ( r1_subset_1 @ C @ D ) =>
% 0.39/0.62                     ( ![E:$i]:
% 0.39/0.62                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.39/0.62                           ( m1_subset_1 @
% 0.39/0.62                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.39/0.62                         ( ![F:$i]:
% 0.39/0.62                           ( ( ( v1_funct_1 @ F ) & 
% 0.39/0.62                               ( v1_funct_2 @ F @ D @ B ) & 
% 0.39/0.62                               ( m1_subset_1 @
% 0.39/0.62                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.39/0.62                             ( ( ( k2_partfun1 @
% 0.39/0.62                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.39/0.62                                 ( k2_partfun1 @
% 0.39/0.62                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.39/0.62                               ( ( k2_partfun1 @
% 0.39/0.62                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.39/0.62                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.39/0.62                                 ( E ) ) & 
% 0.39/0.62                               ( ( k2_partfun1 @
% 0.39/0.62                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.39/0.62                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.39/0.62                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.62  thf(zf_stmt_0, negated_conjecture,
% 0.39/0.62    (~( ![A:$i]:
% 0.39/0.62        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.62          ( ![B:$i]:
% 0.39/0.62            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.39/0.62              ( ![C:$i]:
% 0.39/0.62                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.39/0.62                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.39/0.62                  ( ![D:$i]:
% 0.39/0.62                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.39/0.62                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.39/0.62                      ( ( r1_subset_1 @ C @ D ) =>
% 0.39/0.62                        ( ![E:$i]:
% 0.39/0.62                          ( ( ( v1_funct_1 @ E ) & 
% 0.39/0.62                              ( v1_funct_2 @ E @ C @ B ) & 
% 0.39/0.62                              ( m1_subset_1 @
% 0.39/0.62                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.39/0.62                            ( ![F:$i]:
% 0.39/0.62                              ( ( ( v1_funct_1 @ F ) & 
% 0.39/0.62                                  ( v1_funct_2 @ F @ D @ B ) & 
% 0.39/0.62                                  ( m1_subset_1 @
% 0.39/0.62                                    F @ 
% 0.39/0.62                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.39/0.62                                ( ( ( k2_partfun1 @
% 0.39/0.62                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.39/0.62                                    ( k2_partfun1 @
% 0.39/0.62                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.39/0.62                                  ( ( k2_partfun1 @
% 0.39/0.62                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.39/0.62                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.39/0.62                                    ( E ) ) & 
% 0.39/0.62                                  ( ( k2_partfun1 @
% 0.39/0.62                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.39/0.62                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.39/0.62                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.39/0.62    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 0.39/0.62  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(t110_relat_1, axiom,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ( v1_relat_1 @ A ) =>
% 0.39/0.62       ( ( k7_relat_1 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ) ))).
% 0.39/0.62  thf('1', plain,
% 0.39/0.62      (![X13 : $i]:
% 0.39/0.62         (((k7_relat_1 @ X13 @ k1_xboole_0) = (k1_xboole_0))
% 0.39/0.62          | ~ (v1_relat_1 @ X13))),
% 0.39/0.62      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.39/0.62  thf('2', plain,
% 0.39/0.62      (![X13 : $i]:
% 0.39/0.62         (((k7_relat_1 @ X13 @ k1_xboole_0) = (k1_xboole_0))
% 0.39/0.62          | ~ (v1_relat_1 @ X13))),
% 0.39/0.62      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.39/0.62  thf('3', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('4', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('5', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_B)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(dt_k1_tmap_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.39/0.62     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.39/0.62         ( ~( v1_xboole_0 @ C ) ) & 
% 0.39/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 0.39/0.62         ( ~( v1_xboole_0 @ D ) ) & 
% 0.39/0.62         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 0.39/0.62         ( v1_funct_2 @ E @ C @ B ) & 
% 0.39/0.62         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.39/0.62         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.39/0.62         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.39/0.62       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.39/0.62         ( v1_funct_2 @
% 0.39/0.62           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.39/0.62           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.39/0.62         ( m1_subset_1 @
% 0.39/0.62           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.39/0.62           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 0.39/0.62  thf('6', plain,
% 0.39/0.62      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.39/0.62         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.39/0.62          | ~ (v1_funct_2 @ X30 @ X31 @ X32)
% 0.39/0.62          | ~ (v1_funct_1 @ X30)
% 0.39/0.62          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 0.39/0.62          | (v1_xboole_0 @ X33)
% 0.39/0.62          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X34))
% 0.39/0.62          | (v1_xboole_0 @ X31)
% 0.39/0.62          | (v1_xboole_0 @ X32)
% 0.39/0.62          | (v1_xboole_0 @ X34)
% 0.39/0.62          | ~ (v1_funct_1 @ X35)
% 0.39/0.62          | ~ (v1_funct_2 @ X35 @ X33 @ X32)
% 0.39/0.62          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.39/0.62          | (v1_funct_1 @ (k1_tmap_1 @ X34 @ X32 @ X31 @ X33 @ X30 @ X35)))),
% 0.39/0.62      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.39/0.62  thf('7', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.62         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C_2 @ X1 @ sk_E @ X0))
% 0.39/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.39/0.62          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.39/0.62          | ~ (v1_funct_1 @ X0)
% 0.39/0.62          | (v1_xboole_0 @ X2)
% 0.39/0.62          | (v1_xboole_0 @ sk_B)
% 0.39/0.62          | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X2))
% 0.39/0.62          | (v1_xboole_0 @ X1)
% 0.39/0.62          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.39/0.62          | ~ (v1_funct_1 @ sk_E)
% 0.39/0.62          | ~ (v1_funct_2 @ sk_E @ sk_C_2 @ sk_B))),
% 0.39/0.62      inference('sup-', [status(thm)], ['5', '6'])).
% 0.39/0.62  thf('8', plain, ((v1_funct_1 @ sk_E)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('9', plain, ((v1_funct_2 @ sk_E @ sk_C_2 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('10', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.62         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C_2 @ X1 @ sk_E @ X0))
% 0.39/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.39/0.62          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.39/0.62          | ~ (v1_funct_1 @ X0)
% 0.39/0.62          | (v1_xboole_0 @ X2)
% 0.39/0.62          | (v1_xboole_0 @ sk_B)
% 0.39/0.62          | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X2))
% 0.39/0.62          | (v1_xboole_0 @ X1)
% 0.39/0.62          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.39/0.62      inference('demod', [status(thm)], ['7', '8', '9'])).
% 0.39/0.62  thf('11', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.39/0.62          | (v1_xboole_0 @ sk_D)
% 0.39/0.62          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X0))
% 0.39/0.62          | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62          | (v1_xboole_0 @ sk_B)
% 0.39/0.62          | (v1_xboole_0 @ X0)
% 0.39/0.62          | ~ (v1_funct_1 @ sk_F)
% 0.39/0.62          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.39/0.62          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['4', '10'])).
% 0.39/0.62  thf('12', plain, ((v1_funct_1 @ sk_F)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('13', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('14', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.39/0.62          | (v1_xboole_0 @ sk_D)
% 0.39/0.62          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X0))
% 0.39/0.62          | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62          | (v1_xboole_0 @ sk_B)
% 0.39/0.62          | (v1_xboole_0 @ X0)
% 0.39/0.62          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F)))),
% 0.39/0.62      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.39/0.62  thf('15', plain,
% 0.39/0.62      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 0.39/0.62        | (v1_xboole_0 @ sk_A)
% 0.39/0.62        | (v1_xboole_0 @ sk_B)
% 0.39/0.62        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62        | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))
% 0.39/0.62        | (v1_xboole_0 @ sk_D))),
% 0.39/0.62      inference('sup-', [status(thm)], ['3', '14'])).
% 0.39/0.62  thf('16', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('17', plain,
% 0.39/0.62      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 0.39/0.62        | (v1_xboole_0 @ sk_A)
% 0.39/0.62        | (v1_xboole_0 @ sk_B)
% 0.39/0.62        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62        | (v1_xboole_0 @ sk_D))),
% 0.39/0.62      inference('demod', [status(thm)], ['15', '16'])).
% 0.39/0.62  thf('18', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('19', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('20', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_B)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('21', plain,
% 0.39/0.62      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.39/0.62         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.39/0.62          | ~ (v1_funct_2 @ X30 @ X31 @ X32)
% 0.39/0.62          | ~ (v1_funct_1 @ X30)
% 0.39/0.62          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 0.39/0.62          | (v1_xboole_0 @ X33)
% 0.39/0.62          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X34))
% 0.39/0.62          | (v1_xboole_0 @ X31)
% 0.39/0.62          | (v1_xboole_0 @ X32)
% 0.39/0.62          | (v1_xboole_0 @ X34)
% 0.39/0.62          | ~ (v1_funct_1 @ X35)
% 0.39/0.62          | ~ (v1_funct_2 @ X35 @ X33 @ X32)
% 0.39/0.62          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.39/0.62          | (v1_funct_2 @ (k1_tmap_1 @ X34 @ X32 @ X31 @ X33 @ X30 @ X35) @ 
% 0.39/0.62             (k4_subset_1 @ X34 @ X31 @ X33) @ X32))),
% 0.39/0.62      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.39/0.62  thf('22', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.62         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C_2 @ X0 @ sk_E @ X2) @ 
% 0.39/0.62           (k4_subset_1 @ X1 @ sk_C_2 @ X0) @ sk_B)
% 0.39/0.62          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.39/0.62          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.39/0.62          | ~ (v1_funct_1 @ X2)
% 0.39/0.62          | (v1_xboole_0 @ X1)
% 0.39/0.62          | (v1_xboole_0 @ sk_B)
% 0.39/0.62          | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X1))
% 0.39/0.62          | (v1_xboole_0 @ X0)
% 0.39/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.39/0.62          | ~ (v1_funct_1 @ sk_E)
% 0.39/0.62          | ~ (v1_funct_2 @ sk_E @ sk_C_2 @ sk_B))),
% 0.39/0.62      inference('sup-', [status(thm)], ['20', '21'])).
% 0.39/0.62  thf('23', plain, ((v1_funct_1 @ sk_E)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('24', plain, ((v1_funct_2 @ sk_E @ sk_C_2 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('25', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.62         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C_2 @ X0 @ sk_E @ X2) @ 
% 0.39/0.62           (k4_subset_1 @ X1 @ sk_C_2 @ X0) @ sk_B)
% 0.39/0.62          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.39/0.62          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.39/0.62          | ~ (v1_funct_1 @ X2)
% 0.39/0.62          | (v1_xboole_0 @ X1)
% 0.39/0.62          | (v1_xboole_0 @ sk_B)
% 0.39/0.62          | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X1))
% 0.39/0.62          | (v1_xboole_0 @ X0)
% 0.39/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.39/0.62      inference('demod', [status(thm)], ['22', '23', '24'])).
% 0.39/0.62  thf('26', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.39/0.62          | (v1_xboole_0 @ sk_D)
% 0.39/0.62          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X0))
% 0.39/0.62          | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62          | (v1_xboole_0 @ sk_B)
% 0.39/0.62          | (v1_xboole_0 @ X0)
% 0.39/0.62          | ~ (v1_funct_1 @ sk_F)
% 0.39/0.62          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.39/0.62          | (v1_funct_2 @ 
% 0.39/0.62             (k1_tmap_1 @ X0 @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.62             (k4_subset_1 @ X0 @ sk_C_2 @ sk_D) @ sk_B))),
% 0.39/0.62      inference('sup-', [status(thm)], ['19', '25'])).
% 0.39/0.62  thf('27', plain, ((v1_funct_1 @ sk_F)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('28', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('29', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.39/0.62          | (v1_xboole_0 @ sk_D)
% 0.39/0.62          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X0))
% 0.39/0.62          | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62          | (v1_xboole_0 @ sk_B)
% 0.39/0.62          | (v1_xboole_0 @ X0)
% 0.39/0.62          | (v1_funct_2 @ 
% 0.39/0.62             (k1_tmap_1 @ X0 @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.62             (k4_subset_1 @ X0 @ sk_C_2 @ sk_D) @ sk_B))),
% 0.39/0.62      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.39/0.62  thf('30', plain,
% 0.39/0.62      (((v1_funct_2 @ 
% 0.39/0.62         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.62         (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B)
% 0.39/0.62        | (v1_xboole_0 @ sk_A)
% 0.39/0.62        | (v1_xboole_0 @ sk_B)
% 0.39/0.62        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62        | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))
% 0.39/0.62        | (v1_xboole_0 @ sk_D))),
% 0.39/0.62      inference('sup-', [status(thm)], ['18', '29'])).
% 0.39/0.62  thf('31', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('32', plain,
% 0.39/0.62      (((v1_funct_2 @ 
% 0.39/0.62         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.62         (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B)
% 0.39/0.62        | (v1_xboole_0 @ sk_A)
% 0.39/0.62        | (v1_xboole_0 @ sk_B)
% 0.39/0.62        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62        | (v1_xboole_0 @ sk_D))),
% 0.39/0.62      inference('demod', [status(thm)], ['30', '31'])).
% 0.39/0.62  thf('33', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('34', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('35', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_B)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('36', plain,
% 0.39/0.62      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.39/0.62         (~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32)))
% 0.39/0.62          | ~ (v1_funct_2 @ X30 @ X31 @ X32)
% 0.39/0.62          | ~ (v1_funct_1 @ X30)
% 0.39/0.62          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X34))
% 0.39/0.62          | (v1_xboole_0 @ X33)
% 0.39/0.62          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ X34))
% 0.39/0.62          | (v1_xboole_0 @ X31)
% 0.39/0.62          | (v1_xboole_0 @ X32)
% 0.39/0.62          | (v1_xboole_0 @ X34)
% 0.39/0.62          | ~ (v1_funct_1 @ X35)
% 0.39/0.62          | ~ (v1_funct_2 @ X35 @ X33 @ X32)
% 0.39/0.62          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X32)))
% 0.39/0.62          | (m1_subset_1 @ (k1_tmap_1 @ X34 @ X32 @ X31 @ X33 @ X30 @ X35) @ 
% 0.39/0.62             (k1_zfmisc_1 @ 
% 0.39/0.62              (k2_zfmisc_1 @ (k4_subset_1 @ X34 @ X31 @ X33) @ X32))))),
% 0.39/0.62      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.39/0.62  thf('37', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.62         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C_2 @ X0 @ sk_E @ X2) @ 
% 0.39/0.62           (k1_zfmisc_1 @ 
% 0.39/0.62            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C_2 @ X0) @ sk_B)))
% 0.39/0.62          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.39/0.62          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.39/0.62          | ~ (v1_funct_1 @ X2)
% 0.39/0.62          | (v1_xboole_0 @ X1)
% 0.39/0.62          | (v1_xboole_0 @ sk_B)
% 0.39/0.62          | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X1))
% 0.39/0.62          | (v1_xboole_0 @ X0)
% 0.39/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.39/0.62          | ~ (v1_funct_1 @ sk_E)
% 0.39/0.62          | ~ (v1_funct_2 @ sk_E @ sk_C_2 @ sk_B))),
% 0.39/0.62      inference('sup-', [status(thm)], ['35', '36'])).
% 0.39/0.62  thf('38', plain, ((v1_funct_1 @ sk_E)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('39', plain, ((v1_funct_2 @ sk_E @ sk_C_2 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('40', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.62         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C_2 @ X0 @ sk_E @ X2) @ 
% 0.39/0.62           (k1_zfmisc_1 @ 
% 0.39/0.62            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C_2 @ X0) @ sk_B)))
% 0.39/0.62          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.39/0.62          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.39/0.62          | ~ (v1_funct_1 @ X2)
% 0.39/0.62          | (v1_xboole_0 @ X1)
% 0.39/0.62          | (v1_xboole_0 @ sk_B)
% 0.39/0.62          | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X1))
% 0.39/0.62          | (v1_xboole_0 @ X0)
% 0.39/0.62          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.39/0.62      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.39/0.62  thf('41', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.39/0.62          | (v1_xboole_0 @ sk_D)
% 0.39/0.62          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X0))
% 0.39/0.62          | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62          | (v1_xboole_0 @ sk_B)
% 0.39/0.62          | (v1_xboole_0 @ X0)
% 0.39/0.62          | ~ (v1_funct_1 @ sk_F)
% 0.39/0.62          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.39/0.62          | (m1_subset_1 @ 
% 0.39/0.62             (k1_tmap_1 @ X0 @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.62             (k1_zfmisc_1 @ 
% 0.39/0.62              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C_2 @ sk_D) @ sk_B))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['34', '40'])).
% 0.39/0.62  thf('42', plain, ((v1_funct_1 @ sk_F)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('43', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('44', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.39/0.62          | (v1_xboole_0 @ sk_D)
% 0.39/0.62          | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ X0))
% 0.39/0.62          | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62          | (v1_xboole_0 @ sk_B)
% 0.39/0.62          | (v1_xboole_0 @ X0)
% 0.39/0.62          | (m1_subset_1 @ 
% 0.39/0.62             (k1_tmap_1 @ X0 @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.62             (k1_zfmisc_1 @ 
% 0.39/0.62              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C_2 @ sk_D) @ sk_B))))),
% 0.39/0.62      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.39/0.62  thf('45', plain,
% 0.39/0.62      (((m1_subset_1 @ 
% 0.39/0.62         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.62         (k1_zfmisc_1 @ 
% 0.39/0.62          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B)))
% 0.39/0.62        | (v1_xboole_0 @ sk_A)
% 0.39/0.62        | (v1_xboole_0 @ sk_B)
% 0.39/0.62        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62        | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))
% 0.39/0.62        | (v1_xboole_0 @ sk_D))),
% 0.39/0.62      inference('sup-', [status(thm)], ['33', '44'])).
% 0.39/0.62  thf('46', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('47', plain,
% 0.39/0.62      (((m1_subset_1 @ 
% 0.39/0.62         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.62         (k1_zfmisc_1 @ 
% 0.39/0.62          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B)))
% 0.39/0.62        | (v1_xboole_0 @ sk_A)
% 0.39/0.62        | (v1_xboole_0 @ sk_B)
% 0.39/0.62        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62        | (v1_xboole_0 @ sk_D))),
% 0.39/0.62      inference('demod', [status(thm)], ['45', '46'])).
% 0.39/0.62  thf(d1_tmap_1, axiom,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.39/0.62       ( ![B:$i]:
% 0.39/0.62         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.39/0.62           ( ![C:$i]:
% 0.39/0.62             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.39/0.62                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.39/0.62               ( ![D:$i]:
% 0.39/0.62                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.39/0.62                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.39/0.62                   ( ![E:$i]:
% 0.39/0.62                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.39/0.62                         ( m1_subset_1 @
% 0.39/0.62                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.39/0.62                       ( ![F:$i]:
% 0.39/0.62                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.39/0.62                             ( m1_subset_1 @
% 0.39/0.62                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.39/0.62                           ( ( ( k2_partfun1 @
% 0.39/0.62                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.39/0.62                               ( k2_partfun1 @
% 0.39/0.62                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 0.39/0.62                             ( ![G:$i]:
% 0.39/0.62                               ( ( ( v1_funct_1 @ G ) & 
% 0.39/0.62                                   ( v1_funct_2 @
% 0.39/0.62                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.39/0.62                                   ( m1_subset_1 @
% 0.39/0.62                                     G @ 
% 0.39/0.62                                     ( k1_zfmisc_1 @
% 0.39/0.62                                       ( k2_zfmisc_1 @
% 0.39/0.62                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 0.39/0.62                                 ( ( ( G ) =
% 0.39/0.62                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.39/0.62                                   ( ( ( k2_partfun1 @
% 0.39/0.62                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.39/0.62                                         C ) =
% 0.39/0.62                                       ( E ) ) & 
% 0.39/0.62                                     ( ( k2_partfun1 @
% 0.39/0.62                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.39/0.62                                         D ) =
% 0.39/0.62                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.39/0.62  thf('48', plain,
% 0.39/0.62      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.39/0.62         ((v1_xboole_0 @ X23)
% 0.39/0.62          | (v1_xboole_0 @ X24)
% 0.39/0.62          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 0.39/0.62          | ~ (v1_funct_1 @ X26)
% 0.39/0.62          | ~ (v1_funct_2 @ X26 @ X24 @ X23)
% 0.39/0.62          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 0.39/0.62          | ((X29) != (k1_tmap_1 @ X25 @ X23 @ X28 @ X24 @ X27 @ X26))
% 0.39/0.62          | ((k2_partfun1 @ (k4_subset_1 @ X25 @ X28 @ X24) @ X23 @ X29 @ X28)
% 0.39/0.62              = (X27))
% 0.39/0.62          | ~ (m1_subset_1 @ X29 @ 
% 0.39/0.62               (k1_zfmisc_1 @ 
% 0.39/0.62                (k2_zfmisc_1 @ (k4_subset_1 @ X25 @ X28 @ X24) @ X23)))
% 0.39/0.62          | ~ (v1_funct_2 @ X29 @ (k4_subset_1 @ X25 @ X28 @ X24) @ X23)
% 0.39/0.62          | ~ (v1_funct_1 @ X29)
% 0.39/0.62          | ((k2_partfun1 @ X28 @ X23 @ X27 @ (k9_subset_1 @ X25 @ X28 @ X24))
% 0.39/0.62              != (k2_partfun1 @ X24 @ X23 @ X26 @ 
% 0.39/0.62                  (k9_subset_1 @ X25 @ X28 @ X24)))
% 0.39/0.62          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X23)))
% 0.39/0.62          | ~ (v1_funct_2 @ X27 @ X28 @ X23)
% 0.39/0.62          | ~ (v1_funct_1 @ X27)
% 0.39/0.62          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X25))
% 0.39/0.62          | (v1_xboole_0 @ X28)
% 0.39/0.62          | (v1_xboole_0 @ X25))),
% 0.39/0.62      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.39/0.62  thf('49', plain,
% 0.39/0.62      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.39/0.62         ((v1_xboole_0 @ X25)
% 0.39/0.62          | (v1_xboole_0 @ X28)
% 0.39/0.62          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X25))
% 0.39/0.62          | ~ (v1_funct_1 @ X27)
% 0.39/0.62          | ~ (v1_funct_2 @ X27 @ X28 @ X23)
% 0.39/0.62          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X23)))
% 0.39/0.62          | ((k2_partfun1 @ X28 @ X23 @ X27 @ (k9_subset_1 @ X25 @ X28 @ X24))
% 0.39/0.62              != (k2_partfun1 @ X24 @ X23 @ X26 @ 
% 0.39/0.62                  (k9_subset_1 @ X25 @ X28 @ X24)))
% 0.39/0.62          | ~ (v1_funct_1 @ (k1_tmap_1 @ X25 @ X23 @ X28 @ X24 @ X27 @ X26))
% 0.39/0.62          | ~ (v1_funct_2 @ (k1_tmap_1 @ X25 @ X23 @ X28 @ X24 @ X27 @ X26) @ 
% 0.39/0.62               (k4_subset_1 @ X25 @ X28 @ X24) @ X23)
% 0.39/0.62          | ~ (m1_subset_1 @ (k1_tmap_1 @ X25 @ X23 @ X28 @ X24 @ X27 @ X26) @ 
% 0.39/0.62               (k1_zfmisc_1 @ 
% 0.39/0.62                (k2_zfmisc_1 @ (k4_subset_1 @ X25 @ X28 @ X24) @ X23)))
% 0.39/0.62          | ((k2_partfun1 @ (k4_subset_1 @ X25 @ X28 @ X24) @ X23 @ 
% 0.39/0.62              (k1_tmap_1 @ X25 @ X23 @ X28 @ X24 @ X27 @ X26) @ X28) = (
% 0.39/0.62              X27))
% 0.39/0.62          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 0.39/0.62          | ~ (v1_funct_2 @ X26 @ X24 @ X23)
% 0.39/0.62          | ~ (v1_funct_1 @ X26)
% 0.39/0.62          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 0.39/0.62          | (v1_xboole_0 @ X24)
% 0.39/0.62          | (v1_xboole_0 @ X23))),
% 0.39/0.62      inference('simplify', [status(thm)], ['48'])).
% 0.39/0.62  thf('50', plain,
% 0.39/0.62      (((v1_xboole_0 @ sk_D)
% 0.39/0.62        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62        | (v1_xboole_0 @ sk_B)
% 0.39/0.62        | (v1_xboole_0 @ sk_A)
% 0.39/0.62        | (v1_xboole_0 @ sk_B)
% 0.39/0.62        | (v1_xboole_0 @ sk_D)
% 0.39/0.62        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.39/0.62        | ~ (v1_funct_1 @ sk_F)
% 0.39/0.62        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.39/0.62        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.39/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 0.39/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_C_2)
% 0.39/0.62            = (sk_E))
% 0.39/0.62        | ~ (v1_funct_2 @ 
% 0.39/0.62             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.62             (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B)
% 0.39/0.62        | ~ (v1_funct_1 @ 
% 0.39/0.62             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 0.39/0.62        | ((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ 
% 0.39/0.62            (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 0.39/0.62            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.39/0.62                (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))
% 0.39/0.62        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_B)))
% 0.39/0.62        | ~ (v1_funct_2 @ sk_E @ sk_C_2 @ sk_B)
% 0.39/0.62        | ~ (v1_funct_1 @ sk_E)
% 0.39/0.62        | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))
% 0.39/0.62        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62        | (v1_xboole_0 @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['47', '49'])).
% 0.39/0.62  thf('51', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('52', plain, ((v1_funct_1 @ sk_F)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('53', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('54', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('55', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(redefinition_k9_subset_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.39/0.62       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.39/0.62  thf('56', plain,
% 0.39/0.62      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.39/0.62         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 0.39/0.62          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.39/0.62      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.39/0.62  thf('57', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.39/0.62      inference('sup-', [status(thm)], ['55', '56'])).
% 0.39/0.62  thf('58', plain, ((r1_subset_1 @ sk_C_2 @ sk_D)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(redefinition_r1_subset_1, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.39/0.62       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 0.39/0.62  thf('59', plain,
% 0.39/0.62      (![X14 : $i, X15 : $i]:
% 0.39/0.62         ((v1_xboole_0 @ X14)
% 0.39/0.62          | (v1_xboole_0 @ X15)
% 0.39/0.62          | (r1_xboole_0 @ X14 @ X15)
% 0.39/0.62          | ~ (r1_subset_1 @ X14 @ X15))),
% 0.39/0.62      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 0.39/0.62  thf('60', plain,
% 0.39/0.62      (((r1_xboole_0 @ sk_C_2 @ sk_D)
% 0.39/0.62        | (v1_xboole_0 @ sk_D)
% 0.39/0.62        | (v1_xboole_0 @ sk_C_2))),
% 0.39/0.62      inference('sup-', [status(thm)], ['58', '59'])).
% 0.39/0.62  thf('61', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('62', plain, (((v1_xboole_0 @ sk_C_2) | (r1_xboole_0 @ sk_C_2 @ sk_D))),
% 0.39/0.62      inference('clc', [status(thm)], ['60', '61'])).
% 0.39/0.62  thf('63', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('64', plain, ((r1_xboole_0 @ sk_C_2 @ sk_D)),
% 0.39/0.62      inference('clc', [status(thm)], ['62', '63'])).
% 0.39/0.62  thf(t3_xboole_0, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.39/0.62            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.39/0.62       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.39/0.62            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.39/0.62  thf('65', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i]:
% 0.39/0.62         ((r1_xboole_0 @ X0 @ X1) | (r2_hidden @ (sk_C @ X1 @ X0) @ X0))),
% 0.39/0.62      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.39/0.62  thf(t4_xboole_0, axiom,
% 0.39/0.62    (![A:$i,B:$i]:
% 0.39/0.62     ( ( ~( ( ?[C:$i]: ( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) & 
% 0.39/0.62            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.39/0.62       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.39/0.62            ( ![C:$i]: ( ~( r2_hidden @ C @ ( k3_xboole_0 @ A @ B ) ) ) ) ) ) ))).
% 0.39/0.62  thf('66', plain,
% 0.39/0.62      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.39/0.62         (~ (r2_hidden @ X6 @ (k3_xboole_0 @ X4 @ X7))
% 0.39/0.62          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.39/0.62      inference('cnf', [status(esa)], [t4_xboole_0])).
% 0.39/0.62  thf('67', plain,
% 0.39/0.62      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.39/0.62         ((r1_xboole_0 @ (k3_xboole_0 @ X1 @ X0) @ X2)
% 0.39/0.62          | ~ (r1_xboole_0 @ X1 @ X0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['65', '66'])).
% 0.39/0.62  thf('68', plain,
% 0.39/0.62      (![X0 : $i]: (r1_xboole_0 @ (k3_xboole_0 @ sk_C_2 @ sk_D) @ X0)),
% 0.39/0.62      inference('sup-', [status(thm)], ['64', '67'])).
% 0.39/0.62  thf(t66_xboole_1, axiom,
% 0.39/0.62    (![A:$i]:
% 0.39/0.62     ( ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( r1_xboole_0 @ A @ A ) ) ) & 
% 0.39/0.62       ( ~( ( ~( r1_xboole_0 @ A @ A ) ) & ( ( A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.39/0.62  thf('69', plain,
% 0.39/0.62      (![X9 : $i]: (((X9) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X9 @ X9))),
% 0.39/0.62      inference('cnf', [status(esa)], [t66_xboole_1])).
% 0.39/0.62  thf('70', plain, (((k3_xboole_0 @ sk_C_2 @ sk_D) = (k1_xboole_0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['68', '69'])).
% 0.39/0.62  thf('71', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_B)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(redefinition_k2_partfun1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i,D:$i]:
% 0.39/0.62     ( ( ( v1_funct_1 @ C ) & 
% 0.39/0.62         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.39/0.62       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.39/0.62  thf('72', plain,
% 0.39/0.62      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.39/0.62         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.39/0.62          | ~ (v1_funct_1 @ X19)
% 0.39/0.62          | ((k2_partfun1 @ X20 @ X21 @ X19 @ X22) = (k7_relat_1 @ X19 @ X22)))),
% 0.39/0.62      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.39/0.62  thf('73', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 0.39/0.62          | ~ (v1_funct_1 @ sk_E))),
% 0.39/0.62      inference('sup-', [status(thm)], ['71', '72'])).
% 0.39/0.62  thf('74', plain, ((v1_funct_1 @ sk_E)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('75', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.39/0.62      inference('demod', [status(thm)], ['73', '74'])).
% 0.39/0.62  thf('76', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.39/0.62      inference('sup-', [status(thm)], ['55', '56'])).
% 0.39/0.62  thf('77', plain, (((k3_xboole_0 @ sk_C_2 @ sk_D) = (k1_xboole_0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['68', '69'])).
% 0.39/0.62  thf('78', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('79', plain,
% 0.39/0.62      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.39/0.62         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X20 @ X21)))
% 0.39/0.62          | ~ (v1_funct_1 @ X19)
% 0.39/0.62          | ((k2_partfun1 @ X20 @ X21 @ X19 @ X22) = (k7_relat_1 @ X19 @ X22)))),
% 0.39/0.62      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.39/0.62  thf('80', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         (((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 0.39/0.62          | ~ (v1_funct_1 @ sk_F))),
% 0.39/0.62      inference('sup-', [status(thm)], ['78', '79'])).
% 0.39/0.62  thf('81', plain, ((v1_funct_1 @ sk_F)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('82', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.39/0.62      inference('demod', [status(thm)], ['80', '81'])).
% 0.39/0.62  thf('83', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_B)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('84', plain, ((v1_funct_2 @ sk_E @ sk_C_2 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('85', plain, ((v1_funct_1 @ sk_E)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('86', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('87', plain,
% 0.39/0.62      (((v1_xboole_0 @ sk_D)
% 0.39/0.62        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62        | (v1_xboole_0 @ sk_B)
% 0.39/0.62        | (v1_xboole_0 @ sk_A)
% 0.39/0.62        | (v1_xboole_0 @ sk_B)
% 0.39/0.62        | (v1_xboole_0 @ sk_D)
% 0.39/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 0.39/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_C_2)
% 0.39/0.62            = (sk_E))
% 0.39/0.62        | ~ (v1_funct_2 @ 
% 0.39/0.62             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.62             (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B)
% 0.39/0.62        | ~ (v1_funct_1 @ 
% 0.39/0.62             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 0.39/0.62        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.39/0.62            != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.39/0.62        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62        | (v1_xboole_0 @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)],
% 0.39/0.62                ['50', '51', '52', '53', '54', '57', '70', '75', '76', '77', 
% 0.39/0.62                 '82', '83', '84', '85', '86'])).
% 0.39/0.62  thf('88', plain,
% 0.39/0.62      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.39/0.62        | ~ (v1_funct_1 @ 
% 0.39/0.62             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 0.39/0.62        | ~ (v1_funct_2 @ 
% 0.39/0.62             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.62             (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B)
% 0.39/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 0.39/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_C_2)
% 0.39/0.62            = (sk_E))
% 0.39/0.62        | (v1_xboole_0 @ sk_A)
% 0.39/0.62        | (v1_xboole_0 @ sk_B)
% 0.39/0.62        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62        | (v1_xboole_0 @ sk_D))),
% 0.39/0.62      inference('simplify', [status(thm)], ['87'])).
% 0.39/0.62  thf('89', plain,
% 0.39/0.62      (((v1_xboole_0 @ sk_D)
% 0.39/0.62        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62        | (v1_xboole_0 @ sk_B)
% 0.39/0.62        | (v1_xboole_0 @ sk_A)
% 0.39/0.62        | (v1_xboole_0 @ sk_D)
% 0.39/0.62        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62        | (v1_xboole_0 @ sk_B)
% 0.39/0.62        | (v1_xboole_0 @ sk_A)
% 0.39/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 0.39/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_C_2)
% 0.39/0.62            = (sk_E))
% 0.39/0.62        | ~ (v1_funct_1 @ 
% 0.39/0.62             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 0.39/0.62        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.39/0.62            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['32', '88'])).
% 0.39/0.62  thf('90', plain,
% 0.39/0.62      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.39/0.62        | ~ (v1_funct_1 @ 
% 0.39/0.62             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 0.39/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 0.39/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_C_2)
% 0.39/0.62            = (sk_E))
% 0.39/0.62        | (v1_xboole_0 @ sk_A)
% 0.39/0.62        | (v1_xboole_0 @ sk_B)
% 0.39/0.62        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62        | (v1_xboole_0 @ sk_D))),
% 0.39/0.62      inference('simplify', [status(thm)], ['89'])).
% 0.39/0.62  thf('91', plain,
% 0.39/0.62      ((((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ 
% 0.39/0.62          (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 0.39/0.62          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.39/0.62              (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))
% 0.39/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 0.39/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_C_2)
% 0.39/0.62            != (sk_E))
% 0.39/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 0.39/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.39/0.62            != (sk_F)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('92', plain,
% 0.39/0.62      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 0.39/0.62          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_C_2)
% 0.39/0.62          != (sk_E)))
% 0.39/0.62         <= (~
% 0.39/0.62             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 0.39/0.62                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.62                sk_C_2) = (sk_E))))),
% 0.39/0.62      inference('split', [status(esa)], ['91'])).
% 0.39/0.62  thf('93', plain,
% 0.39/0.62      (![X13 : $i]:
% 0.39/0.62         (((k7_relat_1 @ X13 @ k1_xboole_0) = (k1_xboole_0))
% 0.39/0.62          | ~ (v1_relat_1 @ X13))),
% 0.39/0.62      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.39/0.62  thf('94', plain,
% 0.39/0.62      (![X13 : $i]:
% 0.39/0.62         (((k7_relat_1 @ X13 @ k1_xboole_0) = (k1_xboole_0))
% 0.39/0.62          | ~ (v1_relat_1 @ X13))),
% 0.39/0.62      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.39/0.62  thf('95', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.39/0.62      inference('demod', [status(thm)], ['80', '81'])).
% 0.39/0.62  thf('96', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.39/0.62      inference('sup-', [status(thm)], ['55', '56'])).
% 0.39/0.62  thf('97', plain,
% 0.39/0.62      ((((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ 
% 0.39/0.62          (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 0.39/0.62          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.39/0.62              (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))))
% 0.39/0.62         <= (~
% 0.39/0.62             (((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ 
% 0.39/0.62                (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 0.39/0.62                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.39/0.62                   (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))))),
% 0.39/0.62      inference('split', [status(esa)], ['91'])).
% 0.39/0.62  thf('98', plain,
% 0.39/0.62      ((((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ 
% 0.39/0.62          (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 0.39/0.62          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C_2 @ sk_D))))
% 0.39/0.62         <= (~
% 0.39/0.62             (((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ 
% 0.39/0.62                (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 0.39/0.62                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.39/0.62                   (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['96', '97'])).
% 0.39/0.62  thf('99', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.39/0.62      inference('sup-', [status(thm)], ['55', '56'])).
% 0.39/0.62  thf('100', plain,
% 0.39/0.62      ((((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C_2 @ sk_D))
% 0.39/0.62          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C_2 @ sk_D))))
% 0.39/0.62         <= (~
% 0.39/0.62             (((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ 
% 0.39/0.62                (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 0.39/0.62                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.39/0.62                   (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))))),
% 0.39/0.62      inference('demod', [status(thm)], ['98', '99'])).
% 0.39/0.62  thf('101', plain,
% 0.39/0.62      ((((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C_2 @ sk_D))
% 0.39/0.62          != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C_2 @ sk_D))))
% 0.39/0.62         <= (~
% 0.39/0.62             (((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ 
% 0.39/0.62                (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 0.39/0.62                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.39/0.62                   (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['95', '100'])).
% 0.39/0.62  thf('102', plain, (((k3_xboole_0 @ sk_C_2 @ sk_D) = (k1_xboole_0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['68', '69'])).
% 0.39/0.62  thf('103', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.39/0.62      inference('demod', [status(thm)], ['73', '74'])).
% 0.39/0.62  thf('104', plain, (((k3_xboole_0 @ sk_C_2 @ sk_D) = (k1_xboole_0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['68', '69'])).
% 0.39/0.62  thf('105', plain,
% 0.39/0.62      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0)))
% 0.39/0.62         <= (~
% 0.39/0.62             (((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ 
% 0.39/0.62                (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 0.39/0.62                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.39/0.62                   (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))))),
% 0.39/0.62      inference('demod', [status(thm)], ['101', '102', '103', '104'])).
% 0.39/0.62  thf('106', plain,
% 0.39/0.62      (((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.39/0.62         | ~ (v1_relat_1 @ sk_F)))
% 0.39/0.62         <= (~
% 0.39/0.62             (((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ 
% 0.39/0.62                (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 0.39/0.62                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.39/0.62                   (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['94', '105'])).
% 0.39/0.62  thf('107', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf(cc1_relset_1, axiom,
% 0.39/0.62    (![A:$i,B:$i,C:$i]:
% 0.39/0.62     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.39/0.62       ( v1_relat_1 @ C ) ))).
% 0.39/0.62  thf('108', plain,
% 0.39/0.62      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.39/0.62         ((v1_relat_1 @ X16)
% 0.39/0.62          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.39/0.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.39/0.62  thf('109', plain, ((v1_relat_1 @ sk_F)),
% 0.39/0.62      inference('sup-', [status(thm)], ['107', '108'])).
% 0.39/0.62  thf('110', plain,
% 0.39/0.62      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0)))
% 0.39/0.62         <= (~
% 0.39/0.62             (((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ 
% 0.39/0.62                (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 0.39/0.62                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.39/0.62                   (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))))),
% 0.39/0.62      inference('demod', [status(thm)], ['106', '109'])).
% 0.39/0.62  thf('111', plain,
% 0.39/0.62      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_E)))
% 0.39/0.62         <= (~
% 0.39/0.62             (((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ 
% 0.39/0.62                (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 0.39/0.62                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.39/0.62                   (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))))),
% 0.39/0.62      inference('sup-', [status(thm)], ['93', '110'])).
% 0.39/0.62  thf('112', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_B)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('113', plain,
% 0.39/0.62      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.39/0.62         ((v1_relat_1 @ X16)
% 0.39/0.62          | ~ (m1_subset_1 @ X16 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X17 @ X18))))),
% 0.39/0.62      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.39/0.62  thf('114', plain, ((v1_relat_1 @ sk_E)),
% 0.39/0.62      inference('sup-', [status(thm)], ['112', '113'])).
% 0.39/0.62  thf('115', plain,
% 0.39/0.62      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.39/0.62         <= (~
% 0.39/0.62             (((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ 
% 0.39/0.62                (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 0.39/0.62                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.39/0.62                   (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))))),
% 0.39/0.62      inference('demod', [status(thm)], ['111', '114'])).
% 0.39/0.62  thf('116', plain,
% 0.39/0.62      ((((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ 
% 0.39/0.62          (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 0.39/0.62          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.39/0.62             (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))))),
% 0.39/0.62      inference('simplify', [status(thm)], ['115'])).
% 0.39/0.62  thf('117', plain,
% 0.39/0.62      (![X13 : $i]:
% 0.39/0.62         (((k7_relat_1 @ X13 @ k1_xboole_0) = (k1_xboole_0))
% 0.39/0.62          | ~ (v1_relat_1 @ X13))),
% 0.39/0.62      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.39/0.62  thf('118', plain,
% 0.39/0.62      (![X13 : $i]:
% 0.39/0.62         (((k7_relat_1 @ X13 @ k1_xboole_0) = (k1_xboole_0))
% 0.39/0.62          | ~ (v1_relat_1 @ X13))),
% 0.39/0.62      inference('cnf', [status(esa)], [t110_relat_1])).
% 0.39/0.62  thf('119', plain,
% 0.39/0.62      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 0.39/0.62        | (v1_xboole_0 @ sk_A)
% 0.39/0.62        | (v1_xboole_0 @ sk_B)
% 0.39/0.62        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62        | (v1_xboole_0 @ sk_D))),
% 0.39/0.62      inference('demod', [status(thm)], ['15', '16'])).
% 0.39/0.62  thf('120', plain,
% 0.39/0.62      (((v1_funct_2 @ 
% 0.39/0.62         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.62         (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B)
% 0.39/0.62        | (v1_xboole_0 @ sk_A)
% 0.39/0.62        | (v1_xboole_0 @ sk_B)
% 0.39/0.62        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62        | (v1_xboole_0 @ sk_D))),
% 0.39/0.62      inference('demod', [status(thm)], ['30', '31'])).
% 0.39/0.62  thf('121', plain,
% 0.39/0.62      (((m1_subset_1 @ 
% 0.39/0.62         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.62         (k1_zfmisc_1 @ 
% 0.39/0.62          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B)))
% 0.39/0.62        | (v1_xboole_0 @ sk_A)
% 0.39/0.62        | (v1_xboole_0 @ sk_B)
% 0.39/0.62        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62        | (v1_xboole_0 @ sk_D))),
% 0.39/0.62      inference('demod', [status(thm)], ['45', '46'])).
% 0.39/0.62  thf('122', plain,
% 0.39/0.62      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.39/0.62         ((v1_xboole_0 @ X23)
% 0.39/0.62          | (v1_xboole_0 @ X24)
% 0.39/0.62          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 0.39/0.62          | ~ (v1_funct_1 @ X26)
% 0.39/0.62          | ~ (v1_funct_2 @ X26 @ X24 @ X23)
% 0.39/0.62          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 0.39/0.62          | ((X29) != (k1_tmap_1 @ X25 @ X23 @ X28 @ X24 @ X27 @ X26))
% 0.39/0.62          | ((k2_partfun1 @ (k4_subset_1 @ X25 @ X28 @ X24) @ X23 @ X29 @ X24)
% 0.39/0.62              = (X26))
% 0.39/0.62          | ~ (m1_subset_1 @ X29 @ 
% 0.39/0.62               (k1_zfmisc_1 @ 
% 0.39/0.62                (k2_zfmisc_1 @ (k4_subset_1 @ X25 @ X28 @ X24) @ X23)))
% 0.39/0.62          | ~ (v1_funct_2 @ X29 @ (k4_subset_1 @ X25 @ X28 @ X24) @ X23)
% 0.39/0.62          | ~ (v1_funct_1 @ X29)
% 0.39/0.62          | ((k2_partfun1 @ X28 @ X23 @ X27 @ (k9_subset_1 @ X25 @ X28 @ X24))
% 0.39/0.62              != (k2_partfun1 @ X24 @ X23 @ X26 @ 
% 0.39/0.62                  (k9_subset_1 @ X25 @ X28 @ X24)))
% 0.39/0.62          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X23)))
% 0.39/0.62          | ~ (v1_funct_2 @ X27 @ X28 @ X23)
% 0.39/0.62          | ~ (v1_funct_1 @ X27)
% 0.39/0.62          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X25))
% 0.39/0.62          | (v1_xboole_0 @ X28)
% 0.39/0.62          | (v1_xboole_0 @ X25))),
% 0.39/0.62      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.39/0.62  thf('123', plain,
% 0.39/0.62      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.39/0.62         ((v1_xboole_0 @ X25)
% 0.39/0.62          | (v1_xboole_0 @ X28)
% 0.39/0.62          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ X25))
% 0.39/0.62          | ~ (v1_funct_1 @ X27)
% 0.39/0.62          | ~ (v1_funct_2 @ X27 @ X28 @ X23)
% 0.39/0.62          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ X23)))
% 0.39/0.62          | ((k2_partfun1 @ X28 @ X23 @ X27 @ (k9_subset_1 @ X25 @ X28 @ X24))
% 0.39/0.62              != (k2_partfun1 @ X24 @ X23 @ X26 @ 
% 0.39/0.62                  (k9_subset_1 @ X25 @ X28 @ X24)))
% 0.39/0.62          | ~ (v1_funct_1 @ (k1_tmap_1 @ X25 @ X23 @ X28 @ X24 @ X27 @ X26))
% 0.39/0.62          | ~ (v1_funct_2 @ (k1_tmap_1 @ X25 @ X23 @ X28 @ X24 @ X27 @ X26) @ 
% 0.39/0.62               (k4_subset_1 @ X25 @ X28 @ X24) @ X23)
% 0.39/0.62          | ~ (m1_subset_1 @ (k1_tmap_1 @ X25 @ X23 @ X28 @ X24 @ X27 @ X26) @ 
% 0.39/0.62               (k1_zfmisc_1 @ 
% 0.39/0.62                (k2_zfmisc_1 @ (k4_subset_1 @ X25 @ X28 @ X24) @ X23)))
% 0.39/0.62          | ((k2_partfun1 @ (k4_subset_1 @ X25 @ X28 @ X24) @ X23 @ 
% 0.39/0.62              (k1_tmap_1 @ X25 @ X23 @ X28 @ X24 @ X27 @ X26) @ X24) = (
% 0.39/0.62              X26))
% 0.39/0.62          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X24 @ X23)))
% 0.39/0.62          | ~ (v1_funct_2 @ X26 @ X24 @ X23)
% 0.39/0.62          | ~ (v1_funct_1 @ X26)
% 0.39/0.62          | ~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 0.39/0.62          | (v1_xboole_0 @ X24)
% 0.39/0.62          | (v1_xboole_0 @ X23))),
% 0.39/0.62      inference('simplify', [status(thm)], ['122'])).
% 0.39/0.62  thf('124', plain,
% 0.39/0.62      (((v1_xboole_0 @ sk_D)
% 0.39/0.62        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62        | (v1_xboole_0 @ sk_B)
% 0.39/0.62        | (v1_xboole_0 @ sk_A)
% 0.39/0.62        | (v1_xboole_0 @ sk_B)
% 0.39/0.62        | (v1_xboole_0 @ sk_D)
% 0.39/0.62        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.39/0.62        | ~ (v1_funct_1 @ sk_F)
% 0.39/0.62        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.39/0.62        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.39/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 0.39/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.39/0.62            = (sk_F))
% 0.39/0.62        | ~ (v1_funct_2 @ 
% 0.39/0.62             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.62             (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B)
% 0.39/0.62        | ~ (v1_funct_1 @ 
% 0.39/0.62             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 0.39/0.62        | ((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ 
% 0.39/0.62            (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 0.39/0.62            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.39/0.62                (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D)))
% 0.39/0.62        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_B)))
% 0.39/0.62        | ~ (v1_funct_2 @ sk_E @ sk_C_2 @ sk_B)
% 0.39/0.62        | ~ (v1_funct_1 @ sk_E)
% 0.39/0.62        | ~ (m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))
% 0.39/0.62        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62        | (v1_xboole_0 @ sk_A))),
% 0.39/0.62      inference('sup-', [status(thm)], ['121', '123'])).
% 0.39/0.62  thf('125', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('126', plain, ((v1_funct_1 @ sk_F)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('127', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('128', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('129', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.39/0.62      inference('sup-', [status(thm)], ['55', '56'])).
% 0.39/0.62  thf('130', plain, (((k3_xboole_0 @ sk_C_2 @ sk_D) = (k1_xboole_0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['68', '69'])).
% 0.39/0.62  thf('131', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.39/0.62      inference('demod', [status(thm)], ['73', '74'])).
% 0.39/0.62  thf('132', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.39/0.62      inference('sup-', [status(thm)], ['55', '56'])).
% 0.39/0.62  thf('133', plain, (((k3_xboole_0 @ sk_C_2 @ sk_D) = (k1_xboole_0))),
% 0.39/0.62      inference('sup-', [status(thm)], ['68', '69'])).
% 0.39/0.62  thf('134', plain,
% 0.39/0.62      (![X0 : $i]:
% 0.39/0.62         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.39/0.62      inference('demod', [status(thm)], ['80', '81'])).
% 0.39/0.62  thf('135', plain,
% 0.39/0.62      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_2 @ sk_B)))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('136', plain, ((v1_funct_2 @ sk_E @ sk_C_2 @ sk_B)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('137', plain, ((v1_funct_1 @ sk_E)),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('138', plain, ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ sk_A))),
% 0.39/0.62      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.62  thf('139', plain,
% 0.39/0.62      (((v1_xboole_0 @ sk_D)
% 0.39/0.62        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62        | (v1_xboole_0 @ sk_B)
% 0.39/0.62        | (v1_xboole_0 @ sk_A)
% 0.39/0.62        | (v1_xboole_0 @ sk_B)
% 0.39/0.62        | (v1_xboole_0 @ sk_D)
% 0.39/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 0.39/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.39/0.62            = (sk_F))
% 0.39/0.62        | ~ (v1_funct_2 @ 
% 0.39/0.62             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.62             (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B)
% 0.39/0.62        | ~ (v1_funct_1 @ 
% 0.39/0.62             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 0.39/0.62        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.39/0.62            != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.39/0.62        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62        | (v1_xboole_0 @ sk_A))),
% 0.39/0.62      inference('demod', [status(thm)],
% 0.39/0.62                ['124', '125', '126', '127', '128', '129', '130', '131', 
% 0.39/0.62                 '132', '133', '134', '135', '136', '137', '138'])).
% 0.39/0.62  thf('140', plain,
% 0.39/0.62      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.39/0.62        | ~ (v1_funct_1 @ 
% 0.39/0.62             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 0.39/0.62        | ~ (v1_funct_2 @ 
% 0.39/0.62             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ 
% 0.39/0.62             (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B)
% 0.39/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 0.39/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.39/0.62            = (sk_F))
% 0.39/0.62        | (v1_xboole_0 @ sk_A)
% 0.39/0.62        | (v1_xboole_0 @ sk_B)
% 0.39/0.62        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62        | (v1_xboole_0 @ sk_D))),
% 0.39/0.62      inference('simplify', [status(thm)], ['139'])).
% 0.39/0.62  thf('141', plain,
% 0.39/0.62      (((v1_xboole_0 @ sk_D)
% 0.39/0.62        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62        | (v1_xboole_0 @ sk_B)
% 0.39/0.62        | (v1_xboole_0 @ sk_A)
% 0.39/0.62        | (v1_xboole_0 @ sk_D)
% 0.39/0.62        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.62        | (v1_xboole_0 @ sk_B)
% 0.39/0.62        | (v1_xboole_0 @ sk_A)
% 0.39/0.62        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 0.39/0.62            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.39/0.62            = (sk_F))
% 0.39/0.62        | ~ (v1_funct_1 @ 
% 0.39/0.62             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 0.39/0.62        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.39/0.62            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.39/0.62      inference('sup-', [status(thm)], ['120', '140'])).
% 0.39/0.62  thf('142', plain,
% 0.39/0.62      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.39/0.63        | ~ (v1_funct_1 @ 
% 0.39/0.63             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 0.39/0.63        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 0.39/0.63            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.39/0.63            = (sk_F))
% 0.39/0.63        | (v1_xboole_0 @ sk_A)
% 0.39/0.63        | (v1_xboole_0 @ sk_B)
% 0.39/0.63        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.63        | (v1_xboole_0 @ sk_D))),
% 0.39/0.63      inference('simplify', [status(thm)], ['141'])).
% 0.39/0.63  thf('143', plain,
% 0.39/0.63      (((v1_xboole_0 @ sk_D)
% 0.39/0.63        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.63        | (v1_xboole_0 @ sk_B)
% 0.39/0.63        | (v1_xboole_0 @ sk_A)
% 0.39/0.63        | (v1_xboole_0 @ sk_D)
% 0.39/0.63        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.63        | (v1_xboole_0 @ sk_B)
% 0.39/0.63        | (v1_xboole_0 @ sk_A)
% 0.39/0.63        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 0.39/0.63            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.39/0.63            = (sk_F))
% 0.39/0.63        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.39/0.63            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.39/0.63      inference('sup-', [status(thm)], ['119', '142'])).
% 0.39/0.63  thf('144', plain,
% 0.39/0.63      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.39/0.63        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 0.39/0.63            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.39/0.63            = (sk_F))
% 0.39/0.63        | (v1_xboole_0 @ sk_A)
% 0.39/0.63        | (v1_xboole_0 @ sk_B)
% 0.39/0.63        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.63        | (v1_xboole_0 @ sk_D))),
% 0.39/0.63      inference('simplify', [status(thm)], ['143'])).
% 0.39/0.63  thf('145', plain,
% 0.39/0.63      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.39/0.63        | ~ (v1_relat_1 @ sk_F)
% 0.39/0.63        | (v1_xboole_0 @ sk_D)
% 0.39/0.63        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.63        | (v1_xboole_0 @ sk_B)
% 0.39/0.63        | (v1_xboole_0 @ sk_A)
% 0.39/0.63        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 0.39/0.63            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.39/0.63            = (sk_F)))),
% 0.39/0.63      inference('sup-', [status(thm)], ['118', '144'])).
% 0.39/0.63  thf('146', plain, ((v1_relat_1 @ sk_F)),
% 0.39/0.63      inference('sup-', [status(thm)], ['107', '108'])).
% 0.39/0.63  thf('147', plain,
% 0.39/0.63      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.39/0.63        | (v1_xboole_0 @ sk_D)
% 0.39/0.63        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.63        | (v1_xboole_0 @ sk_B)
% 0.39/0.63        | (v1_xboole_0 @ sk_A)
% 0.39/0.63        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 0.39/0.63            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.39/0.63            = (sk_F)))),
% 0.39/0.63      inference('demod', [status(thm)], ['145', '146'])).
% 0.39/0.63  thf('148', plain,
% 0.39/0.63      ((((k1_xboole_0) != (k1_xboole_0))
% 0.39/0.63        | ~ (v1_relat_1 @ sk_E)
% 0.39/0.63        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 0.39/0.63            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.39/0.63            = (sk_F))
% 0.39/0.63        | (v1_xboole_0 @ sk_A)
% 0.39/0.63        | (v1_xboole_0 @ sk_B)
% 0.39/0.63        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.63        | (v1_xboole_0 @ sk_D))),
% 0.39/0.63      inference('sup-', [status(thm)], ['117', '147'])).
% 0.39/0.63  thf('149', plain, ((v1_relat_1 @ sk_E)),
% 0.39/0.63      inference('sup-', [status(thm)], ['112', '113'])).
% 0.39/0.63  thf('150', plain,
% 0.39/0.63      ((((k1_xboole_0) != (k1_xboole_0))
% 0.39/0.63        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 0.39/0.63            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.39/0.63            = (sk_F))
% 0.39/0.63        | (v1_xboole_0 @ sk_A)
% 0.39/0.63        | (v1_xboole_0 @ sk_B)
% 0.39/0.63        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.63        | (v1_xboole_0 @ sk_D))),
% 0.39/0.63      inference('demod', [status(thm)], ['148', '149'])).
% 0.39/0.63  thf('151', plain,
% 0.39/0.63      (((v1_xboole_0 @ sk_D)
% 0.39/0.63        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.63        | (v1_xboole_0 @ sk_B)
% 0.39/0.63        | (v1_xboole_0 @ sk_A)
% 0.39/0.63        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 0.39/0.63            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.39/0.63            = (sk_F)))),
% 0.39/0.63      inference('simplify', [status(thm)], ['150'])).
% 0.39/0.63  thf('152', plain,
% 0.39/0.63      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 0.39/0.63          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.39/0.63          != (sk_F)))
% 0.39/0.63         <= (~
% 0.39/0.63             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 0.39/0.63                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.39/0.63                = (sk_F))))),
% 0.39/0.63      inference('split', [status(esa)], ['91'])).
% 0.39/0.63  thf('153', plain,
% 0.39/0.63      (((((sk_F) != (sk_F))
% 0.39/0.63         | (v1_xboole_0 @ sk_A)
% 0.39/0.63         | (v1_xboole_0 @ sk_B)
% 0.39/0.63         | (v1_xboole_0 @ sk_C_2)
% 0.39/0.63         | (v1_xboole_0 @ sk_D)))
% 0.39/0.63         <= (~
% 0.39/0.63             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 0.39/0.63                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.39/0.63                = (sk_F))))),
% 0.39/0.63      inference('sup-', [status(thm)], ['151', '152'])).
% 0.39/0.63  thf('154', plain,
% 0.39/0.63      ((((v1_xboole_0 @ sk_D)
% 0.39/0.63         | (v1_xboole_0 @ sk_C_2)
% 0.39/0.63         | (v1_xboole_0 @ sk_B)
% 0.39/0.63         | (v1_xboole_0 @ sk_A)))
% 0.39/0.63         <= (~
% 0.39/0.63             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 0.39/0.63                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.39/0.63                = (sk_F))))),
% 0.39/0.63      inference('simplify', [status(thm)], ['153'])).
% 0.39/0.63  thf('155', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('156', plain,
% 0.39/0.63      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_C_2)))
% 0.39/0.63         <= (~
% 0.39/0.63             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 0.39/0.63                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.39/0.63                = (sk_F))))),
% 0.39/0.63      inference('sup-', [status(thm)], ['154', '155'])).
% 0.39/0.63  thf('157', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('158', plain,
% 0.39/0.63      ((((v1_xboole_0 @ sk_C_2) | (v1_xboole_0 @ sk_B)))
% 0.39/0.63         <= (~
% 0.39/0.63             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 0.39/0.63                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.39/0.63                = (sk_F))))),
% 0.39/0.63      inference('clc', [status(thm)], ['156', '157'])).
% 0.39/0.63  thf('159', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('160', plain,
% 0.39/0.63      (((v1_xboole_0 @ sk_B))
% 0.39/0.63         <= (~
% 0.39/0.63             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 0.39/0.63                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.39/0.63                = (sk_F))))),
% 0.39/0.63      inference('clc', [status(thm)], ['158', '159'])).
% 0.39/0.63  thf('161', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('162', plain,
% 0.39/0.63      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 0.39/0.63          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.39/0.63          = (sk_F)))),
% 0.39/0.63      inference('sup-', [status(thm)], ['160', '161'])).
% 0.39/0.63  thf('163', plain,
% 0.39/0.63      (~
% 0.39/0.63       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 0.39/0.63          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_C_2)
% 0.39/0.63          = (sk_E))) | 
% 0.39/0.63       ~
% 0.39/0.63       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 0.39/0.63          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.39/0.63          = (sk_F))) | 
% 0.39/0.63       ~
% 0.39/0.63       (((k2_partfun1 @ sk_C_2 @ sk_B @ sk_E @ 
% 0.39/0.63          (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))
% 0.39/0.63          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.39/0.63             (k9_subset_1 @ sk_A @ sk_C_2 @ sk_D))))),
% 0.39/0.63      inference('split', [status(esa)], ['91'])).
% 0.39/0.63  thf('164', plain,
% 0.39/0.63      (~
% 0.39/0.63       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 0.39/0.63          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_C_2)
% 0.39/0.63          = (sk_E)))),
% 0.39/0.63      inference('sat_resolution*', [status(thm)], ['116', '162', '163'])).
% 0.39/0.63  thf('165', plain,
% 0.39/0.63      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_2 @ sk_D) @ sk_B @ 
% 0.39/0.63         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F) @ sk_C_2)
% 0.39/0.63         != (sk_E))),
% 0.39/0.63      inference('simpl_trail', [status(thm)], ['92', '164'])).
% 0.39/0.63  thf('166', plain,
% 0.39/0.63      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.39/0.63        | ~ (v1_funct_1 @ 
% 0.39/0.63             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_2 @ sk_D @ sk_E @ sk_F))
% 0.39/0.63        | (v1_xboole_0 @ sk_A)
% 0.39/0.63        | (v1_xboole_0 @ sk_B)
% 0.39/0.63        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.63        | (v1_xboole_0 @ sk_D))),
% 0.39/0.63      inference('simplify_reflect-', [status(thm)], ['90', '165'])).
% 0.39/0.63  thf('167', plain,
% 0.39/0.63      (((v1_xboole_0 @ sk_D)
% 0.39/0.63        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.63        | (v1_xboole_0 @ sk_B)
% 0.39/0.63        | (v1_xboole_0 @ sk_A)
% 0.39/0.63        | (v1_xboole_0 @ sk_D)
% 0.39/0.63        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.63        | (v1_xboole_0 @ sk_B)
% 0.39/0.63        | (v1_xboole_0 @ sk_A)
% 0.39/0.63        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.39/0.63            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.39/0.63      inference('sup-', [status(thm)], ['17', '166'])).
% 0.39/0.63  thf('168', plain,
% 0.39/0.63      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.39/0.63        | (v1_xboole_0 @ sk_A)
% 0.39/0.63        | (v1_xboole_0 @ sk_B)
% 0.39/0.63        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.63        | (v1_xboole_0 @ sk_D))),
% 0.39/0.63      inference('simplify', [status(thm)], ['167'])).
% 0.39/0.63  thf('169', plain,
% 0.39/0.63      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.39/0.63        | ~ (v1_relat_1 @ sk_F)
% 0.39/0.63        | (v1_xboole_0 @ sk_D)
% 0.39/0.63        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.63        | (v1_xboole_0 @ sk_B)
% 0.39/0.63        | (v1_xboole_0 @ sk_A))),
% 0.39/0.63      inference('sup-', [status(thm)], ['2', '168'])).
% 0.39/0.63  thf('170', plain, ((v1_relat_1 @ sk_F)),
% 0.39/0.63      inference('sup-', [status(thm)], ['107', '108'])).
% 0.39/0.63  thf('171', plain,
% 0.39/0.63      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.39/0.63        | (v1_xboole_0 @ sk_D)
% 0.39/0.63        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.63        | (v1_xboole_0 @ sk_B)
% 0.39/0.63        | (v1_xboole_0 @ sk_A))),
% 0.39/0.63      inference('demod', [status(thm)], ['169', '170'])).
% 0.39/0.63  thf('172', plain,
% 0.39/0.63      ((((k1_xboole_0) != (k1_xboole_0))
% 0.39/0.63        | ~ (v1_relat_1 @ sk_E)
% 0.39/0.63        | (v1_xboole_0 @ sk_A)
% 0.39/0.63        | (v1_xboole_0 @ sk_B)
% 0.39/0.63        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.63        | (v1_xboole_0 @ sk_D))),
% 0.39/0.63      inference('sup-', [status(thm)], ['1', '171'])).
% 0.39/0.63  thf('173', plain, ((v1_relat_1 @ sk_E)),
% 0.39/0.63      inference('sup-', [status(thm)], ['112', '113'])).
% 0.39/0.63  thf('174', plain,
% 0.39/0.63      ((((k1_xboole_0) != (k1_xboole_0))
% 0.39/0.63        | (v1_xboole_0 @ sk_A)
% 0.39/0.63        | (v1_xboole_0 @ sk_B)
% 0.39/0.63        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.63        | (v1_xboole_0 @ sk_D))),
% 0.39/0.63      inference('demod', [status(thm)], ['172', '173'])).
% 0.39/0.63  thf('175', plain,
% 0.39/0.63      (((v1_xboole_0 @ sk_D)
% 0.39/0.63        | (v1_xboole_0 @ sk_C_2)
% 0.39/0.63        | (v1_xboole_0 @ sk_B)
% 0.39/0.63        | (v1_xboole_0 @ sk_A))),
% 0.39/0.63      inference('simplify', [status(thm)], ['174'])).
% 0.39/0.63  thf('176', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('177', plain,
% 0.39/0.63      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_C_2))),
% 0.39/0.63      inference('sup-', [status(thm)], ['175', '176'])).
% 0.39/0.63  thf('178', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('179', plain, (((v1_xboole_0 @ sk_C_2) | (v1_xboole_0 @ sk_B))),
% 0.39/0.63      inference('clc', [status(thm)], ['177', '178'])).
% 0.39/0.63  thf('180', plain, (~ (v1_xboole_0 @ sk_C_2)),
% 0.39/0.63      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.39/0.63  thf('181', plain, ((v1_xboole_0 @ sk_B)),
% 0.39/0.63      inference('clc', [status(thm)], ['179', '180'])).
% 0.39/0.63  thf('182', plain, ($false), inference('demod', [status(thm)], ['0', '181'])).
% 0.39/0.63  
% 0.39/0.63  % SZS output end Refutation
% 0.39/0.63  
% 0.39/0.63  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
