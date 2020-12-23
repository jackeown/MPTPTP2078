%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Zr63DVPaao

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:00:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 301 expanded)
%              Number of leaves         :   33 (  98 expanded)
%              Depth                    :   20
%              Number of atoms          : 2394 (8991 expanded)
%              Number of equality atoms :   51 ( 182 expanded)
%              Maximal formula depth    :   21 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k5_funct_2_type,type,(
    k5_funct_2: $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k3_funct_2_type,type,(
    k3_funct_2: $i > $i > $i > $i > $i )).

thf(k4_funct_2_type,type,(
    k4_funct_2: $i > $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(t196_funct_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ~ ( v1_xboole_0 @ C )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ A @ ( k2_zfmisc_1 @ B @ C ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ A )
                     => ( ( k3_funct_2 @ A @ ( k2_zfmisc_1 @ B @ C ) @ D @ E )
                        = ( k4_tarski @ ( k3_funct_2 @ A @ B @ ( k4_funct_2 @ A @ B @ C @ D ) @ E ) @ ( k3_funct_2 @ A @ C @ ( k5_funct_2 @ A @ B @ C @ D ) @ E ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ~ ( v1_xboole_0 @ C )
               => ! [D: $i] :
                    ( ( ( v1_funct_1 @ D )
                      & ( v1_funct_2 @ D @ A @ ( k2_zfmisc_1 @ B @ C ) )
                      & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ A )
                       => ( ( k3_funct_2 @ A @ ( k2_zfmisc_1 @ B @ C ) @ D @ E )
                          = ( k4_tarski @ ( k3_funct_2 @ A @ B @ ( k4_funct_2 @ A @ B @ C @ D ) @ E ) @ ( k3_funct_2 @ A @ C @ ( k5_funct_2 @ A @ B @ C @ D ) @ E ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t196_funct_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k5_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B )
        & ~ ( v1_xboole_0 @ C )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )
     => ( ( v1_funct_1 @ ( k5_funct_2 @ A @ B @ C @ D ) )
        & ( v1_funct_2 @ ( k5_funct_2 @ A @ B @ C @ D ) @ A @ C )
        & ( m1_subset_1 @ ( k5_funct_2 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ) )).

thf('3',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ( v1_xboole_0 @ X24 )
      | ( v1_xboole_0 @ X25 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ X25 @ ( k2_zfmisc_1 @ X24 @ X23 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) )
      | ( v1_funct_1 @ ( k5_funct_2 @ X25 @ X24 @ X23 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_funct_2])).

thf('4',plain,
    ( ( v1_funct_1 @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_funct_1 @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ( v1_xboole_0 @ X24 )
      | ( v1_xboole_0 @ X25 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ X25 @ ( k2_zfmisc_1 @ X24 @ X23 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) )
      | ( v1_funct_2 @ ( k5_funct_2 @ X25 @ X24 @ X23 @ X26 ) @ X25 @ X23 ) ) ),
    inference(cnf,[status(esa)],[dt_k5_funct_2])).

thf('10',plain,
    ( ( v1_funct_2 @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_A @ sk_C )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( v1_funct_2 @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_A @ sk_C )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['10','11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( v1_xboole_0 @ X23 )
      | ( v1_xboole_0 @ X24 )
      | ( v1_xboole_0 @ X25 )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_funct_2 @ X26 @ X25 @ ( k2_zfmisc_1 @ X24 @ X23 ) )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ ( k2_zfmisc_1 @ X24 @ X23 ) ) ) )
      | ( m1_subset_1 @ ( k5_funct_2 @ X25 @ X24 @ X23 @ X26 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X23 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k5_funct_2])).

thf('16',plain,
    ( ( m1_subset_1 @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,
    ( ( m1_subset_1 @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['16','17','18'])).

thf(d7_funct_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ~ ( v1_xboole_0 @ C )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ A @ ( k2_zfmisc_1 @ B @ C ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ A @ C )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) )
                     => ( ( E
                          = ( k5_funct_2 @ A @ B @ C @ D ) )
                      <=> ! [F: $i] :
                            ( ( m1_subset_1 @ F @ A )
                           => ( ( k3_funct_2 @ A @ C @ E @ F )
                              = ( k2_mcart_1 @ ( k3_funct_2 @ A @ ( k2_zfmisc_1 @ B @ C ) @ D @ F ) ) ) ) ) ) ) ) ) ) )).

thf('20',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X17: $i,X18: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ~ ( v1_funct_1 @ X14 )
      | ~ ( v1_funct_2 @ X14 @ X15 @ ( k2_zfmisc_1 @ X13 @ X16 ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ ( k2_zfmisc_1 @ X13 @ X16 ) ) ) )
      | ( X17
       != ( k5_funct_2 @ X15 @ X13 @ X16 @ X14 ) )
      | ( ( k3_funct_2 @ X15 @ X16 @ X17 @ X18 )
        = ( k2_mcart_1 @ ( k3_funct_2 @ X15 @ ( k2_zfmisc_1 @ X13 @ X16 ) @ X14 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X18 @ X15 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( v1_funct_2 @ X17 @ X15 @ X16 )
      | ~ ( v1_funct_1 @ X17 )
      | ( v1_xboole_0 @ X16 )
      | ( v1_xboole_0 @ X15 ) ) ),
    inference(cnf,[status(esa)],[d7_funct_2])).

thf('21',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i,X18: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( v1_funct_1 @ ( k5_funct_2 @ X15 @ X13 @ X16 @ X14 ) )
      | ~ ( v1_funct_2 @ ( k5_funct_2 @ X15 @ X13 @ X16 @ X14 ) @ X15 @ X16 )
      | ~ ( m1_subset_1 @ ( k5_funct_2 @ X15 @ X13 @ X16 @ X14 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) ) )
      | ~ ( m1_subset_1 @ X18 @ X15 )
      | ( ( k3_funct_2 @ X15 @ X16 @ ( k5_funct_2 @ X15 @ X13 @ X16 @ X14 ) @ X18 )
        = ( k2_mcart_1 @ ( k3_funct_2 @ X15 @ ( k2_zfmisc_1 @ X13 @ X16 ) @ X14 @ X18 ) ) )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X15 @ ( k2_zfmisc_1 @ X13 @ X16 ) ) ) )
      | ~ ( v1_funct_2 @ X14 @ X15 @ ( k2_zfmisc_1 @ X13 @ X16 ) )
      | ~ ( v1_funct_1 @ X14 )
      | ( v1_xboole_0 @ X13 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
      | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) )
      | ( ( k3_funct_2 @ sk_A @ sk_C @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
        = ( k2_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( v1_funct_2 @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_A @ sk_C )
      | ~ ( v1_funct_1 @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['19','21'])).

thf('23',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( ( k3_funct_2 @ sk_A @ sk_C @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
        = ( k2_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( v1_funct_2 @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_A @ sk_C )
      | ~ ( v1_funct_1 @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['22','23','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ~ ( v1_funct_2 @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_A @ sk_C )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_C @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
        = ( k2_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_C @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
        = ( k2_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( v1_funct_1 @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['13','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_C @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
        = ( k2_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_C @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
        = ( k2_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['7','29'])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_C @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
        = ( k2_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['30'])).

thf('32',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k3_funct_2 @ sk_A @ sk_C @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E )
      = ( k2_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['1','31'])).

thf('33',plain,(
    m1_subset_1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
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

thf('35',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( v1_funct_1 @ X31 )
      | ( v1_xboole_0 @ X32 )
      | ~ ( m1_subset_1 @ X34 @ X32 )
      | ( ( k3_funct_2 @ X32 @ X33 @ X31 @ X34 )
        = ( k1_funct_1 @ X31 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k3_funct_2])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 )
        = ( k1_funct_1 @ sk_D @ X0 ) ) ) ),
    inference(clc,[status(thm)],['39','40'])).

thf('42',plain,
    ( ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ sk_E )
    = ( k1_funct_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['33','41'])).

thf('43',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k3_funct_2 @ sk_A @ sk_C @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E )
      = ( k2_mcart_1 @ ( k1_funct_1 @ sk_D @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['32','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k4_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B )
        & ~ ( v1_xboole_0 @ C )
        & ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ A @ ( k2_zfmisc_1 @ B @ C ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )
     => ( ( v1_funct_1 @ ( k4_funct_2 @ A @ B @ C @ D ) )
        & ( v1_funct_2 @ ( k4_funct_2 @ A @ B @ C @ D ) @ A @ B )
        & ( m1_subset_1 @ ( k4_funct_2 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('46',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ( v1_xboole_0 @ X20 )
      | ( v1_xboole_0 @ X21 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_2 @ X22 @ X21 @ ( k2_zfmisc_1 @ X20 @ X19 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) )
      | ( v1_funct_1 @ ( k4_funct_2 @ X21 @ X20 @ X19 @ X22 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_funct_2])).

thf('47',plain,
    ( ( v1_funct_1 @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v1_funct_1 @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ( v1_xboole_0 @ X20 )
      | ( v1_xboole_0 @ X21 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_2 @ X22 @ X21 @ ( k2_zfmisc_1 @ X20 @ X19 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) )
      | ( v1_funct_2 @ ( k4_funct_2 @ X21 @ X20 @ X19 @ X22 ) @ X21 @ X20 ) ) ),
    inference(cnf,[status(esa)],[dt_k4_funct_2])).

thf('53',plain,
    ( ( v1_funct_2 @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_A @ sk_B )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( v1_funct_2 @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_A @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['53','54','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ( v1_xboole_0 @ X19 )
      | ( v1_xboole_0 @ X20 )
      | ( v1_xboole_0 @ X21 )
      | ~ ( v1_funct_1 @ X22 )
      | ~ ( v1_funct_2 @ X22 @ X21 @ ( k2_zfmisc_1 @ X20 @ X19 ) )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ ( k2_zfmisc_1 @ X20 @ X19 ) ) ) )
      | ( m1_subset_1 @ ( k4_funct_2 @ X21 @ X20 @ X19 @ X22 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X20 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k4_funct_2])).

thf('59',plain,
    ( ( m1_subset_1 @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( m1_subset_1 @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf(d6_funct_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ~ ( v1_xboole_0 @ C )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ A @ ( k2_zfmisc_1 @ B @ C ) )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )
                 => ! [E: $i] :
                      ( ( ( v1_funct_1 @ E )
                        & ( v1_funct_2 @ E @ A @ B )
                        & ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
                     => ( ( E
                          = ( k4_funct_2 @ A @ B @ C @ D ) )
                      <=> ! [F: $i] :
                            ( ( m1_subset_1 @ F @ A )
                           => ( ( k3_funct_2 @ A @ B @ E @ F )
                              = ( k1_mcart_1 @ ( k3_funct_2 @ A @ ( k2_zfmisc_1 @ B @ C ) @ D @ F ) ) ) ) ) ) ) ) ) ) )).

thf('63',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( v1_xboole_0 @ X7 )
      | ~ ( v1_funct_1 @ X8 )
      | ~ ( v1_funct_2 @ X8 @ X9 @ ( k2_zfmisc_1 @ X7 @ X10 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ ( k2_zfmisc_1 @ X7 @ X10 ) ) ) )
      | ( X11
       != ( k4_funct_2 @ X9 @ X7 @ X10 @ X8 ) )
      | ( ( k3_funct_2 @ X9 @ X7 @ X11 @ X12 )
        = ( k1_mcart_1 @ ( k3_funct_2 @ X9 @ ( k2_zfmisc_1 @ X7 @ X10 ) @ X8 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X12 @ X9 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X7 ) ) )
      | ~ ( v1_funct_2 @ X11 @ X9 @ X7 )
      | ~ ( v1_funct_1 @ X11 )
      | ( v1_xboole_0 @ X10 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[d6_funct_2])).

thf('64',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X12: $i] :
      ( ( v1_xboole_0 @ X9 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( v1_funct_1 @ ( k4_funct_2 @ X9 @ X7 @ X10 @ X8 ) )
      | ~ ( v1_funct_2 @ ( k4_funct_2 @ X9 @ X7 @ X10 @ X8 ) @ X9 @ X7 )
      | ~ ( m1_subset_1 @ ( k4_funct_2 @ X9 @ X7 @ X10 @ X8 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X12 @ X9 )
      | ( ( k3_funct_2 @ X9 @ X7 @ ( k4_funct_2 @ X9 @ X7 @ X10 @ X8 ) @ X12 )
        = ( k1_mcart_1 @ ( k3_funct_2 @ X9 @ ( k2_zfmisc_1 @ X7 @ X10 ) @ X8 @ X12 ) ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ ( k2_zfmisc_1 @ X7 @ X10 ) ) ) )
      | ~ ( v1_funct_2 @ X8 @ X9 @ ( k2_zfmisc_1 @ X7 @ X10 ) )
      | ~ ( v1_funct_1 @ X8 )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_D )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
      | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) )
      | ( ( k3_funct_2 @ sk_A @ sk_B @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
        = ( k1_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( v1_funct_2 @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['62','64'])).

thf('66',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( ( k3_funct_2 @ sk_A @ sk_B @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
        = ( k1_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( v1_funct_2 @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['65','66','67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ~ ( v1_funct_2 @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_A @ sk_B )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_B @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
        = ( k1_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_B @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
        = ( k1_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( v1_funct_1 @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['56','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_B @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
        = ( k1_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_B @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
        = ( k1_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 ) ) )
      | ~ ( m1_subset_1 @ X0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['50','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( ( k3_funct_2 @ sk_A @ sk_B @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ X0 )
        = ( k1_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(simplify,[status(thm)],['73'])).

thf('75',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k3_funct_2 @ sk_A @ sk_B @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E )
      = ( k1_mcart_1 @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['44','74'])).

thf('76',plain,
    ( ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ sk_E )
    = ( k1_funct_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['33','41'])).

thf('77',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k3_funct_2 @ sk_A @ sk_B @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E )
      = ( k1_mcart_1 @ ( k1_funct_1 @ sk_D @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['75','76'])).

thf('78',plain,(
    ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ sk_E )
 != ( k4_tarski @ ( k3_funct_2 @ sk_A @ sk_B @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) @ ( k3_funct_2 @ sk_A @ sk_C @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,
    ( ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ sk_E )
    = ( k1_funct_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['33','41'])).

thf('80',plain,(
    ( k1_funct_1 @ sk_D @ sk_E )
 != ( k4_tarski @ ( k3_funct_2 @ sk_A @ sk_B @ ( k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) @ ( k3_funct_2 @ sk_A @ sk_C @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,
    ( ( ( k1_funct_1 @ sk_D @ sk_E )
     != ( k4_tarski @ ( k1_mcart_1 @ ( k1_funct_1 @ sk_D @ sk_E ) ) @ ( k3_funct_2 @ sk_A @ sk_C @ ( k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D ) @ sk_E ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['77','80'])).

thf('82',plain,
    ( ( ( k1_funct_1 @ sk_D @ sk_E )
     != ( k4_tarski @ ( k1_mcart_1 @ ( k1_funct_1 @ sk_D @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_funct_1 @ sk_D @ sk_E ) ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['43','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_E @ sk_A ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t189_funct_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ A )
             => ! [D: $i] :
                  ( ( ( v1_funct_1 @ D )
                    & ( v1_funct_2 @ D @ A @ B )
                    & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
                 => ( r2_hidden @ ( k3_funct_2 @ A @ B @ D @ C ) @ ( k2_relset_1 @ A @ B @ D ) ) ) ) ) ) )).

thf('85',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ( v1_xboole_0 @ X35 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X37 @ X35 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X35 ) ) )
      | ( r2_hidden @ ( k3_funct_2 @ X37 @ X35 @ X36 @ X38 ) @ ( k2_relset_1 @ X37 @ X35 @ X36 ) )
      | ~ ( m1_subset_1 @ X38 @ X37 )
      | ( v1_xboole_0 @ X37 ) ) ),
    inference(cnf,[status(esa)],[t189_funct_2])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r2_hidden @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 ) @ ( k2_relset_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D ) )
      | ~ ( v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
      | ~ ( v1_funct_1 @ sk_D )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('88',plain,(
    ! [X2: $i,X3: $i,X4: $i] :
      ( ( ( k2_relset_1 @ X3 @ X4 @ X2 )
        = ( k2_relat_1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X3 @ X4 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('89',plain,
    ( ( k2_relset_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D )
    = ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    v1_funct_2 @ sk_D @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ sk_A )
      | ( r2_hidden @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ X0 ) @ ( k2_relat_1 @ sk_D ) )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(demod,[status(thm)],['86','89','90','91'])).

thf('93',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ sk_E ) @ ( k2_relat_1 @ sk_D ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['83','92'])).

thf('94',plain,
    ( ( k3_funct_2 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) @ sk_D @ sk_E )
    = ( k1_funct_1 @ sk_D @ sk_E ) ),
    inference('sup-',[status(thm)],['33','41'])).

thf('95',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_E ) @ ( k2_relat_1 @ sk_D ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['93','94'])).

thf('96',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('97',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_E ) @ ( k2_relat_1 @ sk_D ) )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ),
    inference(clc,[status(thm)],['95','96'])).

thf(fc10_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('98',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ X1 )
      | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ),
    inference(cnf,[status(esa)],[fc10_subset_1])).

thf('99',plain,
    ( ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_E ) @ ( k2_relat_1 @ sk_D ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( r2_hidden @ ( k1_funct_1 @ sk_D @ sk_E ) @ ( k2_relat_1 @ sk_D ) ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    r2_hidden @ ( k1_funct_1 @ sk_D @ sk_E ) @ ( k2_relat_1 @ sk_D ) ),
    inference(clc,[status(thm)],['101','102'])).

thf(t23_mcart_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( r2_hidden @ A @ B )
       => ( A
          = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ) )).

thf('104',plain,(
    ! [X5: $i,X6: $i] :
      ( ( X5
        = ( k4_tarski @ ( k1_mcart_1 @ X5 ) @ ( k2_mcart_1 @ X5 ) ) )
      | ~ ( v1_relat_1 @ X6 )
      | ~ ( r2_hidden @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t23_mcart_1])).

thf('105',plain,
    ( ~ ( v1_relat_1 @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_funct_1 @ sk_D @ sk_E )
      = ( k4_tarski @ ( k1_mcart_1 @ ( k1_funct_1 @ sk_D @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_funct_1 @ sk_D @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['103','104'])).

thf('106',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ ( k2_zfmisc_1 @ sk_B @ sk_C ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc9_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) )
     => ( v1_relat_1 @ ( k2_relat_1 @ D ) ) ) )).

thf('107',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ ( k2_relat_1 @ X27 ) )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X28 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ) ),
    inference(cnf,[status(esa)],[fc9_relset_1])).

thf('108',plain,(
    v1_relat_1 @ ( k2_relat_1 @ sk_D ) ),
    inference('sup-',[status(thm)],['106','107'])).

thf('109',plain,
    ( ( k1_funct_1 @ sk_D @ sk_E )
    = ( k4_tarski @ ( k1_mcart_1 @ ( k1_funct_1 @ sk_D @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_funct_1 @ sk_D @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['105','108'])).

thf('110',plain,
    ( ( ( k1_funct_1 @ sk_D @ sk_E )
     != ( k1_funct_1 @ sk_D @ sk_E ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['82','109'])).

thf('111',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['110'])).

thf('112',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['111','112'])).

thf('114',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('115',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['113','114'])).

thf('116',plain,(
    $false ),
    inference(demod,[status(thm)],['0','115'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Zr63DVPaao
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:57:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.20/0.55  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.55  % Solved by: fo/fo7.sh
% 0.20/0.55  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.55  % done 108 iterations in 0.107s
% 0.20/0.55  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.55  % SZS output start Refutation
% 0.20/0.55  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.55  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.55  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.55  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.20/0.55  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.55  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.20/0.55  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.55  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.55  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.55  thf(k5_funct_2_type, type, k5_funct_2: $i > $i > $i > $i > $i).
% 0.20/0.55  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.55  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.55  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.55  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.55  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.20/0.55  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.55  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.55  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.55  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.20/0.55  thf(k3_funct_2_type, type, k3_funct_2: $i > $i > $i > $i > $i).
% 0.20/0.55  thf(k4_funct_2_type, type, k4_funct_2: $i > $i > $i > $i > $i).
% 0.20/0.55  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.55  thf(t196_funct_2, conjecture,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.20/0.55               ( ![D:$i]:
% 0.20/0.55                 ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.55                     ( v1_funct_2 @ D @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.20/0.55                     ( m1_subset_1 @
% 0.20/0.55                       D @ 
% 0.20/0.55                       ( k1_zfmisc_1 @
% 0.20/0.55                         ( k2_zfmisc_1 @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) =>
% 0.20/0.55                   ( ![E:$i]:
% 0.20/0.55                     ( ( m1_subset_1 @ E @ A ) =>
% 0.20/0.55                       ( ( k3_funct_2 @ A @ ( k2_zfmisc_1 @ B @ C ) @ D @ E ) =
% 0.20/0.55                         ( k4_tarski @
% 0.20/0.55                           ( k3_funct_2 @
% 0.20/0.55                             A @ B @ ( k4_funct_2 @ A @ B @ C @ D ) @ E ) @ 
% 0.20/0.55                           ( k3_funct_2 @
% 0.20/0.55                             A @ C @ ( k5_funct_2 @ A @ B @ C @ D ) @ E ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.55    (~( ![A:$i]:
% 0.20/0.55        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.55          ( ![B:$i]:
% 0.20/0.55            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.55              ( ![C:$i]:
% 0.20/0.55                ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.20/0.55                  ( ![D:$i]:
% 0.20/0.55                    ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.55                        ( v1_funct_2 @ D @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.20/0.55                        ( m1_subset_1 @
% 0.20/0.55                          D @ 
% 0.20/0.55                          ( k1_zfmisc_1 @
% 0.20/0.55                            ( k2_zfmisc_1 @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) =>
% 0.20/0.55                      ( ![E:$i]:
% 0.20/0.55                        ( ( m1_subset_1 @ E @ A ) =>
% 0.20/0.55                          ( ( k3_funct_2 @ A @ ( k2_zfmisc_1 @ B @ C ) @ D @ E ) =
% 0.20/0.55                            ( k4_tarski @
% 0.20/0.55                              ( k3_funct_2 @
% 0.20/0.55                                A @ B @ ( k4_funct_2 @ A @ B @ C @ D ) @ E ) @ 
% 0.20/0.55                              ( k3_funct_2 @
% 0.20/0.55                                A @ C @ ( k5_funct_2 @ A @ B @ C @ D ) @ E ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.55    inference('cnf.neg', [status(esa)], [t196_funct_2])).
% 0.20/0.55  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('1', plain, ((m1_subset_1 @ sk_E @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('2', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_D @ 
% 0.20/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(dt_k5_funct_2, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.55         ( ~( v1_xboole_0 @ C ) ) & ( v1_funct_1 @ D ) & 
% 0.20/0.55         ( v1_funct_2 @ D @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.20/0.55         ( m1_subset_1 @
% 0.20/0.55           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) =>
% 0.20/0.55       ( ( v1_funct_1 @ ( k5_funct_2 @ A @ B @ C @ D ) ) & 
% 0.20/0.55         ( v1_funct_2 @ ( k5_funct_2 @ A @ B @ C @ D ) @ A @ C ) & 
% 0.20/0.55         ( m1_subset_1 @
% 0.20/0.55           ( k5_funct_2 @ A @ B @ C @ D ) @ 
% 0.20/0.55           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) ))).
% 0.20/0.55  thf('3', plain,
% 0.20/0.55      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ X23)
% 0.20/0.55          | (v1_xboole_0 @ X24)
% 0.20/0.55          | (v1_xboole_0 @ X25)
% 0.20/0.55          | ~ (v1_funct_1 @ X26)
% 0.20/0.55          | ~ (v1_funct_2 @ X26 @ X25 @ (k2_zfmisc_1 @ X24 @ X23))
% 0.20/0.55          | ~ (m1_subset_1 @ X26 @ 
% 0.20/0.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ (k2_zfmisc_1 @ X24 @ X23))))
% 0.20/0.55          | (v1_funct_1 @ (k5_funct_2 @ X25 @ X24 @ X23 @ X26)))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k5_funct_2])).
% 0.20/0.55  thf('4', plain,
% 0.20/0.55      (((v1_funct_1 @ (k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.20/0.55        | ~ (v1_funct_2 @ sk_D @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))
% 0.20/0.55        | ~ (v1_funct_1 @ sk_D)
% 0.20/0.55        | (v1_xboole_0 @ sk_A)
% 0.20/0.55        | (v1_xboole_0 @ sk_B)
% 0.20/0.55        | (v1_xboole_0 @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['2', '3'])).
% 0.20/0.55  thf('5', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('6', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('7', plain,
% 0.20/0.55      (((v1_funct_1 @ (k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.20/0.55        | (v1_xboole_0 @ sk_A)
% 0.20/0.55        | (v1_xboole_0 @ sk_B)
% 0.20/0.55        | (v1_xboole_0 @ sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.20/0.55  thf('8', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_D @ 
% 0.20/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('9', plain,
% 0.20/0.55      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ X23)
% 0.20/0.55          | (v1_xboole_0 @ X24)
% 0.20/0.55          | (v1_xboole_0 @ X25)
% 0.20/0.55          | ~ (v1_funct_1 @ X26)
% 0.20/0.55          | ~ (v1_funct_2 @ X26 @ X25 @ (k2_zfmisc_1 @ X24 @ X23))
% 0.20/0.55          | ~ (m1_subset_1 @ X26 @ 
% 0.20/0.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ (k2_zfmisc_1 @ X24 @ X23))))
% 0.20/0.55          | (v1_funct_2 @ (k5_funct_2 @ X25 @ X24 @ X23 @ X26) @ X25 @ X23))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k5_funct_2])).
% 0.20/0.55  thf('10', plain,
% 0.20/0.55      (((v1_funct_2 @ (k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_A @ sk_C)
% 0.20/0.55        | ~ (v1_funct_2 @ sk_D @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))
% 0.20/0.55        | ~ (v1_funct_1 @ sk_D)
% 0.20/0.55        | (v1_xboole_0 @ sk_A)
% 0.20/0.55        | (v1_xboole_0 @ sk_B)
% 0.20/0.55        | (v1_xboole_0 @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['8', '9'])).
% 0.20/0.55  thf('11', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('12', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('13', plain,
% 0.20/0.55      (((v1_funct_2 @ (k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_A @ sk_C)
% 0.20/0.55        | (v1_xboole_0 @ sk_A)
% 0.20/0.55        | (v1_xboole_0 @ sk_B)
% 0.20/0.55        | (v1_xboole_0 @ sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['10', '11', '12'])).
% 0.20/0.55  thf('14', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_D @ 
% 0.20/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('15', plain,
% 0.20/0.55      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ X23)
% 0.20/0.55          | (v1_xboole_0 @ X24)
% 0.20/0.55          | (v1_xboole_0 @ X25)
% 0.20/0.55          | ~ (v1_funct_1 @ X26)
% 0.20/0.55          | ~ (v1_funct_2 @ X26 @ X25 @ (k2_zfmisc_1 @ X24 @ X23))
% 0.20/0.55          | ~ (m1_subset_1 @ X26 @ 
% 0.20/0.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ (k2_zfmisc_1 @ X24 @ X23))))
% 0.20/0.55          | (m1_subset_1 @ (k5_funct_2 @ X25 @ X24 @ X23 @ X26) @ 
% 0.20/0.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X23))))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k5_funct_2])).
% 0.20/0.55  thf('16', plain,
% 0.20/0.55      (((m1_subset_1 @ (k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.55         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))
% 0.20/0.55        | ~ (v1_funct_2 @ sk_D @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))
% 0.20/0.55        | ~ (v1_funct_1 @ sk_D)
% 0.20/0.55        | (v1_xboole_0 @ sk_A)
% 0.20/0.55        | (v1_xboole_0 @ sk_B)
% 0.20/0.55        | (v1_xboole_0 @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['14', '15'])).
% 0.20/0.55  thf('17', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('18', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('19', plain,
% 0.20/0.55      (((m1_subset_1 @ (k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.55         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_C)))
% 0.20/0.55        | (v1_xboole_0 @ sk_A)
% 0.20/0.55        | (v1_xboole_0 @ sk_B)
% 0.20/0.55        | (v1_xboole_0 @ sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['16', '17', '18'])).
% 0.20/0.55  thf(d7_funct_2, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.20/0.55               ( ![D:$i]:
% 0.20/0.55                 ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.55                     ( v1_funct_2 @ D @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.20/0.55                     ( m1_subset_1 @
% 0.20/0.55                       D @ 
% 0.20/0.55                       ( k1_zfmisc_1 @
% 0.20/0.55                         ( k2_zfmisc_1 @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) =>
% 0.20/0.55                   ( ![E:$i]:
% 0.20/0.55                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ C ) & 
% 0.20/0.55                         ( m1_subset_1 @
% 0.20/0.55                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) ) =>
% 0.20/0.55                       ( ( ( E ) = ( k5_funct_2 @ A @ B @ C @ D ) ) <=>
% 0.20/0.55                         ( ![F:$i]:
% 0.20/0.55                           ( ( m1_subset_1 @ F @ A ) =>
% 0.20/0.55                             ( ( k3_funct_2 @ A @ C @ E @ F ) =
% 0.20/0.55                               ( k2_mcart_1 @
% 0.20/0.55                                 ( k3_funct_2 @
% 0.20/0.55                                   A @ ( k2_zfmisc_1 @ B @ C ) @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf('20', plain,
% 0.20/0.55      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X17 : $i, X18 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ X13)
% 0.20/0.55          | ~ (v1_funct_1 @ X14)
% 0.20/0.55          | ~ (v1_funct_2 @ X14 @ X15 @ (k2_zfmisc_1 @ X13 @ X16))
% 0.20/0.55          | ~ (m1_subset_1 @ X14 @ 
% 0.20/0.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ (k2_zfmisc_1 @ X13 @ X16))))
% 0.20/0.55          | ((X17) != (k5_funct_2 @ X15 @ X13 @ X16 @ X14))
% 0.20/0.55          | ((k3_funct_2 @ X15 @ X16 @ X17 @ X18)
% 0.20/0.55              = (k2_mcart_1 @ 
% 0.20/0.55                 (k3_funct_2 @ X15 @ (k2_zfmisc_1 @ X13 @ X16) @ X14 @ X18)))
% 0.20/0.55          | ~ (m1_subset_1 @ X18 @ X15)
% 0.20/0.55          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.20/0.55          | ~ (v1_funct_2 @ X17 @ X15 @ X16)
% 0.20/0.55          | ~ (v1_funct_1 @ X17)
% 0.20/0.55          | (v1_xboole_0 @ X16)
% 0.20/0.55          | (v1_xboole_0 @ X15))),
% 0.20/0.55      inference('cnf', [status(esa)], [d7_funct_2])).
% 0.20/0.55  thf('21', plain,
% 0.20/0.55      (![X13 : $i, X14 : $i, X15 : $i, X16 : $i, X18 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ X15)
% 0.20/0.55          | (v1_xboole_0 @ X16)
% 0.20/0.55          | ~ (v1_funct_1 @ (k5_funct_2 @ X15 @ X13 @ X16 @ X14))
% 0.20/0.55          | ~ (v1_funct_2 @ (k5_funct_2 @ X15 @ X13 @ X16 @ X14) @ X15 @ X16)
% 0.20/0.55          | ~ (m1_subset_1 @ (k5_funct_2 @ X15 @ X13 @ X16 @ X14) @ 
% 0.20/0.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ X16)))
% 0.20/0.55          | ~ (m1_subset_1 @ X18 @ X15)
% 0.20/0.55          | ((k3_funct_2 @ X15 @ X16 @ (k5_funct_2 @ X15 @ X13 @ X16 @ X14) @ 
% 0.20/0.55              X18)
% 0.20/0.55              = (k2_mcart_1 @ 
% 0.20/0.55                 (k3_funct_2 @ X15 @ (k2_zfmisc_1 @ X13 @ X16) @ X14 @ X18)))
% 0.20/0.55          | ~ (m1_subset_1 @ X14 @ 
% 0.20/0.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X15 @ (k2_zfmisc_1 @ X13 @ X16))))
% 0.20/0.55          | ~ (v1_funct_2 @ X14 @ X15 @ (k2_zfmisc_1 @ X13 @ X16))
% 0.20/0.55          | ~ (v1_funct_1 @ X14)
% 0.20/0.55          | (v1_xboole_0 @ X13))),
% 0.20/0.55      inference('simplify', [status(thm)], ['20'])).
% 0.20/0.55  thf('22', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ sk_C)
% 0.20/0.55          | (v1_xboole_0 @ sk_B)
% 0.20/0.55          | (v1_xboole_0 @ sk_A)
% 0.20/0.55          | (v1_xboole_0 @ sk_B)
% 0.20/0.55          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.55          | ~ (v1_funct_2 @ sk_D @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))
% 0.20/0.55          | ~ (m1_subset_1 @ sk_D @ 
% 0.20/0.55               (k1_zfmisc_1 @ 
% 0.20/0.55                (k2_zfmisc_1 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))))
% 0.20/0.55          | ((k3_funct_2 @ sk_A @ sk_C @ 
% 0.20/0.55              (k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ X0)
% 0.20/0.55              = (k2_mcart_1 @ 
% 0.20/0.55                 (k3_funct_2 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_D @ X0)))
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.55          | ~ (v1_funct_2 @ (k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_A @ 
% 0.20/0.55               sk_C)
% 0.20/0.55          | ~ (v1_funct_1 @ (k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.20/0.55          | (v1_xboole_0 @ sk_C)
% 0.20/0.55          | (v1_xboole_0 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['19', '21'])).
% 0.20/0.55  thf('23', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('24', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('25', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_D @ 
% 0.20/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('26', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ sk_C)
% 0.20/0.55          | (v1_xboole_0 @ sk_B)
% 0.20/0.55          | (v1_xboole_0 @ sk_A)
% 0.20/0.55          | (v1_xboole_0 @ sk_B)
% 0.20/0.55          | ((k3_funct_2 @ sk_A @ sk_C @ 
% 0.20/0.55              (k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ X0)
% 0.20/0.55              = (k2_mcart_1 @ 
% 0.20/0.55                 (k3_funct_2 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_D @ X0)))
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.55          | ~ (v1_funct_2 @ (k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_A @ 
% 0.20/0.55               sk_C)
% 0.20/0.55          | ~ (v1_funct_1 @ (k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.20/0.55          | (v1_xboole_0 @ sk_C)
% 0.20/0.55          | (v1_xboole_0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['22', '23', '24', '25'])).
% 0.20/0.55  thf('27', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_funct_1 @ (k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.20/0.55          | ~ (v1_funct_2 @ (k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_A @ 
% 0.20/0.55               sk_C)
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.55          | ((k3_funct_2 @ sk_A @ sk_C @ 
% 0.20/0.55              (k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ X0)
% 0.20/0.55              = (k2_mcart_1 @ 
% 0.20/0.55                 (k3_funct_2 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_D @ X0)))
% 0.20/0.55          | (v1_xboole_0 @ sk_A)
% 0.20/0.55          | (v1_xboole_0 @ sk_B)
% 0.20/0.55          | (v1_xboole_0 @ sk_C))),
% 0.20/0.55      inference('simplify', [status(thm)], ['26'])).
% 0.20/0.55  thf('28', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ sk_C)
% 0.20/0.55          | (v1_xboole_0 @ sk_B)
% 0.20/0.55          | (v1_xboole_0 @ sk_A)
% 0.20/0.55          | (v1_xboole_0 @ sk_C)
% 0.20/0.55          | (v1_xboole_0 @ sk_B)
% 0.20/0.55          | (v1_xboole_0 @ sk_A)
% 0.20/0.55          | ((k3_funct_2 @ sk_A @ sk_C @ 
% 0.20/0.55              (k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ X0)
% 0.20/0.55              = (k2_mcart_1 @ 
% 0.20/0.55                 (k3_funct_2 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_D @ X0)))
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.55          | ~ (v1_funct_1 @ (k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['13', '27'])).
% 0.20/0.55  thf('29', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_funct_1 @ (k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.55          | ((k3_funct_2 @ sk_A @ sk_C @ 
% 0.20/0.55              (k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ X0)
% 0.20/0.55              = (k2_mcart_1 @ 
% 0.20/0.55                 (k3_funct_2 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_D @ X0)))
% 0.20/0.55          | (v1_xboole_0 @ sk_A)
% 0.20/0.55          | (v1_xboole_0 @ sk_B)
% 0.20/0.55          | (v1_xboole_0 @ sk_C))),
% 0.20/0.55      inference('simplify', [status(thm)], ['28'])).
% 0.20/0.55  thf('30', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ sk_C)
% 0.20/0.55          | (v1_xboole_0 @ sk_B)
% 0.20/0.55          | (v1_xboole_0 @ sk_A)
% 0.20/0.55          | (v1_xboole_0 @ sk_C)
% 0.20/0.55          | (v1_xboole_0 @ sk_B)
% 0.20/0.55          | (v1_xboole_0 @ sk_A)
% 0.20/0.55          | ((k3_funct_2 @ sk_A @ sk_C @ 
% 0.20/0.55              (k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ X0)
% 0.20/0.55              = (k2_mcart_1 @ 
% 0.20/0.55                 (k3_funct_2 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_D @ X0)))
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['7', '29'])).
% 0.20/0.55  thf('31', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.55          | ((k3_funct_2 @ sk_A @ sk_C @ 
% 0.20/0.55              (k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ X0)
% 0.20/0.55              = (k2_mcart_1 @ 
% 0.20/0.55                 (k3_funct_2 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_D @ X0)))
% 0.20/0.55          | (v1_xboole_0 @ sk_A)
% 0.20/0.55          | (v1_xboole_0 @ sk_B)
% 0.20/0.55          | (v1_xboole_0 @ sk_C))),
% 0.20/0.55      inference('simplify', [status(thm)], ['30'])).
% 0.20/0.55  thf('32', plain,
% 0.20/0.55      (((v1_xboole_0 @ sk_C)
% 0.20/0.55        | (v1_xboole_0 @ sk_B)
% 0.20/0.55        | (v1_xboole_0 @ sk_A)
% 0.20/0.55        | ((k3_funct_2 @ sk_A @ sk_C @ 
% 0.20/0.55            (k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)
% 0.20/0.55            = (k2_mcart_1 @ 
% 0.20/0.55               (k3_funct_2 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_D @ sk_E))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['1', '31'])).
% 0.20/0.55  thf('33', plain, ((m1_subset_1 @ sk_E @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('34', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_D @ 
% 0.20/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(redefinition_k3_funct_2, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_funct_1 @ C ) & 
% 0.20/0.55         ( v1_funct_2 @ C @ A @ B ) & 
% 0.20/0.55         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.20/0.55         ( m1_subset_1 @ D @ A ) ) =>
% 0.20/0.55       ( ( k3_funct_2 @ A @ B @ C @ D ) = ( k1_funct_1 @ C @ D ) ) ))).
% 0.20/0.55  thf('35', plain,
% 0.20/0.55      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.20/0.55          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 0.20/0.55          | ~ (v1_funct_1 @ X31)
% 0.20/0.55          | (v1_xboole_0 @ X32)
% 0.20/0.55          | ~ (m1_subset_1 @ X34 @ X32)
% 0.20/0.55          | ((k3_funct_2 @ X32 @ X33 @ X31 @ X34) = (k1_funct_1 @ X31 @ X34)))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k3_funct_2])).
% 0.20/0.55  thf('36', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k3_funct_2 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_D @ X0)
% 0.20/0.55            = (k1_funct_1 @ sk_D @ X0))
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.55          | (v1_xboole_0 @ sk_A)
% 0.20/0.55          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.55          | ~ (v1_funct_2 @ sk_D @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.55  thf('37', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('38', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('39', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (((k3_funct_2 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_D @ X0)
% 0.20/0.55            = (k1_funct_1 @ sk_D @ X0))
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.55          | (v1_xboole_0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.20/0.55  thf('40', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('41', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.55          | ((k3_funct_2 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_D @ X0)
% 0.20/0.55              = (k1_funct_1 @ sk_D @ X0)))),
% 0.20/0.55      inference('clc', [status(thm)], ['39', '40'])).
% 0.20/0.55  thf('42', plain,
% 0.20/0.55      (((k3_funct_2 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_D @ sk_E)
% 0.20/0.55         = (k1_funct_1 @ sk_D @ sk_E))),
% 0.20/0.55      inference('sup-', [status(thm)], ['33', '41'])).
% 0.20/0.55  thf('43', plain,
% 0.20/0.55      (((v1_xboole_0 @ sk_C)
% 0.20/0.55        | (v1_xboole_0 @ sk_B)
% 0.20/0.55        | (v1_xboole_0 @ sk_A)
% 0.20/0.55        | ((k3_funct_2 @ sk_A @ sk_C @ 
% 0.20/0.55            (k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)
% 0.20/0.55            = (k2_mcart_1 @ (k1_funct_1 @ sk_D @ sk_E))))),
% 0.20/0.55      inference('demod', [status(thm)], ['32', '42'])).
% 0.20/0.55  thf('44', plain, ((m1_subset_1 @ sk_E @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('45', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_D @ 
% 0.20/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(dt_k4_funct_2, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.20/0.55         ( ~( v1_xboole_0 @ C ) ) & ( v1_funct_1 @ D ) & 
% 0.20/0.55         ( v1_funct_2 @ D @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.20/0.55         ( m1_subset_1 @
% 0.20/0.55           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) =>
% 0.20/0.55       ( ( v1_funct_1 @ ( k4_funct_2 @ A @ B @ C @ D ) ) & 
% 0.20/0.55         ( v1_funct_2 @ ( k4_funct_2 @ A @ B @ C @ D ) @ A @ B ) & 
% 0.20/0.55         ( m1_subset_1 @
% 0.20/0.55           ( k4_funct_2 @ A @ B @ C @ D ) @ 
% 0.20/0.55           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.20/0.55  thf('46', plain,
% 0.20/0.55      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ X19)
% 0.20/0.55          | (v1_xboole_0 @ X20)
% 0.20/0.55          | (v1_xboole_0 @ X21)
% 0.20/0.55          | ~ (v1_funct_1 @ X22)
% 0.20/0.55          | ~ (v1_funct_2 @ X22 @ X21 @ (k2_zfmisc_1 @ X20 @ X19))
% 0.20/0.55          | ~ (m1_subset_1 @ X22 @ 
% 0.20/0.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ (k2_zfmisc_1 @ X20 @ X19))))
% 0.20/0.55          | (v1_funct_1 @ (k4_funct_2 @ X21 @ X20 @ X19 @ X22)))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k4_funct_2])).
% 0.20/0.55  thf('47', plain,
% 0.20/0.55      (((v1_funct_1 @ (k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.20/0.55        | ~ (v1_funct_2 @ sk_D @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))
% 0.20/0.55        | ~ (v1_funct_1 @ sk_D)
% 0.20/0.55        | (v1_xboole_0 @ sk_A)
% 0.20/0.55        | (v1_xboole_0 @ sk_B)
% 0.20/0.55        | (v1_xboole_0 @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['45', '46'])).
% 0.20/0.55  thf('48', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('49', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('50', plain,
% 0.20/0.55      (((v1_funct_1 @ (k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.20/0.55        | (v1_xboole_0 @ sk_A)
% 0.20/0.55        | (v1_xboole_0 @ sk_B)
% 0.20/0.55        | (v1_xboole_0 @ sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.20/0.55  thf('51', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_D @ 
% 0.20/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('52', plain,
% 0.20/0.55      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ X19)
% 0.20/0.55          | (v1_xboole_0 @ X20)
% 0.20/0.55          | (v1_xboole_0 @ X21)
% 0.20/0.55          | ~ (v1_funct_1 @ X22)
% 0.20/0.55          | ~ (v1_funct_2 @ X22 @ X21 @ (k2_zfmisc_1 @ X20 @ X19))
% 0.20/0.55          | ~ (m1_subset_1 @ X22 @ 
% 0.20/0.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ (k2_zfmisc_1 @ X20 @ X19))))
% 0.20/0.55          | (v1_funct_2 @ (k4_funct_2 @ X21 @ X20 @ X19 @ X22) @ X21 @ X20))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k4_funct_2])).
% 0.20/0.55  thf('53', plain,
% 0.20/0.55      (((v1_funct_2 @ (k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_A @ sk_B)
% 0.20/0.55        | ~ (v1_funct_2 @ sk_D @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))
% 0.20/0.55        | ~ (v1_funct_1 @ sk_D)
% 0.20/0.55        | (v1_xboole_0 @ sk_A)
% 0.20/0.55        | (v1_xboole_0 @ sk_B)
% 0.20/0.55        | (v1_xboole_0 @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.55  thf('54', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('55', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('56', plain,
% 0.20/0.55      (((v1_funct_2 @ (k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_A @ sk_B)
% 0.20/0.55        | (v1_xboole_0 @ sk_A)
% 0.20/0.55        | (v1_xboole_0 @ sk_B)
% 0.20/0.55        | (v1_xboole_0 @ sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['53', '54', '55'])).
% 0.20/0.55  thf('57', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_D @ 
% 0.20/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('58', plain,
% 0.20/0.55      (![X19 : $i, X20 : $i, X21 : $i, X22 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ X19)
% 0.20/0.55          | (v1_xboole_0 @ X20)
% 0.20/0.55          | (v1_xboole_0 @ X21)
% 0.20/0.55          | ~ (v1_funct_1 @ X22)
% 0.20/0.55          | ~ (v1_funct_2 @ X22 @ X21 @ (k2_zfmisc_1 @ X20 @ X19))
% 0.20/0.55          | ~ (m1_subset_1 @ X22 @ 
% 0.20/0.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ (k2_zfmisc_1 @ X20 @ X19))))
% 0.20/0.55          | (m1_subset_1 @ (k4_funct_2 @ X21 @ X20 @ X19 @ X22) @ 
% 0.20/0.55             (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X20))))),
% 0.20/0.55      inference('cnf', [status(esa)], [dt_k4_funct_2])).
% 0.20/0.55  thf('59', plain,
% 0.20/0.55      (((m1_subset_1 @ (k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.55         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.20/0.55        | ~ (v1_funct_2 @ sk_D @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))
% 0.20/0.55        | ~ (v1_funct_1 @ sk_D)
% 0.20/0.55        | (v1_xboole_0 @ sk_A)
% 0.20/0.55        | (v1_xboole_0 @ sk_B)
% 0.20/0.55        | (v1_xboole_0 @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['57', '58'])).
% 0.20/0.55  thf('60', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('61', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('62', plain,
% 0.20/0.55      (((m1_subset_1 @ (k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ 
% 0.20/0.55         (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B)))
% 0.20/0.55        | (v1_xboole_0 @ sk_A)
% 0.20/0.55        | (v1_xboole_0 @ sk_B)
% 0.20/0.55        | (v1_xboole_0 @ sk_C))),
% 0.20/0.55      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.20/0.55  thf(d6_funct_2, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( ~( v1_xboole_0 @ C ) ) =>
% 0.20/0.55               ( ![D:$i]:
% 0.20/0.55                 ( ( ( v1_funct_1 @ D ) & 
% 0.20/0.55                     ( v1_funct_2 @ D @ A @ ( k2_zfmisc_1 @ B @ C ) ) & 
% 0.20/0.55                     ( m1_subset_1 @
% 0.20/0.55                       D @ 
% 0.20/0.55                       ( k1_zfmisc_1 @
% 0.20/0.55                         ( k2_zfmisc_1 @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) =>
% 0.20/0.55                   ( ![E:$i]:
% 0.20/0.55                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ A @ B ) & 
% 0.20/0.55                         ( m1_subset_1 @
% 0.20/0.55                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.55                       ( ( ( E ) = ( k4_funct_2 @ A @ B @ C @ D ) ) <=>
% 0.20/0.55                         ( ![F:$i]:
% 0.20/0.55                           ( ( m1_subset_1 @ F @ A ) =>
% 0.20/0.55                             ( ( k3_funct_2 @ A @ B @ E @ F ) =
% 0.20/0.55                               ( k1_mcart_1 @
% 0.20/0.55                                 ( k3_funct_2 @
% 0.20/0.55                                   A @ ( k2_zfmisc_1 @ B @ C ) @ D @ F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf('63', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ X7)
% 0.20/0.55          | ~ (v1_funct_1 @ X8)
% 0.20/0.55          | ~ (v1_funct_2 @ X8 @ X9 @ (k2_zfmisc_1 @ X7 @ X10))
% 0.20/0.55          | ~ (m1_subset_1 @ X8 @ 
% 0.20/0.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ (k2_zfmisc_1 @ X7 @ X10))))
% 0.20/0.55          | ((X11) != (k4_funct_2 @ X9 @ X7 @ X10 @ X8))
% 0.20/0.55          | ((k3_funct_2 @ X9 @ X7 @ X11 @ X12)
% 0.20/0.55              = (k1_mcart_1 @ 
% 0.20/0.55                 (k3_funct_2 @ X9 @ (k2_zfmisc_1 @ X7 @ X10) @ X8 @ X12)))
% 0.20/0.55          | ~ (m1_subset_1 @ X12 @ X9)
% 0.20/0.55          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X7)))
% 0.20/0.55          | ~ (v1_funct_2 @ X11 @ X9 @ X7)
% 0.20/0.55          | ~ (v1_funct_1 @ X11)
% 0.20/0.55          | (v1_xboole_0 @ X10)
% 0.20/0.55          | (v1_xboole_0 @ X9))),
% 0.20/0.55      inference('cnf', [status(esa)], [d6_funct_2])).
% 0.20/0.55  thf('64', plain,
% 0.20/0.55      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X12 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ X9)
% 0.20/0.55          | (v1_xboole_0 @ X10)
% 0.20/0.55          | ~ (v1_funct_1 @ (k4_funct_2 @ X9 @ X7 @ X10 @ X8))
% 0.20/0.55          | ~ (v1_funct_2 @ (k4_funct_2 @ X9 @ X7 @ X10 @ X8) @ X9 @ X7)
% 0.20/0.55          | ~ (m1_subset_1 @ (k4_funct_2 @ X9 @ X7 @ X10 @ X8) @ 
% 0.20/0.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X7)))
% 0.20/0.55          | ~ (m1_subset_1 @ X12 @ X9)
% 0.20/0.55          | ((k3_funct_2 @ X9 @ X7 @ (k4_funct_2 @ X9 @ X7 @ X10 @ X8) @ X12)
% 0.20/0.55              = (k1_mcart_1 @ 
% 0.20/0.55                 (k3_funct_2 @ X9 @ (k2_zfmisc_1 @ X7 @ X10) @ X8 @ X12)))
% 0.20/0.55          | ~ (m1_subset_1 @ X8 @ 
% 0.20/0.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ (k2_zfmisc_1 @ X7 @ X10))))
% 0.20/0.55          | ~ (v1_funct_2 @ X8 @ X9 @ (k2_zfmisc_1 @ X7 @ X10))
% 0.20/0.55          | ~ (v1_funct_1 @ X8)
% 0.20/0.55          | (v1_xboole_0 @ X7))),
% 0.20/0.55      inference('simplify', [status(thm)], ['63'])).
% 0.20/0.55  thf('65', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ sk_C)
% 0.20/0.55          | (v1_xboole_0 @ sk_B)
% 0.20/0.55          | (v1_xboole_0 @ sk_A)
% 0.20/0.55          | (v1_xboole_0 @ sk_B)
% 0.20/0.55          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.55          | ~ (v1_funct_2 @ sk_D @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))
% 0.20/0.55          | ~ (m1_subset_1 @ sk_D @ 
% 0.20/0.55               (k1_zfmisc_1 @ 
% 0.20/0.55                (k2_zfmisc_1 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))))
% 0.20/0.55          | ((k3_funct_2 @ sk_A @ sk_B @ 
% 0.20/0.55              (k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ X0)
% 0.20/0.55              = (k1_mcart_1 @ 
% 0.20/0.55                 (k3_funct_2 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_D @ X0)))
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.55          | ~ (v1_funct_2 @ (k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_A @ 
% 0.20/0.55               sk_B)
% 0.20/0.55          | ~ (v1_funct_1 @ (k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.20/0.55          | (v1_xboole_0 @ sk_C)
% 0.20/0.55          | (v1_xboole_0 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['62', '64'])).
% 0.20/0.55  thf('66', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('67', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('68', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_D @ 
% 0.20/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('69', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ sk_C)
% 0.20/0.55          | (v1_xboole_0 @ sk_B)
% 0.20/0.55          | (v1_xboole_0 @ sk_A)
% 0.20/0.55          | (v1_xboole_0 @ sk_B)
% 0.20/0.55          | ((k3_funct_2 @ sk_A @ sk_B @ 
% 0.20/0.55              (k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ X0)
% 0.20/0.55              = (k1_mcart_1 @ 
% 0.20/0.55                 (k3_funct_2 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_D @ X0)))
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.55          | ~ (v1_funct_2 @ (k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_A @ 
% 0.20/0.55               sk_B)
% 0.20/0.55          | ~ (v1_funct_1 @ (k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.20/0.55          | (v1_xboole_0 @ sk_C)
% 0.20/0.55          | (v1_xboole_0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['65', '66', '67', '68'])).
% 0.20/0.55  thf('70', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_funct_1 @ (k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.20/0.55          | ~ (v1_funct_2 @ (k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_A @ 
% 0.20/0.55               sk_B)
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.55          | ((k3_funct_2 @ sk_A @ sk_B @ 
% 0.20/0.55              (k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ X0)
% 0.20/0.55              = (k1_mcart_1 @ 
% 0.20/0.55                 (k3_funct_2 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_D @ X0)))
% 0.20/0.55          | (v1_xboole_0 @ sk_A)
% 0.20/0.55          | (v1_xboole_0 @ sk_B)
% 0.20/0.55          | (v1_xboole_0 @ sk_C))),
% 0.20/0.55      inference('simplify', [status(thm)], ['69'])).
% 0.20/0.55  thf('71', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ sk_C)
% 0.20/0.55          | (v1_xboole_0 @ sk_B)
% 0.20/0.55          | (v1_xboole_0 @ sk_A)
% 0.20/0.55          | (v1_xboole_0 @ sk_C)
% 0.20/0.55          | (v1_xboole_0 @ sk_B)
% 0.20/0.55          | (v1_xboole_0 @ sk_A)
% 0.20/0.55          | ((k3_funct_2 @ sk_A @ sk_B @ 
% 0.20/0.55              (k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ X0)
% 0.20/0.55              = (k1_mcart_1 @ 
% 0.20/0.55                 (k3_funct_2 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_D @ X0)))
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.55          | ~ (v1_funct_1 @ (k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['56', '70'])).
% 0.20/0.55  thf('72', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (v1_funct_1 @ (k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D))
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.55          | ((k3_funct_2 @ sk_A @ sk_B @ 
% 0.20/0.55              (k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ X0)
% 0.20/0.55              = (k1_mcart_1 @ 
% 0.20/0.55                 (k3_funct_2 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_D @ X0)))
% 0.20/0.55          | (v1_xboole_0 @ sk_A)
% 0.20/0.55          | (v1_xboole_0 @ sk_B)
% 0.20/0.55          | (v1_xboole_0 @ sk_C))),
% 0.20/0.55      inference('simplify', [status(thm)], ['71'])).
% 0.20/0.55  thf('73', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ sk_C)
% 0.20/0.55          | (v1_xboole_0 @ sk_B)
% 0.20/0.55          | (v1_xboole_0 @ sk_A)
% 0.20/0.55          | (v1_xboole_0 @ sk_C)
% 0.20/0.55          | (v1_xboole_0 @ sk_B)
% 0.20/0.55          | (v1_xboole_0 @ sk_A)
% 0.20/0.55          | ((k3_funct_2 @ sk_A @ sk_B @ 
% 0.20/0.55              (k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ X0)
% 0.20/0.55              = (k1_mcart_1 @ 
% 0.20/0.55                 (k3_funct_2 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_D @ X0)))
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['50', '72'])).
% 0.20/0.55  thf('74', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.55          | ((k3_funct_2 @ sk_A @ sk_B @ 
% 0.20/0.55              (k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ X0)
% 0.20/0.55              = (k1_mcart_1 @ 
% 0.20/0.55                 (k3_funct_2 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_D @ X0)))
% 0.20/0.55          | (v1_xboole_0 @ sk_A)
% 0.20/0.55          | (v1_xboole_0 @ sk_B)
% 0.20/0.55          | (v1_xboole_0 @ sk_C))),
% 0.20/0.55      inference('simplify', [status(thm)], ['73'])).
% 0.20/0.55  thf('75', plain,
% 0.20/0.55      (((v1_xboole_0 @ sk_C)
% 0.20/0.55        | (v1_xboole_0 @ sk_B)
% 0.20/0.55        | (v1_xboole_0 @ sk_A)
% 0.20/0.55        | ((k3_funct_2 @ sk_A @ sk_B @ 
% 0.20/0.55            (k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)
% 0.20/0.55            = (k1_mcart_1 @ 
% 0.20/0.55               (k3_funct_2 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_D @ sk_E))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['44', '74'])).
% 0.20/0.55  thf('76', plain,
% 0.20/0.55      (((k3_funct_2 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_D @ sk_E)
% 0.20/0.55         = (k1_funct_1 @ sk_D @ sk_E))),
% 0.20/0.55      inference('sup-', [status(thm)], ['33', '41'])).
% 0.20/0.55  thf('77', plain,
% 0.20/0.55      (((v1_xboole_0 @ sk_C)
% 0.20/0.55        | (v1_xboole_0 @ sk_B)
% 0.20/0.55        | (v1_xboole_0 @ sk_A)
% 0.20/0.55        | ((k3_funct_2 @ sk_A @ sk_B @ 
% 0.20/0.55            (k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)
% 0.20/0.55            = (k1_mcart_1 @ (k1_funct_1 @ sk_D @ sk_E))))),
% 0.20/0.55      inference('demod', [status(thm)], ['75', '76'])).
% 0.20/0.55  thf('78', plain,
% 0.20/0.55      (((k3_funct_2 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_D @ sk_E)
% 0.20/0.55         != (k4_tarski @ 
% 0.20/0.55             (k3_funct_2 @ sk_A @ sk_B @ 
% 0.20/0.55              (k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E) @ 
% 0.20/0.55             (k3_funct_2 @ sk_A @ sk_C @ 
% 0.20/0.55              (k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('79', plain,
% 0.20/0.55      (((k3_funct_2 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_D @ sk_E)
% 0.20/0.55         = (k1_funct_1 @ sk_D @ sk_E))),
% 0.20/0.55      inference('sup-', [status(thm)], ['33', '41'])).
% 0.20/0.55  thf('80', plain,
% 0.20/0.55      (((k1_funct_1 @ sk_D @ sk_E)
% 0.20/0.55         != (k4_tarski @ 
% 0.20/0.55             (k3_funct_2 @ sk_A @ sk_B @ 
% 0.20/0.55              (k4_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E) @ 
% 0.20/0.55             (k3_funct_2 @ sk_A @ sk_C @ 
% 0.20/0.55              (k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))),
% 0.20/0.55      inference('demod', [status(thm)], ['78', '79'])).
% 0.20/0.55  thf('81', plain,
% 0.20/0.55      ((((k1_funct_1 @ sk_D @ sk_E)
% 0.20/0.55          != (k4_tarski @ (k1_mcart_1 @ (k1_funct_1 @ sk_D @ sk_E)) @ 
% 0.20/0.55              (k3_funct_2 @ sk_A @ sk_C @ 
% 0.20/0.55               (k5_funct_2 @ sk_A @ sk_B @ sk_C @ sk_D) @ sk_E)))
% 0.20/0.55        | (v1_xboole_0 @ sk_A)
% 0.20/0.55        | (v1_xboole_0 @ sk_B)
% 0.20/0.55        | (v1_xboole_0 @ sk_C))),
% 0.20/0.55      inference('sup-', [status(thm)], ['77', '80'])).
% 0.20/0.55  thf('82', plain,
% 0.20/0.55      ((((k1_funct_1 @ sk_D @ sk_E)
% 0.20/0.55          != (k4_tarski @ (k1_mcart_1 @ (k1_funct_1 @ sk_D @ sk_E)) @ 
% 0.20/0.55              (k2_mcart_1 @ (k1_funct_1 @ sk_D @ sk_E))))
% 0.20/0.55        | (v1_xboole_0 @ sk_A)
% 0.20/0.55        | (v1_xboole_0 @ sk_B)
% 0.20/0.55        | (v1_xboole_0 @ sk_C)
% 0.20/0.55        | (v1_xboole_0 @ sk_C)
% 0.20/0.55        | (v1_xboole_0 @ sk_B)
% 0.20/0.55        | (v1_xboole_0 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['43', '81'])).
% 0.20/0.55  thf('83', plain, ((m1_subset_1 @ sk_E @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('84', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_D @ 
% 0.20/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(t189_funct_2, axiom,
% 0.20/0.55    (![A:$i]:
% 0.20/0.55     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.55       ( ![B:$i]:
% 0.20/0.55         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.55           ( ![C:$i]:
% 0.20/0.55             ( ( m1_subset_1 @ C @ A ) =>
% 0.20/0.55               ( ![D:$i]:
% 0.20/0.55                 ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.20/0.55                     ( m1_subset_1 @
% 0.20/0.55                       D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.20/0.55                   ( r2_hidden @
% 0.20/0.55                     ( k3_funct_2 @ A @ B @ D @ C ) @ 
% 0.20/0.55                     ( k2_relset_1 @ A @ B @ D ) ) ) ) ) ) ) ) ))).
% 0.20/0.55  thf('85', plain,
% 0.20/0.55      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ X35)
% 0.20/0.55          | ~ (v1_funct_1 @ X36)
% 0.20/0.55          | ~ (v1_funct_2 @ X36 @ X37 @ X35)
% 0.20/0.55          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X35)))
% 0.20/0.55          | (r2_hidden @ (k3_funct_2 @ X37 @ X35 @ X36 @ X38) @ 
% 0.20/0.55             (k2_relset_1 @ X37 @ X35 @ X36))
% 0.20/0.55          | ~ (m1_subset_1 @ X38 @ X37)
% 0.20/0.55          | (v1_xboole_0 @ X37))),
% 0.20/0.55      inference('cnf', [status(esa)], [t189_funct_2])).
% 0.20/0.55  thf('86', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ sk_A)
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.55          | (r2_hidden @ 
% 0.20/0.55             (k3_funct_2 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_D @ X0) @ 
% 0.20/0.55             (k2_relset_1 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_D))
% 0.20/0.55          | ~ (v1_funct_2 @ sk_D @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))
% 0.20/0.55          | ~ (v1_funct_1 @ sk_D)
% 0.20/0.55          | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.20/0.55      inference('sup-', [status(thm)], ['84', '85'])).
% 0.20/0.55  thf('87', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_D @ 
% 0.20/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i]:
% 0.20/0.55     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.55       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.55  thf('88', plain,
% 0.20/0.55      (![X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.55         (((k2_relset_1 @ X3 @ X4 @ X2) = (k2_relat_1 @ X2))
% 0.20/0.55          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X3 @ X4))))),
% 0.20/0.55      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.55  thf('89', plain,
% 0.20/0.55      (((k2_relset_1 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_D)
% 0.20/0.55         = (k2_relat_1 @ sk_D))),
% 0.20/0.55      inference('sup-', [status(thm)], ['87', '88'])).
% 0.20/0.55  thf('90', plain, ((v1_funct_2 @ sk_D @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('91', plain, ((v1_funct_1 @ sk_D)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('92', plain,
% 0.20/0.55      (![X0 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ sk_A)
% 0.20/0.55          | ~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.55          | (r2_hidden @ 
% 0.20/0.55             (k3_funct_2 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_D @ X0) @ 
% 0.20/0.55             (k2_relat_1 @ sk_D))
% 0.20/0.55          | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.20/0.55      inference('demod', [status(thm)], ['86', '89', '90', '91'])).
% 0.20/0.55  thf('93', plain,
% 0.20/0.55      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C))
% 0.20/0.55        | (r2_hidden @ 
% 0.20/0.55           (k3_funct_2 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_D @ sk_E) @ 
% 0.20/0.55           (k2_relat_1 @ sk_D))
% 0.20/0.55        | (v1_xboole_0 @ sk_A))),
% 0.20/0.55      inference('sup-', [status(thm)], ['83', '92'])).
% 0.20/0.55  thf('94', plain,
% 0.20/0.55      (((k3_funct_2 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C) @ sk_D @ sk_E)
% 0.20/0.55         = (k1_funct_1 @ sk_D @ sk_E))),
% 0.20/0.55      inference('sup-', [status(thm)], ['33', '41'])).
% 0.20/0.55  thf('95', plain,
% 0.20/0.55      (((v1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C))
% 0.20/0.55        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_E) @ (k2_relat_1 @ sk_D))
% 0.20/0.55        | (v1_xboole_0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['93', '94'])).
% 0.20/0.55  thf('96', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('97', plain,
% 0.20/0.55      (((r2_hidden @ (k1_funct_1 @ sk_D @ sk_E) @ (k2_relat_1 @ sk_D))
% 0.20/0.55        | (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B @ sk_C)))),
% 0.20/0.55      inference('clc', [status(thm)], ['95', '96'])).
% 0.20/0.55  thf(fc10_subset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.20/0.55       ( ~( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) ))).
% 0.20/0.55  thf('98', plain,
% 0.20/0.55      (![X0 : $i, X1 : $i]:
% 0.20/0.55         ((v1_xboole_0 @ X0)
% 0.20/0.55          | (v1_xboole_0 @ X1)
% 0.20/0.55          | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ X0 @ X1)))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc10_subset_1])).
% 0.20/0.55  thf('99', plain,
% 0.20/0.55      (((r2_hidden @ (k1_funct_1 @ sk_D @ sk_E) @ (k2_relat_1 @ sk_D))
% 0.20/0.55        | (v1_xboole_0 @ sk_C)
% 0.20/0.55        | (v1_xboole_0 @ sk_B))),
% 0.20/0.55      inference('sup-', [status(thm)], ['97', '98'])).
% 0.20/0.55  thf('100', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('101', plain,
% 0.20/0.55      (((v1_xboole_0 @ sk_B)
% 0.20/0.55        | (r2_hidden @ (k1_funct_1 @ sk_D @ sk_E) @ (k2_relat_1 @ sk_D)))),
% 0.20/0.55      inference('clc', [status(thm)], ['99', '100'])).
% 0.20/0.55  thf('102', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('103', plain,
% 0.20/0.55      ((r2_hidden @ (k1_funct_1 @ sk_D @ sk_E) @ (k2_relat_1 @ sk_D))),
% 0.20/0.55      inference('clc', [status(thm)], ['101', '102'])).
% 0.20/0.55  thf(t23_mcart_1, axiom,
% 0.20/0.55    (![A:$i,B:$i]:
% 0.20/0.55     ( ( v1_relat_1 @ B ) =>
% 0.20/0.55       ( ( r2_hidden @ A @ B ) =>
% 0.20/0.55         ( ( A ) = ( k4_tarski @ ( k1_mcart_1 @ A ) @ ( k2_mcart_1 @ A ) ) ) ) ))).
% 0.20/0.55  thf('104', plain,
% 0.20/0.55      (![X5 : $i, X6 : $i]:
% 0.20/0.55         (((X5) = (k4_tarski @ (k1_mcart_1 @ X5) @ (k2_mcart_1 @ X5)))
% 0.20/0.55          | ~ (v1_relat_1 @ X6)
% 0.20/0.55          | ~ (r2_hidden @ X5 @ X6))),
% 0.20/0.55      inference('cnf', [status(esa)], [t23_mcart_1])).
% 0.20/0.55  thf('105', plain,
% 0.20/0.55      ((~ (v1_relat_1 @ (k2_relat_1 @ sk_D))
% 0.20/0.55        | ((k1_funct_1 @ sk_D @ sk_E)
% 0.20/0.55            = (k4_tarski @ (k1_mcart_1 @ (k1_funct_1 @ sk_D @ sk_E)) @ 
% 0.20/0.55               (k2_mcart_1 @ (k1_funct_1 @ sk_D @ sk_E)))))),
% 0.20/0.55      inference('sup-', [status(thm)], ['103', '104'])).
% 0.20/0.55  thf('106', plain,
% 0.20/0.55      ((m1_subset_1 @ sk_D @ 
% 0.20/0.55        (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ (k2_zfmisc_1 @ sk_B @ sk_C))))),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf(fc9_relset_1, axiom,
% 0.20/0.55    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.55     ( ( m1_subset_1 @
% 0.20/0.55         D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ ( k2_zfmisc_1 @ B @ C ) ) ) ) =>
% 0.20/0.55       ( v1_relat_1 @ ( k2_relat_1 @ D ) ) ))).
% 0.20/0.55  thf('107', plain,
% 0.20/0.55      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.55         ((v1_relat_1 @ (k2_relat_1 @ X27))
% 0.20/0.55          | ~ (m1_subset_1 @ X27 @ 
% 0.20/0.55               (k1_zfmisc_1 @ (k2_zfmisc_1 @ X28 @ (k2_zfmisc_1 @ X29 @ X30)))))),
% 0.20/0.55      inference('cnf', [status(esa)], [fc9_relset_1])).
% 0.20/0.55  thf('108', plain, ((v1_relat_1 @ (k2_relat_1 @ sk_D))),
% 0.20/0.55      inference('sup-', [status(thm)], ['106', '107'])).
% 0.20/0.55  thf('109', plain,
% 0.20/0.55      (((k1_funct_1 @ sk_D @ sk_E)
% 0.20/0.55         = (k4_tarski @ (k1_mcart_1 @ (k1_funct_1 @ sk_D @ sk_E)) @ 
% 0.20/0.55            (k2_mcart_1 @ (k1_funct_1 @ sk_D @ sk_E))))),
% 0.20/0.55      inference('demod', [status(thm)], ['105', '108'])).
% 0.20/0.55  thf('110', plain,
% 0.20/0.55      ((((k1_funct_1 @ sk_D @ sk_E) != (k1_funct_1 @ sk_D @ sk_E))
% 0.20/0.55        | (v1_xboole_0 @ sk_A)
% 0.20/0.55        | (v1_xboole_0 @ sk_B)
% 0.20/0.55        | (v1_xboole_0 @ sk_C)
% 0.20/0.55        | (v1_xboole_0 @ sk_C)
% 0.20/0.55        | (v1_xboole_0 @ sk_B)
% 0.20/0.55        | (v1_xboole_0 @ sk_A))),
% 0.20/0.55      inference('demod', [status(thm)], ['82', '109'])).
% 0.20/0.55  thf('111', plain,
% 0.20/0.55      (((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.20/0.55      inference('simplify', [status(thm)], ['110'])).
% 0.20/0.55  thf('112', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('113', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B))),
% 0.20/0.55      inference('clc', [status(thm)], ['111', '112'])).
% 0.20/0.55  thf('114', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.20/0.55      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.55  thf('115', plain, ((v1_xboole_0 @ sk_B)),
% 0.20/0.55      inference('clc', [status(thm)], ['113', '114'])).
% 0.20/0.55  thf('116', plain, ($false), inference('demod', [status(thm)], ['0', '115'])).
% 0.20/0.55  
% 0.20/0.55  % SZS output end Refutation
% 0.20/0.55  
% 0.20/0.56  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
