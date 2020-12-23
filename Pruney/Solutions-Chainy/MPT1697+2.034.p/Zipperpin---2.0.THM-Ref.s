%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0zo3ksrd4G

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:58 EST 2020

% Result     : Theorem 0.52s
% Output     : Refutation 0.52s
% Verified   : 
% Statistics : Number of formulae       :  311 (1409 expanded)
%              Number of leaves         :   43 ( 413 expanded)
%              Depth                    :   46
%              Number of atoms          : 4890 (57102 expanded)
%              Number of equality atoms :  155 (1751 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

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

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('1',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r1_tarski @ X7 @ X8 )
      | ( X7 != X8 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('2',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X21 ) @ X22 )
      | ( v4_relat_1 @ X21 @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
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
    ! [X26: $i,X27: $i] :
      ( ( X26
        = ( k7_relat_1 @ X26 @ X27 ) )
      | ~ ( v4_relat_1 @ X26 @ X27 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
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

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('8',plain,(
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

thf('9',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_xboole_0 @ X3 @ X4 )
      | ( r2_hidden @ ( sk_C @ X4 @ X3 ) @ X4 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('10',plain,(
    ! [X8: $i] :
      ( r1_tarski @ X8 @ X8 ) ),
    inference(simplify,[status(thm)],['1'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X15: $i,X17: $i] :
      ( ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X17 ) )
      | ~ ( r1_tarski @ X15 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('13',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( r2_hidden @ X18 @ X19 )
      | ~ ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['8','15'])).

thf(t207_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r1_xboole_0 @ A @ B )
       => ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B )
          = k1_xboole_0 ) ) ) )).

thf('17',plain,(
    ! [X23: $i,X24: $i,X25: $i] :
      ( ~ ( r1_xboole_0 @ X23 @ X24 )
      | ~ ( v1_relat_1 @ X25 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X25 @ X23 ) @ X24 )
        = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t207_relat_1])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
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

thf('24',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X46 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) )
      | ( v1_xboole_0 @ X47 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X48 ) )
      | ( v1_xboole_0 @ X45 )
      | ( v1_xboole_0 @ X46 )
      | ( v1_xboole_0 @ X48 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X47 @ X46 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X48 @ X46 @ X45 @ X47 @ X44 @ X49 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('25',plain,(
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
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
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
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
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
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['29','30','31'])).

thf('33',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['21','32'])).

thf('34',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('36',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X46 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) )
      | ( v1_xboole_0 @ X47 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X48 ) )
      | ( v1_xboole_0 @ X45 )
      | ( v1_xboole_0 @ X46 )
      | ( v1_xboole_0 @ X48 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X47 @ X46 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X48 @ X46 @ X45 @ X47 @ X44 @ X49 ) @ ( k4_subset_1 @ X48 @ X45 @ X47 ) @ X46 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('40',plain,(
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
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
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
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
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
    inference('sup-',[status(thm)],['37','43'])).

thf('45',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_D ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['44','45','46'])).

thf('48',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['36','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('52',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X44: $i,X45: $i,X46: $i,X47: $i,X48: $i,X49: $i] :
      ( ~ ( m1_subset_1 @ X44 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X45 @ X46 ) ) )
      | ~ ( v1_funct_2 @ X44 @ X45 @ X46 )
      | ~ ( v1_funct_1 @ X44 )
      | ~ ( m1_subset_1 @ X47 @ ( k1_zfmisc_1 @ X48 ) )
      | ( v1_xboole_0 @ X47 )
      | ~ ( m1_subset_1 @ X45 @ ( k1_zfmisc_1 @ X48 ) )
      | ( v1_xboole_0 @ X45 )
      | ( v1_xboole_0 @ X46 )
      | ( v1_xboole_0 @ X48 )
      | ~ ( v1_funct_1 @ X49 )
      | ~ ( v1_funct_2 @ X49 @ X47 @ X46 )
      | ~ ( m1_subset_1 @ X49 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X47 @ X46 ) ) )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X48 @ X46 @ X45 @ X47 @ X44 @ X49 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X48 @ X45 @ X47 ) @ X46 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('55',plain,(
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
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
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
    inference(demod,[status(thm)],['55','56','57'])).

thf('59',plain,(
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
    inference('sup-',[status(thm)],['52','58'])).

thf('60',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_D ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['59','60','61'])).

thf('63',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['51','62'])).

thf('64',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['63','64'])).

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

thf('66',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( v1_xboole_0 @ X37 )
      | ( v1_xboole_0 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X38 @ X37 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ( X43
       != ( k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X39 @ X42 @ X38 ) @ X37 @ X43 @ X42 )
        = X41 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X39 @ X42 @ X38 ) @ X37 ) ) )
      | ~ ( v1_funct_2 @ X43 @ ( k4_subset_1 @ X39 @ X42 @ X38 ) @ X37 )
      | ~ ( v1_funct_1 @ X43 )
      | ( ( k2_partfun1 @ X42 @ X37 @ X41 @ ( k9_subset_1 @ X39 @ X42 @ X38 ) )
       != ( k2_partfun1 @ X38 @ X37 @ X40 @ ( k9_subset_1 @ X39 @ X42 @ X38 ) ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X37 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X39 ) )
      | ( v1_xboole_0 @ X42 )
      | ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('67',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( v1_xboole_0 @ X39 )
      | ( v1_xboole_0 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X37 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X37 ) ) )
      | ( ( k2_partfun1 @ X42 @ X37 @ X41 @ ( k9_subset_1 @ X39 @ X42 @ X38 ) )
       != ( k2_partfun1 @ X38 @ X37 @ X40 @ ( k9_subset_1 @ X39 @ X42 @ X38 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40 ) @ ( k4_subset_1 @ X39 @ X42 @ X38 ) @ X37 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X39 @ X42 @ X38 ) @ X37 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X39 @ X42 @ X38 ) @ X37 @ ( k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40 ) @ X42 )
        = X41 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ( v1_xboole_0 @ X38 )
      | ( v1_xboole_0 @ X37 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,
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
    inference('sup-',[status(thm)],['65','67'])).

thf('69',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('71',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('73',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('74',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('76',plain,(
    r1_subset_1 @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r1_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ( ( r1_subset_1 @ A @ B )
      <=> ( r1_xboole_0 @ A @ B ) ) ) )).

thf('77',plain,(
    ! [X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X28 )
      | ( v1_xboole_0 @ X29 )
      | ( r1_xboole_0 @ X28 @ X29 )
      | ~ ( r1_subset_1 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_subset_1])).

thf('78',plain,
    ( ( r1_xboole_0 @ sk_C_1 @ sk_D )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('80',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r1_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(clc,[status(thm)],['78','79'])).

thf('81',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_D ),
    inference(clc,[status(thm)],['80','81'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('83',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('84',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['82','83'])).

thf('85',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('86',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ( ( k2_partfun1 @ X34 @ X35 @ X33 @ X36 )
        = ( k7_relat_1 @ X33 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('91',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
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
    inference(demod,[status(thm)],['55','56','57'])).

thf('93',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_C_1 ) @ sk_B ) ) ) ) ),
    inference('sup-',[status(thm)],['91','92'])).

thf('94',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_C_1 ) @ sk_B ) ) ) ) ),
    inference(demod,[status(thm)],['93','94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_C_1 ) @ sk_B ) ) )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['90','97'])).

thf('99',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['98'])).

thf('100',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('101',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( m1_subset_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B ) ) ) ),
    inference(clc,[status(thm)],['99','100'])).

thf('102',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('103',plain,(
    m1_subset_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('104',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i,X43: $i] :
      ( ( v1_xboole_0 @ X37 )
      | ( v1_xboole_0 @ X38 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( v1_funct_2 @ X40 @ X38 @ X37 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ( X43
       != ( k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X39 @ X42 @ X38 ) @ X37 @ X43 @ X38 )
        = X40 )
      | ~ ( m1_subset_1 @ X43 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X39 @ X42 @ X38 ) @ X37 ) ) )
      | ~ ( v1_funct_2 @ X43 @ ( k4_subset_1 @ X39 @ X42 @ X38 ) @ X37 )
      | ~ ( v1_funct_1 @ X43 )
      | ( ( k2_partfun1 @ X42 @ X37 @ X41 @ ( k9_subset_1 @ X39 @ X42 @ X38 ) )
       != ( k2_partfun1 @ X38 @ X37 @ X40 @ ( k9_subset_1 @ X39 @ X42 @ X38 ) ) )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X37 )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X39 ) )
      | ( v1_xboole_0 @ X42 )
      | ( v1_xboole_0 @ X39 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('105',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( v1_xboole_0 @ X39 )
      | ( v1_xboole_0 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X37 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X37 ) ) )
      | ( ( k2_partfun1 @ X42 @ X37 @ X41 @ ( k9_subset_1 @ X39 @ X42 @ X38 ) )
       != ( k2_partfun1 @ X38 @ X37 @ X40 @ ( k9_subset_1 @ X39 @ X42 @ X38 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40 ) @ ( k4_subset_1 @ X39 @ X42 @ X38 ) @ X37 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X39 @ X42 @ X38 ) @ X37 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X39 @ X42 @ X38 ) @ X37 @ ( k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40 ) @ X38 )
        = X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ( v1_xboole_0 @ X38 )
      | ( v1_xboole_0 @ X37 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('106',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_C_1 ) )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B @ ( k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ sk_C_1 )
      = sk_E )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) )
    | ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) )
     != ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) ) )
    | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) )
    | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B )
    | ~ ( v1_funct_1 @ sk_E )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_C_1 ) )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['103','105'])).

thf('107',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('108',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('109',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('110',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('111',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('112',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('113',plain,(
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
    inference(demod,[status(thm)],['40','41','42'])).

thf('114',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_C_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['112','113'])).

thf('115',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('116',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_C_1 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['114','115','116'])).

thf('118',plain,(
    ! [X0: $i] :
      ( ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_C_1 ) @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['117'])).

thf('119',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_funct_2 @ ( k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B ) ),
    inference('sup-',[status(thm)],['111','118'])).

thf('120',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('122',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( v1_funct_2 @ ( k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B ) ),
    inference(clc,[status(thm)],['120','121'])).

thf('123',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('124',plain,(
    v1_funct_2 @ ( k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B ),
    inference(clc,[status(thm)],['122','123'])).

thf('125',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('126',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('127',plain,(
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
    inference(demod,[status(thm)],['25','26','27'])).

thf('128',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ~ ( v1_funct_1 @ sk_E )
      | ~ ( v1_funct_2 @ sk_E @ sk_C_1 @ sk_B )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['126','127'])).

thf('129',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['128','129','130'])).

thf('132',plain,(
    ! [X0: $i] :
      ( ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) )
      | ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_1 )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['131'])).

thf('133',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_funct_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) ) ),
    inference('sup-',[status(thm)],['125','132'])).

thf('134',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['133'])).

thf('135',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( v1_funct_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) ) ),
    inference(clc,[status(thm)],['134','135'])).

thf('137',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('138',plain,(
    v1_funct_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('139',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('140',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('141',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('143',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k9_subset_1 @ X0 @ X1 @ X0 )
      = ( k3_xboole_0 @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['139','140'])).

thf('144',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('145',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('148',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('149',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B @ ( k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ sk_C_1 )
      = sk_E )
    | ( ( k7_relat_1 @ sk_E @ ( k3_xboole_0 @ sk_C_1 @ sk_C_1 ) )
     != ( k7_relat_1 @ sk_E @ ( k3_xboole_0 @ sk_C_1 @ sk_C_1 ) ) )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference(demod,[status(thm)],['106','107','108','109','110','124','138','141','142','143','144','145','146','147','148'])).

thf('150',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B @ ( k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ sk_C_1 )
      = sk_E )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('152',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B @ ( k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ sk_C_1 )
      = sk_E ) ),
    inference(clc,[status(thm)],['150','151'])).

thf('153',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('154',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B @ ( k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ sk_C_1 )
    = sk_E ),
    inference(clc,[status(thm)],['152','153'])).

thf('155',plain,(
    m1_subset_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['101','102'])).

thf('156',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ( ( k2_partfun1 @ X34 @ X35 @ X33 @ X36 )
        = ( k7_relat_1 @ X33 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('157',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B @ ( k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ X0 )
        = ( k7_relat_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ X0 ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) ) ) ),
    inference('sup-',[status(thm)],['155','156'])).

thf('158',plain,(
    v1_funct_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) ),
    inference(clc,[status(thm)],['136','137'])).

thf('159',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B @ ( k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ X0 )
      = ( k7_relat_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ X0 ) ) ),
    inference(demod,[status(thm)],['157','158'])).

thf('160',plain,
    ( ( k7_relat_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ sk_C_1 )
    = sk_E ),
    inference(demod,[status(thm)],['154','159'])).

thf('161',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ k1_xboole_0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('162',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
      = k1_xboole_0 )
    | ~ ( v1_relat_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) ) ),
    inference('sup+',[status(thm)],['160','161'])).

thf('163',plain,(
    m1_subset_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1 ) @ sk_B ) ) ),
    inference(clc,[status(thm)],['101','102'])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('164',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_relat_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('165',plain,(
    v1_relat_1 @ ( k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E ) ),
    inference('sup-',[status(thm)],['163','164'])).

thf('166',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['162','165'])).

thf('167',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('168',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['82','83'])).

thf('169',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,(
    ! [X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( v1_funct_1 @ X33 )
      | ( ( k2_partfun1 @ X34 @ X35 @ X33 @ X36 )
        = ( k7_relat_1 @ X33 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('171',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['169','170'])).

thf('172',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('173',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('174',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('175',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ),
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
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_D )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( k1_xboole_0
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['68','69','70','71','72','75','84','89','166','167','168','173','174','175','176','177'])).

thf('179',plain,
    ( ( k1_xboole_0
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['178'])).

thf('180',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( k1_xboole_0
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['50','179'])).

thf('181',plain,
    ( ( k1_xboole_0
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['180'])).

thf('182',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('183',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E ) ),
    inference(split,[status(esa)],['182'])).

thf('184',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('185',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('186',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('187',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('188',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(split,[status(esa)],['182'])).

thf('189',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C_1 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('191',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k3_xboole_0 @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k3_xboole_0 @ sk_C_1 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['189','190'])).

thf('192',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k3_xboole_0 @ sk_C_1 @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C_1 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['186','191'])).

thf('193',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['82','83'])).

thf('194',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('195',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['82','83'])).

thf('196',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['192','193','194','195'])).

thf('197',plain,
    ( ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_F ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['185','196'])).

thf('198',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('199',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_relat_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('200',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['198','199'])).

thf('201',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['197','200'])).

thf('202',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_E ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['184','201'])).

thf('203',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('204',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ( v1_relat_1 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('205',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['203','204'])).

thf('206',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['202','205'])).

thf('207',plain,
    ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['206'])).

thf('208',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('209',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['33','34'])).

thf('210',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('211',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['63','64'])).

thf('212',plain,(
    ! [X37: $i,X38: $i,X39: $i,X40: $i,X41: $i,X42: $i] :
      ( ( v1_xboole_0 @ X39 )
      | ( v1_xboole_0 @ X42 )
      | ~ ( m1_subset_1 @ X42 @ ( k1_zfmisc_1 @ X39 ) )
      | ~ ( v1_funct_1 @ X41 )
      | ~ ( v1_funct_2 @ X41 @ X42 @ X37 )
      | ~ ( m1_subset_1 @ X41 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X42 @ X37 ) ) )
      | ( ( k2_partfun1 @ X42 @ X37 @ X41 @ ( k9_subset_1 @ X39 @ X42 @ X38 ) )
       != ( k2_partfun1 @ X38 @ X37 @ X40 @ ( k9_subset_1 @ X39 @ X42 @ X38 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40 ) @ ( k4_subset_1 @ X39 @ X42 @ X38 ) @ X37 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X39 @ X42 @ X38 ) @ X37 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X39 @ X42 @ X38 ) @ X37 @ ( k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40 ) @ X38 )
        = X40 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X37 ) ) )
      | ~ ( v1_funct_2 @ X40 @ X38 @ X37 )
      | ~ ( v1_funct_1 @ X40 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ X39 ) )
      | ( v1_xboole_0 @ X38 )
      | ( v1_xboole_0 @ X37 ) ) ),
    inference(simplify,[status(thm)],['104'])).

thf('213',plain,
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
    inference('sup-',[status(thm)],['211','212'])).

thf('214',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('215',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('216',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('217',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('218',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('219',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['82','83'])).

thf('220',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['87','88'])).

thf('221',plain,
    ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['162','165'])).

thf('222',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['73','74'])).

thf('223',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['82','83'])).

thf('224',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['171','172'])).

thf('225',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('226',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('227',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('228',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('229',plain,
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
    | ( k1_xboole_0
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['213','214','215','216','217','218','219','220','221','222','223','224','225','226','227','228'])).

thf('230',plain,
    ( ( k1_xboole_0
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['229'])).

thf('231',plain,
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
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( k1_xboole_0
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['210','230'])).

thf('232',plain,
    ( ( k1_xboole_0
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['231'])).

thf('233',plain,
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
    | ( k1_xboole_0
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['209','232'])).

thf('234',plain,
    ( ( k1_xboole_0
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['233'])).

thf('235',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference('sup-',[status(thm)],['208','234'])).

thf('236',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['198','199'])).

thf('237',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference(demod,[status(thm)],['235','236'])).

thf('238',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['237'])).

thf('239',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['182'])).

thf('240',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['238','239'])).

thf('241',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['240'])).

thf('242',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('243',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['241','242'])).

thf('244',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('245',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['243','244'])).

thf('246',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('247',plain,
    ( ( v1_xboole_0 @ sk_B )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['245','246'])).

thf('248',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('249',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['247','248'])).

thf('250',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(split,[status(esa)],['182'])).

thf('251',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['207','249','250'])).

thf('252',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['183','251'])).

thf('253',plain,
    ( ( k1_xboole_0
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['181','252'])).

thf('254',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( k1_xboole_0
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['35','253'])).

thf('255',plain,
    ( ( k1_xboole_0
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['254'])).

thf('256',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['20','255'])).

thf('257',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['198','199'])).

thf('258',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['256','257'])).

thf('259',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['258'])).

thf('260',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('261',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['259','260'])).

thf('262',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('263',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['261','262'])).

thf('264',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('265',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['263','264'])).

thf('266',plain,(
    $false ),
    inference(demod,[status(thm)],['0','265'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.0zo3ksrd4G
% 0.13/0.37  % Computer   : n020.cluster.edu
% 0.13/0.37  % Model      : x86_64 x86_64
% 0.13/0.37  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.37  % Memory     : 8042.1875MB
% 0.13/0.37  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.37  % CPULimit   : 60
% 0.13/0.37  % DateTime   : Tue Dec  1 18:52:07 EST 2020
% 0.13/0.37  % CPUTime    : 
% 0.13/0.37  % Running portfolio for 600 s
% 0.13/0.37  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.37  % Number of cores: 8
% 0.13/0.38  % Python version: Python 3.6.8
% 0.13/0.38  % Running in FO mode
% 0.52/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.52/0.70  % Solved by: fo/fo7.sh
% 0.52/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.52/0.70  % done 517 iterations in 0.215s
% 0.52/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.52/0.70  % SZS output start Refutation
% 0.52/0.70  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 0.52/0.70  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.52/0.70  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.52/0.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.52/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.52/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.52/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.52/0.70  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.52/0.70  thf(sk_D_type, type, sk_D: $i).
% 0.52/0.70  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.52/0.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.52/0.70  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.52/0.70  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.52/0.70  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.52/0.70  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.52/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.52/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.52/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.52/0.70  thf(sk_B_type, type, sk_B: $i).
% 0.52/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.52/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.52/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.52/0.70  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.52/0.70  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.52/0.70  thf(sk_F_type, type, sk_F: $i).
% 0.52/0.70  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.52/0.70  thf(sk_E_type, type, sk_E: $i).
% 0.52/0.70  thf(t6_tmap_1, conjecture,
% 0.52/0.70    (![A:$i]:
% 0.52/0.70     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.52/0.70       ( ![B:$i]:
% 0.52/0.70         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.52/0.70           ( ![C:$i]:
% 0.52/0.70             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.52/0.70                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.52/0.70               ( ![D:$i]:
% 0.52/0.70                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.52/0.70                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.52/0.70                   ( ( r1_subset_1 @ C @ D ) =>
% 0.52/0.70                     ( ![E:$i]:
% 0.52/0.70                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.52/0.70                           ( m1_subset_1 @
% 0.52/0.70                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.52/0.70                         ( ![F:$i]:
% 0.52/0.70                           ( ( ( v1_funct_1 @ F ) & 
% 0.52/0.70                               ( v1_funct_2 @ F @ D @ B ) & 
% 0.52/0.70                               ( m1_subset_1 @
% 0.52/0.70                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.52/0.70                             ( ( ( k2_partfun1 @
% 0.52/0.70                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.52/0.70                                 ( k2_partfun1 @
% 0.52/0.70                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.52/0.70                               ( ( k2_partfun1 @
% 0.52/0.70                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.52/0.70                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.52/0.70                                 ( E ) ) & 
% 0.52/0.70                               ( ( k2_partfun1 @
% 0.52/0.70                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.52/0.70                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.52/0.70                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.52/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.52/0.70    (~( ![A:$i]:
% 0.52/0.70        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.52/0.70          ( ![B:$i]:
% 0.52/0.70            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.52/0.70              ( ![C:$i]:
% 0.52/0.70                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.52/0.70                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.52/0.70                  ( ![D:$i]:
% 0.52/0.70                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.52/0.70                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.52/0.70                      ( ( r1_subset_1 @ C @ D ) =>
% 0.52/0.70                        ( ![E:$i]:
% 0.52/0.70                          ( ( ( v1_funct_1 @ E ) & 
% 0.52/0.70                              ( v1_funct_2 @ E @ C @ B ) & 
% 0.52/0.70                              ( m1_subset_1 @
% 0.52/0.70                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.52/0.70                            ( ![F:$i]:
% 0.52/0.70                              ( ( ( v1_funct_1 @ F ) & 
% 0.52/0.70                                  ( v1_funct_2 @ F @ D @ B ) & 
% 0.52/0.70                                  ( m1_subset_1 @
% 0.52/0.70                                    F @ 
% 0.52/0.70                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.52/0.70                                ( ( ( k2_partfun1 @
% 0.52/0.70                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.52/0.70                                    ( k2_partfun1 @
% 0.52/0.70                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.52/0.70                                  ( ( k2_partfun1 @
% 0.52/0.70                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.52/0.70                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.52/0.70                                    ( E ) ) & 
% 0.52/0.70                                  ( ( k2_partfun1 @
% 0.52/0.70                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.52/0.70                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.52/0.70                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.52/0.70    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 0.52/0.70  thf('0', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf(d10_xboole_0, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.52/0.70  thf('1', plain,
% 0.52/0.70      (![X7 : $i, X8 : $i]: ((r1_tarski @ X7 @ X8) | ((X7) != (X8)))),
% 0.52/0.70      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.52/0.70  thf('2', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.52/0.70      inference('simplify', [status(thm)], ['1'])).
% 0.52/0.70  thf(d18_relat_1, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( v1_relat_1 @ B ) =>
% 0.52/0.70       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.52/0.70  thf('3', plain,
% 0.52/0.70      (![X21 : $i, X22 : $i]:
% 0.52/0.70         (~ (r1_tarski @ (k1_relat_1 @ X21) @ X22)
% 0.52/0.70          | (v4_relat_1 @ X21 @ X22)
% 0.52/0.70          | ~ (v1_relat_1 @ X21))),
% 0.52/0.70      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.52/0.70  thf('4', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['2', '3'])).
% 0.52/0.70  thf(t209_relat_1, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.52/0.70       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.52/0.70  thf('5', plain,
% 0.52/0.70      (![X26 : $i, X27 : $i]:
% 0.52/0.70         (((X26) = (k7_relat_1 @ X26 @ X27))
% 0.52/0.70          | ~ (v4_relat_1 @ X26 @ X27)
% 0.52/0.70          | ~ (v1_relat_1 @ X26))),
% 0.52/0.70      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.52/0.70  thf('6', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X0)
% 0.52/0.70          | ~ (v1_relat_1 @ X0)
% 0.52/0.70          | ((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.52/0.70      inference('sup-', [status(thm)], ['4', '5'])).
% 0.52/0.70  thf('7', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))) | ~ (v1_relat_1 @ X0))),
% 0.52/0.70      inference('simplify', [status(thm)], ['6'])).
% 0.52/0.70  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.52/0.70  thf('8', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.52/0.70      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.52/0.70  thf(t3_xboole_0, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.52/0.70            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.52/0.70       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.52/0.70            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.52/0.70  thf('9', plain,
% 0.52/0.70      (![X3 : $i, X4 : $i]:
% 0.52/0.70         ((r1_xboole_0 @ X3 @ X4) | (r2_hidden @ (sk_C @ X4 @ X3) @ X4))),
% 0.52/0.70      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.52/0.70  thf('10', plain, (![X8 : $i]: (r1_tarski @ X8 @ X8)),
% 0.52/0.70      inference('simplify', [status(thm)], ['1'])).
% 0.52/0.70  thf(t3_subset, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.52/0.70  thf('11', plain,
% 0.52/0.70      (![X15 : $i, X17 : $i]:
% 0.52/0.70         ((m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X17)) | ~ (r1_tarski @ X15 @ X17))),
% 0.52/0.70      inference('cnf', [status(esa)], [t3_subset])).
% 0.52/0.70  thf('12', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['10', '11'])).
% 0.52/0.70  thf(t5_subset, axiom,
% 0.52/0.70    (![A:$i,B:$i,C:$i]:
% 0.52/0.70     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.52/0.70          ( v1_xboole_0 @ C ) ) ))).
% 0.52/0.70  thf('13', plain,
% 0.52/0.70      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.52/0.70         (~ (r2_hidden @ X18 @ X19)
% 0.52/0.70          | ~ (v1_xboole_0 @ X20)
% 0.52/0.70          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20)))),
% 0.52/0.70      inference('cnf', [status(esa)], [t5_subset])).
% 0.52/0.70  thf('14', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]: (~ (v1_xboole_0 @ X0) | ~ (r2_hidden @ X1 @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['12', '13'])).
% 0.52/0.70  thf('15', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['9', '14'])).
% 0.52/0.70  thf('16', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.52/0.70      inference('sup-', [status(thm)], ['8', '15'])).
% 0.52/0.70  thf(t207_relat_1, axiom,
% 0.52/0.70    (![A:$i,B:$i,C:$i]:
% 0.52/0.70     ( ( v1_relat_1 @ C ) =>
% 0.52/0.70       ( ( r1_xboole_0 @ A @ B ) =>
% 0.52/0.70         ( ( k7_relat_1 @ ( k7_relat_1 @ C @ A ) @ B ) = ( k1_xboole_0 ) ) ) ))).
% 0.52/0.70  thf('17', plain,
% 0.52/0.70      (![X23 : $i, X24 : $i, X25 : $i]:
% 0.52/0.70         (~ (r1_xboole_0 @ X23 @ X24)
% 0.52/0.70          | ~ (v1_relat_1 @ X25)
% 0.52/0.70          | ((k7_relat_1 @ (k7_relat_1 @ X25 @ X23) @ X24) = (k1_xboole_0)))),
% 0.52/0.70      inference('cnf', [status(esa)], [t207_relat_1])).
% 0.52/0.70  thf('18', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 0.52/0.70          | ~ (v1_relat_1 @ X1))),
% 0.52/0.70      inference('sup-', [status(thm)], ['16', '17'])).
% 0.52/0.70  thf('19', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))
% 0.52/0.70          | ~ (v1_relat_1 @ X0)
% 0.52/0.70          | ~ (v1_relat_1 @ X0))),
% 0.52/0.70      inference('sup+', [status(thm)], ['7', '18'])).
% 0.52/0.70  thf('20', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X0)
% 0.52/0.70          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.52/0.70      inference('simplify', [status(thm)], ['19'])).
% 0.52/0.70  thf('21', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('22', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('23', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf(dt_k1_tmap_1, axiom,
% 0.52/0.70    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.52/0.70     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.52/0.70         ( ~( v1_xboole_0 @ C ) ) & 
% 0.52/0.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 0.52/0.70         ( ~( v1_xboole_0 @ D ) ) & 
% 0.52/0.70         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 0.52/0.70         ( v1_funct_2 @ E @ C @ B ) & 
% 0.52/0.70         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.52/0.70         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.52/0.70         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.52/0.70       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.52/0.70         ( v1_funct_2 @
% 0.52/0.70           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.52/0.70           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.52/0.70         ( m1_subset_1 @
% 0.52/0.70           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.52/0.70           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 0.52/0.70  thf('24', plain,
% 0.52/0.70      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 0.52/0.70          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 0.52/0.70          | ~ (v1_funct_1 @ X44)
% 0.52/0.70          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48))
% 0.52/0.70          | (v1_xboole_0 @ X47)
% 0.52/0.70          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X48))
% 0.52/0.70          | (v1_xboole_0 @ X45)
% 0.52/0.70          | (v1_xboole_0 @ X46)
% 0.52/0.70          | (v1_xboole_0 @ X48)
% 0.52/0.70          | ~ (v1_funct_1 @ X49)
% 0.52/0.70          | ~ (v1_funct_2 @ X49 @ X47 @ X46)
% 0.52/0.70          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46)))
% 0.52/0.70          | (v1_funct_1 @ (k1_tmap_1 @ X48 @ X46 @ X45 @ X47 @ X44 @ X49)))),
% 0.52/0.70      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.52/0.70  thf('25', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.70         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C_1 @ X1 @ sk_E @ X0))
% 0.52/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.52/0.70          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.52/0.70          | ~ (v1_funct_1 @ X0)
% 0.52/0.70          | (v1_xboole_0 @ X2)
% 0.52/0.70          | (v1_xboole_0 @ sk_B)
% 0.52/0.70          | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X2))
% 0.52/0.70          | (v1_xboole_0 @ X1)
% 0.52/0.70          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.52/0.70          | ~ (v1_funct_1 @ sk_E)
% 0.52/0.70          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B))),
% 0.52/0.70      inference('sup-', [status(thm)], ['23', '24'])).
% 0.52/0.70  thf('26', plain, ((v1_funct_1 @ sk_E)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('27', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('28', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.70         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C_1 @ X1 @ sk_E @ X0))
% 0.52/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.52/0.70          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.52/0.70          | ~ (v1_funct_1 @ X0)
% 0.52/0.70          | (v1_xboole_0 @ X2)
% 0.52/0.70          | (v1_xboole_0 @ sk_B)
% 0.52/0.70          | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X2))
% 0.52/0.70          | (v1_xboole_0 @ X1)
% 0.52/0.70          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.52/0.70      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.52/0.70  thf('29', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ sk_D)
% 0.52/0.70          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70          | (v1_xboole_0 @ sk_B)
% 0.52/0.70          | (v1_xboole_0 @ X0)
% 0.52/0.70          | ~ (v1_funct_1 @ sk_F)
% 0.52/0.70          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.52/0.70          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['22', '28'])).
% 0.52/0.70  thf('30', plain, ((v1_funct_1 @ sk_F)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('31', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('32', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ sk_D)
% 0.52/0.70          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70          | (v1_xboole_0 @ sk_B)
% 0.52/0.70          | (v1_xboole_0 @ X0)
% 0.52/0.70          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F)))),
% 0.52/0.70      inference('demod', [status(thm)], ['29', '30', '31'])).
% 0.52/0.70  thf('33', plain,
% 0.52/0.70      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.52/0.70        | (v1_xboole_0 @ sk_A)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.52/0.70        | (v1_xboole_0 @ sk_D))),
% 0.52/0.70      inference('sup-', [status(thm)], ['21', '32'])).
% 0.52/0.70  thf('34', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('35', plain,
% 0.52/0.70      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.52/0.70        | (v1_xboole_0 @ sk_A)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_D))),
% 0.52/0.70      inference('demod', [status(thm)], ['33', '34'])).
% 0.52/0.70  thf('36', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('37', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('38', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('39', plain,
% 0.52/0.70      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 0.52/0.70          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 0.52/0.70          | ~ (v1_funct_1 @ X44)
% 0.52/0.70          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48))
% 0.52/0.70          | (v1_xboole_0 @ X47)
% 0.52/0.70          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X48))
% 0.52/0.70          | (v1_xboole_0 @ X45)
% 0.52/0.70          | (v1_xboole_0 @ X46)
% 0.52/0.70          | (v1_xboole_0 @ X48)
% 0.52/0.70          | ~ (v1_funct_1 @ X49)
% 0.52/0.70          | ~ (v1_funct_2 @ X49 @ X47 @ X46)
% 0.52/0.70          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46)))
% 0.52/0.70          | (v1_funct_2 @ (k1_tmap_1 @ X48 @ X46 @ X45 @ X47 @ X44 @ X49) @ 
% 0.52/0.70             (k4_subset_1 @ X48 @ X45 @ X47) @ X46))),
% 0.52/0.70      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.52/0.70  thf('40', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.70         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.52/0.70           (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B)
% 0.52/0.70          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.52/0.70          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.52/0.70          | ~ (v1_funct_1 @ X2)
% 0.52/0.70          | (v1_xboole_0 @ X1)
% 0.52/0.70          | (v1_xboole_0 @ sk_B)
% 0.52/0.70          | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.52/0.70          | (v1_xboole_0 @ X0)
% 0.52/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.52/0.70          | ~ (v1_funct_1 @ sk_E)
% 0.52/0.70          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B))),
% 0.52/0.70      inference('sup-', [status(thm)], ['38', '39'])).
% 0.52/0.70  thf('41', plain, ((v1_funct_1 @ sk_E)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('42', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('43', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.70         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.52/0.70           (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B)
% 0.52/0.70          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.52/0.70          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.52/0.70          | ~ (v1_funct_1 @ X2)
% 0.52/0.70          | (v1_xboole_0 @ X1)
% 0.52/0.70          | (v1_xboole_0 @ sk_B)
% 0.52/0.70          | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.52/0.70          | (v1_xboole_0 @ X0)
% 0.52/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.52/0.70      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.52/0.70  thf('44', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ sk_D)
% 0.52/0.70          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70          | (v1_xboole_0 @ sk_B)
% 0.52/0.70          | (v1_xboole_0 @ X0)
% 0.52/0.70          | ~ (v1_funct_1 @ sk_F)
% 0.52/0.70          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.52/0.70          | (v1_funct_2 @ 
% 0.52/0.70             (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.52/0.70             (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B))),
% 0.52/0.70      inference('sup-', [status(thm)], ['37', '43'])).
% 0.52/0.70  thf('45', plain, ((v1_funct_1 @ sk_F)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('46', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('47', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ sk_D)
% 0.52/0.70          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70          | (v1_xboole_0 @ sk_B)
% 0.52/0.70          | (v1_xboole_0 @ X0)
% 0.52/0.70          | (v1_funct_2 @ 
% 0.52/0.70             (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.52/0.70             (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B))),
% 0.52/0.70      inference('demod', [status(thm)], ['44', '45', '46'])).
% 0.52/0.70  thf('48', plain,
% 0.52/0.70      (((v1_funct_2 @ 
% 0.52/0.70         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.52/0.70         (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_A)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.52/0.70        | (v1_xboole_0 @ sk_D))),
% 0.52/0.70      inference('sup-', [status(thm)], ['36', '47'])).
% 0.52/0.70  thf('49', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('50', plain,
% 0.52/0.70      (((v1_funct_2 @ 
% 0.52/0.70         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.52/0.70         (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_A)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_D))),
% 0.52/0.70      inference('demod', [status(thm)], ['48', '49'])).
% 0.52/0.70  thf('51', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('52', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('53', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('54', plain,
% 0.52/0.70      (![X44 : $i, X45 : $i, X46 : $i, X47 : $i, X48 : $i, X49 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ X44 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X45 @ X46)))
% 0.52/0.70          | ~ (v1_funct_2 @ X44 @ X45 @ X46)
% 0.52/0.70          | ~ (v1_funct_1 @ X44)
% 0.52/0.70          | ~ (m1_subset_1 @ X47 @ (k1_zfmisc_1 @ X48))
% 0.52/0.70          | (v1_xboole_0 @ X47)
% 0.52/0.70          | ~ (m1_subset_1 @ X45 @ (k1_zfmisc_1 @ X48))
% 0.52/0.70          | (v1_xboole_0 @ X45)
% 0.52/0.70          | (v1_xboole_0 @ X46)
% 0.52/0.70          | (v1_xboole_0 @ X48)
% 0.52/0.70          | ~ (v1_funct_1 @ X49)
% 0.52/0.70          | ~ (v1_funct_2 @ X49 @ X47 @ X46)
% 0.52/0.70          | ~ (m1_subset_1 @ X49 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X47 @ X46)))
% 0.52/0.70          | (m1_subset_1 @ (k1_tmap_1 @ X48 @ X46 @ X45 @ X47 @ X44 @ X49) @ 
% 0.52/0.70             (k1_zfmisc_1 @ 
% 0.52/0.70              (k2_zfmisc_1 @ (k4_subset_1 @ X48 @ X45 @ X47) @ X46))))),
% 0.52/0.70      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.52/0.70  thf('55', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.70         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.52/0.70           (k1_zfmisc_1 @ 
% 0.52/0.70            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B)))
% 0.52/0.70          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.52/0.70          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.52/0.70          | ~ (v1_funct_1 @ X2)
% 0.52/0.70          | (v1_xboole_0 @ X1)
% 0.52/0.70          | (v1_xboole_0 @ sk_B)
% 0.52/0.70          | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.52/0.70          | (v1_xboole_0 @ X0)
% 0.52/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.52/0.70          | ~ (v1_funct_1 @ sk_E)
% 0.52/0.70          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B))),
% 0.52/0.70      inference('sup-', [status(thm)], ['53', '54'])).
% 0.52/0.70  thf('56', plain, ((v1_funct_1 @ sk_E)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('57', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('58', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.70         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.52/0.70           (k1_zfmisc_1 @ 
% 0.52/0.70            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B)))
% 0.52/0.70          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.52/0.70          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.52/0.70          | ~ (v1_funct_1 @ X2)
% 0.52/0.70          | (v1_xboole_0 @ X1)
% 0.52/0.70          | (v1_xboole_0 @ sk_B)
% 0.52/0.70          | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.52/0.70          | (v1_xboole_0 @ X0)
% 0.52/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.52/0.70      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.52/0.70  thf('59', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ sk_D)
% 0.52/0.70          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70          | (v1_xboole_0 @ sk_B)
% 0.52/0.70          | (v1_xboole_0 @ X0)
% 0.52/0.70          | ~ (v1_funct_1 @ sk_F)
% 0.52/0.70          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.52/0.70          | (m1_subset_1 @ 
% 0.52/0.70             (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.52/0.70             (k1_zfmisc_1 @ 
% 0.52/0.70              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B))))),
% 0.52/0.70      inference('sup-', [status(thm)], ['52', '58'])).
% 0.52/0.70  thf('60', plain, ((v1_funct_1 @ sk_F)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('61', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('62', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ sk_D)
% 0.52/0.70          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70          | (v1_xboole_0 @ sk_B)
% 0.52/0.70          | (v1_xboole_0 @ X0)
% 0.52/0.70          | (m1_subset_1 @ 
% 0.52/0.70             (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.52/0.70             (k1_zfmisc_1 @ 
% 0.52/0.70              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B))))),
% 0.52/0.70      inference('demod', [status(thm)], ['59', '60', '61'])).
% 0.52/0.70  thf('63', plain,
% 0.52/0.70      (((m1_subset_1 @ 
% 0.52/0.70         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.52/0.70         (k1_zfmisc_1 @ 
% 0.52/0.70          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)))
% 0.52/0.70        | (v1_xboole_0 @ sk_A)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.52/0.70        | (v1_xboole_0 @ sk_D))),
% 0.52/0.70      inference('sup-', [status(thm)], ['51', '62'])).
% 0.52/0.70  thf('64', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('65', plain,
% 0.52/0.70      (((m1_subset_1 @ 
% 0.52/0.70         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.52/0.70         (k1_zfmisc_1 @ 
% 0.52/0.70          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)))
% 0.52/0.70        | (v1_xboole_0 @ sk_A)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_D))),
% 0.52/0.70      inference('demod', [status(thm)], ['63', '64'])).
% 0.52/0.70  thf(d1_tmap_1, axiom,
% 0.52/0.70    (![A:$i]:
% 0.52/0.70     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.52/0.70       ( ![B:$i]:
% 0.52/0.70         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.52/0.70           ( ![C:$i]:
% 0.52/0.70             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.52/0.70                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.52/0.70               ( ![D:$i]:
% 0.52/0.70                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.52/0.70                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.52/0.70                   ( ![E:$i]:
% 0.52/0.70                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.52/0.70                         ( m1_subset_1 @
% 0.52/0.70                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.52/0.70                       ( ![F:$i]:
% 0.52/0.70                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.52/0.70                             ( m1_subset_1 @
% 0.52/0.70                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.52/0.70                           ( ( ( k2_partfun1 @
% 0.52/0.70                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.52/0.70                               ( k2_partfun1 @
% 0.52/0.70                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 0.52/0.70                             ( ![G:$i]:
% 0.52/0.70                               ( ( ( v1_funct_1 @ G ) & 
% 0.52/0.70                                   ( v1_funct_2 @
% 0.52/0.70                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.52/0.70                                   ( m1_subset_1 @
% 0.52/0.70                                     G @ 
% 0.52/0.70                                     ( k1_zfmisc_1 @
% 0.52/0.70                                       ( k2_zfmisc_1 @
% 0.52/0.70                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 0.52/0.70                                 ( ( ( G ) =
% 0.52/0.70                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.52/0.70                                   ( ( ( k2_partfun1 @
% 0.52/0.70                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.52/0.70                                         C ) =
% 0.52/0.70                                       ( E ) ) & 
% 0.52/0.70                                     ( ( k2_partfun1 @
% 0.52/0.70                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.52/0.70                                         D ) =
% 0.52/0.70                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.52/0.70  thf('66', plain,
% 0.52/0.70      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.52/0.70         ((v1_xboole_0 @ X37)
% 0.52/0.70          | (v1_xboole_0 @ X38)
% 0.52/0.70          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 0.52/0.70          | ~ (v1_funct_1 @ X40)
% 0.52/0.70          | ~ (v1_funct_2 @ X40 @ X38 @ X37)
% 0.52/0.70          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 0.52/0.70          | ((X43) != (k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40))
% 0.52/0.70          | ((k2_partfun1 @ (k4_subset_1 @ X39 @ X42 @ X38) @ X37 @ X43 @ X42)
% 0.52/0.70              = (X41))
% 0.52/0.70          | ~ (m1_subset_1 @ X43 @ 
% 0.52/0.70               (k1_zfmisc_1 @ 
% 0.52/0.70                (k2_zfmisc_1 @ (k4_subset_1 @ X39 @ X42 @ X38) @ X37)))
% 0.52/0.70          | ~ (v1_funct_2 @ X43 @ (k4_subset_1 @ X39 @ X42 @ X38) @ X37)
% 0.52/0.70          | ~ (v1_funct_1 @ X43)
% 0.52/0.70          | ((k2_partfun1 @ X42 @ X37 @ X41 @ (k9_subset_1 @ X39 @ X42 @ X38))
% 0.52/0.70              != (k2_partfun1 @ X38 @ X37 @ X40 @ 
% 0.52/0.70                  (k9_subset_1 @ X39 @ X42 @ X38)))
% 0.52/0.70          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X37)))
% 0.52/0.70          | ~ (v1_funct_2 @ X41 @ X42 @ X37)
% 0.52/0.70          | ~ (v1_funct_1 @ X41)
% 0.52/0.70          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X39))
% 0.52/0.70          | (v1_xboole_0 @ X42)
% 0.52/0.70          | (v1_xboole_0 @ X39))),
% 0.52/0.70      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.52/0.70  thf('67', plain,
% 0.52/0.70      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.52/0.70         ((v1_xboole_0 @ X39)
% 0.52/0.70          | (v1_xboole_0 @ X42)
% 0.52/0.70          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X39))
% 0.52/0.70          | ~ (v1_funct_1 @ X41)
% 0.52/0.70          | ~ (v1_funct_2 @ X41 @ X42 @ X37)
% 0.52/0.70          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X37)))
% 0.52/0.70          | ((k2_partfun1 @ X42 @ X37 @ X41 @ (k9_subset_1 @ X39 @ X42 @ X38))
% 0.52/0.70              != (k2_partfun1 @ X38 @ X37 @ X40 @ 
% 0.52/0.70                  (k9_subset_1 @ X39 @ X42 @ X38)))
% 0.52/0.70          | ~ (v1_funct_1 @ (k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40))
% 0.52/0.70          | ~ (v1_funct_2 @ (k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40) @ 
% 0.52/0.70               (k4_subset_1 @ X39 @ X42 @ X38) @ X37)
% 0.52/0.70          | ~ (m1_subset_1 @ (k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40) @ 
% 0.52/0.70               (k1_zfmisc_1 @ 
% 0.52/0.70                (k2_zfmisc_1 @ (k4_subset_1 @ X39 @ X42 @ X38) @ X37)))
% 0.52/0.70          | ((k2_partfun1 @ (k4_subset_1 @ X39 @ X42 @ X38) @ X37 @ 
% 0.52/0.70              (k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40) @ X42) = (
% 0.52/0.70              X41))
% 0.52/0.70          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 0.52/0.70          | ~ (v1_funct_2 @ X40 @ X38 @ X37)
% 0.52/0.70          | ~ (v1_funct_1 @ X40)
% 0.52/0.70          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 0.52/0.70          | (v1_xboole_0 @ X38)
% 0.52/0.70          | (v1_xboole_0 @ X37))),
% 0.52/0.70      inference('simplify', [status(thm)], ['66'])).
% 0.52/0.70  thf('68', plain,
% 0.52/0.70      (((v1_xboole_0 @ sk_D)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_A)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_D)
% 0.52/0.70        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.52/0.70        | ~ (v1_funct_1 @ sk_F)
% 0.52/0.70        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.52/0.70        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.52/0.70        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.52/0.70            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.52/0.70            = (sk_E))
% 0.52/0.70        | ~ (v1_funct_2 @ 
% 0.52/0.70             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.52/0.70             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 0.52/0.70        | ~ (v1_funct_1 @ 
% 0.52/0.70             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.52/0.70        | ((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.52/0.70            (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.52/0.70            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.52/0.70                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))
% 0.52/0.70        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))
% 0.52/0.70        | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)
% 0.52/0.70        | ~ (v1_funct_1 @ sk_E)
% 0.52/0.70        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_A))),
% 0.52/0.70      inference('sup-', [status(thm)], ['65', '67'])).
% 0.52/0.70  thf('69', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('70', plain, ((v1_funct_1 @ sk_F)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('71', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('72', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('73', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf(redefinition_k9_subset_1, axiom,
% 0.52/0.70    (![A:$i,B:$i,C:$i]:
% 0.52/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.52/0.70       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.52/0.70  thf('74', plain,
% 0.52/0.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.52/0.70         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 0.52/0.70          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.52/0.70      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.52/0.70  thf('75', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.52/0.70      inference('sup-', [status(thm)], ['73', '74'])).
% 0.52/0.70  thf('76', plain, ((r1_subset_1 @ sk_C_1 @ sk_D)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf(redefinition_r1_subset_1, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.52/0.70       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 0.52/0.70  thf('77', plain,
% 0.52/0.70      (![X28 : $i, X29 : $i]:
% 0.52/0.70         ((v1_xboole_0 @ X28)
% 0.52/0.70          | (v1_xboole_0 @ X29)
% 0.52/0.70          | (r1_xboole_0 @ X28 @ X29)
% 0.52/0.70          | ~ (r1_subset_1 @ X28 @ X29))),
% 0.52/0.70      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 0.52/0.70  thf('78', plain,
% 0.52/0.70      (((r1_xboole_0 @ sk_C_1 @ sk_D)
% 0.52/0.70        | (v1_xboole_0 @ sk_D)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1))),
% 0.52/0.70      inference('sup-', [status(thm)], ['76', '77'])).
% 0.52/0.70  thf('79', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('80', plain, (((v1_xboole_0 @ sk_C_1) | (r1_xboole_0 @ sk_C_1 @ sk_D))),
% 0.52/0.70      inference('clc', [status(thm)], ['78', '79'])).
% 0.52/0.70  thf('81', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('82', plain, ((r1_xboole_0 @ sk_C_1 @ sk_D)),
% 0.52/0.70      inference('clc', [status(thm)], ['80', '81'])).
% 0.52/0.70  thf(d7_xboole_0, axiom,
% 0.52/0.70    (![A:$i,B:$i]:
% 0.52/0.70     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.52/0.70       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.52/0.70  thf('83', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.52/0.70      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.52/0.70  thf('84', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['82', '83'])).
% 0.52/0.70  thf('85', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf(redefinition_k2_partfun1, axiom,
% 0.52/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.52/0.70     ( ( ( v1_funct_1 @ C ) & 
% 0.52/0.70         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.52/0.70       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.52/0.70  thf('86', plain,
% 0.52/0.70      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.52/0.70          | ~ (v1_funct_1 @ X33)
% 0.52/0.70          | ((k2_partfun1 @ X34 @ X35 @ X33 @ X36) = (k7_relat_1 @ X33 @ X36)))),
% 0.52/0.70      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.52/0.70  thf('87', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 0.52/0.70          | ~ (v1_funct_1 @ sk_E))),
% 0.52/0.70      inference('sup-', [status(thm)], ['85', '86'])).
% 0.52/0.70  thf('88', plain, ((v1_funct_1 @ sk_E)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('89', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.52/0.70      inference('demod', [status(thm)], ['87', '88'])).
% 0.52/0.70  thf('90', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['10', '11'])).
% 0.52/0.70  thf('91', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('92', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.70         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.52/0.70           (k1_zfmisc_1 @ 
% 0.52/0.70            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B)))
% 0.52/0.70          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.52/0.70          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.52/0.70          | ~ (v1_funct_1 @ X2)
% 0.52/0.70          | (v1_xboole_0 @ X1)
% 0.52/0.70          | (v1_xboole_0 @ sk_B)
% 0.52/0.70          | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.52/0.70          | (v1_xboole_0 @ X0)
% 0.52/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.52/0.70      inference('demod', [status(thm)], ['55', '56', '57'])).
% 0.52/0.70  thf('93', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70          | (v1_xboole_0 @ sk_B)
% 0.52/0.70          | (v1_xboole_0 @ X0)
% 0.52/0.70          | ~ (v1_funct_1 @ sk_E)
% 0.52/0.70          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)
% 0.52/0.70          | (m1_subset_1 @ 
% 0.52/0.70             (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.52/0.70             (k1_zfmisc_1 @ 
% 0.52/0.70              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C_1 @ sk_C_1) @ sk_B))))),
% 0.52/0.70      inference('sup-', [status(thm)], ['91', '92'])).
% 0.52/0.70  thf('94', plain, ((v1_funct_1 @ sk_E)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('95', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('96', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70          | (v1_xboole_0 @ sk_B)
% 0.52/0.70          | (v1_xboole_0 @ X0)
% 0.52/0.70          | (m1_subset_1 @ 
% 0.52/0.70             (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.52/0.70             (k1_zfmisc_1 @ 
% 0.52/0.70              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C_1 @ sk_C_1) @ sk_B))))),
% 0.52/0.70      inference('demod', [status(thm)], ['93', '94', '95'])).
% 0.52/0.70  thf('97', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((m1_subset_1 @ 
% 0.52/0.70           (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.52/0.70           (k1_zfmisc_1 @ 
% 0.52/0.70            (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C_1 @ sk_C_1) @ sk_B)))
% 0.52/0.70          | (v1_xboole_0 @ X0)
% 0.52/0.70          | (v1_xboole_0 @ sk_B)
% 0.52/0.70          | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0)))),
% 0.52/0.70      inference('simplify', [status(thm)], ['96'])).
% 0.52/0.70  thf('98', plain,
% 0.52/0.70      (((v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (m1_subset_1 @ 
% 0.52/0.70           (k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.52/0.70           (k1_zfmisc_1 @ 
% 0.52/0.70            (k2_zfmisc_1 @ (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B))))),
% 0.52/0.70      inference('sup-', [status(thm)], ['90', '97'])).
% 0.52/0.70  thf('99', plain,
% 0.52/0.70      (((m1_subset_1 @ 
% 0.52/0.70         (k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.52/0.70         (k1_zfmisc_1 @ 
% 0.52/0.70          (k2_zfmisc_1 @ (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B)))
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1))),
% 0.52/0.70      inference('simplify', [status(thm)], ['98'])).
% 0.52/0.70  thf('100', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('101', plain,
% 0.52/0.70      (((v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (m1_subset_1 @ 
% 0.52/0.70           (k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.52/0.70           (k1_zfmisc_1 @ 
% 0.52/0.70            (k2_zfmisc_1 @ (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B))))),
% 0.52/0.70      inference('clc', [status(thm)], ['99', '100'])).
% 0.52/0.70  thf('102', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('103', plain,
% 0.52/0.70      ((m1_subset_1 @ 
% 0.52/0.70        (k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.52/0.70        (k1_zfmisc_1 @ 
% 0.52/0.70         (k2_zfmisc_1 @ (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B)))),
% 0.52/0.70      inference('clc', [status(thm)], ['101', '102'])).
% 0.52/0.70  thf('104', plain,
% 0.52/0.70      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i, X43 : $i]:
% 0.52/0.70         ((v1_xboole_0 @ X37)
% 0.52/0.70          | (v1_xboole_0 @ X38)
% 0.52/0.70          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 0.52/0.70          | ~ (v1_funct_1 @ X40)
% 0.52/0.70          | ~ (v1_funct_2 @ X40 @ X38 @ X37)
% 0.52/0.70          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 0.52/0.70          | ((X43) != (k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40))
% 0.52/0.70          | ((k2_partfun1 @ (k4_subset_1 @ X39 @ X42 @ X38) @ X37 @ X43 @ X38)
% 0.52/0.70              = (X40))
% 0.52/0.70          | ~ (m1_subset_1 @ X43 @ 
% 0.52/0.70               (k1_zfmisc_1 @ 
% 0.52/0.70                (k2_zfmisc_1 @ (k4_subset_1 @ X39 @ X42 @ X38) @ X37)))
% 0.52/0.70          | ~ (v1_funct_2 @ X43 @ (k4_subset_1 @ X39 @ X42 @ X38) @ X37)
% 0.52/0.70          | ~ (v1_funct_1 @ X43)
% 0.52/0.70          | ((k2_partfun1 @ X42 @ X37 @ X41 @ (k9_subset_1 @ X39 @ X42 @ X38))
% 0.52/0.70              != (k2_partfun1 @ X38 @ X37 @ X40 @ 
% 0.52/0.70                  (k9_subset_1 @ X39 @ X42 @ X38)))
% 0.52/0.70          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X37)))
% 0.52/0.70          | ~ (v1_funct_2 @ X41 @ X42 @ X37)
% 0.52/0.70          | ~ (v1_funct_1 @ X41)
% 0.52/0.70          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X39))
% 0.52/0.70          | (v1_xboole_0 @ X42)
% 0.52/0.70          | (v1_xboole_0 @ X39))),
% 0.52/0.70      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.52/0.70  thf('105', plain,
% 0.52/0.70      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.52/0.70         ((v1_xboole_0 @ X39)
% 0.52/0.70          | (v1_xboole_0 @ X42)
% 0.52/0.70          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X39))
% 0.52/0.70          | ~ (v1_funct_1 @ X41)
% 0.52/0.70          | ~ (v1_funct_2 @ X41 @ X42 @ X37)
% 0.52/0.70          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X37)))
% 0.52/0.70          | ((k2_partfun1 @ X42 @ X37 @ X41 @ (k9_subset_1 @ X39 @ X42 @ X38))
% 0.52/0.70              != (k2_partfun1 @ X38 @ X37 @ X40 @ 
% 0.52/0.70                  (k9_subset_1 @ X39 @ X42 @ X38)))
% 0.52/0.70          | ~ (v1_funct_1 @ (k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40))
% 0.52/0.70          | ~ (v1_funct_2 @ (k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40) @ 
% 0.52/0.70               (k4_subset_1 @ X39 @ X42 @ X38) @ X37)
% 0.52/0.70          | ~ (m1_subset_1 @ (k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40) @ 
% 0.52/0.70               (k1_zfmisc_1 @ 
% 0.52/0.70                (k2_zfmisc_1 @ (k4_subset_1 @ X39 @ X42 @ X38) @ X37)))
% 0.52/0.70          | ((k2_partfun1 @ (k4_subset_1 @ X39 @ X42 @ X38) @ X37 @ 
% 0.52/0.70              (k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40) @ X38) = (
% 0.52/0.70              X40))
% 0.52/0.70          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 0.52/0.70          | ~ (v1_funct_2 @ X40 @ X38 @ X37)
% 0.52/0.70          | ~ (v1_funct_1 @ X40)
% 0.52/0.70          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 0.52/0.70          | (v1_xboole_0 @ X38)
% 0.52/0.70          | (v1_xboole_0 @ X37))),
% 0.52/0.70      inference('simplify', [status(thm)], ['104'])).
% 0.52/0.70  thf('106', plain,
% 0.52/0.70      (((v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_C_1))
% 0.52/0.70        | ~ (v1_funct_1 @ sk_E)
% 0.52/0.70        | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)
% 0.52/0.70        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))
% 0.52/0.70        | ((k2_partfun1 @ (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B @ 
% 0.52/0.70            (k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.52/0.70            sk_C_1) = (sk_E))
% 0.52/0.70        | ~ (v1_funct_2 @ 
% 0.52/0.70             (k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.52/0.70             (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B)
% 0.52/0.70        | ~ (v1_funct_1 @ 
% 0.52/0.70             (k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E))
% 0.52/0.70        | ((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.52/0.70            (k9_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1))
% 0.52/0.70            != (k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.52/0.70                (k9_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1)))
% 0.52/0.70        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))
% 0.52/0.70        | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)
% 0.52/0.70        | ~ (v1_funct_1 @ sk_E)
% 0.52/0.70        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_C_1))
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1))),
% 0.52/0.70      inference('sup-', [status(thm)], ['103', '105'])).
% 0.52/0.70  thf('107', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['10', '11'])).
% 0.52/0.70  thf('108', plain, ((v1_funct_1 @ sk_E)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('109', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('110', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('111', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['10', '11'])).
% 0.52/0.70  thf('112', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('113', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.70         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.52/0.70           (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B)
% 0.52/0.70          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B)))
% 0.52/0.70          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B)
% 0.52/0.70          | ~ (v1_funct_1 @ X2)
% 0.52/0.70          | (v1_xboole_0 @ X1)
% 0.52/0.70          | (v1_xboole_0 @ sk_B)
% 0.52/0.70          | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.52/0.70          | (v1_xboole_0 @ X0)
% 0.52/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.52/0.70      inference('demod', [status(thm)], ['40', '41', '42'])).
% 0.52/0.70  thf('114', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70          | (v1_xboole_0 @ sk_B)
% 0.52/0.70          | (v1_xboole_0 @ X0)
% 0.52/0.70          | ~ (v1_funct_1 @ sk_E)
% 0.52/0.70          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)
% 0.52/0.70          | (v1_funct_2 @ 
% 0.52/0.70             (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.52/0.70             (k4_subset_1 @ X0 @ sk_C_1 @ sk_C_1) @ sk_B))),
% 0.52/0.70      inference('sup-', [status(thm)], ['112', '113'])).
% 0.52/0.70  thf('115', plain, ((v1_funct_1 @ sk_E)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('116', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('117', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70          | (v1_xboole_0 @ sk_B)
% 0.52/0.70          | (v1_xboole_0 @ X0)
% 0.52/0.70          | (v1_funct_2 @ 
% 0.52/0.70             (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.52/0.70             (k4_subset_1 @ X0 @ sk_C_1 @ sk_C_1) @ sk_B))),
% 0.52/0.70      inference('demod', [status(thm)], ['114', '115', '116'])).
% 0.52/0.70  thf('118', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((v1_funct_2 @ 
% 0.52/0.70           (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.52/0.70           (k4_subset_1 @ X0 @ sk_C_1 @ sk_C_1) @ sk_B)
% 0.52/0.70          | (v1_xboole_0 @ X0)
% 0.52/0.70          | (v1_xboole_0 @ sk_B)
% 0.52/0.70          | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0)))),
% 0.52/0.70      inference('simplify', [status(thm)], ['117'])).
% 0.52/0.70  thf('119', plain,
% 0.52/0.70      (((v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_funct_2 @ 
% 0.52/0.70           (k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.52/0.70           (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B))),
% 0.52/0.70      inference('sup-', [status(thm)], ['111', '118'])).
% 0.52/0.70  thf('120', plain,
% 0.52/0.70      (((v1_funct_2 @ 
% 0.52/0.70         (k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.52/0.70         (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1))),
% 0.52/0.70      inference('simplify', [status(thm)], ['119'])).
% 0.52/0.70  thf('121', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('122', plain,
% 0.52/0.70      (((v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_funct_2 @ 
% 0.52/0.70           (k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.52/0.70           (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B))),
% 0.52/0.70      inference('clc', [status(thm)], ['120', '121'])).
% 0.52/0.70  thf('123', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('124', plain,
% 0.52/0.70      ((v1_funct_2 @ 
% 0.52/0.70        (k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.52/0.70        (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B)),
% 0.52/0.70      inference('clc', [status(thm)], ['122', '123'])).
% 0.52/0.70  thf('125', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['10', '11'])).
% 0.52/0.70  thf('126', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('127', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.52/0.70         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B @ sk_C_1 @ X1 @ sk_E @ X0))
% 0.52/0.70          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B)))
% 0.52/0.70          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B)
% 0.52/0.70          | ~ (v1_funct_1 @ X0)
% 0.52/0.70          | (v1_xboole_0 @ X2)
% 0.52/0.70          | (v1_xboole_0 @ sk_B)
% 0.52/0.70          | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X2))
% 0.52/0.70          | (v1_xboole_0 @ X1)
% 0.52/0.70          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.52/0.70      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.52/0.70  thf('128', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70          | (v1_xboole_0 @ sk_B)
% 0.52/0.70          | (v1_xboole_0 @ X0)
% 0.52/0.70          | ~ (v1_funct_1 @ sk_E)
% 0.52/0.70          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)
% 0.52/0.70          | (v1_funct_1 @ 
% 0.52/0.70             (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['126', '127'])).
% 0.52/0.70  thf('129', plain, ((v1_funct_1 @ sk_E)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('130', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('131', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.52/0.70          | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70          | (v1_xboole_0 @ sk_B)
% 0.52/0.70          | (v1_xboole_0 @ X0)
% 0.52/0.70          | (v1_funct_1 @ 
% 0.52/0.70             (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E)))),
% 0.52/0.70      inference('demod', [status(thm)], ['128', '129', '130'])).
% 0.52/0.70  thf('132', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E))
% 0.52/0.70          | (v1_xboole_0 @ X0)
% 0.52/0.70          | (v1_xboole_0 @ sk_B)
% 0.52/0.70          | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0)))),
% 0.52/0.70      inference('simplify', [status(thm)], ['131'])).
% 0.52/0.70  thf('133', plain,
% 0.52/0.70      (((v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_funct_1 @ 
% 0.52/0.70           (k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['125', '132'])).
% 0.52/0.70  thf('134', plain,
% 0.52/0.70      (((v1_funct_1 @ 
% 0.52/0.70         (k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E))
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1))),
% 0.52/0.70      inference('simplify', [status(thm)], ['133'])).
% 0.52/0.70  thf('135', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('136', plain,
% 0.52/0.70      (((v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_funct_1 @ 
% 0.52/0.70           (k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E)))),
% 0.52/0.70      inference('clc', [status(thm)], ['134', '135'])).
% 0.52/0.70  thf('137', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('138', plain,
% 0.52/0.70      ((v1_funct_1 @ 
% 0.52/0.70        (k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E))),
% 0.52/0.70      inference('clc', [status(thm)], ['136', '137'])).
% 0.52/0.70  thf('139', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['10', '11'])).
% 0.52/0.70  thf('140', plain,
% 0.52/0.70      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.52/0.70         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 0.52/0.70          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.52/0.70      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.52/0.70  thf('141', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['139', '140'])).
% 0.52/0.70  thf('142', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.52/0.70      inference('demod', [status(thm)], ['87', '88'])).
% 0.52/0.70  thf('143', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         ((k9_subset_1 @ X0 @ X1 @ X0) = (k3_xboole_0 @ X1 @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['139', '140'])).
% 0.52/0.70  thf('144', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.52/0.70      inference('demod', [status(thm)], ['87', '88'])).
% 0.52/0.70  thf('145', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('146', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('147', plain, ((v1_funct_1 @ sk_E)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('148', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['10', '11'])).
% 0.52/0.70  thf('149', plain,
% 0.52/0.70      (((v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | ((k2_partfun1 @ (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B @ 
% 0.52/0.70            (k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.52/0.70            sk_C_1) = (sk_E))
% 0.52/0.70        | ((k7_relat_1 @ sk_E @ (k3_xboole_0 @ sk_C_1 @ sk_C_1))
% 0.52/0.70            != (k7_relat_1 @ sk_E @ (k3_xboole_0 @ sk_C_1 @ sk_C_1)))
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1))),
% 0.52/0.70      inference('demod', [status(thm)],
% 0.52/0.70                ['106', '107', '108', '109', '110', '124', '138', '141', 
% 0.52/0.70                 '142', '143', '144', '145', '146', '147', '148'])).
% 0.52/0.70  thf('150', plain,
% 0.52/0.70      ((((k2_partfun1 @ (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B @ 
% 0.52/0.70          (k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ sk_C_1)
% 0.52/0.70          = (sk_E))
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_B))),
% 0.52/0.70      inference('simplify', [status(thm)], ['149'])).
% 0.52/0.70  thf('151', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('152', plain,
% 0.52/0.70      (((v1_xboole_0 @ sk_B)
% 0.52/0.70        | ((k2_partfun1 @ (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B @ 
% 0.52/0.70            (k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.52/0.70            sk_C_1) = (sk_E)))),
% 0.52/0.70      inference('clc', [status(thm)], ['150', '151'])).
% 0.52/0.70  thf('153', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('154', plain,
% 0.52/0.70      (((k2_partfun1 @ (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B @ 
% 0.52/0.70         (k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ sk_C_1)
% 0.52/0.70         = (sk_E))),
% 0.52/0.70      inference('clc', [status(thm)], ['152', '153'])).
% 0.52/0.70  thf('155', plain,
% 0.52/0.70      ((m1_subset_1 @ 
% 0.52/0.70        (k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.52/0.70        (k1_zfmisc_1 @ 
% 0.52/0.70         (k2_zfmisc_1 @ (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B)))),
% 0.52/0.70      inference('clc', [status(thm)], ['101', '102'])).
% 0.52/0.70  thf('156', plain,
% 0.52/0.70      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.52/0.70          | ~ (v1_funct_1 @ X33)
% 0.52/0.70          | ((k2_partfun1 @ X34 @ X35 @ X33 @ X36) = (k7_relat_1 @ X33 @ X36)))),
% 0.52/0.70      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.52/0.70  thf('157', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (((k2_partfun1 @ (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B @ 
% 0.52/0.70            (k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ X0)
% 0.52/0.70            = (k7_relat_1 @ 
% 0.52/0.70               (k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ X0))
% 0.52/0.70          | ~ (v1_funct_1 @ 
% 0.52/0.70               (k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['155', '156'])).
% 0.52/0.70  thf('158', plain,
% 0.52/0.70      ((v1_funct_1 @ 
% 0.52/0.70        (k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E))),
% 0.52/0.70      inference('clc', [status(thm)], ['136', '137'])).
% 0.52/0.70  thf('159', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((k2_partfun1 @ (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B @ 
% 0.52/0.70           (k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ X0)
% 0.52/0.70           = (k7_relat_1 @ 
% 0.52/0.70              (k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ X0))),
% 0.52/0.70      inference('demod', [status(thm)], ['157', '158'])).
% 0.52/0.70  thf('160', plain,
% 0.52/0.70      (((k7_relat_1 @ 
% 0.52/0.70         (k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ sk_C_1)
% 0.52/0.70         = (sk_E))),
% 0.52/0.70      inference('demod', [status(thm)], ['154', '159'])).
% 0.52/0.70  thf('161', plain,
% 0.52/0.70      (![X0 : $i, X1 : $i]:
% 0.52/0.70         (((k7_relat_1 @ (k7_relat_1 @ X1 @ X0) @ k1_xboole_0) = (k1_xboole_0))
% 0.52/0.70          | ~ (v1_relat_1 @ X1))),
% 0.52/0.70      inference('sup-', [status(thm)], ['16', '17'])).
% 0.52/0.70  thf('162', plain,
% 0.52/0.70      ((((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))
% 0.52/0.70        | ~ (v1_relat_1 @ 
% 0.52/0.70             (k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E)))),
% 0.52/0.70      inference('sup+', [status(thm)], ['160', '161'])).
% 0.52/0.70  thf('163', plain,
% 0.52/0.70      ((m1_subset_1 @ 
% 0.52/0.70        (k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E) @ 
% 0.52/0.70        (k1_zfmisc_1 @ 
% 0.52/0.70         (k2_zfmisc_1 @ (k4_subset_1 @ sk_C_1 @ sk_C_1 @ sk_C_1) @ sk_B)))),
% 0.52/0.70      inference('clc', [status(thm)], ['101', '102'])).
% 0.52/0.70  thf(cc1_relset_1, axiom,
% 0.52/0.70    (![A:$i,B:$i,C:$i]:
% 0.52/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.52/0.70       ( v1_relat_1 @ C ) ))).
% 0.52/0.70  thf('164', plain,
% 0.52/0.70      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.52/0.70         ((v1_relat_1 @ X30)
% 0.52/0.70          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.52/0.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.52/0.70  thf('165', plain,
% 0.52/0.70      ((v1_relat_1 @ 
% 0.52/0.70        (k1_tmap_1 @ sk_C_1 @ sk_B @ sk_C_1 @ sk_C_1 @ sk_E @ sk_E))),
% 0.52/0.70      inference('sup-', [status(thm)], ['163', '164'])).
% 0.52/0.70  thf('166', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.70      inference('demod', [status(thm)], ['162', '165'])).
% 0.52/0.70  thf('167', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.52/0.70      inference('sup-', [status(thm)], ['73', '74'])).
% 0.52/0.70  thf('168', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['82', '83'])).
% 0.52/0.70  thf('169', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('170', plain,
% 0.52/0.70      (![X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.52/0.70         (~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.52/0.70          | ~ (v1_funct_1 @ X33)
% 0.52/0.70          | ((k2_partfun1 @ X34 @ X35 @ X33 @ X36) = (k7_relat_1 @ X33 @ X36)))),
% 0.52/0.70      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.52/0.70  thf('171', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 0.52/0.70          | ~ (v1_funct_1 @ sk_F))),
% 0.52/0.70      inference('sup-', [status(thm)], ['169', '170'])).
% 0.52/0.70  thf('172', plain, ((v1_funct_1 @ sk_F)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('173', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.52/0.70      inference('demod', [status(thm)], ['171', '172'])).
% 0.52/0.70  thf('174', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('175', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('176', plain, ((v1_funct_1 @ sk_E)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('177', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('178', plain,
% 0.52/0.70      (((v1_xboole_0 @ sk_D)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_A)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_D)
% 0.52/0.70        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.52/0.70            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.52/0.70            = (sk_E))
% 0.52/0.70        | ~ (v1_funct_2 @ 
% 0.52/0.70             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.52/0.70             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 0.52/0.70        | ~ (v1_funct_1 @ 
% 0.52/0.70             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.52/0.70        | ((k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_A))),
% 0.52/0.70      inference('demod', [status(thm)],
% 0.52/0.70                ['68', '69', '70', '71', '72', '75', '84', '89', '166', '167', 
% 0.52/0.70                 '168', '173', '174', '175', '176', '177'])).
% 0.52/0.70  thf('179', plain,
% 0.52/0.70      ((((k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.52/0.70        | ~ (v1_funct_1 @ 
% 0.52/0.70             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.52/0.70        | ~ (v1_funct_2 @ 
% 0.52/0.70             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.52/0.70             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 0.52/0.70        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.52/0.70            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.52/0.70            = (sk_E))
% 0.52/0.70        | (v1_xboole_0 @ sk_A)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_D))),
% 0.52/0.70      inference('simplify', [status(thm)], ['178'])).
% 0.52/0.70  thf('180', plain,
% 0.52/0.70      (((v1_xboole_0 @ sk_D)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_A)
% 0.52/0.70        | (v1_xboole_0 @ sk_D)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_A)
% 0.52/0.70        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.52/0.70            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.52/0.70            = (sk_E))
% 0.52/0.70        | ~ (v1_funct_1 @ 
% 0.52/0.70             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.52/0.70        | ((k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['50', '179'])).
% 0.52/0.70  thf('181', plain,
% 0.52/0.70      ((((k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.52/0.70        | ~ (v1_funct_1 @ 
% 0.52/0.70             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.52/0.70        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.52/0.70            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.52/0.70            = (sk_E))
% 0.52/0.70        | (v1_xboole_0 @ sk_A)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_D))),
% 0.52/0.70      inference('simplify', [status(thm)], ['180'])).
% 0.52/0.70  thf('182', plain,
% 0.52/0.70      ((((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.52/0.70          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.52/0.70          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.52/0.70              (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))
% 0.52/0.70        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.52/0.70            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.52/0.70            != (sk_E))
% 0.52/0.70        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.52/0.70            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.70            != (sk_F)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('183', plain,
% 0.52/0.70      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.52/0.70          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.52/0.70          != (sk_E)))
% 0.52/0.70         <= (~
% 0.52/0.70             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.52/0.70                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.52/0.70                sk_C_1) = (sk_E))))),
% 0.52/0.70      inference('split', [status(esa)], ['182'])).
% 0.52/0.70  thf('184', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X0)
% 0.52/0.70          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.52/0.70      inference('simplify', [status(thm)], ['19'])).
% 0.52/0.70  thf('185', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X0)
% 0.52/0.70          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.52/0.70      inference('simplify', [status(thm)], ['19'])).
% 0.52/0.70  thf('186', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.52/0.70      inference('demod', [status(thm)], ['171', '172'])).
% 0.52/0.70  thf('187', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.52/0.70      inference('sup-', [status(thm)], ['73', '74'])).
% 0.52/0.70  thf('188', plain,
% 0.52/0.70      ((((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.52/0.70          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.52/0.70          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.52/0.70              (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))))
% 0.52/0.70         <= (~
% 0.52/0.70             (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.52/0.70                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.52/0.70                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.52/0.70                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.52/0.70      inference('split', [status(esa)], ['182'])).
% 0.52/0.70  thf('189', plain,
% 0.52/0.70      ((((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.52/0.70          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.52/0.70          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C_1 @ sk_D))))
% 0.52/0.70         <= (~
% 0.52/0.70             (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.52/0.70                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.52/0.70                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.52/0.70                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.52/0.70      inference('sup-', [status(thm)], ['187', '188'])).
% 0.52/0.70  thf('190', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.52/0.70      inference('sup-', [status(thm)], ['73', '74'])).
% 0.52/0.70  thf('191', plain,
% 0.52/0.70      ((((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C_1 @ sk_D))
% 0.52/0.70          != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ (k3_xboole_0 @ sk_C_1 @ sk_D))))
% 0.52/0.70         <= (~
% 0.52/0.70             (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.52/0.70                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.52/0.70                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.52/0.70                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.52/0.70      inference('demod', [status(thm)], ['189', '190'])).
% 0.52/0.70  thf('192', plain,
% 0.52/0.70      ((((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ (k3_xboole_0 @ sk_C_1 @ sk_D))
% 0.52/0.70          != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C_1 @ sk_D))))
% 0.52/0.70         <= (~
% 0.52/0.70             (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.52/0.70                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.52/0.70                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.52/0.70                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.52/0.70      inference('sup-', [status(thm)], ['186', '191'])).
% 0.52/0.70  thf('193', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['82', '83'])).
% 0.52/0.70  thf('194', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.52/0.70      inference('demod', [status(thm)], ['87', '88'])).
% 0.52/0.70  thf('195', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['82', '83'])).
% 0.52/0.70  thf('196', plain,
% 0.52/0.70      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0)))
% 0.52/0.70         <= (~
% 0.52/0.70             (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.52/0.70                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.52/0.70                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.52/0.70                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.52/0.70      inference('demod', [status(thm)], ['192', '193', '194', '195'])).
% 0.52/0.70  thf('197', plain,
% 0.52/0.70      (((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.52/0.70         | ~ (v1_relat_1 @ sk_F)))
% 0.52/0.70         <= (~
% 0.52/0.70             (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.52/0.70                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.52/0.70                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.52/0.70                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.52/0.70      inference('sup-', [status(thm)], ['185', '196'])).
% 0.52/0.70  thf('198', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('199', plain,
% 0.52/0.70      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.52/0.70         ((v1_relat_1 @ X30)
% 0.52/0.70          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.52/0.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.52/0.70  thf('200', plain, ((v1_relat_1 @ sk_F)),
% 0.52/0.70      inference('sup-', [status(thm)], ['198', '199'])).
% 0.52/0.70  thf('201', plain,
% 0.52/0.70      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0)))
% 0.52/0.70         <= (~
% 0.52/0.70             (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.52/0.70                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.52/0.70                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.52/0.70                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.52/0.70      inference('demod', [status(thm)], ['197', '200'])).
% 0.52/0.70  thf('202', plain,
% 0.52/0.70      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_E)))
% 0.52/0.70         <= (~
% 0.52/0.70             (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.52/0.70                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.52/0.70                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.52/0.70                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.52/0.70      inference('sup-', [status(thm)], ['184', '201'])).
% 0.52/0.70  thf('203', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('204', plain,
% 0.52/0.70      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.52/0.70         ((v1_relat_1 @ X30)
% 0.52/0.70          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.52/0.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.52/0.70  thf('205', plain, ((v1_relat_1 @ sk_E)),
% 0.52/0.70      inference('sup-', [status(thm)], ['203', '204'])).
% 0.52/0.70  thf('206', plain,
% 0.52/0.70      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.52/0.70         <= (~
% 0.52/0.70             (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.52/0.70                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.52/0.70                = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.52/0.70                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.52/0.70      inference('demod', [status(thm)], ['202', '205'])).
% 0.52/0.70  thf('207', plain,
% 0.52/0.70      ((((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.52/0.70          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.52/0.70          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.52/0.70             (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))))),
% 0.52/0.70      inference('simplify', [status(thm)], ['206'])).
% 0.52/0.70  thf('208', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         (~ (v1_relat_1 @ X0)
% 0.52/0.70          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.52/0.70      inference('simplify', [status(thm)], ['19'])).
% 0.52/0.70  thf('209', plain,
% 0.52/0.70      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.52/0.70        | (v1_xboole_0 @ sk_A)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_D))),
% 0.52/0.70      inference('demod', [status(thm)], ['33', '34'])).
% 0.52/0.70  thf('210', plain,
% 0.52/0.70      (((v1_funct_2 @ 
% 0.52/0.70         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.52/0.70         (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_A)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_D))),
% 0.52/0.70      inference('demod', [status(thm)], ['48', '49'])).
% 0.52/0.70  thf('211', plain,
% 0.52/0.70      (((m1_subset_1 @ 
% 0.52/0.70         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.52/0.70         (k1_zfmisc_1 @ 
% 0.52/0.70          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)))
% 0.52/0.70        | (v1_xboole_0 @ sk_A)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_D))),
% 0.52/0.70      inference('demod', [status(thm)], ['63', '64'])).
% 0.52/0.70  thf('212', plain,
% 0.52/0.70      (![X37 : $i, X38 : $i, X39 : $i, X40 : $i, X41 : $i, X42 : $i]:
% 0.52/0.70         ((v1_xboole_0 @ X39)
% 0.52/0.70          | (v1_xboole_0 @ X42)
% 0.52/0.70          | ~ (m1_subset_1 @ X42 @ (k1_zfmisc_1 @ X39))
% 0.52/0.70          | ~ (v1_funct_1 @ X41)
% 0.52/0.70          | ~ (v1_funct_2 @ X41 @ X42 @ X37)
% 0.52/0.70          | ~ (m1_subset_1 @ X41 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X42 @ X37)))
% 0.52/0.70          | ((k2_partfun1 @ X42 @ X37 @ X41 @ (k9_subset_1 @ X39 @ X42 @ X38))
% 0.52/0.70              != (k2_partfun1 @ X38 @ X37 @ X40 @ 
% 0.52/0.70                  (k9_subset_1 @ X39 @ X42 @ X38)))
% 0.52/0.70          | ~ (v1_funct_1 @ (k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40))
% 0.52/0.70          | ~ (v1_funct_2 @ (k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40) @ 
% 0.52/0.70               (k4_subset_1 @ X39 @ X42 @ X38) @ X37)
% 0.52/0.70          | ~ (m1_subset_1 @ (k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40) @ 
% 0.52/0.70               (k1_zfmisc_1 @ 
% 0.52/0.70                (k2_zfmisc_1 @ (k4_subset_1 @ X39 @ X42 @ X38) @ X37)))
% 0.52/0.70          | ((k2_partfun1 @ (k4_subset_1 @ X39 @ X42 @ X38) @ X37 @ 
% 0.52/0.70              (k1_tmap_1 @ X39 @ X37 @ X42 @ X38 @ X41 @ X40) @ X38) = (
% 0.52/0.70              X40))
% 0.52/0.70          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X37)))
% 0.52/0.70          | ~ (v1_funct_2 @ X40 @ X38 @ X37)
% 0.52/0.70          | ~ (v1_funct_1 @ X40)
% 0.52/0.70          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ X39))
% 0.52/0.70          | (v1_xboole_0 @ X38)
% 0.52/0.70          | (v1_xboole_0 @ X37))),
% 0.52/0.70      inference('simplify', [status(thm)], ['104'])).
% 0.52/0.70  thf('213', plain,
% 0.52/0.70      (((v1_xboole_0 @ sk_D)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_A)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_D)
% 0.52/0.70        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.52/0.70        | ~ (v1_funct_1 @ sk_F)
% 0.52/0.70        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B)
% 0.52/0.70        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))
% 0.52/0.70        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.52/0.70            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.70            = (sk_F))
% 0.52/0.70        | ~ (v1_funct_2 @ 
% 0.52/0.70             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.52/0.70             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 0.52/0.70        | ~ (v1_funct_1 @ 
% 0.52/0.70             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.52/0.70        | ((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.52/0.70            (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.52/0.70            != (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.52/0.70                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))
% 0.52/0.70        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))
% 0.52/0.70        | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)
% 0.52/0.70        | ~ (v1_funct_1 @ sk_E)
% 0.52/0.70        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_A))),
% 0.52/0.70      inference('sup-', [status(thm)], ['211', '212'])).
% 0.52/0.70  thf('214', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('215', plain, ((v1_funct_1 @ sk_F)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('216', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('217', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('218', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.52/0.70      inference('sup-', [status(thm)], ['73', '74'])).
% 0.52/0.70  thf('219', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['82', '83'])).
% 0.52/0.70  thf('220', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.52/0.70      inference('demod', [status(thm)], ['87', '88'])).
% 0.52/0.70  thf('221', plain, (((k7_relat_1 @ sk_E @ k1_xboole_0) = (k1_xboole_0))),
% 0.52/0.70      inference('demod', [status(thm)], ['162', '165'])).
% 0.52/0.70  thf('222', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.52/0.70      inference('sup-', [status(thm)], ['73', '74'])).
% 0.52/0.70  thf('223', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.52/0.70      inference('sup-', [status(thm)], ['82', '83'])).
% 0.52/0.70  thf('224', plain,
% 0.52/0.70      (![X0 : $i]:
% 0.52/0.70         ((k2_partfun1 @ sk_D @ sk_B @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.52/0.70      inference('demod', [status(thm)], ['171', '172'])).
% 0.52/0.70  thf('225', plain,
% 0.52/0.70      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B)))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('226', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('227', plain, ((v1_funct_1 @ sk_E)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('228', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('229', plain,
% 0.52/0.70      (((v1_xboole_0 @ sk_D)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_A)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_D)
% 0.52/0.70        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.52/0.70            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.70            = (sk_F))
% 0.52/0.70        | ~ (v1_funct_2 @ 
% 0.52/0.70             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.52/0.70             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 0.52/0.70        | ~ (v1_funct_1 @ 
% 0.52/0.70             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.52/0.70        | ((k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_A))),
% 0.52/0.70      inference('demod', [status(thm)],
% 0.52/0.70                ['213', '214', '215', '216', '217', '218', '219', '220', 
% 0.52/0.70                 '221', '222', '223', '224', '225', '226', '227', '228'])).
% 0.52/0.70  thf('230', plain,
% 0.52/0.70      ((((k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.52/0.70        | ~ (v1_funct_1 @ 
% 0.52/0.70             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.52/0.70        | ~ (v1_funct_2 @ 
% 0.52/0.70             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.52/0.70             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B)
% 0.52/0.70        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.52/0.70            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.70            = (sk_F))
% 0.52/0.70        | (v1_xboole_0 @ sk_A)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_D))),
% 0.52/0.70      inference('simplify', [status(thm)], ['229'])).
% 0.52/0.70  thf('231', plain,
% 0.52/0.70      (((v1_xboole_0 @ sk_D)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_A)
% 0.52/0.70        | (v1_xboole_0 @ sk_D)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_A)
% 0.52/0.70        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.52/0.70            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.70            = (sk_F))
% 0.52/0.70        | ~ (v1_funct_1 @ 
% 0.52/0.70             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.52/0.70        | ((k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['210', '230'])).
% 0.52/0.70  thf('232', plain,
% 0.52/0.70      ((((k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.52/0.70        | ~ (v1_funct_1 @ 
% 0.52/0.70             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.52/0.70        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.52/0.70            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.70            = (sk_F))
% 0.52/0.70        | (v1_xboole_0 @ sk_A)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_D))),
% 0.52/0.70      inference('simplify', [status(thm)], ['231'])).
% 0.52/0.70  thf('233', plain,
% 0.52/0.70      (((v1_xboole_0 @ sk_D)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_A)
% 0.52/0.70        | (v1_xboole_0 @ sk_D)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_A)
% 0.52/0.70        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.52/0.70            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.70            = (sk_F))
% 0.52/0.70        | ((k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['209', '232'])).
% 0.52/0.70  thf('234', plain,
% 0.52/0.70      ((((k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.52/0.70        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.52/0.70            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.70            = (sk_F))
% 0.52/0.70        | (v1_xboole_0 @ sk_A)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_D))),
% 0.52/0.70      inference('simplify', [status(thm)], ['233'])).
% 0.52/0.70  thf('235', plain,
% 0.52/0.70      ((((k1_xboole_0) != (k1_xboole_0))
% 0.52/0.70        | ~ (v1_relat_1 @ sk_F)
% 0.52/0.70        | (v1_xboole_0 @ sk_D)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_A)
% 0.52/0.70        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.52/0.70            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.70            = (sk_F)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['208', '234'])).
% 0.52/0.70  thf('236', plain, ((v1_relat_1 @ sk_F)),
% 0.52/0.70      inference('sup-', [status(thm)], ['198', '199'])).
% 0.52/0.70  thf('237', plain,
% 0.52/0.70      ((((k1_xboole_0) != (k1_xboole_0))
% 0.52/0.70        | (v1_xboole_0 @ sk_D)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_A)
% 0.52/0.70        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.52/0.70            (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.70            = (sk_F)))),
% 0.52/0.70      inference('demod', [status(thm)], ['235', '236'])).
% 0.52/0.70  thf('238', plain,
% 0.52/0.70      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.52/0.70          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.70          = (sk_F))
% 0.52/0.70        | (v1_xboole_0 @ sk_A)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_D))),
% 0.52/0.70      inference('simplify', [status(thm)], ['237'])).
% 0.52/0.70  thf('239', plain,
% 0.52/0.70      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.52/0.70          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.70          != (sk_F)))
% 0.52/0.70         <= (~
% 0.52/0.70             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.52/0.70                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.70                = (sk_F))))),
% 0.52/0.70      inference('split', [status(esa)], ['182'])).
% 0.52/0.70  thf('240', plain,
% 0.52/0.70      (((((sk_F) != (sk_F))
% 0.52/0.70         | (v1_xboole_0 @ sk_D)
% 0.52/0.70         | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70         | (v1_xboole_0 @ sk_B)
% 0.52/0.70         | (v1_xboole_0 @ sk_A)))
% 0.52/0.70         <= (~
% 0.52/0.70             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.52/0.70                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.70                = (sk_F))))),
% 0.52/0.70      inference('sup-', [status(thm)], ['238', '239'])).
% 0.52/0.70  thf('241', plain,
% 0.52/0.70      ((((v1_xboole_0 @ sk_A)
% 0.52/0.70         | (v1_xboole_0 @ sk_B)
% 0.52/0.70         | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70         | (v1_xboole_0 @ sk_D)))
% 0.52/0.70         <= (~
% 0.52/0.70             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.52/0.70                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.70                = (sk_F))))),
% 0.52/0.70      inference('simplify', [status(thm)], ['240'])).
% 0.52/0.70  thf('242', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('243', plain,
% 0.52/0.70      ((((v1_xboole_0 @ sk_C_1) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A)))
% 0.52/0.70         <= (~
% 0.52/0.70             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.52/0.70                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.70                = (sk_F))))),
% 0.52/0.70      inference('sup-', [status(thm)], ['241', '242'])).
% 0.52/0.70  thf('244', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('245', plain,
% 0.52/0.70      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B)))
% 0.52/0.70         <= (~
% 0.52/0.70             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.52/0.70                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.70                = (sk_F))))),
% 0.52/0.70      inference('clc', [status(thm)], ['243', '244'])).
% 0.52/0.70  thf('246', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('247', plain,
% 0.52/0.70      (((v1_xboole_0 @ sk_B))
% 0.52/0.70         <= (~
% 0.52/0.70             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.52/0.70                (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.70                = (sk_F))))),
% 0.52/0.70      inference('clc', [status(thm)], ['245', '246'])).
% 0.52/0.70  thf('248', plain, (~ (v1_xboole_0 @ sk_B)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('249', plain,
% 0.52/0.70      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.52/0.70          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.70          = (sk_F)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['247', '248'])).
% 0.52/0.70  thf('250', plain,
% 0.52/0.70      (~
% 0.52/0.70       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.52/0.70          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.52/0.70          = (sk_E))) | 
% 0.52/0.70       ~
% 0.52/0.70       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.52/0.70          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.52/0.70          = (sk_F))) | 
% 0.52/0.70       ~
% 0.52/0.70       (((k2_partfun1 @ sk_C_1 @ sk_B @ sk_E @ 
% 0.52/0.70          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.52/0.70          = (k2_partfun1 @ sk_D @ sk_B @ sk_F @ 
% 0.52/0.70             (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))))),
% 0.52/0.70      inference('split', [status(esa)], ['182'])).
% 0.52/0.70  thf('251', plain,
% 0.52/0.70      (~
% 0.52/0.70       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.52/0.70          (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.52/0.70          = (sk_E)))),
% 0.52/0.70      inference('sat_resolution*', [status(thm)], ['207', '249', '250'])).
% 0.52/0.70  thf('252', plain,
% 0.52/0.70      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B @ 
% 0.52/0.70         (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.52/0.70         != (sk_E))),
% 0.52/0.70      inference('simpl_trail', [status(thm)], ['183', '251'])).
% 0.52/0.70  thf('253', plain,
% 0.52/0.70      ((((k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.52/0.70        | ~ (v1_funct_1 @ 
% 0.52/0.70             (k1_tmap_1 @ sk_A @ sk_B @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.52/0.70        | (v1_xboole_0 @ sk_A)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_D))),
% 0.52/0.70      inference('simplify_reflect-', [status(thm)], ['181', '252'])).
% 0.52/0.70  thf('254', plain,
% 0.52/0.70      (((v1_xboole_0 @ sk_D)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_A)
% 0.52/0.70        | (v1_xboole_0 @ sk_D)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_A)
% 0.52/0.70        | ((k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.52/0.70      inference('sup-', [status(thm)], ['35', '253'])).
% 0.52/0.70  thf('255', plain,
% 0.52/0.70      ((((k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.52/0.70        | (v1_xboole_0 @ sk_A)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_D))),
% 0.52/0.70      inference('simplify', [status(thm)], ['254'])).
% 0.52/0.70  thf('256', plain,
% 0.52/0.70      ((((k1_xboole_0) != (k1_xboole_0))
% 0.52/0.70        | ~ (v1_relat_1 @ sk_F)
% 0.52/0.70        | (v1_xboole_0 @ sk_D)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_A))),
% 0.52/0.70      inference('sup-', [status(thm)], ['20', '255'])).
% 0.52/0.70  thf('257', plain, ((v1_relat_1 @ sk_F)),
% 0.52/0.70      inference('sup-', [status(thm)], ['198', '199'])).
% 0.52/0.70  thf('258', plain,
% 0.52/0.70      ((((k1_xboole_0) != (k1_xboole_0))
% 0.52/0.70        | (v1_xboole_0 @ sk_D)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_A))),
% 0.52/0.70      inference('demod', [status(thm)], ['256', '257'])).
% 0.52/0.70  thf('259', plain,
% 0.52/0.70      (((v1_xboole_0 @ sk_A)
% 0.52/0.70        | (v1_xboole_0 @ sk_B)
% 0.52/0.70        | (v1_xboole_0 @ sk_C_1)
% 0.52/0.70        | (v1_xboole_0 @ sk_D))),
% 0.52/0.70      inference('simplify', [status(thm)], ['258'])).
% 0.52/0.70  thf('260', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('261', plain,
% 0.52/0.70      (((v1_xboole_0 @ sk_C_1) | (v1_xboole_0 @ sk_B) | (v1_xboole_0 @ sk_A))),
% 0.52/0.70      inference('sup-', [status(thm)], ['259', '260'])).
% 0.52/0.70  thf('262', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('263', plain, (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B))),
% 0.52/0.70      inference('clc', [status(thm)], ['261', '262'])).
% 0.52/0.70  thf('264', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.52/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.52/0.70  thf('265', plain, ((v1_xboole_0 @ sk_B)),
% 0.52/0.70      inference('clc', [status(thm)], ['263', '264'])).
% 0.52/0.70  thf('266', plain, ($false), inference('demod', [status(thm)], ['0', '265'])).
% 0.52/0.70  
% 0.52/0.70  % SZS output end Refutation
% 0.52/0.70  
% 0.52/0.71  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
