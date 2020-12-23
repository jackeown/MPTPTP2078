%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6PIWjIjDin

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:09:04 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :  229 ( 653 expanded)
%              Number of leaves         :   37 ( 205 expanded)
%              Depth                    :   40
%              Number of atoms          : 3768 (27764 expanded)
%              Number of equality atoms :  134 ( 891 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

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
    ! [X6: $i,X7: $i] :
      ( ( r1_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
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
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X13 ) @ X14 )
      | ( ( k7_relat_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('7',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
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

thf('10',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ( v1_xboole_0 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X35 ) )
      | ( v1_xboole_0 @ X32 )
      | ( v1_xboole_0 @ X33 )
      | ( v1_xboole_0 @ X35 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X34 @ X33 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X35 @ X33 @ X32 @ X34 @ X31 @ X36 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('11',plain,(
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
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
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
    inference(demod,[status(thm)],['11','12','13'])).

thf('15',plain,(
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
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['15','16','17'])).

thf('19',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['7','18'])).

thf('20',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ( v1_xboole_0 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X35 ) )
      | ( v1_xboole_0 @ X32 )
      | ( v1_xboole_0 @ X33 )
      | ( v1_xboole_0 @ X35 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X34 @ X33 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X35 @ X33 @ X32 @ X34 @ X31 @ X36 ) @ ( k4_subset_1 @ X35 @ X32 @ X34 ) @ X33 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('26',plain,(
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
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
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
    inference(demod,[status(thm)],['26','27','28'])).

thf('30',plain,(
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
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_D ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['22','33'])).

thf('35',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('37',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,(
    ! [X31: $i,X32: $i,X33: $i,X34: $i,X35: $i,X36: $i] :
      ( ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) )
      | ~ ( v1_funct_2 @ X31 @ X32 @ X33 )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ X35 ) )
      | ( v1_xboole_0 @ X34 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ X35 ) )
      | ( v1_xboole_0 @ X32 )
      | ( v1_xboole_0 @ X33 )
      | ( v1_xboole_0 @ X35 )
      | ~ ( v1_funct_1 @ X36 )
      | ~ ( v1_funct_2 @ X36 @ X34 @ X33 )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X33 ) ) )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X35 @ X33 @ X32 @ X34 @ X31 @ X36 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X35 @ X32 @ X34 ) @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('41',plain,(
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
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('43',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
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
    inference(demod,[status(thm)],['41','42','43'])).

thf('45',plain,(
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
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C_1 @ sk_D ) @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['45','46','47'])).

thf('49',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['37','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
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
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) )
      | ( X30
       != ( k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X26 @ X29 @ X25 ) @ X24 @ X30 @ X29 )
        = X28 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X26 @ X29 @ X25 ) @ X24 ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( k4_subset_1 @ X26 @ X29 @ X25 ) @ X24 )
      | ~ ( v1_funct_1 @ X30 )
      | ( ( k2_partfun1 @ X29 @ X24 @ X28 @ ( k9_subset_1 @ X26 @ X29 @ X25 ) )
       != ( k2_partfun1 @ X25 @ X24 @ X27 @ ( k9_subset_1 @ X26 @ X29 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X24 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X26 ) )
      | ( v1_xboole_0 @ X29 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('53',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ( v1_xboole_0 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X24 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X24 ) ) )
      | ( ( k2_partfun1 @ X29 @ X24 @ X28 @ ( k9_subset_1 @ X26 @ X29 @ X25 ) )
       != ( k2_partfun1 @ X25 @ X24 @ X27 @ ( k9_subset_1 @ X26 @ X29 @ X25 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27 ) @ ( k4_subset_1 @ X26 @ X29 @ X25 ) @ X24 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X26 @ X29 @ X25 ) @ X24 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X26 @ X29 @ X25 ) @ X24 @ ( k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27 ) @ X29 )
        = X28 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X25 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( v1_xboole_0 @ X25 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,
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
    ! [X10: $i,X11: $i,X12: $i] :
      ( ( ( k9_subset_1 @ X12 @ X10 @ X11 )
        = ( k3_xboole_0 @ X10 @ X11 ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    r1_subset_1 @ sk_C_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r1_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ( ( r1_subset_1 @ A @ B )
      <=> ( r1_xboole_0 @ A @ B ) ) ) )).

thf('63',plain,(
    ! [X15: $i,X16: $i] :
      ( ( v1_xboole_0 @ X15 )
      | ( v1_xboole_0 @ X16 )
      | ( r1_xboole_0 @ X15 @ X16 )
      | ~ ( r1_subset_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_subset_1])).

thf('64',plain,
    ( ( r1_xboole_0 @ sk_C_1 @ sk_D )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r1_xboole_0 @ sk_C_1 @ sk_D ) ),
    inference(clc,[status(thm)],['64','65'])).

thf('67',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    r1_xboole_0 @ sk_C_1 @ sk_D ),
    inference(clc,[status(thm)],['66','67'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('69',plain,(
    ! [X3: $i,X4: $i] :
      ( ( ( k3_xboole_0 @ X3 @ X4 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('70',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('72',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ( ( k2_partfun1 @ X21 @ X22 @ X20 @ X23 )
        = ( k7_relat_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('77',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['68','69'])).

thf('78',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('79',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) )
      | ~ ( v1_funct_1 @ X20 )
      | ( ( k2_partfun1 @ X21 @ X22 @ X20 @ X23 )
        = ( k7_relat_1 @ X20 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('80',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['78','79'])).

thf('81',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('83',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('84',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('86',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('87',plain,
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
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['54','55','56','57','58','61','70','75','76','77','82','83','84','85','86'])).

thf('88',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['87'])).

thf('89',plain,
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
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['36','88'])).

thf('90',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['89'])).

thf('91',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E ) ),
    inference(split,[status(esa)],['91'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('93',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('94',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_xboole_0 @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('95',plain,(
    ! [X0: $i] :
      ( r1_xboole_0 @ X0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['93','94'])).

thf('96',plain,(
    ! [X13: $i,X14: $i] :
      ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ X13 ) @ X14 )
      | ( ( k7_relat_1 @ X13 @ X14 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('97',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('98',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k7_relat_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['95','96'])).

thf('99',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('100',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('101',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(split,[status(esa)],['91'])).

thf('102',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k3_xboole_0 @ sk_C_1 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['100','101'])).

thf('103',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('104',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k3_xboole_0 @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k3_xboole_0 @ sk_C_1 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['102','103'])).

thf('105',plain,
    ( ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k3_xboole_0 @ sk_C_1 @ sk_D ) )
     != ( k7_relat_1 @ sk_F @ ( k3_xboole_0 @ sk_C_1 @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['99','104'])).

thf('106',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['68','69'])).

thf('107',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('108',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['68','69'])).

thf('109',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['105','106','107','108'])).

thf('110',plain,
    ( ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_F ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['98','109'])).

thf('111',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('112',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('113',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['111','112'])).

thf('114',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['110','113'])).

thf('115',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_E ) )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['97','114'])).

thf('116',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('117',plain,(
    ! [X17: $i,X18: $i,X19: $i] :
      ( ( v1_relat_1 @ X17 )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('118',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['116','117'])).

thf('119',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['115','118'])).

thf('120',plain,
    ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ),
    inference(simplify,[status(thm)],['119'])).

thf('121',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('122',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('123',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('124',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['34','35'])).

thf('125',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['49','50'])).

thf('126',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v1_xboole_0 @ X24 )
      | ( v1_xboole_0 @ X25 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_funct_2 @ X27 @ X25 @ X24 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) )
      | ( X30
       != ( k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X26 @ X29 @ X25 ) @ X24 @ X30 @ X25 )
        = X27 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X26 @ X29 @ X25 ) @ X24 ) ) )
      | ~ ( v1_funct_2 @ X30 @ ( k4_subset_1 @ X26 @ X29 @ X25 ) @ X24 )
      | ~ ( v1_funct_1 @ X30 )
      | ( ( k2_partfun1 @ X29 @ X24 @ X28 @ ( k9_subset_1 @ X26 @ X29 @ X25 ) )
       != ( k2_partfun1 @ X25 @ X24 @ X27 @ ( k9_subset_1 @ X26 @ X29 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X24 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X26 ) )
      | ( v1_xboole_0 @ X29 )
      | ( v1_xboole_0 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('127',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( v1_xboole_0 @ X26 )
      | ( v1_xboole_0 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X29 @ X24 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X24 ) ) )
      | ( ( k2_partfun1 @ X29 @ X24 @ X28 @ ( k9_subset_1 @ X26 @ X29 @ X25 ) )
       != ( k2_partfun1 @ X25 @ X24 @ X27 @ ( k9_subset_1 @ X26 @ X29 @ X25 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27 ) @ ( k4_subset_1 @ X26 @ X29 @ X25 ) @ X24 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X26 @ X29 @ X25 ) @ X24 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X26 @ X29 @ X25 ) @ X24 @ ( k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27 ) @ X25 )
        = X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X24 ) ) )
      | ~ ( v1_funct_2 @ X27 @ X25 @ X24 )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) )
      | ( v1_xboole_0 @ X25 )
      | ( v1_xboole_0 @ X24 ) ) ),
    inference(simplify,[status(thm)],['126'])).

thf('128',plain,
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
    inference('sup-',[status(thm)],['125','127'])).

thf('129',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('130',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('131',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('132',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('133',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('134',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['68','69'])).

thf('135',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('136',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('137',plain,
    ( ( k3_xboole_0 @ sk_C_1 @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['68','69'])).

thf('138',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['80','81'])).

thf('139',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C_1 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('140',plain,(
    v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('141',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('142',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('143',plain,
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
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['128','129','130','131','132','133','134','135','136','137','138','139','140','141','142'])).

thf('144',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['143'])).

thf('145',plain,
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
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['124','144'])).

thf('146',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['145'])).

thf('147',plain,
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
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['123','146'])).

thf('148',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference('sup-',[status(thm)],['122','148'])).

thf('150',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['111','112'])).

thf('151',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('152',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference(demod,[status(thm)],['149','150','151'])).

thf('153',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['121','152'])).

thf('154',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['116','117'])).

thf('155',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('156',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('157',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference(simplify,[status(thm)],['156'])).

thf('158',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['91'])).

thf('159',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['157','158'])).

thf('160',plain,
    ( ( ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['159'])).

thf('161',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('162',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C_1 ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['160','161'])).

thf('163',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('164',plain,
    ( ( ( v1_xboole_0 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['162','163'])).

thf('165',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['164','165'])).

thf('167',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['166','167'])).

thf('169',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C_1 @ sk_D ) ) ) ),
    inference(split,[status(esa)],['91'])).

thf('170',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['120','168','169'])).

thf('171',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C_1 @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) @ sk_C_1 )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['92','170'])).

thf('172',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['90','171'])).

thf('173',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','172'])).

thf('174',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['173'])).

thf('175',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['6','174'])).

thf('176',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['111','112'])).

thf('177',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('178',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['175','176','177'])).

thf('179',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['5','178'])).

thf('180',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['116','117'])).

thf('181',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('182',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['179','180','181'])).

thf('183',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['182'])).

thf('184',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('185',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['183','184'])).

thf('186',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('187',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['185','186'])).

thf('188',plain,(
    ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(clc,[status(thm)],['187','188'])).

thf('190',plain,(
    $false ),
    inference(demod,[status(thm)],['0','189'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.6PIWjIjDin
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:14:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.46/0.64  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.46/0.64  % Solved by: fo/fo7.sh
% 0.46/0.64  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.64  % done 309 iterations in 0.180s
% 0.46/0.64  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.46/0.64  % SZS output start Refutation
% 0.46/0.64  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.46/0.64  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.46/0.64  thf(sk_F_type, type, sk_F: $i).
% 0.46/0.64  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.46/0.64  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.46/0.64  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.46/0.64  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.46/0.64  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.46/0.64  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 0.46/0.64  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.64  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.46/0.64  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.46/0.64  thf(sk_E_type, type, sk_E: $i).
% 0.46/0.64  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.64  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.46/0.64  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.46/0.64  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.46/0.64  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.46/0.64  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.64  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.64  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.46/0.64  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.46/0.64  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.46/0.64  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.46/0.64  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.46/0.64  thf(t6_tmap_1, conjecture,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.46/0.64           ( ![C:$i]:
% 0.46/0.64             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.46/0.64                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.46/0.64               ( ![D:$i]:
% 0.46/0.64                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.46/0.64                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.46/0.64                   ( ( r1_subset_1 @ C @ D ) =>
% 0.46/0.64                     ( ![E:$i]:
% 0.46/0.64                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.46/0.64                           ( m1_subset_1 @
% 0.46/0.64                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.46/0.64                         ( ![F:$i]:
% 0.46/0.64                           ( ( ( v1_funct_1 @ F ) & 
% 0.46/0.64                               ( v1_funct_2 @ F @ D @ B ) & 
% 0.46/0.64                               ( m1_subset_1 @
% 0.46/0.64                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.46/0.64                             ( ( ( k2_partfun1 @
% 0.46/0.64                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.46/0.64                                 ( k2_partfun1 @
% 0.46/0.64                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.46/0.64                               ( ( k2_partfun1 @
% 0.46/0.64                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.46/0.64                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.46/0.64                                 ( E ) ) & 
% 0.46/0.64                               ( ( k2_partfun1 @
% 0.46/0.64                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.46/0.64                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.46/0.64                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.64  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.64    (~( ![A:$i]:
% 0.46/0.64        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.64          ( ![B:$i]:
% 0.46/0.64            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.46/0.64              ( ![C:$i]:
% 0.46/0.64                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.46/0.64                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.46/0.64                  ( ![D:$i]:
% 0.46/0.64                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.46/0.64                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.46/0.64                      ( ( r1_subset_1 @ C @ D ) =>
% 0.46/0.64                        ( ![E:$i]:
% 0.46/0.64                          ( ( ( v1_funct_1 @ E ) & 
% 0.46/0.64                              ( v1_funct_2 @ E @ C @ B ) & 
% 0.46/0.64                              ( m1_subset_1 @
% 0.46/0.64                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.46/0.64                            ( ![F:$i]:
% 0.46/0.64                              ( ( ( v1_funct_1 @ F ) & 
% 0.46/0.64                                  ( v1_funct_2 @ F @ D @ B ) & 
% 0.46/0.64                                  ( m1_subset_1 @
% 0.46/0.64                                    F @ 
% 0.46/0.64                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.46/0.64                                ( ( ( k2_partfun1 @
% 0.46/0.64                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.46/0.64                                    ( k2_partfun1 @
% 0.46/0.64                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.46/0.64                                  ( ( k2_partfun1 @
% 0.46/0.64                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.46/0.64                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.46/0.64                                    ( E ) ) & 
% 0.46/0.64                                  ( ( k2_partfun1 @
% 0.46/0.64                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.46/0.64                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.46/0.64                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.46/0.64    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 0.46/0.64  thf('0', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(t3_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.46/0.64            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.46/0.64       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.46/0.64            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.46/0.64  thf('1', plain,
% 0.46/0.64      (![X6 : $i, X7 : $i]:
% 0.46/0.64         ((r1_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.46/0.64      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.46/0.64  thf(d1_xboole_0, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.46/0.64  thf('2', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.46/0.64      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.46/0.64  thf('3', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.64  thf(t95_relat_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( v1_relat_1 @ B ) =>
% 0.46/0.64       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.46/0.64         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.46/0.64  thf('4', plain,
% 0.46/0.64      (![X13 : $i, X14 : $i]:
% 0.46/0.64         (~ (r1_xboole_0 @ (k1_relat_1 @ X13) @ X14)
% 0.46/0.64          | ((k7_relat_1 @ X13 @ X14) = (k1_xboole_0))
% 0.46/0.64          | ~ (v1_relat_1 @ X13))),
% 0.46/0.64      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.46/0.64  thf('5', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (v1_xboole_0 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X1)
% 0.46/0.64          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.64  thf('6', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (v1_xboole_0 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X1)
% 0.46/0.64          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.64  thf('7', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('8', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('9', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(dt_k1_tmap_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.46/0.64     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.46/0.64         ( ~( v1_xboole_0 @ C ) ) & 
% 0.46/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 0.46/0.64         ( ~( v1_xboole_0 @ D ) ) & 
% 0.46/0.64         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 0.46/0.64         ( v1_funct_2 @ E @ C @ B ) & 
% 0.46/0.64         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.46/0.64         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.46/0.64         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.46/0.64       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.46/0.64         ( v1_funct_2 @
% 0.46/0.64           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.46/0.64           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.46/0.64         ( m1_subset_1 @
% 0.46/0.64           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.46/0.64           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 0.46/0.64  thf('10', plain,
% 0.46/0.64      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.46/0.64          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 0.46/0.64          | ~ (v1_funct_1 @ X31)
% 0.46/0.64          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.46/0.64          | (v1_xboole_0 @ X34)
% 0.46/0.64          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X35))
% 0.46/0.64          | (v1_xboole_0 @ X32)
% 0.46/0.64          | (v1_xboole_0 @ X33)
% 0.46/0.64          | (v1_xboole_0 @ X35)
% 0.46/0.64          | ~ (v1_funct_1 @ X36)
% 0.46/0.64          | ~ (v1_funct_2 @ X36 @ X34 @ X33)
% 0.46/0.64          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.46/0.64          | (v1_funct_1 @ (k1_tmap_1 @ X35 @ X33 @ X32 @ X34 @ X31 @ X36)))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.46/0.64  thf('11', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_E @ X0))
% 0.46/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 0.46/0.64          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | (v1_xboole_0 @ X2)
% 0.46/0.64          | (v1_xboole_0 @ sk_B_1)
% 0.46/0.64          | (v1_xboole_0 @ sk_C_1)
% 0.46/0.64          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X2))
% 0.46/0.64          | (v1_xboole_0 @ X1)
% 0.46/0.64          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.46/0.64          | ~ (v1_funct_1 @ sk_E)
% 0.46/0.64          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['9', '10'])).
% 0.46/0.64  thf('12', plain, ((v1_funct_1 @ sk_E)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('13', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('14', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B_1 @ sk_C_1 @ X1 @ sk_E @ X0))
% 0.46/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 0.46/0.64          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 0.46/0.64          | ~ (v1_funct_1 @ X0)
% 0.46/0.64          | (v1_xboole_0 @ X2)
% 0.46/0.64          | (v1_xboole_0 @ sk_B_1)
% 0.46/0.64          | (v1_xboole_0 @ sk_C_1)
% 0.46/0.64          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X2))
% 0.46/0.64          | (v1_xboole_0 @ X1)
% 0.46/0.64          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.46/0.64      inference('demod', [status(thm)], ['11', '12', '13'])).
% 0.46/0.64  thf('15', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.46/0.64          | (v1_xboole_0 @ sk_D)
% 0.46/0.64          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.46/0.64          | (v1_xboole_0 @ sk_C_1)
% 0.46/0.64          | (v1_xboole_0 @ sk_B_1)
% 0.46/0.64          | (v1_xboole_0 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ sk_F)
% 0.46/0.64          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 0.46/0.64          | (v1_funct_1 @ 
% 0.46/0.64             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['8', '14'])).
% 0.46/0.64  thf('16', plain, ((v1_funct_1 @ sk_F)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('17', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('18', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.46/0.64          | (v1_xboole_0 @ sk_D)
% 0.46/0.64          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.46/0.64          | (v1_xboole_0 @ sk_C_1)
% 0.46/0.64          | (v1_xboole_0 @ sk_B_1)
% 0.46/0.64          | (v1_xboole_0 @ X0)
% 0.46/0.64          | (v1_funct_1 @ 
% 0.46/0.64             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F)))),
% 0.46/0.64      inference('demod', [status(thm)], ['15', '16', '17'])).
% 0.46/0.64  thf('19', plain,
% 0.46/0.64      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.46/0.64        | (v1_xboole_0 @ sk_A)
% 0.46/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.64        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.64        | (v1_xboole_0 @ sk_D))),
% 0.46/0.64      inference('sup-', [status(thm)], ['7', '18'])).
% 0.46/0.64  thf('20', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('21', plain,
% 0.46/0.64      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.46/0.64        | (v1_xboole_0 @ sk_A)
% 0.46/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_D))),
% 0.46/0.64      inference('demod', [status(thm)], ['19', '20'])).
% 0.46/0.64  thf('22', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('23', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('24', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('25', plain,
% 0.46/0.64      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.46/0.64          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 0.46/0.64          | ~ (v1_funct_1 @ X31)
% 0.46/0.64          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.46/0.64          | (v1_xboole_0 @ X34)
% 0.46/0.64          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X35))
% 0.46/0.64          | (v1_xboole_0 @ X32)
% 0.46/0.64          | (v1_xboole_0 @ X33)
% 0.46/0.64          | (v1_xboole_0 @ X35)
% 0.46/0.64          | ~ (v1_funct_1 @ X36)
% 0.46/0.64          | ~ (v1_funct_2 @ X36 @ X34 @ X33)
% 0.46/0.64          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.46/0.64          | (v1_funct_2 @ (k1_tmap_1 @ X35 @ X33 @ X32 @ X34 @ X31 @ X36) @ 
% 0.46/0.64             (k4_subset_1 @ X35 @ X32 @ X34) @ X33))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.46/0.64  thf('26', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.46/0.64           (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B_1)
% 0.46/0.64          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.46/0.64          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 0.46/0.64          | ~ (v1_funct_1 @ X2)
% 0.46/0.64          | (v1_xboole_0 @ X1)
% 0.46/0.64          | (v1_xboole_0 @ sk_B_1)
% 0.46/0.64          | (v1_xboole_0 @ sk_C_1)
% 0.46/0.64          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.46/0.64          | (v1_xboole_0 @ X0)
% 0.46/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.46/0.64          | ~ (v1_funct_1 @ sk_E)
% 0.46/0.64          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['24', '25'])).
% 0.46/0.64  thf('27', plain, ((v1_funct_1 @ sk_E)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('28', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('29', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.46/0.64           (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B_1)
% 0.46/0.64          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.46/0.64          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 0.46/0.64          | ~ (v1_funct_1 @ X2)
% 0.46/0.64          | (v1_xboole_0 @ X1)
% 0.46/0.64          | (v1_xboole_0 @ sk_B_1)
% 0.46/0.64          | (v1_xboole_0 @ sk_C_1)
% 0.46/0.64          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.46/0.64          | (v1_xboole_0 @ X0)
% 0.46/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.46/0.64      inference('demod', [status(thm)], ['26', '27', '28'])).
% 0.46/0.64  thf('30', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.46/0.64          | (v1_xboole_0 @ sk_D)
% 0.46/0.64          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.46/0.64          | (v1_xboole_0 @ sk_C_1)
% 0.46/0.64          | (v1_xboole_0 @ sk_B_1)
% 0.46/0.64          | (v1_xboole_0 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ sk_F)
% 0.46/0.64          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 0.46/0.64          | (v1_funct_2 @ 
% 0.46/0.64             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.64             (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B_1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['23', '29'])).
% 0.46/0.64  thf('31', plain, ((v1_funct_1 @ sk_F)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('32', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('33', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.46/0.64          | (v1_xboole_0 @ sk_D)
% 0.46/0.64          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.46/0.64          | (v1_xboole_0 @ sk_C_1)
% 0.46/0.64          | (v1_xboole_0 @ sk_B_1)
% 0.46/0.64          | (v1_xboole_0 @ X0)
% 0.46/0.64          | (v1_funct_2 @ 
% 0.46/0.64             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.64             (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B_1))),
% 0.46/0.64      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.46/0.64  thf('34', plain,
% 0.46/0.64      (((v1_funct_2 @ 
% 0.46/0.64         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.64         (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_A)
% 0.46/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.64        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.64        | (v1_xboole_0 @ sk_D))),
% 0.46/0.64      inference('sup-', [status(thm)], ['22', '33'])).
% 0.46/0.64  thf('35', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('36', plain,
% 0.46/0.64      (((v1_funct_2 @ 
% 0.46/0.64         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.64         (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_A)
% 0.46/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_D))),
% 0.46/0.64      inference('demod', [status(thm)], ['34', '35'])).
% 0.46/0.64  thf('37', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('38', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('39', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('40', plain,
% 0.46/0.64      (![X31 : $i, X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33)))
% 0.46/0.64          | ~ (v1_funct_2 @ X31 @ X32 @ X33)
% 0.46/0.64          | ~ (v1_funct_1 @ X31)
% 0.46/0.64          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ X35))
% 0.46/0.64          | (v1_xboole_0 @ X34)
% 0.46/0.64          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ X35))
% 0.46/0.64          | (v1_xboole_0 @ X32)
% 0.46/0.64          | (v1_xboole_0 @ X33)
% 0.46/0.64          | (v1_xboole_0 @ X35)
% 0.46/0.64          | ~ (v1_funct_1 @ X36)
% 0.46/0.64          | ~ (v1_funct_2 @ X36 @ X34 @ X33)
% 0.46/0.64          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X33)))
% 0.46/0.64          | (m1_subset_1 @ (k1_tmap_1 @ X35 @ X33 @ X32 @ X34 @ X31 @ X36) @ 
% 0.46/0.64             (k1_zfmisc_1 @ 
% 0.46/0.64              (k2_zfmisc_1 @ (k4_subset_1 @ X35 @ X32 @ X34) @ X33))))),
% 0.46/0.64      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.46/0.64  thf('41', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.46/0.64           (k1_zfmisc_1 @ 
% 0.46/0.64            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B_1)))
% 0.46/0.64          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.46/0.64          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 0.46/0.64          | ~ (v1_funct_1 @ X2)
% 0.46/0.64          | (v1_xboole_0 @ X1)
% 0.46/0.64          | (v1_xboole_0 @ sk_B_1)
% 0.46/0.64          | (v1_xboole_0 @ sk_C_1)
% 0.46/0.64          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.46/0.64          | (v1_xboole_0 @ X0)
% 0.46/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.46/0.64          | ~ (v1_funct_1 @ sk_E)
% 0.46/0.64          | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['39', '40'])).
% 0.46/0.64  thf('42', plain, ((v1_funct_1 @ sk_E)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('43', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('44', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.46/0.64         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C_1 @ X0 @ sk_E @ X2) @ 
% 0.46/0.64           (k1_zfmisc_1 @ 
% 0.46/0.64            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C_1 @ X0) @ sk_B_1)))
% 0.46/0.64          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.46/0.64          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 0.46/0.64          | ~ (v1_funct_1 @ X2)
% 0.46/0.64          | (v1_xboole_0 @ X1)
% 0.46/0.64          | (v1_xboole_0 @ sk_B_1)
% 0.46/0.64          | (v1_xboole_0 @ sk_C_1)
% 0.46/0.64          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X1))
% 0.46/0.64          | (v1_xboole_0 @ X0)
% 0.46/0.64          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.46/0.64      inference('demod', [status(thm)], ['41', '42', '43'])).
% 0.46/0.64  thf('45', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.46/0.64          | (v1_xboole_0 @ sk_D)
% 0.46/0.64          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.46/0.64          | (v1_xboole_0 @ sk_C_1)
% 0.46/0.64          | (v1_xboole_0 @ sk_B_1)
% 0.46/0.64          | (v1_xboole_0 @ X0)
% 0.46/0.64          | ~ (v1_funct_1 @ sk_F)
% 0.46/0.64          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 0.46/0.64          | (m1_subset_1 @ 
% 0.46/0.64             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.64             (k1_zfmisc_1 @ 
% 0.46/0.64              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B_1))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['38', '44'])).
% 0.46/0.64  thf('46', plain, ((v1_funct_1 @ sk_F)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('47', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('48', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.46/0.64          | (v1_xboole_0 @ sk_D)
% 0.46/0.64          | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ X0))
% 0.46/0.64          | (v1_xboole_0 @ sk_C_1)
% 0.46/0.64          | (v1_xboole_0 @ sk_B_1)
% 0.46/0.64          | (v1_xboole_0 @ X0)
% 0.46/0.64          | (m1_subset_1 @ 
% 0.46/0.64             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.64             (k1_zfmisc_1 @ 
% 0.46/0.64              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C_1 @ sk_D) @ sk_B_1))))),
% 0.46/0.64      inference('demod', [status(thm)], ['45', '46', '47'])).
% 0.46/0.64  thf('49', plain,
% 0.46/0.64      (((m1_subset_1 @ 
% 0.46/0.64         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.64         (k1_zfmisc_1 @ 
% 0.46/0.64          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)))
% 0.46/0.64        | (v1_xboole_0 @ sk_A)
% 0.46/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.64        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.64        | (v1_xboole_0 @ sk_D))),
% 0.46/0.64      inference('sup-', [status(thm)], ['37', '48'])).
% 0.46/0.64  thf('50', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('51', plain,
% 0.46/0.64      (((m1_subset_1 @ 
% 0.46/0.64         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.64         (k1_zfmisc_1 @ 
% 0.46/0.64          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)))
% 0.46/0.64        | (v1_xboole_0 @ sk_A)
% 0.46/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_D))),
% 0.46/0.64      inference('demod', [status(thm)], ['49', '50'])).
% 0.46/0.64  thf(d1_tmap_1, axiom,
% 0.46/0.64    (![A:$i]:
% 0.46/0.64     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.46/0.64       ( ![B:$i]:
% 0.46/0.64         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.46/0.64           ( ![C:$i]:
% 0.46/0.64             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.46/0.64                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.46/0.64               ( ![D:$i]:
% 0.46/0.64                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.46/0.64                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.46/0.64                   ( ![E:$i]:
% 0.46/0.64                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.46/0.64                         ( m1_subset_1 @
% 0.46/0.64                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.46/0.64                       ( ![F:$i]:
% 0.46/0.64                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.46/0.64                             ( m1_subset_1 @
% 0.46/0.64                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.46/0.64                           ( ( ( k2_partfun1 @
% 0.46/0.64                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.46/0.64                               ( k2_partfun1 @
% 0.46/0.64                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 0.46/0.64                             ( ![G:$i]:
% 0.46/0.64                               ( ( ( v1_funct_1 @ G ) & 
% 0.46/0.64                                   ( v1_funct_2 @
% 0.46/0.64                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.46/0.64                                   ( m1_subset_1 @
% 0.46/0.64                                     G @ 
% 0.46/0.64                                     ( k1_zfmisc_1 @
% 0.46/0.64                                       ( k2_zfmisc_1 @
% 0.46/0.64                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 0.46/0.64                                 ( ( ( G ) =
% 0.46/0.64                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.46/0.64                                   ( ( ( k2_partfun1 @
% 0.46/0.64                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.46/0.64                                         C ) =
% 0.46/0.64                                       ( E ) ) & 
% 0.46/0.64                                     ( ( k2_partfun1 @
% 0.46/0.64                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.46/0.64                                         D ) =
% 0.46/0.64                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.46/0.64  thf('52', plain,
% 0.46/0.64      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.46/0.64         ((v1_xboole_0 @ X24)
% 0.46/0.64          | (v1_xboole_0 @ X25)
% 0.46/0.64          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 0.46/0.64          | ~ (v1_funct_1 @ X27)
% 0.46/0.64          | ~ (v1_funct_2 @ X27 @ X25 @ X24)
% 0.46/0.64          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 0.46/0.64          | ((X30) != (k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27))
% 0.46/0.64          | ((k2_partfun1 @ (k4_subset_1 @ X26 @ X29 @ X25) @ X24 @ X30 @ X29)
% 0.46/0.64              = (X28))
% 0.46/0.64          | ~ (m1_subset_1 @ X30 @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k2_zfmisc_1 @ (k4_subset_1 @ X26 @ X29 @ X25) @ X24)))
% 0.46/0.64          | ~ (v1_funct_2 @ X30 @ (k4_subset_1 @ X26 @ X29 @ X25) @ X24)
% 0.46/0.64          | ~ (v1_funct_1 @ X30)
% 0.46/0.64          | ((k2_partfun1 @ X29 @ X24 @ X28 @ (k9_subset_1 @ X26 @ X29 @ X25))
% 0.46/0.64              != (k2_partfun1 @ X25 @ X24 @ X27 @ 
% 0.46/0.64                  (k9_subset_1 @ X26 @ X29 @ X25)))
% 0.46/0.64          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X24)))
% 0.46/0.64          | ~ (v1_funct_2 @ X28 @ X29 @ X24)
% 0.46/0.64          | ~ (v1_funct_1 @ X28)
% 0.46/0.64          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X26))
% 0.46/0.64          | (v1_xboole_0 @ X29)
% 0.46/0.64          | (v1_xboole_0 @ X26))),
% 0.46/0.64      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.46/0.64  thf('53', plain,
% 0.46/0.64      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.46/0.64         ((v1_xboole_0 @ X26)
% 0.46/0.64          | (v1_xboole_0 @ X29)
% 0.46/0.64          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X26))
% 0.46/0.64          | ~ (v1_funct_1 @ X28)
% 0.46/0.64          | ~ (v1_funct_2 @ X28 @ X29 @ X24)
% 0.46/0.64          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X24)))
% 0.46/0.64          | ((k2_partfun1 @ X29 @ X24 @ X28 @ (k9_subset_1 @ X26 @ X29 @ X25))
% 0.46/0.64              != (k2_partfun1 @ X25 @ X24 @ X27 @ 
% 0.46/0.64                  (k9_subset_1 @ X26 @ X29 @ X25)))
% 0.46/0.64          | ~ (v1_funct_1 @ (k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27))
% 0.46/0.64          | ~ (v1_funct_2 @ (k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27) @ 
% 0.46/0.64               (k4_subset_1 @ X26 @ X29 @ X25) @ X24)
% 0.46/0.64          | ~ (m1_subset_1 @ (k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27) @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k2_zfmisc_1 @ (k4_subset_1 @ X26 @ X29 @ X25) @ X24)))
% 0.46/0.64          | ((k2_partfun1 @ (k4_subset_1 @ X26 @ X29 @ X25) @ X24 @ 
% 0.46/0.64              (k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27) @ X29) = (
% 0.46/0.64              X28))
% 0.46/0.64          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 0.46/0.64          | ~ (v1_funct_2 @ X27 @ X25 @ X24)
% 0.46/0.64          | ~ (v1_funct_1 @ X27)
% 0.46/0.64          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 0.46/0.64          | (v1_xboole_0 @ X25)
% 0.46/0.64          | (v1_xboole_0 @ X24))),
% 0.46/0.64      inference('simplify', [status(thm)], ['52'])).
% 0.46/0.64  thf('54', plain,
% 0.46/0.64      (((v1_xboole_0 @ sk_D)
% 0.46/0.64        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_A)
% 0.46/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_D)
% 0.46/0.64        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.64        | ~ (v1_funct_1 @ sk_F)
% 0.46/0.64        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 0.46/0.64        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))
% 0.46/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.46/0.64            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.46/0.64            = (sk_E))
% 0.46/0.64        | ~ (v1_funct_2 @ 
% 0.46/0.64             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.64             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.46/0.64        | ~ (v1_funct_1 @ 
% 0.46/0.64             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.46/0.64        | ((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.46/0.64            (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.46/0.64            != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.46/0.64                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))
% 0.46/0.64        | ~ (m1_subset_1 @ sk_E @ 
% 0.46/0.64             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))
% 0.46/0.64        | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_E)
% 0.46/0.64        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.64        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['51', '53'])).
% 0.46/0.64  thf('55', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('56', plain, ((v1_funct_1 @ sk_F)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('57', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('58', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('59', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(redefinition_k9_subset_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.46/0.64       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.46/0.64  thf('60', plain,
% 0.46/0.64      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.46/0.64         (((k9_subset_1 @ X12 @ X10 @ X11) = (k3_xboole_0 @ X10 @ X11))
% 0.46/0.64          | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.46/0.64  thf('61', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.46/0.64      inference('sup-', [status(thm)], ['59', '60'])).
% 0.46/0.64  thf('62', plain, ((r1_subset_1 @ sk_C_1 @ sk_D)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(redefinition_r1_subset_1, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.46/0.64       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 0.46/0.64  thf('63', plain,
% 0.46/0.64      (![X15 : $i, X16 : $i]:
% 0.46/0.64         ((v1_xboole_0 @ X15)
% 0.46/0.64          | (v1_xboole_0 @ X16)
% 0.46/0.64          | (r1_xboole_0 @ X15 @ X16)
% 0.46/0.64          | ~ (r1_subset_1 @ X15 @ X16))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 0.46/0.64  thf('64', plain,
% 0.46/0.64      (((r1_xboole_0 @ sk_C_1 @ sk_D)
% 0.46/0.64        | (v1_xboole_0 @ sk_D)
% 0.46/0.64        | (v1_xboole_0 @ sk_C_1))),
% 0.46/0.64      inference('sup-', [status(thm)], ['62', '63'])).
% 0.46/0.64  thf('65', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('66', plain, (((v1_xboole_0 @ sk_C_1) | (r1_xboole_0 @ sk_C_1 @ sk_D))),
% 0.46/0.64      inference('clc', [status(thm)], ['64', '65'])).
% 0.46/0.64  thf('67', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('68', plain, ((r1_xboole_0 @ sk_C_1 @ sk_D)),
% 0.46/0.64      inference('clc', [status(thm)], ['66', '67'])).
% 0.46/0.64  thf(d7_xboole_0, axiom,
% 0.46/0.64    (![A:$i,B:$i]:
% 0.46/0.64     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.46/0.64       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.46/0.64  thf('69', plain,
% 0.46/0.64      (![X3 : $i, X4 : $i]:
% 0.46/0.64         (((k3_xboole_0 @ X3 @ X4) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X3 @ X4))),
% 0.46/0.64      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.46/0.64  thf('70', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['68', '69'])).
% 0.46/0.64  thf('71', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(redefinition_k2_partfun1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i,D:$i]:
% 0.46/0.64     ( ( ( v1_funct_1 @ C ) & 
% 0.46/0.64         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.46/0.64       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.46/0.64  thf('72', plain,
% 0.46/0.64      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.46/0.64          | ~ (v1_funct_1 @ X20)
% 0.46/0.64          | ((k2_partfun1 @ X21 @ X22 @ X20 @ X23) = (k7_relat_1 @ X20 @ X23)))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.46/0.64  thf('73', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0)
% 0.46/0.64            = (k7_relat_1 @ sk_E @ X0))
% 0.46/0.64          | ~ (v1_funct_1 @ sk_E))),
% 0.46/0.64      inference('sup-', [status(thm)], ['71', '72'])).
% 0.46/0.64  thf('74', plain, ((v1_funct_1 @ sk_E)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('75', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0)
% 0.46/0.64           = (k7_relat_1 @ sk_E @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['73', '74'])).
% 0.46/0.64  thf('76', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.46/0.64      inference('sup-', [status(thm)], ['59', '60'])).
% 0.46/0.64  thf('77', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['68', '69'])).
% 0.46/0.64  thf('78', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('79', plain,
% 0.46/0.64      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i]:
% 0.46/0.64         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22)))
% 0.46/0.64          | ~ (v1_funct_1 @ X20)
% 0.46/0.64          | ((k2_partfun1 @ X21 @ X22 @ X20 @ X23) = (k7_relat_1 @ X20 @ X23)))),
% 0.46/0.64      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.46/0.64  thf('80', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 0.46/0.64          | ~ (v1_funct_1 @ sk_F))),
% 0.46/0.64      inference('sup-', [status(thm)], ['78', '79'])).
% 0.46/0.64  thf('81', plain, ((v1_funct_1 @ sk_F)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('82', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['80', '81'])).
% 0.46/0.64  thf('83', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('84', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('85', plain, ((v1_funct_1 @ sk_E)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('86', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('87', plain,
% 0.46/0.64      (((v1_xboole_0 @ sk_D)
% 0.46/0.64        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_A)
% 0.46/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_D)
% 0.46/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.46/0.64            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.46/0.64            = (sk_E))
% 0.46/0.64        | ~ (v1_funct_2 @ 
% 0.46/0.64             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.64             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.46/0.64        | ~ (v1_funct_1 @ 
% 0.46/0.64             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.46/0.64        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.46/0.64            != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.46/0.64        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)],
% 0.46/0.64                ['54', '55', '56', '57', '58', '61', '70', '75', '76', '77', 
% 0.46/0.64                 '82', '83', '84', '85', '86'])).
% 0.46/0.64  thf('88', plain,
% 0.46/0.64      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.46/0.64        | ~ (v1_funct_1 @ 
% 0.46/0.64             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.46/0.64        | ~ (v1_funct_2 @ 
% 0.46/0.64             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.64             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.46/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.46/0.64            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.46/0.64            = (sk_E))
% 0.46/0.64        | (v1_xboole_0 @ sk_A)
% 0.46/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_D))),
% 0.46/0.64      inference('simplify', [status(thm)], ['87'])).
% 0.46/0.64  thf('89', plain,
% 0.46/0.64      (((v1_xboole_0 @ sk_D)
% 0.46/0.64        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_A)
% 0.46/0.64        | (v1_xboole_0 @ sk_D)
% 0.46/0.64        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_A)
% 0.46/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.46/0.64            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.46/0.64            = (sk_E))
% 0.46/0.64        | ~ (v1_funct_1 @ 
% 0.46/0.64             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.46/0.64        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.46/0.64            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['36', '88'])).
% 0.46/0.64  thf('90', plain,
% 0.46/0.64      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.46/0.64        | ~ (v1_funct_1 @ 
% 0.46/0.64             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.46/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.46/0.64            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.46/0.64            = (sk_E))
% 0.46/0.64        | (v1_xboole_0 @ sk_A)
% 0.46/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_D))),
% 0.46/0.64      inference('simplify', [status(thm)], ['89'])).
% 0.46/0.64  thf('91', plain,
% 0.46/0.64      ((((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.46/0.64          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.46/0.64          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.46/0.64              (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))
% 0.46/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.46/0.64            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.46/0.64            != (sk_E))
% 0.46/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.46/0.64            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.46/0.64            != (sk_F)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('92', plain,
% 0.46/0.64      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.46/0.64          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.46/0.64          != (sk_E)))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.46/0.64                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.64                sk_C_1) = (sk_E))))),
% 0.46/0.64      inference('split', [status(esa)], ['91'])).
% 0.46/0.64  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.46/0.64  thf('93', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.64      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.64  thf('94', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]: ((r1_xboole_0 @ X1 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['1', '2'])).
% 0.46/0.64  thf('95', plain, (![X0 : $i]: (r1_xboole_0 @ X0 @ k1_xboole_0)),
% 0.46/0.64      inference('sup-', [status(thm)], ['93', '94'])).
% 0.46/0.64  thf('96', plain,
% 0.46/0.64      (![X13 : $i, X14 : $i]:
% 0.46/0.64         (~ (r1_xboole_0 @ (k1_relat_1 @ X13) @ X14)
% 0.46/0.64          | ((k7_relat_1 @ X13 @ X14) = (k1_xboole_0))
% 0.46/0.64          | ~ (v1_relat_1 @ X13))),
% 0.46/0.64      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.46/0.64  thf('97', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0)
% 0.46/0.64          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['95', '96'])).
% 0.46/0.64  thf('98', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         (~ (v1_relat_1 @ X0)
% 0.46/0.64          | ((k7_relat_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['95', '96'])).
% 0.46/0.64  thf('99', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['80', '81'])).
% 0.46/0.64  thf('100', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.46/0.64      inference('sup-', [status(thm)], ['59', '60'])).
% 0.46/0.64  thf('101', plain,
% 0.46/0.64      ((((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.46/0.64          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.46/0.64          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.46/0.64              (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.46/0.64                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.46/0.64                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.46/0.64                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.46/0.64      inference('split', [status(esa)], ['91'])).
% 0.46/0.64  thf('102', plain,
% 0.46/0.64      ((((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.46/0.64          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.46/0.64          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.46/0.64              (k3_xboole_0 @ sk_C_1 @ sk_D))))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.46/0.64                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.46/0.64                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.46/0.64                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['100', '101'])).
% 0.46/0.64  thf('103', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.46/0.64      inference('sup-', [status(thm)], ['59', '60'])).
% 0.46/0.64  thf('104', plain,
% 0.46/0.64      ((((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ (k3_xboole_0 @ sk_C_1 @ sk_D))
% 0.46/0.64          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.46/0.64              (k3_xboole_0 @ sk_C_1 @ sk_D))))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.46/0.64                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.46/0.64                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.46/0.64                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.46/0.64      inference('demod', [status(thm)], ['102', '103'])).
% 0.46/0.64  thf('105', plain,
% 0.46/0.64      ((((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ (k3_xboole_0 @ sk_C_1 @ sk_D))
% 0.46/0.64          != (k7_relat_1 @ sk_F @ (k3_xboole_0 @ sk_C_1 @ sk_D))))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.46/0.64                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.46/0.64                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.46/0.64                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['99', '104'])).
% 0.46/0.64  thf('106', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['68', '69'])).
% 0.46/0.64  thf('107', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0)
% 0.46/0.64           = (k7_relat_1 @ sk_E @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['73', '74'])).
% 0.46/0.64  thf('108', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['68', '69'])).
% 0.46/0.64  thf('109', plain,
% 0.46/0.64      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0)))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.46/0.64                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.46/0.64                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.46/0.64                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.46/0.64      inference('demod', [status(thm)], ['105', '106', '107', '108'])).
% 0.46/0.64  thf('110', plain,
% 0.46/0.64      (((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.46/0.64         | ~ (v1_relat_1 @ sk_F)))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.46/0.64                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.46/0.64                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.46/0.64                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['98', '109'])).
% 0.46/0.64  thf('111', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf(cc1_relset_1, axiom,
% 0.46/0.64    (![A:$i,B:$i,C:$i]:
% 0.46/0.64     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.46/0.64       ( v1_relat_1 @ C ) ))).
% 0.46/0.64  thf('112', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.64         ((v1_relat_1 @ X17)
% 0.46/0.64          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.64  thf('113', plain, ((v1_relat_1 @ sk_F)),
% 0.46/0.64      inference('sup-', [status(thm)], ['111', '112'])).
% 0.46/0.64  thf('114', plain,
% 0.46/0.64      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0)))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.46/0.64                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.46/0.64                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.46/0.64                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.46/0.64      inference('demod', [status(thm)], ['110', '113'])).
% 0.46/0.64  thf('115', plain,
% 0.46/0.64      (((((k1_xboole_0) != (k1_xboole_0)) | ~ (v1_relat_1 @ sk_E)))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.46/0.64                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.46/0.64                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.46/0.64                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.46/0.64      inference('sup-', [status(thm)], ['97', '114'])).
% 0.46/0.64  thf('116', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('117', plain,
% 0.46/0.64      (![X17 : $i, X18 : $i, X19 : $i]:
% 0.46/0.64         ((v1_relat_1 @ X17)
% 0.46/0.64          | ~ (m1_subset_1 @ X17 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X19))))),
% 0.46/0.64      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.46/0.64  thf('118', plain, ((v1_relat_1 @ sk_E)),
% 0.46/0.64      inference('sup-', [status(thm)], ['116', '117'])).
% 0.46/0.64  thf('119', plain,
% 0.46/0.64      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.46/0.64         <= (~
% 0.46/0.64             (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.46/0.64                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.46/0.64                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.46/0.64                   (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))))),
% 0.46/0.64      inference('demod', [status(thm)], ['115', '118'])).
% 0.46/0.64  thf('120', plain,
% 0.46/0.64      ((((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.46/0.64          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.46/0.64          = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.46/0.64             (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))))),
% 0.46/0.64      inference('simplify', [status(thm)], ['119'])).
% 0.46/0.64  thf('121', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (v1_xboole_0 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X1)
% 0.46/0.64          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.64  thf('122', plain,
% 0.46/0.64      (![X0 : $i, X1 : $i]:
% 0.46/0.64         (~ (v1_xboole_0 @ X0)
% 0.46/0.64          | ~ (v1_relat_1 @ X1)
% 0.46/0.64          | ((k7_relat_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.46/0.64      inference('sup-', [status(thm)], ['3', '4'])).
% 0.46/0.64  thf('123', plain,
% 0.46/0.64      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.46/0.64        | (v1_xboole_0 @ sk_A)
% 0.46/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_D))),
% 0.46/0.64      inference('demod', [status(thm)], ['19', '20'])).
% 0.46/0.64  thf('124', plain,
% 0.46/0.64      (((v1_funct_2 @ 
% 0.46/0.64         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.64         (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_A)
% 0.46/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_D))),
% 0.46/0.64      inference('demod', [status(thm)], ['34', '35'])).
% 0.46/0.64  thf('125', plain,
% 0.46/0.64      (((m1_subset_1 @ 
% 0.46/0.64         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.64         (k1_zfmisc_1 @ 
% 0.46/0.64          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)))
% 0.46/0.64        | (v1_xboole_0 @ sk_A)
% 0.46/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_D))),
% 0.46/0.64      inference('demod', [status(thm)], ['49', '50'])).
% 0.46/0.64  thf('126', plain,
% 0.46/0.64      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.46/0.64         ((v1_xboole_0 @ X24)
% 0.46/0.64          | (v1_xboole_0 @ X25)
% 0.46/0.64          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 0.46/0.64          | ~ (v1_funct_1 @ X27)
% 0.46/0.64          | ~ (v1_funct_2 @ X27 @ X25 @ X24)
% 0.46/0.64          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 0.46/0.64          | ((X30) != (k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27))
% 0.46/0.64          | ((k2_partfun1 @ (k4_subset_1 @ X26 @ X29 @ X25) @ X24 @ X30 @ X25)
% 0.46/0.64              = (X27))
% 0.46/0.64          | ~ (m1_subset_1 @ X30 @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k2_zfmisc_1 @ (k4_subset_1 @ X26 @ X29 @ X25) @ X24)))
% 0.46/0.64          | ~ (v1_funct_2 @ X30 @ (k4_subset_1 @ X26 @ X29 @ X25) @ X24)
% 0.46/0.64          | ~ (v1_funct_1 @ X30)
% 0.46/0.64          | ((k2_partfun1 @ X29 @ X24 @ X28 @ (k9_subset_1 @ X26 @ X29 @ X25))
% 0.46/0.64              != (k2_partfun1 @ X25 @ X24 @ X27 @ 
% 0.46/0.64                  (k9_subset_1 @ X26 @ X29 @ X25)))
% 0.46/0.64          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X24)))
% 0.46/0.64          | ~ (v1_funct_2 @ X28 @ X29 @ X24)
% 0.46/0.64          | ~ (v1_funct_1 @ X28)
% 0.46/0.64          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X26))
% 0.46/0.64          | (v1_xboole_0 @ X29)
% 0.46/0.64          | (v1_xboole_0 @ X26))),
% 0.46/0.64      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.46/0.64  thf('127', plain,
% 0.46/0.64      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.46/0.64         ((v1_xboole_0 @ X26)
% 0.46/0.64          | (v1_xboole_0 @ X29)
% 0.46/0.64          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ X26))
% 0.46/0.64          | ~ (v1_funct_1 @ X28)
% 0.46/0.64          | ~ (v1_funct_2 @ X28 @ X29 @ X24)
% 0.46/0.64          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X24)))
% 0.46/0.64          | ((k2_partfun1 @ X29 @ X24 @ X28 @ (k9_subset_1 @ X26 @ X29 @ X25))
% 0.46/0.64              != (k2_partfun1 @ X25 @ X24 @ X27 @ 
% 0.46/0.64                  (k9_subset_1 @ X26 @ X29 @ X25)))
% 0.46/0.64          | ~ (v1_funct_1 @ (k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27))
% 0.46/0.64          | ~ (v1_funct_2 @ (k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27) @ 
% 0.46/0.64               (k4_subset_1 @ X26 @ X29 @ X25) @ X24)
% 0.46/0.64          | ~ (m1_subset_1 @ (k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27) @ 
% 0.46/0.64               (k1_zfmisc_1 @ 
% 0.46/0.64                (k2_zfmisc_1 @ (k4_subset_1 @ X26 @ X29 @ X25) @ X24)))
% 0.46/0.64          | ((k2_partfun1 @ (k4_subset_1 @ X26 @ X29 @ X25) @ X24 @ 
% 0.46/0.64              (k1_tmap_1 @ X26 @ X24 @ X29 @ X25 @ X28 @ X27) @ X25) = (
% 0.46/0.64              X27))
% 0.46/0.64          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X24)))
% 0.46/0.64          | ~ (v1_funct_2 @ X27 @ X25 @ X24)
% 0.46/0.64          | ~ (v1_funct_1 @ X27)
% 0.46/0.64          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ X26))
% 0.46/0.64          | (v1_xboole_0 @ X25)
% 0.46/0.64          | (v1_xboole_0 @ X24))),
% 0.46/0.64      inference('simplify', [status(thm)], ['126'])).
% 0.46/0.64  thf('128', plain,
% 0.46/0.64      (((v1_xboole_0 @ sk_D)
% 0.46/0.64        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_A)
% 0.46/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_D)
% 0.46/0.64        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.64        | ~ (v1_funct_1 @ sk_F)
% 0.46/0.64        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 0.46/0.64        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))
% 0.46/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.46/0.64            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.46/0.64            = (sk_F))
% 0.46/0.64        | ~ (v1_funct_2 @ 
% 0.46/0.64             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.64             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.46/0.64        | ~ (v1_funct_1 @ 
% 0.46/0.64             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.46/0.64        | ((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.46/0.64            (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.46/0.64            != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.46/0.64                (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D)))
% 0.46/0.64        | ~ (m1_subset_1 @ sk_E @ 
% 0.46/0.64             (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))
% 0.46/0.64        | ~ (v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)
% 0.46/0.64        | ~ (v1_funct_1 @ sk_E)
% 0.46/0.64        | ~ (m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))
% 0.46/0.64        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_A))),
% 0.46/0.64      inference('sup-', [status(thm)], ['125', '127'])).
% 0.46/0.64  thf('129', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('130', plain, ((v1_funct_1 @ sk_F)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('131', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('132', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('133', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.46/0.64      inference('sup-', [status(thm)], ['59', '60'])).
% 0.46/0.64  thf('134', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['68', '69'])).
% 0.46/0.64  thf('135', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ X0)
% 0.46/0.64           = (k7_relat_1 @ sk_E @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['73', '74'])).
% 0.46/0.64  thf('136', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.46/0.64      inference('sup-', [status(thm)], ['59', '60'])).
% 0.46/0.64  thf('137', plain, (((k3_xboole_0 @ sk_C_1 @ sk_D) = (k1_xboole_0))),
% 0.46/0.64      inference('sup-', [status(thm)], ['68', '69'])).
% 0.46/0.64  thf('138', plain,
% 0.46/0.64      (![X0 : $i]:
% 0.46/0.64         ((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.46/0.64      inference('demod', [status(thm)], ['80', '81'])).
% 0.46/0.64  thf('139', plain,
% 0.46/0.64      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C_1 @ sk_B_1)))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('140', plain, ((v1_funct_2 @ sk_E @ sk_C_1 @ sk_B_1)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('141', plain, ((v1_funct_1 @ sk_E)),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('142', plain, ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ sk_A))),
% 0.46/0.64      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.64  thf('143', plain,
% 0.46/0.64      (((v1_xboole_0 @ sk_D)
% 0.46/0.64        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_A)
% 0.46/0.64        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_D)
% 0.46/0.64        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.46/0.64            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.46/0.64            = (sk_F))
% 0.46/0.64        | ~ (v1_funct_2 @ 
% 0.46/0.64             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.64             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.46/0.64        | ~ (v1_funct_1 @ 
% 0.46/0.64             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.46/0.64        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.46/0.64            != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.46/0.64        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.64        | (v1_xboole_0 @ sk_A))),
% 0.46/0.64      inference('demod', [status(thm)],
% 0.46/0.64                ['128', '129', '130', '131', '132', '133', '134', '135', 
% 0.46/0.64                 '136', '137', '138', '139', '140', '141', '142'])).
% 0.46/0.64  thf('144', plain,
% 0.46/0.64      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.46/0.64        | ~ (v1_funct_1 @ 
% 0.46/0.64             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.46/0.64        | ~ (v1_funct_2 @ 
% 0.46/0.64             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.65             (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1)
% 0.46/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.46/0.65            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.46/0.65            = (sk_F))
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_D))),
% 0.46/0.65      inference('simplify', [status(thm)], ['143'])).
% 0.46/0.65  thf('145', plain,
% 0.46/0.65      (((v1_xboole_0 @ sk_D)
% 0.46/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_D)
% 0.46/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.46/0.65            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.46/0.65            = (sk_F))
% 0.46/0.65        | ~ (v1_funct_1 @ 
% 0.46/0.65             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.46/0.65        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.46/0.65            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['124', '144'])).
% 0.46/0.65  thf('146', plain,
% 0.46/0.65      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.46/0.65        | ~ (v1_funct_1 @ 
% 0.46/0.65             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.46/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.46/0.65            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.46/0.65            = (sk_F))
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_D))),
% 0.46/0.65      inference('simplify', [status(thm)], ['145'])).
% 0.46/0.65  thf('147', plain,
% 0.46/0.65      (((v1_xboole_0 @ sk_D)
% 0.46/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_D)
% 0.46/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.46/0.65            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.46/0.65            = (sk_F))
% 0.46/0.65        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.46/0.65            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['123', '146'])).
% 0.46/0.65  thf('148', plain,
% 0.46/0.65      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.46/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.46/0.65            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.46/0.65            = (sk_F))
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_D))),
% 0.46/0.65      inference('simplify', [status(thm)], ['147'])).
% 0.46/0.65  thf('149', plain,
% 0.46/0.65      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.46/0.65        | ~ (v1_relat_1 @ sk_F)
% 0.46/0.65        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.65        | (v1_xboole_0 @ sk_D)
% 0.46/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.46/0.65            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.46/0.65            = (sk_F)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['122', '148'])).
% 0.46/0.65  thf('150', plain, ((v1_relat_1 @ sk_F)),
% 0.46/0.65      inference('sup-', [status(thm)], ['111', '112'])).
% 0.46/0.65  thf('151', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.65  thf('152', plain,
% 0.46/0.65      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.46/0.65        | (v1_xboole_0 @ sk_D)
% 0.46/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.46/0.65            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.46/0.65            = (sk_F)))),
% 0.46/0.65      inference('demod', [status(thm)], ['149', '150', '151'])).
% 0.46/0.65  thf('153', plain,
% 0.46/0.65      ((((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.65        | ~ (v1_relat_1 @ sk_E)
% 0.46/0.65        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.46/0.65            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.46/0.65            = (sk_F))
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_D))),
% 0.46/0.65      inference('sup-', [status(thm)], ['121', '152'])).
% 0.46/0.65  thf('154', plain, ((v1_relat_1 @ sk_E)),
% 0.46/0.65      inference('sup-', [status(thm)], ['116', '117'])).
% 0.46/0.65  thf('155', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.65  thf('156', plain,
% 0.46/0.65      ((((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.46/0.65            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.46/0.65            = (sk_F))
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_D))),
% 0.46/0.65      inference('demod', [status(thm)], ['153', '154', '155'])).
% 0.46/0.65  thf('157', plain,
% 0.46/0.65      (((v1_xboole_0 @ sk_D)
% 0.46/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.46/0.65            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.46/0.65            = (sk_F)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['156'])).
% 0.46/0.65  thf('158', plain,
% 0.46/0.65      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.46/0.65          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.46/0.65          != (sk_F)))
% 0.46/0.65         <= (~
% 0.46/0.65             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.46/0.65                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.65                sk_D) = (sk_F))))),
% 0.46/0.65      inference('split', [status(esa)], ['91'])).
% 0.46/0.65  thf('159', plain,
% 0.46/0.65      (((((sk_F) != (sk_F))
% 0.46/0.65         | (v1_xboole_0 @ sk_A)
% 0.46/0.65         | (v1_xboole_0 @ sk_B_1)
% 0.46/0.65         | (v1_xboole_0 @ sk_C_1)
% 0.46/0.65         | (v1_xboole_0 @ sk_D)))
% 0.46/0.65         <= (~
% 0.46/0.65             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.46/0.65                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.65                sk_D) = (sk_F))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['157', '158'])).
% 0.46/0.65  thf('160', plain,
% 0.46/0.65      ((((v1_xboole_0 @ sk_D)
% 0.46/0.65         | (v1_xboole_0 @ sk_C_1)
% 0.46/0.65         | (v1_xboole_0 @ sk_B_1)
% 0.46/0.65         | (v1_xboole_0 @ sk_A)))
% 0.46/0.65         <= (~
% 0.46/0.65             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.46/0.65                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.65                sk_D) = (sk_F))))),
% 0.46/0.65      inference('simplify', [status(thm)], ['159'])).
% 0.46/0.65  thf('161', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('162', plain,
% 0.46/0.65      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_C_1)))
% 0.46/0.65         <= (~
% 0.46/0.65             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.46/0.65                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.65                sk_D) = (sk_F))))),
% 0.46/0.65      inference('sup-', [status(thm)], ['160', '161'])).
% 0.46/0.65  thf('163', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('164', plain,
% 0.46/0.65      ((((v1_xboole_0 @ sk_C_1) | (v1_xboole_0 @ sk_B_1)))
% 0.46/0.65         <= (~
% 0.46/0.65             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.46/0.65                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.65                sk_D) = (sk_F))))),
% 0.46/0.65      inference('clc', [status(thm)], ['162', '163'])).
% 0.46/0.65  thf('165', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('166', plain,
% 0.46/0.65      (((v1_xboole_0 @ sk_B_1))
% 0.46/0.65         <= (~
% 0.46/0.65             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.46/0.65                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ 
% 0.46/0.65                sk_D) = (sk_F))))),
% 0.46/0.65      inference('clc', [status(thm)], ['164', '165'])).
% 0.46/0.65  thf('167', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('168', plain,
% 0.46/0.65      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.46/0.65          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.46/0.65          = (sk_F)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['166', '167'])).
% 0.46/0.65  thf('169', plain,
% 0.46/0.65      (~
% 0.46/0.65       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.46/0.65          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.46/0.65          = (sk_E))) | 
% 0.46/0.65       ~
% 0.46/0.65       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.46/0.65          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.46/0.65          = (sk_F))) | 
% 0.46/0.65       ~
% 0.46/0.65       (((k2_partfun1 @ sk_C_1 @ sk_B_1 @ sk_E @ 
% 0.46/0.65          (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))
% 0.46/0.65          = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.46/0.65             (k9_subset_1 @ sk_A @ sk_C_1 @ sk_D))))),
% 0.46/0.65      inference('split', [status(esa)], ['91'])).
% 0.46/0.65  thf('170', plain,
% 0.46/0.65      (~
% 0.46/0.65       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.46/0.65          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.46/0.65          = (sk_E)))),
% 0.46/0.65      inference('sat_resolution*', [status(thm)], ['120', '168', '169'])).
% 0.46/0.65  thf('171', plain,
% 0.46/0.65      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C_1 @ sk_D) @ sk_B_1 @ 
% 0.46/0.65         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F) @ sk_C_1)
% 0.46/0.65         != (sk_E))),
% 0.46/0.65      inference('simpl_trail', [status(thm)], ['92', '170'])).
% 0.46/0.65  thf('172', plain,
% 0.46/0.65      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.46/0.65        | ~ (v1_funct_1 @ 
% 0.46/0.65             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C_1 @ sk_D @ sk_E @ sk_F))
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_D))),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)], ['90', '171'])).
% 0.46/0.65  thf('173', plain,
% 0.46/0.65      (((v1_xboole_0 @ sk_D)
% 0.46/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_D)
% 0.46/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.46/0.65            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['21', '172'])).
% 0.46/0.65  thf('174', plain,
% 0.46/0.65      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_D))),
% 0.46/0.65      inference('simplify', [status(thm)], ['173'])).
% 0.46/0.65  thf('175', plain,
% 0.46/0.65      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.46/0.65        | ~ (v1_relat_1 @ sk_F)
% 0.46/0.65        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.65        | (v1_xboole_0 @ sk_D)
% 0.46/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_A))),
% 0.46/0.65      inference('sup-', [status(thm)], ['6', '174'])).
% 0.46/0.65  thf('176', plain, ((v1_relat_1 @ sk_F)),
% 0.46/0.65      inference('sup-', [status(thm)], ['111', '112'])).
% 0.46/0.65  thf('177', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.65  thf('178', plain,
% 0.46/0.65      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.46/0.65        | (v1_xboole_0 @ sk_D)
% 0.46/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_A))),
% 0.46/0.65      inference('demod', [status(thm)], ['175', '176', '177'])).
% 0.46/0.65  thf('179', plain,
% 0.46/0.65      ((((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.65        | ~ (v1_relat_1 @ sk_E)
% 0.46/0.65        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_D))),
% 0.46/0.65      inference('sup-', [status(thm)], ['5', '178'])).
% 0.46/0.65  thf('180', plain, ((v1_relat_1 @ sk_E)),
% 0.46/0.65      inference('sup-', [status(thm)], ['116', '117'])).
% 0.46/0.65  thf('181', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.46/0.65      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.46/0.65  thf('182', plain,
% 0.46/0.65      ((((k1_xboole_0) != (k1_xboole_0))
% 0.46/0.65        | (v1_xboole_0 @ sk_A)
% 0.46/0.65        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_D))),
% 0.46/0.65      inference('demod', [status(thm)], ['179', '180', '181'])).
% 0.46/0.65  thf('183', plain,
% 0.46/0.65      (((v1_xboole_0 @ sk_D)
% 0.46/0.65        | (v1_xboole_0 @ sk_C_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_B_1)
% 0.46/0.65        | (v1_xboole_0 @ sk_A))),
% 0.46/0.65      inference('simplify', [status(thm)], ['182'])).
% 0.46/0.65  thf('184', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('185', plain,
% 0.46/0.65      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_C_1))),
% 0.46/0.65      inference('sup-', [status(thm)], ['183', '184'])).
% 0.46/0.65  thf('186', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('187', plain, (((v1_xboole_0 @ sk_C_1) | (v1_xboole_0 @ sk_B_1))),
% 0.46/0.65      inference('clc', [status(thm)], ['185', '186'])).
% 0.46/0.65  thf('188', plain, (~ (v1_xboole_0 @ sk_C_1)),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('189', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.46/0.65      inference('clc', [status(thm)], ['187', '188'])).
% 0.46/0.65  thf('190', plain, ($false), inference('demod', [status(thm)], ['0', '189'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.46/0.65  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
