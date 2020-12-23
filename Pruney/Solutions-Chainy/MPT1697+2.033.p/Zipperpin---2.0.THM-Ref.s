%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sRMWla2EiR

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 14:08:58 EST 2020

% Result     : Theorem 0.69s
% Output     : Refutation 0.69s
% Verified   : 
% Statistics : Number of formulae       :  234 ( 704 expanded)
%              Number of leaves         :   38 ( 222 expanded)
%              Depth                    :   40
%              Number of atoms          : 3807 (28142 expanded)
%              Number of equality atoms :  139 ( 927 expanded)
%              Maximal formula depth    :   28 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_subset_1_type,type,(
    r1_subset_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_tmap_1_type,type,(
    k1_tmap_1: $i > $i > $i > $i > $i > $i > $i )).

thf(k2_partfun1_type,type,(
    k2_partfun1: $i > $i > $i > $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k3_xboole_0_type,type,(
    k3_xboole_0: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k4_subset_1_type,type,(
    k4_subset_1: $i > $i > $i > $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k9_subset_1_type,type,(
    k9_subset_1: $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

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
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(rc1_subset_1,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ? [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
          & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf('1',plain,(
    ! [X5: $i] :
      ( ( m1_subset_1 @ ( sk_B @ X5 ) @ ( k1_zfmisc_1 @ X5 ) )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[rc1_subset_1])).

thf(cc3_relset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( v1_xboole_0 @ C ) ) ) )).

thf('2',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ~ ( v1_xboole_0 @ X18 )
      | ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X20 ) ) )
      | ( v1_xboole_0 @ X19 ) ) ),
    inference(cnf,[status(esa)],[cc3_relset_1])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ( v1_xboole_0 @ ( sk_B @ ( k2_zfmisc_1 @ X1 @ X0 ) ) )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X5: $i] :
      ( ~ ( v1_xboole_0 @ ( sk_B @ X5 ) )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[rc1_subset_1])).

thf('5',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['3','4'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('6',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(t96_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k7_relat_1 @ B @ A )
        = ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ A @ ( k2_relat_1 @ B ) ) ) ) ) )).

thf('8',plain,(
    ! [X11: $i,X12: $i] :
      ( ( ( k7_relat_1 @ X11 @ X12 )
        = ( k3_xboole_0 @ X11 @ ( k2_zfmisc_1 @ X12 @ ( k2_relat_1 @ X11 ) ) ) )
      | ~ ( v1_relat_1 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t96_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X0 @ X1 )
        = ( k3_xboole_0 @ X0 @ k1_xboole_0 ) )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','8'])).

thf(t2_boole,axiom,(
    ! [A: $i] :
      ( ( k3_xboole_0 @ A @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('10',plain,(
    ! [X4: $i] :
      ( ( k3_xboole_0 @ X4 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t2_boole])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('13',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
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

thf('16',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ( v1_xboole_0 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X36 ) )
      | ( v1_xboole_0 @ X33 )
      | ( v1_xboole_0 @ X34 )
      | ( v1_xboole_0 @ X36 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X35 @ X34 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X36 @ X34 @ X33 @ X35 @ X32 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('17',plain,(
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
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
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
    inference(demod,[status(thm)],['17','18','19'])).

thf('21',plain,(
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
    inference('sup-',[status(thm)],['14','20'])).

thf('22',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_1 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['21','22','23'])).

thf('25',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['13','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ( v1_xboole_0 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X36 ) )
      | ( v1_xboole_0 @ X33 )
      | ( v1_xboole_0 @ X34 )
      | ( v1_xboole_0 @ X36 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X35 @ X34 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X36 @ X34 @ X33 @ X35 @ X32 @ X37 ) @ ( k4_subset_1 @ X36 @ X33 @ X35 ) @ X34 ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('32',plain,(
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
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('35',plain,(
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
    inference(demod,[status(thm)],['32','33','34'])).

thf('36',plain,(
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
    inference('sup-',[status(thm)],['29','35'])).

thf('37',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ( v1_funct_2 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ X0 @ sk_C @ sk_D ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['36','37','38'])).

thf('40',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['28','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('42',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    ! [X32: $i,X33: $i,X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( v1_funct_1 @ X32 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ X36 ) )
      | ( v1_xboole_0 @ X35 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X36 ) )
      | ( v1_xboole_0 @ X33 )
      | ( v1_xboole_0 @ X34 )
      | ( v1_xboole_0 @ X36 )
      | ~ ( v1_funct_1 @ X37 )
      | ~ ( v1_funct_2 @ X37 @ X35 @ X34 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X34 ) ) )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X36 @ X34 @ X33 @ X35 @ X32 @ X37 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X36 @ X33 @ X35 ) @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k1_tmap_1])).

thf('47',plain,(
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
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
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
    inference(demod,[status(thm)],['47','48','49'])).

thf('51',plain,(
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
    inference('sup-',[status(thm)],['44','50'])).

thf('52',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_D )
      | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ X0 )
      | ( m1_subset_1 @ ( k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X0 @ sk_C @ sk_D ) @ sk_B_1 ) ) ) ) ),
    inference(demod,[status(thm)],['51','52','53'])).

thf('55',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ~ ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['43','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('57',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['55','56'])).

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

thf('58',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X26 @ X25 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ( X31
       != ( k1_tmap_1 @ X27 @ X25 @ X30 @ X26 @ X29 @ X28 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X27 @ X30 @ X26 ) @ X25 @ X31 @ X30 )
        = X29 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X27 @ X30 @ X26 ) @ X25 ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( k4_subset_1 @ X27 @ X30 @ X26 ) @ X25 )
      | ~ ( v1_funct_1 @ X31 )
      | ( ( k2_partfun1 @ X30 @ X25 @ X29 @ ( k9_subset_1 @ X27 @ X30 @ X26 ) )
       != ( k2_partfun1 @ X26 @ X25 @ X28 @ ( k9_subset_1 @ X27 @ X30 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X25 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X27 ) )
      | ( v1_xboole_0 @ X30 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('59',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X25 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X25 ) ) )
      | ( ( k2_partfun1 @ X30 @ X25 @ X29 @ ( k9_subset_1 @ X27 @ X30 @ X26 ) )
       != ( k2_partfun1 @ X26 @ X25 @ X28 @ ( k9_subset_1 @ X27 @ X30 @ X26 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X27 @ X25 @ X30 @ X26 @ X29 @ X28 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X27 @ X25 @ X30 @ X26 @ X29 @ X28 ) @ ( k4_subset_1 @ X27 @ X30 @ X26 ) @ X25 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X27 @ X25 @ X30 @ X26 @ X29 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X27 @ X30 @ X26 ) @ X25 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X27 @ X30 @ X26 ) @ X25 @ ( k1_tmap_1 @ X27 @ X25 @ X30 @ X26 @ X29 @ X28 ) @ X30 )
        = X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ( v1_xboole_0 @ X26 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(simplify,[status(thm)],['58'])).

thf('60',plain,
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
    inference('sup-',[status(thm)],['57','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('63',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('64',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('65',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k9_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) )
     => ( ( k9_subset_1 @ A @ B @ C )
        = ( k3_xboole_0 @ B @ C ) ) ) )).

thf('66',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( ( k9_subset_1 @ X8 @ X6 @ X7 )
        = ( k3_xboole_0 @ X6 @ X7 ) )
      | ~ ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k9_subset_1])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    r1_subset_1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r1_subset_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B ) )
     => ( ( r1_subset_1 @ A @ B )
      <=> ( r1_xboole_0 @ A @ B ) ) ) )).

thf('69',plain,(
    ! [X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X13 )
      | ( v1_xboole_0 @ X14 )
      | ( r1_xboole_0 @ X13 @ X14 )
      | ~ ( r1_subset_1 @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r1_subset_1])).

thf('70',plain,
    ( ( r1_xboole_0 @ sk_C @ sk_D )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r1_xboole_0 @ sk_C @ sk_D ) ),
    inference(clc,[status(thm)],['70','71'])).

thf('73',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    r1_xboole_0 @ sk_C @ sk_D ),
    inference(clc,[status(thm)],['72','73'])).

thf(d7_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_xboole_0 @ A @ B )
    <=> ( ( k3_xboole_0 @ A @ B )
        = k1_xboole_0 ) ) )).

thf('75',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k3_xboole_0 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d7_xboole_0])).

thf('76',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( k2_partfun1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('78',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ( ( k2_partfun1 @ X22 @ X23 @ X21 @ X24 )
        = ( k7_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ X0 )
        = ( k7_relat_1 @ sk_E @ X0 ) )
      | ~ ( v1_funct_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('83',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['74','75'])).

thf('84',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('85',plain,(
    ! [X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ~ ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X22 @ X23 ) ) )
      | ~ ( v1_funct_1 @ X21 )
      | ( ( k2_partfun1 @ X22 @ X23 @ X21 @ X24 )
        = ( k7_relat_1 @ X21 @ X24 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_partfun1])).

thf('86',plain,(
    ! [X0: $i] :
      ( ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
        = ( k7_relat_1 @ sk_F @ X0 ) )
      | ~ ( v1_funct_1 @ sk_F ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('89',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('90',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('91',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('92',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,
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
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['60','61','62','63','64','67','76','81','82','83','88','89','90','91','92'])).

thf('94',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['93'])).

thf('95',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['42','94'])).

thf('96',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
      = sk_E )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['95'])).

thf('97',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('98',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E ) ),
    inference(split,[status(esa)],['97'])).

thf('99',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('100',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('101',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('102',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('103',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['97'])).

thf('104',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k3_xboole_0 @ sk_C @ sk_D ) ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['102','103'])).

thf('105',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('106',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['74','75'])).

thf('107',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['74','75'])).

thf('108',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ k1_xboole_0 )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['104','105','106','107'])).

thf('109',plain,
    ( ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['101','108'])).

thf('110',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('111',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['109','110'])).

thf('112',plain,
    ( ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_F )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['100','111'])).

thf('113',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('114',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('115',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['113','114'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('116',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('117',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['112','115','116'])).

thf('118',plain,
    ( ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_E )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['99','117'])).

thf('119',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('120',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( v1_relat_1 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('121',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['119','120'])).

thf('122',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('123',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
   <= ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['118','121','122'])).

thf('124',plain,
    ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
    = ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ),
    inference(simplify,[status(thm)],['123'])).

thf('125',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('126',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ X0 @ X1 )
        = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['9','10'])).

thf('127',plain,
    ( ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('128',plain,
    ( ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('129',plain,
    ( ( m1_subset_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('130',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i,X31: $i] :
      ( ( v1_xboole_0 @ X25 )
      | ( v1_xboole_0 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( v1_funct_2 @ X28 @ X26 @ X25 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ( X31
       != ( k1_tmap_1 @ X27 @ X25 @ X30 @ X26 @ X29 @ X28 ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X27 @ X30 @ X26 ) @ X25 @ X31 @ X26 )
        = X28 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X27 @ X30 @ X26 ) @ X25 ) ) )
      | ~ ( v1_funct_2 @ X31 @ ( k4_subset_1 @ X27 @ X30 @ X26 ) @ X25 )
      | ~ ( v1_funct_1 @ X31 )
      | ( ( k2_partfun1 @ X30 @ X25 @ X29 @ ( k9_subset_1 @ X27 @ X30 @ X26 ) )
       != ( k2_partfun1 @ X26 @ X25 @ X28 @ ( k9_subset_1 @ X27 @ X30 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X25 )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X27 ) )
      | ( v1_xboole_0 @ X30 )
      | ( v1_xboole_0 @ X27 ) ) ),
    inference(cnf,[status(esa)],[d1_tmap_1])).

thf('131',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( v1_xboole_0 @ X27 )
      | ( v1_xboole_0 @ X30 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( v1_funct_1 @ X29 )
      | ~ ( v1_funct_2 @ X29 @ X30 @ X25 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X25 ) ) )
      | ( ( k2_partfun1 @ X30 @ X25 @ X29 @ ( k9_subset_1 @ X27 @ X30 @ X26 ) )
       != ( k2_partfun1 @ X26 @ X25 @ X28 @ ( k9_subset_1 @ X27 @ X30 @ X26 ) ) )
      | ~ ( v1_funct_1 @ ( k1_tmap_1 @ X27 @ X25 @ X30 @ X26 @ X29 @ X28 ) )
      | ~ ( v1_funct_2 @ ( k1_tmap_1 @ X27 @ X25 @ X30 @ X26 @ X29 @ X28 ) @ ( k4_subset_1 @ X27 @ X30 @ X26 ) @ X25 )
      | ~ ( m1_subset_1 @ ( k1_tmap_1 @ X27 @ X25 @ X30 @ X26 @ X29 @ X28 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ X27 @ X30 @ X26 ) @ X25 ) ) )
      | ( ( k2_partfun1 @ ( k4_subset_1 @ X27 @ X30 @ X26 ) @ X25 @ ( k1_tmap_1 @ X27 @ X25 @ X30 @ X26 @ X29 @ X28 ) @ X26 )
        = X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_2 @ X28 @ X26 @ X25 )
      | ~ ( v1_funct_1 @ X28 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ X27 ) )
      | ( v1_xboole_0 @ X26 )
      | ( v1_xboole_0 @ X25 ) ) ),
    inference(simplify,[status(thm)],['130'])).

thf('132',plain,
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
    inference('sup-',[status(thm)],['129','131'])).

thf('133',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('134',plain,(
    v1_funct_1 @ sk_F ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('135',plain,(
    v1_funct_2 @ sk_F @ sk_D @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('136',plain,(
    m1_subset_1 @ sk_F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_D @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('137',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('138',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['74','75'])).

thf('139',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ X0 )
      = ( k7_relat_1 @ sk_E @ X0 ) ) ),
    inference(demod,[status(thm)],['79','80'])).

thf('140',plain,(
    ! [X0: $i] :
      ( ( k9_subset_1 @ sk_A @ X0 @ sk_D )
      = ( k3_xboole_0 @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('141',plain,
    ( ( k3_xboole_0 @ sk_C @ sk_D )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['74','75'])).

thf('142',plain,(
    ! [X0: $i] :
      ( ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0 )
      = ( k7_relat_1 @ sk_F @ X0 ) ) ),
    inference(demod,[status(thm)],['86','87'])).

thf('143',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_C @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('144',plain,(
    v1_funct_2 @ sk_E @ sk_C @ sk_B_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('145',plain,(
    v1_funct_1 @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('146',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('147',plain,
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
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['132','133','134','135','136','137','138','139','140','141','142','143','144','145','146'])).

thf('148',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ~ ( v1_funct_2 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['147'])).

thf('149',plain,
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
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['128','148'])).

thf('150',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['149'])).

thf('151',plain,
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
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['127','150'])).

thf('152',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['151'])).

thf('153',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference('sup-',[status(thm)],['126','152'])).

thf('154',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['113','114'])).

thf('155',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('156',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference(demod,[status(thm)],['153','154','155'])).

thf('157',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['125','156'])).

thf('158',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['119','120'])).

thf('159',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('160',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['157','158','159'])).

thf('161',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
      = sk_F ) ),
    inference(simplify,[status(thm)],['160'])).

thf('162',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(split,[status(esa)],['97'])).

thf('163',plain,
    ( ( ( sk_F != sk_F )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_D ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['161','162'])).

thf('164',plain,
    ( ( ( v1_xboole_0 @ sk_D )
      | ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_A ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(simplify,[status(thm)],['163'])).

thf('165',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('166',plain,
    ( ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B_1 )
      | ( v1_xboole_0 @ sk_C ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference('sup-',[status(thm)],['164','165'])).

thf('167',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('168',plain,
    ( ( ( v1_xboole_0 @ sk_C )
      | ( v1_xboole_0 @ sk_B_1 ) )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['166','167'])).

thf('169',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('170',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
   <= ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F ) ),
    inference(clc,[status(thm)],['168','169'])).

thf('171',plain,(
    ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('172',plain,
    ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
    = sk_F ),
    inference('sup-',[status(thm)],['170','171'])).

thf('173',plain,
    ( ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
     != sk_E )
    | ( ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_D )
     != sk_F )
    | ( ( k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) )
     != ( k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ ( k9_subset_1 @ sk_A @ sk_C @ sk_D ) ) ) ),
    inference(split,[status(esa)],['97'])).

thf('174',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference('sat_resolution*',[status(thm)],['124','172','173'])).

thf('175',plain,(
    ( k2_partfun1 @ ( k4_subset_1 @ sk_A @ sk_C @ sk_D ) @ sk_B_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) @ sk_C )
 != sk_E ),
    inference(simpl_trail,[status(thm)],['98','174'])).

thf('176',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ~ ( v1_funct_1 @ ( k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('simplify_reflect-',[status(thm)],['96','175'])).

thf('177',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A )
    | ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','176'])).

thf('178',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != ( k7_relat_1 @ sk_F @ k1_xboole_0 ) )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(simplify,[status(thm)],['177'])).

thf('179',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_F )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['12','178'])).

thf('180',plain,(
    v1_relat_1 @ sk_F ),
    inference('sup-',[status(thm)],['113','114'])).

thf('181',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('182',plain,
    ( ( ( k7_relat_1 @ sk_E @ k1_xboole_0 )
     != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(demod,[status(thm)],['179','180','181'])).

thf('183',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_E )
    | ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference('sup-',[status(thm)],['11','182'])).

thf('184',plain,(
    v1_relat_1 @ sk_E ),
    inference('sup-',[status(thm)],['119','120'])).

thf('185',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('186',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_D ) ),
    inference(demod,[status(thm)],['183','184','185'])).

thf('187',plain,
    ( ( v1_xboole_0 @ sk_D )
    | ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['186'])).

thf('188',plain,(
    ~ ( v1_xboole_0 @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('189',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['187','188'])).

thf('190',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('191',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['189','190'])).

thf('192',plain,(
    ~ ( v1_xboole_0 @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('193',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference(clc,[status(thm)],['191','192'])).

thf('194',plain,(
    $false ),
    inference(demod,[status(thm)],['0','193'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.sRMWla2EiR
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:02:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running portfolio for 600 s
% 0.14/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.34  % Number of cores: 8
% 0.14/0.34  % Python version: Python 3.6.8
% 0.14/0.35  % Running in FO mode
% 0.69/0.90  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.69/0.90  % Solved by: fo/fo7.sh
% 0.69/0.90  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.69/0.90  % done 384 iterations in 0.410s
% 0.69/0.90  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.69/0.90  % SZS output start Refutation
% 0.69/0.90  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.69/0.90  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.69/0.90  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.69/0.90  thf(sk_D_type, type, sk_D: $i).
% 0.69/0.90  thf(sk_B_type, type, sk_B: $i > $i).
% 0.69/0.90  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.69/0.90  thf(r1_subset_1_type, type, r1_subset_1: $i > $i > $o).
% 0.69/0.90  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.69/0.90  thf(sk_A_type, type, sk_A: $i).
% 0.69/0.90  thf(k1_tmap_1_type, type, k1_tmap_1: $i > $i > $i > $i > $i > $i > $i).
% 0.69/0.90  thf(k2_partfun1_type, type, k2_partfun1: $i > $i > $i > $i > $i).
% 0.69/0.90  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.69/0.90  thf(k3_xboole_0_type, type, k3_xboole_0: $i > $i > $i).
% 0.69/0.90  thf(sk_C_type, type, sk_C: $i).
% 0.69/0.90  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.69/0.90  thf(sk_E_type, type, sk_E: $i).
% 0.69/0.90  thf(k4_subset_1_type, type, k4_subset_1: $i > $i > $i > $i).
% 0.69/0.90  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.69/0.90  thf(k9_subset_1_type, type, k9_subset_1: $i > $i > $i > $i).
% 0.69/0.90  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.69/0.90  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.69/0.90  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.69/0.90  thf(sk_F_type, type, sk_F: $i).
% 0.69/0.90  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.69/0.90  thf(t6_tmap_1, conjecture,
% 0.69/0.90    (![A:$i]:
% 0.69/0.90     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.69/0.90       ( ![B:$i]:
% 0.69/0.90         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.69/0.90           ( ![C:$i]:
% 0.69/0.90             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.69/0.90                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.69/0.90               ( ![D:$i]:
% 0.69/0.90                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.69/0.90                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.69/0.90                   ( ( r1_subset_1 @ C @ D ) =>
% 0.69/0.90                     ( ![E:$i]:
% 0.69/0.90                       ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.69/0.90                           ( m1_subset_1 @
% 0.69/0.90                             E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.69/0.90                         ( ![F:$i]:
% 0.69/0.90                           ( ( ( v1_funct_1 @ F ) & 
% 0.69/0.90                               ( v1_funct_2 @ F @ D @ B ) & 
% 0.69/0.90                               ( m1_subset_1 @
% 0.69/0.90                                 F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.69/0.90                             ( ( ( k2_partfun1 @
% 0.69/0.90                                   C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.69/0.90                                 ( k2_partfun1 @
% 0.69/0.90                                   D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.69/0.90                               ( ( k2_partfun1 @
% 0.69/0.90                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.69/0.90                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.69/0.90                                 ( E ) ) & 
% 0.69/0.90                               ( ( k2_partfun1 @
% 0.69/0.90                                   ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.69/0.90                                   ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.69/0.90                                 ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.69/0.90  thf(zf_stmt_0, negated_conjecture,
% 0.69/0.90    (~( ![A:$i]:
% 0.69/0.90        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.69/0.90          ( ![B:$i]:
% 0.69/0.90            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.69/0.90              ( ![C:$i]:
% 0.69/0.90                ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.69/0.90                    ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.69/0.90                  ( ![D:$i]:
% 0.69/0.90                    ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.69/0.90                        ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.69/0.90                      ( ( r1_subset_1 @ C @ D ) =>
% 0.69/0.90                        ( ![E:$i]:
% 0.69/0.90                          ( ( ( v1_funct_1 @ E ) & 
% 0.69/0.90                              ( v1_funct_2 @ E @ C @ B ) & 
% 0.69/0.90                              ( m1_subset_1 @
% 0.69/0.90                                E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.69/0.90                            ( ![F:$i]:
% 0.69/0.90                              ( ( ( v1_funct_1 @ F ) & 
% 0.69/0.90                                  ( v1_funct_2 @ F @ D @ B ) & 
% 0.69/0.90                                  ( m1_subset_1 @
% 0.69/0.90                                    F @ 
% 0.69/0.90                                    ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.69/0.90                                ( ( ( k2_partfun1 @
% 0.69/0.90                                      C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.69/0.90                                    ( k2_partfun1 @
% 0.69/0.90                                      D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) & 
% 0.69/0.90                                  ( ( k2_partfun1 @
% 0.69/0.90                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.69/0.90                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ C ) =
% 0.69/0.90                                    ( E ) ) & 
% 0.69/0.90                                  ( ( k2_partfun1 @
% 0.69/0.90                                      ( k4_subset_1 @ A @ C @ D ) @ B @ 
% 0.69/0.90                                      ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ D ) =
% 0.69/0.90                                    ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.69/0.90    inference('cnf.neg', [status(esa)], [t6_tmap_1])).
% 0.69/0.90  thf('0', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf(rc1_subset_1, axiom,
% 0.69/0.90    (![A:$i]:
% 0.69/0.90     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.69/0.90       ( ?[B:$i]:
% 0.69/0.90         ( ( ~( v1_xboole_0 @ B ) ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) ) ) ))).
% 0.69/0.90  thf('1', plain,
% 0.69/0.90      (![X5 : $i]:
% 0.69/0.90         ((m1_subset_1 @ (sk_B @ X5) @ (k1_zfmisc_1 @ X5)) | (v1_xboole_0 @ X5))),
% 0.69/0.90      inference('cnf', [status(esa)], [rc1_subset_1])).
% 0.69/0.90  thf(cc3_relset_1, axiom,
% 0.69/0.90    (![A:$i,B:$i]:
% 0.69/0.90     ( ( v1_xboole_0 @ A ) =>
% 0.69/0.90       ( ![C:$i]:
% 0.69/0.90         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.69/0.90           ( v1_xboole_0 @ C ) ) ) ))).
% 0.69/0.90  thf('2', plain,
% 0.69/0.90      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.69/0.90         (~ (v1_xboole_0 @ X18)
% 0.69/0.90          | ~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X18 @ X20)))
% 0.69/0.90          | (v1_xboole_0 @ X19))),
% 0.69/0.90      inference('cnf', [status(esa)], [cc3_relset_1])).
% 0.69/0.90  thf('3', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i]:
% 0.69/0.90         ((v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0))
% 0.69/0.90          | (v1_xboole_0 @ (sk_B @ (k2_zfmisc_1 @ X1 @ X0)))
% 0.69/0.90          | ~ (v1_xboole_0 @ X1))),
% 0.69/0.90      inference('sup-', [status(thm)], ['1', '2'])).
% 0.69/0.90  thf('4', plain,
% 0.69/0.90      (![X5 : $i]: (~ (v1_xboole_0 @ (sk_B @ X5)) | (v1_xboole_0 @ X5))),
% 0.69/0.90      inference('cnf', [status(esa)], [rc1_subset_1])).
% 0.69/0.90  thf('5', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i]:
% 0.69/0.90         (~ (v1_xboole_0 @ X1) | (v1_xboole_0 @ (k2_zfmisc_1 @ X1 @ X0)))),
% 0.69/0.90      inference('clc', [status(thm)], ['3', '4'])).
% 0.69/0.90  thf(l13_xboole_0, axiom,
% 0.69/0.90    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.69/0.90  thf('6', plain,
% 0.69/0.90      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.69/0.90      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.69/0.90  thf('7', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i]:
% 0.69/0.90         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['5', '6'])).
% 0.69/0.90  thf(t96_relat_1, axiom,
% 0.69/0.90    (![A:$i,B:$i]:
% 0.69/0.90     ( ( v1_relat_1 @ B ) =>
% 0.69/0.90       ( ( k7_relat_1 @ B @ A ) =
% 0.69/0.90         ( k3_xboole_0 @ B @ ( k2_zfmisc_1 @ A @ ( k2_relat_1 @ B ) ) ) ) ))).
% 0.69/0.90  thf('8', plain,
% 0.69/0.90      (![X11 : $i, X12 : $i]:
% 0.69/0.90         (((k7_relat_1 @ X11 @ X12)
% 0.69/0.90            = (k3_xboole_0 @ X11 @ (k2_zfmisc_1 @ X12 @ (k2_relat_1 @ X11))))
% 0.69/0.90          | ~ (v1_relat_1 @ X11))),
% 0.69/0.90      inference('cnf', [status(esa)], [t96_relat_1])).
% 0.69/0.90  thf('9', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i]:
% 0.69/0.90         (((k7_relat_1 @ X0 @ X1) = (k3_xboole_0 @ X0 @ k1_xboole_0))
% 0.69/0.90          | ~ (v1_xboole_0 @ X1)
% 0.69/0.90          | ~ (v1_relat_1 @ X0))),
% 0.69/0.90      inference('sup+', [status(thm)], ['7', '8'])).
% 0.69/0.90  thf(t2_boole, axiom,
% 0.69/0.90    (![A:$i]: ( ( k3_xboole_0 @ A @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.69/0.90  thf('10', plain,
% 0.69/0.90      (![X4 : $i]: ((k3_xboole_0 @ X4 @ k1_xboole_0) = (k1_xboole_0))),
% 0.69/0.90      inference('cnf', [status(esa)], [t2_boole])).
% 0.69/0.90  thf('11', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i]:
% 0.69/0.90         (((k7_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.69/0.90          | ~ (v1_xboole_0 @ X1)
% 0.69/0.90          | ~ (v1_relat_1 @ X0))),
% 0.69/0.90      inference('demod', [status(thm)], ['9', '10'])).
% 0.69/0.90  thf('12', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i]:
% 0.69/0.90         (((k7_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.69/0.90          | ~ (v1_xboole_0 @ X1)
% 0.69/0.90          | ~ (v1_relat_1 @ X0))),
% 0.69/0.90      inference('demod', [status(thm)], ['9', '10'])).
% 0.69/0.90  thf('13', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('14', plain,
% 0.69/0.90      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('15', plain,
% 0.69/0.90      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf(dt_k1_tmap_1, axiom,
% 0.69/0.90    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.69/0.90     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) & 
% 0.69/0.90         ( ~( v1_xboole_0 @ C ) ) & 
% 0.69/0.90         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) & 
% 0.69/0.90         ( ~( v1_xboole_0 @ D ) ) & 
% 0.69/0.90         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) & ( v1_funct_1 @ E ) & 
% 0.69/0.90         ( v1_funct_2 @ E @ C @ B ) & 
% 0.69/0.90         ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) & 
% 0.69/0.90         ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.69/0.90         ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.69/0.90       ( ( v1_funct_1 @ ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) & 
% 0.69/0.90         ( v1_funct_2 @
% 0.69/0.90           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.69/0.90           ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.69/0.90         ( m1_subset_1 @
% 0.69/0.90           ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) @ 
% 0.69/0.90           ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) ))).
% 0.69/0.90  thf('16', plain,
% 0.69/0.90      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.69/0.90         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.69/0.90          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 0.69/0.90          | ~ (v1_funct_1 @ X32)
% 0.69/0.90          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 0.69/0.90          | (v1_xboole_0 @ X35)
% 0.69/0.90          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X36))
% 0.69/0.90          | (v1_xboole_0 @ X33)
% 0.69/0.90          | (v1_xboole_0 @ X34)
% 0.69/0.90          | (v1_xboole_0 @ X36)
% 0.69/0.90          | ~ (v1_funct_1 @ X37)
% 0.69/0.90          | ~ (v1_funct_2 @ X37 @ X35 @ X34)
% 0.69/0.90          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.69/0.90          | (v1_funct_1 @ (k1_tmap_1 @ X36 @ X34 @ X33 @ X35 @ X32 @ X37)))),
% 0.69/0.90      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.69/0.90  thf('17', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.90         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B_1 @ sk_C @ X1 @ sk_E @ X0))
% 0.69/0.90          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 0.69/0.90          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 0.69/0.90          | ~ (v1_funct_1 @ X0)
% 0.69/0.90          | (v1_xboole_0 @ X2)
% 0.69/0.90          | (v1_xboole_0 @ sk_B_1)
% 0.69/0.90          | (v1_xboole_0 @ sk_C)
% 0.69/0.90          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.69/0.90          | (v1_xboole_0 @ X1)
% 0.69/0.90          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2))
% 0.69/0.90          | ~ (v1_funct_1 @ sk_E)
% 0.69/0.90          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B_1))),
% 0.69/0.90      inference('sup-', [status(thm)], ['15', '16'])).
% 0.69/0.90  thf('18', plain, ((v1_funct_1 @ sk_E)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('19', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B_1)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('20', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.90         ((v1_funct_1 @ (k1_tmap_1 @ X2 @ sk_B_1 @ sk_C @ X1 @ sk_E @ X0))
% 0.69/0.90          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X1 @ sk_B_1)))
% 0.69/0.90          | ~ (v1_funct_2 @ X0 @ X1 @ sk_B_1)
% 0.69/0.90          | ~ (v1_funct_1 @ X0)
% 0.69/0.90          | (v1_xboole_0 @ X2)
% 0.69/0.90          | (v1_xboole_0 @ sk_B_1)
% 0.69/0.90          | (v1_xboole_0 @ sk_C)
% 0.69/0.90          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X2))
% 0.69/0.90          | (v1_xboole_0 @ X1)
% 0.69/0.90          | ~ (m1_subset_1 @ X1 @ (k1_zfmisc_1 @ X2)))),
% 0.69/0.90      inference('demod', [status(thm)], ['17', '18', '19'])).
% 0.69/0.90  thf('21', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.69/0.90          | (v1_xboole_0 @ sk_D)
% 0.69/0.90          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.69/0.90          | (v1_xboole_0 @ sk_C)
% 0.69/0.90          | (v1_xboole_0 @ sk_B_1)
% 0.69/0.90          | (v1_xboole_0 @ X0)
% 0.69/0.90          | ~ (v1_funct_1 @ sk_F)
% 0.69/0.90          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 0.69/0.90          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.69/0.90      inference('sup-', [status(thm)], ['14', '20'])).
% 0.69/0.90  thf('22', plain, ((v1_funct_1 @ sk_F)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('23', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('24', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.69/0.90          | (v1_xboole_0 @ sk_D)
% 0.69/0.90          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.69/0.90          | (v1_xboole_0 @ sk_C)
% 0.69/0.90          | (v1_xboole_0 @ sk_B_1)
% 0.69/0.90          | (v1_xboole_0 @ X0)
% 0.69/0.90          | (v1_funct_1 @ (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F)))),
% 0.69/0.90      inference('demod', [status(thm)], ['21', '22', '23'])).
% 0.69/0.90  thf('25', plain,
% 0.69/0.90      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.69/0.90        | (v1_xboole_0 @ sk_A)
% 0.69/0.90        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.90        | (v1_xboole_0 @ sk_C)
% 0.69/0.90        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.69/0.90        | (v1_xboole_0 @ sk_D))),
% 0.69/0.90      inference('sup-', [status(thm)], ['13', '24'])).
% 0.69/0.90  thf('26', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('27', plain,
% 0.69/0.90      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.69/0.90        | (v1_xboole_0 @ sk_A)
% 0.69/0.90        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.90        | (v1_xboole_0 @ sk_C)
% 0.69/0.90        | (v1_xboole_0 @ sk_D))),
% 0.69/0.90      inference('demod', [status(thm)], ['25', '26'])).
% 0.69/0.90  thf('28', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('29', plain,
% 0.69/0.90      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('30', plain,
% 0.69/0.90      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('31', plain,
% 0.69/0.90      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.69/0.90         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.69/0.90          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 0.69/0.90          | ~ (v1_funct_1 @ X32)
% 0.69/0.90          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 0.69/0.90          | (v1_xboole_0 @ X35)
% 0.69/0.90          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X36))
% 0.69/0.90          | (v1_xboole_0 @ X33)
% 0.69/0.90          | (v1_xboole_0 @ X34)
% 0.69/0.90          | (v1_xboole_0 @ X36)
% 0.69/0.90          | ~ (v1_funct_1 @ X37)
% 0.69/0.90          | ~ (v1_funct_2 @ X37 @ X35 @ X34)
% 0.69/0.90          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.69/0.90          | (v1_funct_2 @ (k1_tmap_1 @ X36 @ X34 @ X33 @ X35 @ X32 @ X37) @ 
% 0.69/0.90             (k4_subset_1 @ X36 @ X33 @ X35) @ X34))),
% 0.69/0.90      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.69/0.90  thf('32', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.90         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.69/0.90           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B_1)
% 0.69/0.90          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.69/0.90          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 0.69/0.90          | ~ (v1_funct_1 @ X2)
% 0.69/0.90          | (v1_xboole_0 @ X1)
% 0.69/0.90          | (v1_xboole_0 @ sk_B_1)
% 0.69/0.90          | (v1_xboole_0 @ sk_C)
% 0.69/0.90          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.69/0.90          | (v1_xboole_0 @ X0)
% 0.69/0.90          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.69/0.90          | ~ (v1_funct_1 @ sk_E)
% 0.69/0.90          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B_1))),
% 0.69/0.90      inference('sup-', [status(thm)], ['30', '31'])).
% 0.69/0.90  thf('33', plain, ((v1_funct_1 @ sk_E)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('34', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B_1)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('35', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.90         ((v1_funct_2 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.69/0.90           (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B_1)
% 0.69/0.90          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.69/0.90          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 0.69/0.90          | ~ (v1_funct_1 @ X2)
% 0.69/0.90          | (v1_xboole_0 @ X1)
% 0.69/0.90          | (v1_xboole_0 @ sk_B_1)
% 0.69/0.90          | (v1_xboole_0 @ sk_C)
% 0.69/0.90          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.69/0.90          | (v1_xboole_0 @ X0)
% 0.69/0.90          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.69/0.90      inference('demod', [status(thm)], ['32', '33', '34'])).
% 0.69/0.90  thf('36', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.69/0.90          | (v1_xboole_0 @ sk_D)
% 0.69/0.90          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.69/0.90          | (v1_xboole_0 @ sk_C)
% 0.69/0.90          | (v1_xboole_0 @ sk_B_1)
% 0.69/0.90          | (v1_xboole_0 @ X0)
% 0.69/0.90          | ~ (v1_funct_1 @ sk_F)
% 0.69/0.90          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 0.69/0.90          | (v1_funct_2 @ 
% 0.69/0.90             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.69/0.90             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B_1))),
% 0.69/0.90      inference('sup-', [status(thm)], ['29', '35'])).
% 0.69/0.90  thf('37', plain, ((v1_funct_1 @ sk_F)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('38', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('39', plain,
% 0.69/0.90      (![X0 : $i]:
% 0.69/0.90         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.69/0.90          | (v1_xboole_0 @ sk_D)
% 0.69/0.90          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.69/0.90          | (v1_xboole_0 @ sk_C)
% 0.69/0.90          | (v1_xboole_0 @ sk_B_1)
% 0.69/0.90          | (v1_xboole_0 @ X0)
% 0.69/0.90          | (v1_funct_2 @ 
% 0.69/0.90             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.69/0.90             (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B_1))),
% 0.69/0.90      inference('demod', [status(thm)], ['36', '37', '38'])).
% 0.69/0.90  thf('40', plain,
% 0.69/0.90      (((v1_funct_2 @ 
% 0.69/0.90         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.69/0.90         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 0.69/0.90        | (v1_xboole_0 @ sk_A)
% 0.69/0.90        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.90        | (v1_xboole_0 @ sk_C)
% 0.69/0.90        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.69/0.90        | (v1_xboole_0 @ sk_D))),
% 0.69/0.90      inference('sup-', [status(thm)], ['28', '39'])).
% 0.69/0.90  thf('41', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('42', plain,
% 0.69/0.90      (((v1_funct_2 @ 
% 0.69/0.90         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.69/0.90         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 0.69/0.90        | (v1_xboole_0 @ sk_A)
% 0.69/0.90        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.90        | (v1_xboole_0 @ sk_C)
% 0.69/0.90        | (v1_xboole_0 @ sk_D))),
% 0.69/0.90      inference('demod', [status(thm)], ['40', '41'])).
% 0.69/0.90  thf('43', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('44', plain,
% 0.69/0.90      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('45', plain,
% 0.69/0.90      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 0.69/0.90      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.90  thf('46', plain,
% 0.69/0.90      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.69/0.90         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.69/0.90          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 0.69/0.90          | ~ (v1_funct_1 @ X32)
% 0.69/0.90          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ X36))
% 0.69/0.90          | (v1_xboole_0 @ X35)
% 0.69/0.90          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ X36))
% 0.69/0.90          | (v1_xboole_0 @ X33)
% 0.69/0.90          | (v1_xboole_0 @ X34)
% 0.69/0.90          | (v1_xboole_0 @ X36)
% 0.69/0.90          | ~ (v1_funct_1 @ X37)
% 0.69/0.90          | ~ (v1_funct_2 @ X37 @ X35 @ X34)
% 0.69/0.90          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X34)))
% 0.69/0.90          | (m1_subset_1 @ (k1_tmap_1 @ X36 @ X34 @ X33 @ X35 @ X32 @ X37) @ 
% 0.69/0.90             (k1_zfmisc_1 @ 
% 0.69/0.90              (k2_zfmisc_1 @ (k4_subset_1 @ X36 @ X33 @ X35) @ X34))))),
% 0.69/0.90      inference('cnf', [status(esa)], [dt_k1_tmap_1])).
% 0.69/0.90  thf('47', plain,
% 0.69/0.90      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.91         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.69/0.91           (k1_zfmisc_1 @ 
% 0.69/0.91            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B_1)))
% 0.69/0.91          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.69/0.91          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 0.69/0.91          | ~ (v1_funct_1 @ X2)
% 0.69/0.91          | (v1_xboole_0 @ X1)
% 0.69/0.91          | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91          | (v1_xboole_0 @ sk_C)
% 0.69/0.91          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.69/0.91          | (v1_xboole_0 @ X0)
% 0.69/0.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1))
% 0.69/0.91          | ~ (v1_funct_1 @ sk_E)
% 0.69/0.91          | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B_1))),
% 0.69/0.91      inference('sup-', [status(thm)], ['45', '46'])).
% 0.69/0.91  thf('48', plain, ((v1_funct_1 @ sk_E)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('49', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B_1)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('50', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.69/0.91         ((m1_subset_1 @ (k1_tmap_1 @ X1 @ sk_B_1 @ sk_C @ X0 @ sk_E @ X2) @ 
% 0.69/0.91           (k1_zfmisc_1 @ 
% 0.69/0.91            (k2_zfmisc_1 @ (k4_subset_1 @ X1 @ sk_C @ X0) @ sk_B_1)))
% 0.69/0.91          | ~ (m1_subset_1 @ X2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_B_1)))
% 0.69/0.91          | ~ (v1_funct_2 @ X2 @ X0 @ sk_B_1)
% 0.69/0.91          | ~ (v1_funct_1 @ X2)
% 0.69/0.91          | (v1_xboole_0 @ X1)
% 0.69/0.91          | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91          | (v1_xboole_0 @ sk_C)
% 0.69/0.91          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X1))
% 0.69/0.91          | (v1_xboole_0 @ X0)
% 0.69/0.91          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X1)))),
% 0.69/0.91      inference('demod', [status(thm)], ['47', '48', '49'])).
% 0.69/0.91  thf('51', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.69/0.91          | (v1_xboole_0 @ sk_D)
% 0.69/0.91          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.69/0.91          | (v1_xboole_0 @ sk_C)
% 0.69/0.91          | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91          | (v1_xboole_0 @ X0)
% 0.69/0.91          | ~ (v1_funct_1 @ sk_F)
% 0.69/0.91          | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 0.69/0.91          | (m1_subset_1 @ 
% 0.69/0.91             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.69/0.91             (k1_zfmisc_1 @ 
% 0.69/0.91              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B_1))))),
% 0.69/0.91      inference('sup-', [status(thm)], ['44', '50'])).
% 0.69/0.91  thf('52', plain, ((v1_funct_1 @ sk_F)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('53', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('54', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         (~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ X0))
% 0.69/0.91          | (v1_xboole_0 @ sk_D)
% 0.69/0.91          | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ X0))
% 0.69/0.91          | (v1_xboole_0 @ sk_C)
% 0.69/0.91          | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91          | (v1_xboole_0 @ X0)
% 0.69/0.91          | (m1_subset_1 @ 
% 0.69/0.91             (k1_tmap_1 @ X0 @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.69/0.91             (k1_zfmisc_1 @ 
% 0.69/0.91              (k2_zfmisc_1 @ (k4_subset_1 @ X0 @ sk_C @ sk_D) @ sk_B_1))))),
% 0.69/0.91      inference('demod', [status(thm)], ['51', '52', '53'])).
% 0.69/0.91  thf('55', plain,
% 0.69/0.91      (((m1_subset_1 @ 
% 0.69/0.91         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.69/0.91         (k1_zfmisc_1 @ 
% 0.69/0.91          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)))
% 0.69/0.91        | (v1_xboole_0 @ sk_A)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.69/0.91        | (v1_xboole_0 @ sk_D))),
% 0.69/0.91      inference('sup-', [status(thm)], ['43', '54'])).
% 0.69/0.91  thf('56', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('57', plain,
% 0.69/0.91      (((m1_subset_1 @ 
% 0.69/0.91         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.69/0.91         (k1_zfmisc_1 @ 
% 0.69/0.91          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)))
% 0.69/0.91        | (v1_xboole_0 @ sk_A)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_D))),
% 0.69/0.91      inference('demod', [status(thm)], ['55', '56'])).
% 0.69/0.91  thf(d1_tmap_1, axiom,
% 0.69/0.91    (![A:$i]:
% 0.69/0.91     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.69/0.91       ( ![B:$i]:
% 0.69/0.91         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.69/0.91           ( ![C:$i]:
% 0.69/0.91             ( ( ( ~( v1_xboole_0 @ C ) ) & 
% 0.69/0.91                 ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.69/0.91               ( ![D:$i]:
% 0.69/0.91                 ( ( ( ~( v1_xboole_0 @ D ) ) & 
% 0.69/0.91                     ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ A ) ) ) =>
% 0.69/0.91                   ( ![E:$i]:
% 0.69/0.91                     ( ( ( v1_funct_1 @ E ) & ( v1_funct_2 @ E @ C @ B ) & 
% 0.69/0.91                         ( m1_subset_1 @
% 0.69/0.91                           E @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ C @ B ) ) ) ) =>
% 0.69/0.91                       ( ![F:$i]:
% 0.69/0.91                         ( ( ( v1_funct_1 @ F ) & ( v1_funct_2 @ F @ D @ B ) & 
% 0.69/0.91                             ( m1_subset_1 @
% 0.69/0.91                               F @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ D @ B ) ) ) ) =>
% 0.69/0.91                           ( ( ( k2_partfun1 @
% 0.69/0.91                                 C @ B @ E @ ( k9_subset_1 @ A @ C @ D ) ) =
% 0.69/0.91                               ( k2_partfun1 @
% 0.69/0.91                                 D @ B @ F @ ( k9_subset_1 @ A @ C @ D ) ) ) =>
% 0.69/0.91                             ( ![G:$i]:
% 0.69/0.91                               ( ( ( v1_funct_1 @ G ) & 
% 0.69/0.91                                   ( v1_funct_2 @
% 0.69/0.91                                     G @ ( k4_subset_1 @ A @ C @ D ) @ B ) & 
% 0.69/0.91                                   ( m1_subset_1 @
% 0.69/0.91                                     G @ 
% 0.69/0.91                                     ( k1_zfmisc_1 @
% 0.69/0.91                                       ( k2_zfmisc_1 @
% 0.69/0.91                                         ( k4_subset_1 @ A @ C @ D ) @ B ) ) ) ) =>
% 0.69/0.91                                 ( ( ( G ) =
% 0.69/0.91                                     ( k1_tmap_1 @ A @ B @ C @ D @ E @ F ) ) <=>
% 0.69/0.91                                   ( ( ( k2_partfun1 @
% 0.69/0.91                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.69/0.91                                         C ) =
% 0.69/0.91                                       ( E ) ) & 
% 0.69/0.91                                     ( ( k2_partfun1 @
% 0.69/0.91                                         ( k4_subset_1 @ A @ C @ D ) @ B @ G @ 
% 0.69/0.91                                         D ) =
% 0.69/0.91                                       ( F ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.69/0.91  thf('58', plain,
% 0.69/0.91      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.69/0.91         ((v1_xboole_0 @ X25)
% 0.69/0.91          | (v1_xboole_0 @ X26)
% 0.69/0.91          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27))
% 0.69/0.91          | ~ (v1_funct_1 @ X28)
% 0.69/0.91          | ~ (v1_funct_2 @ X28 @ X26 @ X25)
% 0.69/0.91          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 0.69/0.91          | ((X31) != (k1_tmap_1 @ X27 @ X25 @ X30 @ X26 @ X29 @ X28))
% 0.69/0.91          | ((k2_partfun1 @ (k4_subset_1 @ X27 @ X30 @ X26) @ X25 @ X31 @ X30)
% 0.69/0.91              = (X29))
% 0.69/0.91          | ~ (m1_subset_1 @ X31 @ 
% 0.69/0.91               (k1_zfmisc_1 @ 
% 0.69/0.91                (k2_zfmisc_1 @ (k4_subset_1 @ X27 @ X30 @ X26) @ X25)))
% 0.69/0.91          | ~ (v1_funct_2 @ X31 @ (k4_subset_1 @ X27 @ X30 @ X26) @ X25)
% 0.69/0.91          | ~ (v1_funct_1 @ X31)
% 0.69/0.91          | ((k2_partfun1 @ X30 @ X25 @ X29 @ (k9_subset_1 @ X27 @ X30 @ X26))
% 0.69/0.91              != (k2_partfun1 @ X26 @ X25 @ X28 @ 
% 0.69/0.91                  (k9_subset_1 @ X27 @ X30 @ X26)))
% 0.69/0.91          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X25)))
% 0.69/0.91          | ~ (v1_funct_2 @ X29 @ X30 @ X25)
% 0.69/0.91          | ~ (v1_funct_1 @ X29)
% 0.69/0.91          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X27))
% 0.69/0.91          | (v1_xboole_0 @ X30)
% 0.69/0.91          | (v1_xboole_0 @ X27))),
% 0.69/0.91      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.69/0.91  thf('59', plain,
% 0.69/0.91      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.69/0.91         ((v1_xboole_0 @ X27)
% 0.69/0.91          | (v1_xboole_0 @ X30)
% 0.69/0.91          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X27))
% 0.69/0.91          | ~ (v1_funct_1 @ X29)
% 0.69/0.91          | ~ (v1_funct_2 @ X29 @ X30 @ X25)
% 0.69/0.91          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X25)))
% 0.69/0.91          | ((k2_partfun1 @ X30 @ X25 @ X29 @ (k9_subset_1 @ X27 @ X30 @ X26))
% 0.69/0.91              != (k2_partfun1 @ X26 @ X25 @ X28 @ 
% 0.69/0.91                  (k9_subset_1 @ X27 @ X30 @ X26)))
% 0.69/0.91          | ~ (v1_funct_1 @ (k1_tmap_1 @ X27 @ X25 @ X30 @ X26 @ X29 @ X28))
% 0.69/0.91          | ~ (v1_funct_2 @ (k1_tmap_1 @ X27 @ X25 @ X30 @ X26 @ X29 @ X28) @ 
% 0.69/0.91               (k4_subset_1 @ X27 @ X30 @ X26) @ X25)
% 0.69/0.91          | ~ (m1_subset_1 @ (k1_tmap_1 @ X27 @ X25 @ X30 @ X26 @ X29 @ X28) @ 
% 0.69/0.91               (k1_zfmisc_1 @ 
% 0.69/0.91                (k2_zfmisc_1 @ (k4_subset_1 @ X27 @ X30 @ X26) @ X25)))
% 0.69/0.91          | ((k2_partfun1 @ (k4_subset_1 @ X27 @ X30 @ X26) @ X25 @ 
% 0.69/0.91              (k1_tmap_1 @ X27 @ X25 @ X30 @ X26 @ X29 @ X28) @ X30) = (
% 0.69/0.91              X29))
% 0.69/0.91          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 0.69/0.91          | ~ (v1_funct_2 @ X28 @ X26 @ X25)
% 0.69/0.91          | ~ (v1_funct_1 @ X28)
% 0.69/0.91          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27))
% 0.69/0.91          | (v1_xboole_0 @ X26)
% 0.69/0.91          | (v1_xboole_0 @ X25))),
% 0.69/0.91      inference('simplify', [status(thm)], ['58'])).
% 0.69/0.91  thf('60', plain,
% 0.69/0.91      (((v1_xboole_0 @ sk_D)
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_A)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_D)
% 0.69/0.91        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.69/0.91        | ~ (v1_funct_1 @ sk_F)
% 0.69/0.91        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 0.69/0.91        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))
% 0.69/0.91        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.69/0.91            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.69/0.91            = (sk_E))
% 0.69/0.91        | ~ (v1_funct_2 @ 
% 0.69/0.91             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.69/0.91             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 0.69/0.91        | ~ (v1_funct_1 @ 
% 0.69/0.91             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.69/0.91        | ((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 0.69/0.91            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.69/0.91            != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.69/0.91                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.69/0.91        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))
% 0.69/0.91        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B_1)
% 0.69/0.91        | ~ (v1_funct_1 @ sk_E)
% 0.69/0.91        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_A))),
% 0.69/0.91      inference('sup-', [status(thm)], ['57', '59'])).
% 0.69/0.91  thf('61', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('62', plain, ((v1_funct_1 @ sk_F)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('63', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('64', plain,
% 0.69/0.91      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('65', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf(redefinition_k9_subset_1, axiom,
% 0.69/0.91    (![A:$i,B:$i,C:$i]:
% 0.69/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ A ) ) =>
% 0.69/0.91       ( ( k9_subset_1 @ A @ B @ C ) = ( k3_xboole_0 @ B @ C ) ) ))).
% 0.69/0.91  thf('66', plain,
% 0.69/0.91      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.69/0.91         (((k9_subset_1 @ X8 @ X6 @ X7) = (k3_xboole_0 @ X6 @ X7))
% 0.69/0.91          | ~ (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X8)))),
% 0.69/0.91      inference('cnf', [status(esa)], [redefinition_k9_subset_1])).
% 0.69/0.91  thf('67', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.69/0.91      inference('sup-', [status(thm)], ['65', '66'])).
% 0.69/0.91  thf('68', plain, ((r1_subset_1 @ sk_C @ sk_D)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf(redefinition_r1_subset_1, axiom,
% 0.69/0.91    (![A:$i,B:$i]:
% 0.69/0.91     ( ( ( ~( v1_xboole_0 @ A ) ) & ( ~( v1_xboole_0 @ B ) ) ) =>
% 0.69/0.91       ( ( r1_subset_1 @ A @ B ) <=> ( r1_xboole_0 @ A @ B ) ) ))).
% 0.69/0.91  thf('69', plain,
% 0.69/0.91      (![X13 : $i, X14 : $i]:
% 0.69/0.91         ((v1_xboole_0 @ X13)
% 0.69/0.91          | (v1_xboole_0 @ X14)
% 0.69/0.91          | (r1_xboole_0 @ X13 @ X14)
% 0.69/0.91          | ~ (r1_subset_1 @ X13 @ X14))),
% 0.69/0.91      inference('cnf', [status(esa)], [redefinition_r1_subset_1])).
% 0.69/0.91  thf('70', plain,
% 0.69/0.91      (((r1_xboole_0 @ sk_C @ sk_D)
% 0.69/0.91        | (v1_xboole_0 @ sk_D)
% 0.69/0.91        | (v1_xboole_0 @ sk_C))),
% 0.69/0.91      inference('sup-', [status(thm)], ['68', '69'])).
% 0.69/0.91  thf('71', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('72', plain, (((v1_xboole_0 @ sk_C) | (r1_xboole_0 @ sk_C @ sk_D))),
% 0.69/0.91      inference('clc', [status(thm)], ['70', '71'])).
% 0.69/0.91  thf('73', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('74', plain, ((r1_xboole_0 @ sk_C @ sk_D)),
% 0.69/0.91      inference('clc', [status(thm)], ['72', '73'])).
% 0.69/0.91  thf(d7_xboole_0, axiom,
% 0.69/0.91    (![A:$i,B:$i]:
% 0.69/0.91     ( ( r1_xboole_0 @ A @ B ) <=>
% 0.69/0.91       ( ( k3_xboole_0 @ A @ B ) = ( k1_xboole_0 ) ) ))).
% 0.69/0.91  thf('75', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         (((k3_xboole_0 @ X0 @ X1) = (k1_xboole_0)) | ~ (r1_xboole_0 @ X0 @ X1))),
% 0.69/0.91      inference('cnf', [status(esa)], [d7_xboole_0])).
% 0.69/0.91  thf('76', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.69/0.91      inference('sup-', [status(thm)], ['74', '75'])).
% 0.69/0.91  thf('77', plain,
% 0.69/0.91      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf(redefinition_k2_partfun1, axiom,
% 0.69/0.91    (![A:$i,B:$i,C:$i,D:$i]:
% 0.69/0.91     ( ( ( v1_funct_1 @ C ) & 
% 0.69/0.91         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.69/0.91       ( ( k2_partfun1 @ A @ B @ C @ D ) = ( k7_relat_1 @ C @ D ) ) ))).
% 0.69/0.91  thf('78', plain,
% 0.69/0.91      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.69/0.91         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.69/0.91          | ~ (v1_funct_1 @ X21)
% 0.69/0.91          | ((k2_partfun1 @ X22 @ X23 @ X21 @ X24) = (k7_relat_1 @ X21 @ X24)))),
% 0.69/0.91      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.69/0.91  thf('79', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))
% 0.69/0.91          | ~ (v1_funct_1 @ sk_E))),
% 0.69/0.91      inference('sup-', [status(thm)], ['77', '78'])).
% 0.69/0.91  thf('80', plain, ((v1_funct_1 @ sk_E)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('81', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         ((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.69/0.91      inference('demod', [status(thm)], ['79', '80'])).
% 0.69/0.91  thf('82', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.69/0.91      inference('sup-', [status(thm)], ['65', '66'])).
% 0.69/0.91  thf('83', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.69/0.91      inference('sup-', [status(thm)], ['74', '75'])).
% 0.69/0.91  thf('84', plain,
% 0.69/0.91      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('85', plain,
% 0.69/0.91      (![X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.69/0.91         (~ (m1_subset_1 @ X21 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X22 @ X23)))
% 0.69/0.91          | ~ (v1_funct_1 @ X21)
% 0.69/0.91          | ((k2_partfun1 @ X22 @ X23 @ X21 @ X24) = (k7_relat_1 @ X21 @ X24)))),
% 0.69/0.91      inference('cnf', [status(esa)], [redefinition_k2_partfun1])).
% 0.69/0.91  thf('86', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         (((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))
% 0.69/0.91          | ~ (v1_funct_1 @ sk_F))),
% 0.69/0.91      inference('sup-', [status(thm)], ['84', '85'])).
% 0.69/0.91  thf('87', plain, ((v1_funct_1 @ sk_F)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('88', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         ((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.69/0.91      inference('demod', [status(thm)], ['86', '87'])).
% 0.69/0.91  thf('89', plain,
% 0.69/0.91      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('90', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B_1)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('91', plain, ((v1_funct_1 @ sk_E)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('92', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('93', plain,
% 0.69/0.91      (((v1_xboole_0 @ sk_D)
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_A)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_D)
% 0.69/0.91        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.69/0.91            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.69/0.91            = (sk_E))
% 0.69/0.91        | ~ (v1_funct_2 @ 
% 0.69/0.91             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.69/0.91             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 0.69/0.91        | ~ (v1_funct_1 @ 
% 0.69/0.91             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.69/0.91        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.69/0.91            != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_A))),
% 0.69/0.91      inference('demod', [status(thm)],
% 0.69/0.91                ['60', '61', '62', '63', '64', '67', '76', '81', '82', '83', 
% 0.69/0.91                 '88', '89', '90', '91', '92'])).
% 0.69/0.91  thf('94', plain,
% 0.69/0.91      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.69/0.91        | ~ (v1_funct_1 @ 
% 0.69/0.91             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.69/0.91        | ~ (v1_funct_2 @ 
% 0.69/0.91             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.69/0.91             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 0.69/0.91        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.69/0.91            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.69/0.91            = (sk_E))
% 0.69/0.91        | (v1_xboole_0 @ sk_A)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_D))),
% 0.69/0.91      inference('simplify', [status(thm)], ['93'])).
% 0.69/0.91  thf('95', plain,
% 0.69/0.91      (((v1_xboole_0 @ sk_D)
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_A)
% 0.69/0.91        | (v1_xboole_0 @ sk_D)
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_A)
% 0.69/0.91        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.69/0.91            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.69/0.91            = (sk_E))
% 0.69/0.91        | ~ (v1_funct_1 @ 
% 0.69/0.91             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.69/0.91        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.69/0.91            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.69/0.91      inference('sup-', [status(thm)], ['42', '94'])).
% 0.69/0.91  thf('96', plain,
% 0.69/0.91      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.69/0.91        | ~ (v1_funct_1 @ 
% 0.69/0.91             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.69/0.91        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.69/0.91            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.69/0.91            = (sk_E))
% 0.69/0.91        | (v1_xboole_0 @ sk_A)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_D))),
% 0.69/0.91      inference('simplify', [status(thm)], ['95'])).
% 0.69/0.91  thf('97', plain,
% 0.69/0.91      ((((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 0.69/0.91          (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.69/0.91          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.69/0.91              (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.69/0.91        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.69/0.91            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.69/0.91            != (sk_E))
% 0.69/0.91        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.69/0.91            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.69/0.91            != (sk_F)))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('98', plain,
% 0.69/0.91      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.69/0.91          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.69/0.91          != (sk_E)))
% 0.69/0.91         <= (~
% 0.69/0.91             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.69/0.91                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.69/0.91                = (sk_E))))),
% 0.69/0.91      inference('split', [status(esa)], ['97'])).
% 0.69/0.91  thf('99', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         (((k7_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.69/0.91          | ~ (v1_xboole_0 @ X1)
% 0.69/0.91          | ~ (v1_relat_1 @ X0))),
% 0.69/0.91      inference('demod', [status(thm)], ['9', '10'])).
% 0.69/0.91  thf('100', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         (((k7_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.69/0.91          | ~ (v1_xboole_0 @ X1)
% 0.69/0.91          | ~ (v1_relat_1 @ X0))),
% 0.69/0.91      inference('demod', [status(thm)], ['9', '10'])).
% 0.69/0.91  thf('101', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         ((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.69/0.91      inference('demod', [status(thm)], ['86', '87'])).
% 0.69/0.91  thf('102', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.69/0.91      inference('sup-', [status(thm)], ['65', '66'])).
% 0.69/0.91  thf('103', plain,
% 0.69/0.91      ((((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 0.69/0.91          (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.69/0.91          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.69/0.91              (k9_subset_1 @ sk_A @ sk_C @ sk_D))))
% 0.69/0.91         <= (~
% 0.69/0.91             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 0.69/0.91                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.69/0.91                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.69/0.91                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.69/0.91      inference('split', [status(esa)], ['97'])).
% 0.69/0.91  thf('104', plain,
% 0.69/0.91      ((((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 0.69/0.91          (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.69/0.91          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ (k3_xboole_0 @ sk_C @ sk_D))))
% 0.69/0.91         <= (~
% 0.69/0.91             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 0.69/0.91                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.69/0.91                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.69/0.91                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.69/0.91      inference('sup-', [status(thm)], ['102', '103'])).
% 0.69/0.91  thf('105', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.69/0.91      inference('sup-', [status(thm)], ['65', '66'])).
% 0.69/0.91  thf('106', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.69/0.91      inference('sup-', [status(thm)], ['74', '75'])).
% 0.69/0.91  thf('107', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.69/0.91      inference('sup-', [status(thm)], ['74', '75'])).
% 0.69/0.91  thf('108', plain,
% 0.69/0.91      ((((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ k1_xboole_0)
% 0.69/0.91          != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ k1_xboole_0)))
% 0.69/0.91         <= (~
% 0.69/0.91             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 0.69/0.91                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.69/0.91                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.69/0.91                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.69/0.91      inference('demod', [status(thm)], ['104', '105', '106', '107'])).
% 0.69/0.91  thf('109', plain,
% 0.69/0.91      ((((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ k1_xboole_0)
% 0.69/0.91          != (k7_relat_1 @ sk_F @ k1_xboole_0)))
% 0.69/0.91         <= (~
% 0.69/0.91             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 0.69/0.91                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.69/0.91                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.69/0.91                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.69/0.91      inference('sup-', [status(thm)], ['101', '108'])).
% 0.69/0.91  thf('110', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         ((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.69/0.91      inference('demod', [status(thm)], ['79', '80'])).
% 0.69/0.91  thf('111', plain,
% 0.69/0.91      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0)))
% 0.69/0.91         <= (~
% 0.69/0.91             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 0.69/0.91                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.69/0.91                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.69/0.91                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.69/0.91      inference('demod', [status(thm)], ['109', '110'])).
% 0.69/0.91  thf('112', plain,
% 0.69/0.91      (((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.69/0.91         | ~ (v1_relat_1 @ sk_F)
% 0.69/0.91         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.69/0.91         <= (~
% 0.69/0.91             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 0.69/0.91                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.69/0.91                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.69/0.91                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.69/0.91      inference('sup-', [status(thm)], ['100', '111'])).
% 0.69/0.91  thf('113', plain,
% 0.69/0.91      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf(cc1_relset_1, axiom,
% 0.69/0.91    (![A:$i,B:$i,C:$i]:
% 0.69/0.91     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.69/0.91       ( v1_relat_1 @ C ) ))).
% 0.69/0.91  thf('114', plain,
% 0.69/0.91      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.69/0.91         ((v1_relat_1 @ X15)
% 0.69/0.91          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.69/0.91      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.69/0.91  thf('115', plain, ((v1_relat_1 @ sk_F)),
% 0.69/0.91      inference('sup-', [status(thm)], ['113', '114'])).
% 0.69/0.91  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.69/0.91  thf('116', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.91      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.91  thf('117', plain,
% 0.69/0.91      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0)))
% 0.69/0.91         <= (~
% 0.69/0.91             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 0.69/0.91                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.69/0.91                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.69/0.91                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.69/0.91      inference('demod', [status(thm)], ['112', '115', '116'])).
% 0.69/0.91  thf('118', plain,
% 0.69/0.91      (((((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.91         | ~ (v1_relat_1 @ sk_E)
% 0.69/0.91         | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.69/0.91         <= (~
% 0.69/0.91             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 0.69/0.91                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.69/0.91                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.69/0.91                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.69/0.91      inference('sup-', [status(thm)], ['99', '117'])).
% 0.69/0.91  thf('119', plain,
% 0.69/0.91      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('120', plain,
% 0.69/0.91      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.69/0.91         ((v1_relat_1 @ X15)
% 0.69/0.91          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X16 @ X17))))),
% 0.69/0.91      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.69/0.91  thf('121', plain, ((v1_relat_1 @ sk_E)),
% 0.69/0.91      inference('sup-', [status(thm)], ['119', '120'])).
% 0.69/0.91  thf('122', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.91      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.91  thf('123', plain,
% 0.69/0.91      ((((k1_xboole_0) != (k1_xboole_0)))
% 0.69/0.91         <= (~
% 0.69/0.91             (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 0.69/0.91                (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.69/0.91                = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.69/0.91                   (k9_subset_1 @ sk_A @ sk_C @ sk_D)))))),
% 0.69/0.91      inference('demod', [status(thm)], ['118', '121', '122'])).
% 0.69/0.91  thf('124', plain,
% 0.69/0.91      ((((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 0.69/0.91          (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.69/0.91          = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.69/0.91             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.69/0.91      inference('simplify', [status(thm)], ['123'])).
% 0.69/0.91  thf('125', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         (((k7_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.69/0.91          | ~ (v1_xboole_0 @ X1)
% 0.69/0.91          | ~ (v1_relat_1 @ X0))),
% 0.69/0.91      inference('demod', [status(thm)], ['9', '10'])).
% 0.69/0.91  thf('126', plain,
% 0.69/0.91      (![X0 : $i, X1 : $i]:
% 0.69/0.91         (((k7_relat_1 @ X0 @ X1) = (k1_xboole_0))
% 0.69/0.91          | ~ (v1_xboole_0 @ X1)
% 0.69/0.91          | ~ (v1_relat_1 @ X0))),
% 0.69/0.91      inference('demod', [status(thm)], ['9', '10'])).
% 0.69/0.91  thf('127', plain,
% 0.69/0.91      (((v1_funct_1 @ (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.69/0.91        | (v1_xboole_0 @ sk_A)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_D))),
% 0.69/0.91      inference('demod', [status(thm)], ['25', '26'])).
% 0.69/0.91  thf('128', plain,
% 0.69/0.91      (((v1_funct_2 @ 
% 0.69/0.91         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.69/0.91         (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_A)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_D))),
% 0.69/0.91      inference('demod', [status(thm)], ['40', '41'])).
% 0.69/0.91  thf('129', plain,
% 0.69/0.91      (((m1_subset_1 @ 
% 0.69/0.91         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.69/0.91         (k1_zfmisc_1 @ 
% 0.69/0.91          (k2_zfmisc_1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)))
% 0.69/0.91        | (v1_xboole_0 @ sk_A)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_D))),
% 0.69/0.91      inference('demod', [status(thm)], ['55', '56'])).
% 0.69/0.91  thf('130', plain,
% 0.69/0.91      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i, X31 : $i]:
% 0.69/0.91         ((v1_xboole_0 @ X25)
% 0.69/0.91          | (v1_xboole_0 @ X26)
% 0.69/0.91          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27))
% 0.69/0.91          | ~ (v1_funct_1 @ X28)
% 0.69/0.91          | ~ (v1_funct_2 @ X28 @ X26 @ X25)
% 0.69/0.91          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 0.69/0.91          | ((X31) != (k1_tmap_1 @ X27 @ X25 @ X30 @ X26 @ X29 @ X28))
% 0.69/0.91          | ((k2_partfun1 @ (k4_subset_1 @ X27 @ X30 @ X26) @ X25 @ X31 @ X26)
% 0.69/0.91              = (X28))
% 0.69/0.91          | ~ (m1_subset_1 @ X31 @ 
% 0.69/0.91               (k1_zfmisc_1 @ 
% 0.69/0.91                (k2_zfmisc_1 @ (k4_subset_1 @ X27 @ X30 @ X26) @ X25)))
% 0.69/0.91          | ~ (v1_funct_2 @ X31 @ (k4_subset_1 @ X27 @ X30 @ X26) @ X25)
% 0.69/0.91          | ~ (v1_funct_1 @ X31)
% 0.69/0.91          | ((k2_partfun1 @ X30 @ X25 @ X29 @ (k9_subset_1 @ X27 @ X30 @ X26))
% 0.69/0.91              != (k2_partfun1 @ X26 @ X25 @ X28 @ 
% 0.69/0.91                  (k9_subset_1 @ X27 @ X30 @ X26)))
% 0.69/0.91          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X25)))
% 0.69/0.91          | ~ (v1_funct_2 @ X29 @ X30 @ X25)
% 0.69/0.91          | ~ (v1_funct_1 @ X29)
% 0.69/0.91          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X27))
% 0.69/0.91          | (v1_xboole_0 @ X30)
% 0.69/0.91          | (v1_xboole_0 @ X27))),
% 0.69/0.91      inference('cnf', [status(esa)], [d1_tmap_1])).
% 0.69/0.91  thf('131', plain,
% 0.69/0.91      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.69/0.91         ((v1_xboole_0 @ X27)
% 0.69/0.91          | (v1_xboole_0 @ X30)
% 0.69/0.91          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X27))
% 0.69/0.91          | ~ (v1_funct_1 @ X29)
% 0.69/0.91          | ~ (v1_funct_2 @ X29 @ X30 @ X25)
% 0.69/0.91          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X25)))
% 0.69/0.91          | ((k2_partfun1 @ X30 @ X25 @ X29 @ (k9_subset_1 @ X27 @ X30 @ X26))
% 0.69/0.91              != (k2_partfun1 @ X26 @ X25 @ X28 @ 
% 0.69/0.91                  (k9_subset_1 @ X27 @ X30 @ X26)))
% 0.69/0.91          | ~ (v1_funct_1 @ (k1_tmap_1 @ X27 @ X25 @ X30 @ X26 @ X29 @ X28))
% 0.69/0.91          | ~ (v1_funct_2 @ (k1_tmap_1 @ X27 @ X25 @ X30 @ X26 @ X29 @ X28) @ 
% 0.69/0.91               (k4_subset_1 @ X27 @ X30 @ X26) @ X25)
% 0.69/0.91          | ~ (m1_subset_1 @ (k1_tmap_1 @ X27 @ X25 @ X30 @ X26 @ X29 @ X28) @ 
% 0.69/0.91               (k1_zfmisc_1 @ 
% 0.69/0.91                (k2_zfmisc_1 @ (k4_subset_1 @ X27 @ X30 @ X26) @ X25)))
% 0.69/0.91          | ((k2_partfun1 @ (k4_subset_1 @ X27 @ X30 @ X26) @ X25 @ 
% 0.69/0.91              (k1_tmap_1 @ X27 @ X25 @ X30 @ X26 @ X29 @ X28) @ X26) = (
% 0.69/0.91              X28))
% 0.69/0.91          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X25)))
% 0.69/0.91          | ~ (v1_funct_2 @ X28 @ X26 @ X25)
% 0.69/0.91          | ~ (v1_funct_1 @ X28)
% 0.69/0.91          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ X27))
% 0.69/0.91          | (v1_xboole_0 @ X26)
% 0.69/0.91          | (v1_xboole_0 @ X25))),
% 0.69/0.91      inference('simplify', [status(thm)], ['130'])).
% 0.69/0.91  thf('132', plain,
% 0.69/0.91      (((v1_xboole_0 @ sk_D)
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_A)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_D)
% 0.69/0.91        | ~ (m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))
% 0.69/0.91        | ~ (v1_funct_1 @ sk_F)
% 0.69/0.91        | ~ (v1_funct_2 @ sk_F @ sk_D @ sk_B_1)
% 0.69/0.91        | ~ (m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))
% 0.69/0.91        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.69/0.91            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.69/0.91            = (sk_F))
% 0.69/0.91        | ~ (v1_funct_2 @ 
% 0.69/0.91             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.69/0.91             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 0.69/0.91        | ~ (v1_funct_1 @ 
% 0.69/0.91             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.69/0.91        | ((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 0.69/0.91            (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.69/0.91            != (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.69/0.91                (k9_subset_1 @ sk_A @ sk_C @ sk_D)))
% 0.69/0.91        | ~ (m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))
% 0.69/0.91        | ~ (v1_funct_2 @ sk_E @ sk_C @ sk_B_1)
% 0.69/0.91        | ~ (v1_funct_1 @ sk_E)
% 0.69/0.91        | ~ (m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_A))),
% 0.69/0.91      inference('sup-', [status(thm)], ['129', '131'])).
% 0.69/0.91  thf('133', plain, ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ sk_A))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('134', plain, ((v1_funct_1 @ sk_F)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('135', plain, ((v1_funct_2 @ sk_F @ sk_D @ sk_B_1)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('136', plain,
% 0.69/0.91      ((m1_subset_1 @ sk_F @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_D @ sk_B_1)))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('137', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.69/0.91      inference('sup-', [status(thm)], ['65', '66'])).
% 0.69/0.91  thf('138', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.69/0.91      inference('sup-', [status(thm)], ['74', '75'])).
% 0.69/0.91  thf('139', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         ((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ X0) = (k7_relat_1 @ sk_E @ X0))),
% 0.69/0.91      inference('demod', [status(thm)], ['79', '80'])).
% 0.69/0.91  thf('140', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         ((k9_subset_1 @ sk_A @ X0 @ sk_D) = (k3_xboole_0 @ X0 @ sk_D))),
% 0.69/0.91      inference('sup-', [status(thm)], ['65', '66'])).
% 0.69/0.91  thf('141', plain, (((k3_xboole_0 @ sk_C @ sk_D) = (k1_xboole_0))),
% 0.69/0.91      inference('sup-', [status(thm)], ['74', '75'])).
% 0.69/0.91  thf('142', plain,
% 0.69/0.91      (![X0 : $i]:
% 0.69/0.91         ((k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ X0) = (k7_relat_1 @ sk_F @ X0))),
% 0.69/0.91      inference('demod', [status(thm)], ['86', '87'])).
% 0.69/0.91  thf('143', plain,
% 0.69/0.91      ((m1_subset_1 @ sk_E @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_C @ sk_B_1)))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('144', plain, ((v1_funct_2 @ sk_E @ sk_C @ sk_B_1)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('145', plain, ((v1_funct_1 @ sk_E)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('146', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ sk_A))),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('147', plain,
% 0.69/0.91      (((v1_xboole_0 @ sk_D)
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_A)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_D)
% 0.69/0.91        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.69/0.91            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.69/0.91            = (sk_F))
% 0.69/0.91        | ~ (v1_funct_2 @ 
% 0.69/0.91             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.69/0.91             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 0.69/0.91        | ~ (v1_funct_1 @ 
% 0.69/0.91             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.69/0.91        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.69/0.91            != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_A))),
% 0.69/0.91      inference('demod', [status(thm)],
% 0.69/0.91                ['132', '133', '134', '135', '136', '137', '138', '139', 
% 0.69/0.91                 '140', '141', '142', '143', '144', '145', '146'])).
% 0.69/0.91  thf('148', plain,
% 0.69/0.91      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.69/0.91        | ~ (v1_funct_1 @ 
% 0.69/0.91             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.69/0.91        | ~ (v1_funct_2 @ 
% 0.69/0.91             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ 
% 0.69/0.91             (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1)
% 0.69/0.91        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.69/0.91            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.69/0.91            = (sk_F))
% 0.69/0.91        | (v1_xboole_0 @ sk_A)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_D))),
% 0.69/0.91      inference('simplify', [status(thm)], ['147'])).
% 0.69/0.91  thf('149', plain,
% 0.69/0.91      (((v1_xboole_0 @ sk_D)
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_A)
% 0.69/0.91        | (v1_xboole_0 @ sk_D)
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_A)
% 0.69/0.91        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.69/0.91            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.69/0.91            = (sk_F))
% 0.69/0.91        | ~ (v1_funct_1 @ 
% 0.69/0.91             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.69/0.91        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.69/0.91            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.69/0.91      inference('sup-', [status(thm)], ['128', '148'])).
% 0.69/0.91  thf('150', plain,
% 0.69/0.91      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.69/0.91        | ~ (v1_funct_1 @ 
% 0.69/0.91             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.69/0.91        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.69/0.91            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.69/0.91            = (sk_F))
% 0.69/0.91        | (v1_xboole_0 @ sk_A)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_D))),
% 0.69/0.91      inference('simplify', [status(thm)], ['149'])).
% 0.69/0.91  thf('151', plain,
% 0.69/0.91      (((v1_xboole_0 @ sk_D)
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_A)
% 0.69/0.91        | (v1_xboole_0 @ sk_D)
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_A)
% 0.69/0.91        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.69/0.91            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.69/0.91            = (sk_F))
% 0.69/0.91        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.69/0.91            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.69/0.91      inference('sup-', [status(thm)], ['127', '150'])).
% 0.69/0.91  thf('152', plain,
% 0.69/0.91      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.69/0.91        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.69/0.91            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.69/0.91            = (sk_F))
% 0.69/0.91        | (v1_xboole_0 @ sk_A)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_D))),
% 0.69/0.91      inference('simplify', [status(thm)], ['151'])).
% 0.69/0.91  thf('153', plain,
% 0.69/0.91      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.69/0.91        | ~ (v1_relat_1 @ sk_F)
% 0.69/0.91        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.69/0.91        | (v1_xboole_0 @ sk_D)
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_A)
% 0.69/0.91        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.69/0.91            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.69/0.91            = (sk_F)))),
% 0.69/0.91      inference('sup-', [status(thm)], ['126', '152'])).
% 0.69/0.91  thf('154', plain, ((v1_relat_1 @ sk_F)),
% 0.69/0.91      inference('sup-', [status(thm)], ['113', '114'])).
% 0.69/0.91  thf('155', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.91      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.91  thf('156', plain,
% 0.69/0.91      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.69/0.91        | (v1_xboole_0 @ sk_D)
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_A)
% 0.69/0.91        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.69/0.91            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.69/0.91            = (sk_F)))),
% 0.69/0.91      inference('demod', [status(thm)], ['153', '154', '155'])).
% 0.69/0.91  thf('157', plain,
% 0.69/0.91      ((((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.91        | ~ (v1_relat_1 @ sk_E)
% 0.69/0.91        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.69/0.91        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.69/0.91            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.69/0.91            = (sk_F))
% 0.69/0.91        | (v1_xboole_0 @ sk_A)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_D))),
% 0.69/0.91      inference('sup-', [status(thm)], ['125', '156'])).
% 0.69/0.91  thf('158', plain, ((v1_relat_1 @ sk_E)),
% 0.69/0.91      inference('sup-', [status(thm)], ['119', '120'])).
% 0.69/0.91  thf('159', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.91      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.91  thf('160', plain,
% 0.69/0.91      ((((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.91        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.69/0.91            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.69/0.91            = (sk_F))
% 0.69/0.91        | (v1_xboole_0 @ sk_A)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_D))),
% 0.69/0.91      inference('demod', [status(thm)], ['157', '158', '159'])).
% 0.69/0.91  thf('161', plain,
% 0.69/0.91      (((v1_xboole_0 @ sk_D)
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_A)
% 0.69/0.91        | ((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.69/0.91            (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.69/0.91            = (sk_F)))),
% 0.69/0.91      inference('simplify', [status(thm)], ['160'])).
% 0.69/0.91  thf('162', plain,
% 0.69/0.91      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.69/0.91          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.69/0.91          != (sk_F)))
% 0.69/0.91         <= (~
% 0.69/0.91             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.69/0.91                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.69/0.91                = (sk_F))))),
% 0.69/0.91      inference('split', [status(esa)], ['97'])).
% 0.69/0.91  thf('163', plain,
% 0.69/0.91      (((((sk_F) != (sk_F))
% 0.69/0.91         | (v1_xboole_0 @ sk_A)
% 0.69/0.91         | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91         | (v1_xboole_0 @ sk_C)
% 0.69/0.91         | (v1_xboole_0 @ sk_D)))
% 0.69/0.91         <= (~
% 0.69/0.91             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.69/0.91                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.69/0.91                = (sk_F))))),
% 0.69/0.91      inference('sup-', [status(thm)], ['161', '162'])).
% 0.69/0.91  thf('164', plain,
% 0.69/0.91      ((((v1_xboole_0 @ sk_D)
% 0.69/0.91         | (v1_xboole_0 @ sk_C)
% 0.69/0.91         | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91         | (v1_xboole_0 @ sk_A)))
% 0.69/0.91         <= (~
% 0.69/0.91             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.69/0.91                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.69/0.91                = (sk_F))))),
% 0.69/0.91      inference('simplify', [status(thm)], ['163'])).
% 0.69/0.91  thf('165', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('166', plain,
% 0.69/0.91      ((((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_C)))
% 0.69/0.91         <= (~
% 0.69/0.91             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.69/0.91                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.69/0.91                = (sk_F))))),
% 0.69/0.91      inference('sup-', [status(thm)], ['164', '165'])).
% 0.69/0.91  thf('167', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('168', plain,
% 0.69/0.91      ((((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B_1)))
% 0.69/0.91         <= (~
% 0.69/0.91             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.69/0.91                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.69/0.91                = (sk_F))))),
% 0.69/0.91      inference('clc', [status(thm)], ['166', '167'])).
% 0.69/0.91  thf('169', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('170', plain,
% 0.69/0.91      (((v1_xboole_0 @ sk_B_1))
% 0.69/0.91         <= (~
% 0.69/0.91             (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.69/0.91                (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.69/0.91                = (sk_F))))),
% 0.69/0.91      inference('clc', [status(thm)], ['168', '169'])).
% 0.69/0.91  thf('171', plain, (~ (v1_xboole_0 @ sk_B_1)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('172', plain,
% 0.69/0.91      ((((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.69/0.91          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.69/0.91          = (sk_F)))),
% 0.69/0.91      inference('sup-', [status(thm)], ['170', '171'])).
% 0.69/0.91  thf('173', plain,
% 0.69/0.91      (~
% 0.69/0.91       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.69/0.91          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.69/0.91          = (sk_E))) | 
% 0.69/0.91       ~
% 0.69/0.91       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.69/0.91          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_D)
% 0.69/0.91          = (sk_F))) | 
% 0.69/0.91       ~
% 0.69/0.91       (((k2_partfun1 @ sk_C @ sk_B_1 @ sk_E @ 
% 0.69/0.91          (k9_subset_1 @ sk_A @ sk_C @ sk_D))
% 0.69/0.91          = (k2_partfun1 @ sk_D @ sk_B_1 @ sk_F @ 
% 0.69/0.91             (k9_subset_1 @ sk_A @ sk_C @ sk_D))))),
% 0.69/0.91      inference('split', [status(esa)], ['97'])).
% 0.69/0.91  thf('174', plain,
% 0.69/0.91      (~
% 0.69/0.91       (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.69/0.91          (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.69/0.91          = (sk_E)))),
% 0.69/0.91      inference('sat_resolution*', [status(thm)], ['124', '172', '173'])).
% 0.69/0.91  thf('175', plain,
% 0.69/0.91      (((k2_partfun1 @ (k4_subset_1 @ sk_A @ sk_C @ sk_D) @ sk_B_1 @ 
% 0.69/0.91         (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F) @ sk_C)
% 0.69/0.91         != (sk_E))),
% 0.69/0.91      inference('simpl_trail', [status(thm)], ['98', '174'])).
% 0.69/0.91  thf('176', plain,
% 0.69/0.91      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.69/0.91        | ~ (v1_funct_1 @ 
% 0.69/0.91             (k1_tmap_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D @ sk_E @ sk_F))
% 0.69/0.91        | (v1_xboole_0 @ sk_A)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_D))),
% 0.69/0.91      inference('simplify_reflect-', [status(thm)], ['96', '175'])).
% 0.69/0.91  thf('177', plain,
% 0.69/0.91      (((v1_xboole_0 @ sk_D)
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_A)
% 0.69/0.91        | (v1_xboole_0 @ sk_D)
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_A)
% 0.69/0.91        | ((k7_relat_1 @ sk_E @ k1_xboole_0)
% 0.69/0.91            != (k7_relat_1 @ sk_F @ k1_xboole_0)))),
% 0.69/0.91      inference('sup-', [status(thm)], ['27', '176'])).
% 0.69/0.91  thf('178', plain,
% 0.69/0.91      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k7_relat_1 @ sk_F @ k1_xboole_0))
% 0.69/0.91        | (v1_xboole_0 @ sk_A)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_D))),
% 0.69/0.91      inference('simplify', [status(thm)], ['177'])).
% 0.69/0.91  thf('179', plain,
% 0.69/0.91      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.69/0.91        | ~ (v1_relat_1 @ sk_F)
% 0.69/0.91        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.69/0.91        | (v1_xboole_0 @ sk_D)
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_A))),
% 0.69/0.91      inference('sup-', [status(thm)], ['12', '178'])).
% 0.69/0.91  thf('180', plain, ((v1_relat_1 @ sk_F)),
% 0.69/0.91      inference('sup-', [status(thm)], ['113', '114'])).
% 0.69/0.91  thf('181', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.91      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.91  thf('182', plain,
% 0.69/0.91      ((((k7_relat_1 @ sk_E @ k1_xboole_0) != (k1_xboole_0))
% 0.69/0.91        | (v1_xboole_0 @ sk_D)
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_A))),
% 0.69/0.91      inference('demod', [status(thm)], ['179', '180', '181'])).
% 0.69/0.91  thf('183', plain,
% 0.69/0.91      ((((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.91        | ~ (v1_relat_1 @ sk_E)
% 0.69/0.91        | ~ (v1_xboole_0 @ k1_xboole_0)
% 0.69/0.91        | (v1_xboole_0 @ sk_A)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_D))),
% 0.69/0.91      inference('sup-', [status(thm)], ['11', '182'])).
% 0.69/0.91  thf('184', plain, ((v1_relat_1 @ sk_E)),
% 0.69/0.91      inference('sup-', [status(thm)], ['119', '120'])).
% 0.69/0.91  thf('185', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.69/0.91      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.69/0.91  thf('186', plain,
% 0.69/0.91      ((((k1_xboole_0) != (k1_xboole_0))
% 0.69/0.91        | (v1_xboole_0 @ sk_A)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_D))),
% 0.69/0.91      inference('demod', [status(thm)], ['183', '184', '185'])).
% 0.69/0.91  thf('187', plain,
% 0.69/0.91      (((v1_xboole_0 @ sk_D)
% 0.69/0.91        | (v1_xboole_0 @ sk_C)
% 0.69/0.91        | (v1_xboole_0 @ sk_B_1)
% 0.69/0.91        | (v1_xboole_0 @ sk_A))),
% 0.69/0.91      inference('simplify', [status(thm)], ['186'])).
% 0.69/0.91  thf('188', plain, (~ (v1_xboole_0 @ sk_D)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('189', plain,
% 0.69/0.91      (((v1_xboole_0 @ sk_A) | (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_C))),
% 0.69/0.91      inference('sup-', [status(thm)], ['187', '188'])).
% 0.69/0.91  thf('190', plain, (~ (v1_xboole_0 @ sk_A)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('191', plain, (((v1_xboole_0 @ sk_C) | (v1_xboole_0 @ sk_B_1))),
% 0.69/0.91      inference('clc', [status(thm)], ['189', '190'])).
% 0.69/0.91  thf('192', plain, (~ (v1_xboole_0 @ sk_C)),
% 0.69/0.91      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.69/0.91  thf('193', plain, ((v1_xboole_0 @ sk_B_1)),
% 0.69/0.91      inference('clc', [status(thm)], ['191', '192'])).
% 0.69/0.91  thf('194', plain, ($false), inference('demod', [status(thm)], ['0', '193'])).
% 0.69/0.91  
% 0.69/0.91  % SZS output end Refutation
% 0.69/0.91  
% 0.69/0.91  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
