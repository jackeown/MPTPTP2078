%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1063+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.Tn0cls7KEp

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:59 EST 2020

% Result     : Theorem 0.74s
% Output     : Refutation 0.74s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 345 expanded)
%              Number of leaves         :   27 ( 110 expanded)
%              Depth                    :   26
%              Number of atoms          : 1716 (8498 expanded)
%              Number of equality atoms :    9 (  17 expanded)
%              Maximal formula depth    :   25 (  10 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_G_1_type,type,(
    sk_G_1: $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k7_funct_2_type,type,(
    k7_funct_2: $i > $i > $i > $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(t180_funct_2,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
                     => ( ( r1_tarski @ D @ E )
                       => ( r1_tarski @ ( k7_funct_2 @ A @ B @ C @ D ) @ ( k7_funct_2 @ A @ B @ C @ E ) ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( ( v1_funct_1 @ C )
                  & ( v1_funct_2 @ C @ A @ B )
                  & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
               => ! [D: $i] :
                    ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
                   => ! [E: $i] :
                        ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
                       => ( ( r1_tarski @ D @ E )
                         => ( r1_tarski @ ( k7_funct_2 @ A @ B @ C @ D ) @ ( k7_funct_2 @ A @ B @ C @ E ) ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t180_funct_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ X18 )
      | ( r2_hidden @ ( sk_C @ X18 @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ~ ( v1_xboole_0 @ B )
        & ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) ) )
     => ( m1_subset_1 @ ( k7_funct_2 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ B ) ) ) ) )).

thf('4',plain,(
    ! [X19: $i,X20: $i,X21: $i,X22: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( v1_funct_2 @ X19 @ X20 @ X21 )
      | ~ ( v1_funct_1 @ X19 )
      | ( v1_xboole_0 @ X21 )
      | ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X20 ) ) )
      | ( m1_subset_1 @ ( k7_funct_2 @ X20 @ X21 @ X19 @ X22 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_funct_2])).

thf('5',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('9',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['2','8'])).

thf('10',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,
    ( ( m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['9','10'])).

thf('12',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('14',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( m1_subset_1 @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['1','15'])).

thf('17',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ X18 )
      | ( r2_hidden @ ( sk_C @ X18 @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('18',plain,(
    m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['11','12'])).

thf(d11_funct_2,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
                & ( v1_funct_2 @ C @ A @ B )
                & ( v1_funct_1 @ C ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ B ) ) )
                     => ( ( E
                          = ( k7_funct_2 @ A @ B @ C @ D ) )
                      <=> ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ B ) )
                           => ( ( r2_hidden @ F @ E )
                            <=> ? [G: $i] :
                                  ( ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ A ) )
                                  & ( r2_hidden @ G @ D )
                                  & ( F
                                    = ( k7_relset_1 @ A @ B @ C @ G ) ) ) ) ) ) ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [G: $i,F: $i,D: $i,C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ G @ F @ D @ C @ B @ A )
    <=> ( ( F
          = ( k7_relset_1 @ A @ B @ C @ G ) )
        & ( r2_hidden @ G @ D )
        & ( m1_subset_1 @ G @ ( k1_zfmisc_1 @ A ) ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( ( v1_funct_1 @ C )
                & ( v1_funct_2 @ C @ A @ B )
                & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
             => ! [D: $i] :
                  ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ A ) ) )
                 => ! [E: $i] :
                      ( ( m1_subset_1 @ E @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ B ) ) )
                     => ( ( E
                          = ( k7_funct_2 @ A @ B @ C @ D ) )
                      <=> ! [F: $i] :
                            ( ( m1_subset_1 @ F @ ( k1_zfmisc_1 @ B ) )
                           => ( ( r2_hidden @ F @ E )
                            <=> ? [G: $i] :
                                  ( zip_tseitin_0 @ G @ F @ D @ C @ B @ A ) ) ) ) ) ) ) ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X13: $i] :
      ( ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) )
      | ( X10
       != ( k7_funct_2 @ X9 @ X7 @ X11 @ X8 ) )
      | ( zip_tseitin_0 @ ( sk_G_1 @ X13 @ X8 @ X11 @ X7 @ X9 ) @ X13 @ X8 @ X11 @ X7 @ X9 )
      | ~ ( r2_hidden @ X13 @ X10 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X7 ) ) )
      | ~ ( v1_funct_2 @ X11 @ X9 @ X7 )
      | ~ ( v1_funct_1 @ X11 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('20',plain,(
    ! [X7: $i,X8: $i,X9: $i,X11: $i,X13: $i] :
      ( ( v1_xboole_0 @ X9 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_funct_2 @ X11 @ X9 @ X7 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X7 ) ) )
      | ~ ( m1_subset_1 @ ( k7_funct_2 @ X9 @ X7 @ X11 @ X8 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( r2_hidden @ X13 @ ( k7_funct_2 @ X9 @ X7 @ X11 @ X8 ) )
      | ( zip_tseitin_0 @ ( sk_G_1 @ X13 @ X8 @ X11 @ X7 @ X9 ) @ X13 @ X8 @ X11 @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(simplify,[status(thm)],['19'])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ~ ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( zip_tseitin_0 @ ( sk_G_1 @ X0 @ sk_D @ sk_C_1 @ sk_B @ sk_A ) @ X0 @ sk_D @ sk_C_1 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['18','20'])).

thf('22',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( zip_tseitin_0 @ ( sk_G_1 @ X0 @ sk_D @ sk_C_1 @ sk_B @ sk_A ) @ X0 @ sk_D @ sk_C_1 @ sk_B @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['21','22','23','24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ X0 )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( zip_tseitin_0 @ ( sk_G_1 @ ( sk_C @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_D @ sk_C_1 @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['17','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( zip_tseitin_0 @ ( sk_G_1 @ ( sk_C @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_D @ sk_C_1 @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ( r1_tarski @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['16','27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_G_1 @ ( sk_C @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_D @ sk_C_1 @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_tarski @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( X4
        = ( k7_relset_1 @ X0 @ X1 @ X2 @ X3 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X4 @ X5 @ X2 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( ( sk_C @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) )
        = ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( sk_G_1 @ ( sk_C @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_D @ sk_C_1 @ sk_B @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_G_1 @ ( sk_C @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_D @ sk_C_1 @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_tarski @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( r2_hidden @ X3 @ X5 )
      | ~ ( zip_tseitin_0 @ X3 @ X4 @ X5 @ X2 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ ( sk_G_1 @ ( sk_C @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_D ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    r1_tarski @ sk_D @ sk_E ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('36',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ~ ( r2_hidden @ X15 @ X16 )
      | ( r2_hidden @ X15 @ X17 )
      | ~ ( r1_tarski @ X16 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_E )
      | ~ ( r2_hidden @ X0 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_tarski @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ X0 )
      | ( r2_hidden @ ( sk_G_1 @ ( sk_C @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_D @ sk_C_1 @ sk_B @ sk_A ) @ sk_E ) ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_G_1 @ ( sk_C @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( sk_C @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_D @ sk_C_1 @ sk_B @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_tarski @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['28'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i,X5: $i] :
      ( ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X0 ) )
      | ~ ( zip_tseitin_0 @ X3 @ X4 @ X5 @ X2 @ X1 @ X0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( m1_subset_1 @ ( sk_G_1 @ ( sk_C @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( k1_zfmisc_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,(
    ! [X1: $i,X2: $i,X3: $i,X4: $i,X5: $i,X6: $i] :
      ( ( zip_tseitin_0 @ X3 @ X4 @ X5 @ X2 @ X1 @ X6 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X6 ) )
      | ~ ( r2_hidden @ X3 @ X5 )
      | ( X4
       != ( k7_relset_1 @ X6 @ X1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('43',plain,(
    ! [X1: $i,X2: $i,X3: $i,X5: $i,X6: $i] :
      ( ~ ( r2_hidden @ X3 @ X5 )
      | ~ ( m1_subset_1 @ X3 @ ( k1_zfmisc_1 @ X6 ) )
      | ( zip_tseitin_0 @ X3 @ ( k7_relset_1 @ X6 @ X1 @ X2 @ X3 ) @ X5 @ X2 @ X1 @ X6 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_tarski @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ X0 )
      | ( zip_tseitin_0 @ ( sk_G_1 @ ( sk_C @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( k7_relset_1 @ sk_A @ X1 @ X2 @ ( sk_G_1 @ ( sk_C @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_D @ sk_C_1 @ sk_B @ sk_A ) ) @ X3 @ X2 @ X1 @ sk_A )
      | ~ ( r2_hidden @ ( sk_G_1 @ ( sk_C @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_D @ sk_C_1 @ sk_B @ sk_A ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['41','43'])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r1_tarski @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( zip_tseitin_0 @ ( sk_G_1 @ ( sk_C @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( k7_relset_1 @ sk_A @ X1 @ X2 @ ( sk_G_1 @ ( sk_C @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_D @ sk_C_1 @ sk_B @ sk_A ) ) @ sk_E @ X2 @ X1 @ sk_A )
      | ( r1_tarski @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['38','44'])).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( zip_tseitin_0 @ ( sk_G_1 @ ( sk_C @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_D @ sk_C_1 @ sk_B @ sk_A ) @ ( k7_relset_1 @ sk_A @ X1 @ X2 @ ( sk_G_1 @ ( sk_C @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_D @ sk_C_1 @ sk_B @ sk_A ) ) @ sk_E @ X2 @ X1 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_tarski @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['5','6','7'])).

thf('49',plain,
    ( ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A )
    | ( m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,
    ( ( m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(clc,[status(thm)],['49','50'])).

thf('52',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    m1_subset_1 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference(clc,[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X7 )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) )
      | ( X10
       != ( k7_funct_2 @ X9 @ X7 @ X11 @ X8 ) )
      | ( r2_hidden @ X13 @ X10 )
      | ~ ( zip_tseitin_0 @ X14 @ X13 @ X8 @ X11 @ X7 @ X9 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X7 ) ) )
      | ~ ( v1_funct_2 @ X11 @ X9 @ X7 )
      | ~ ( v1_funct_1 @ X11 )
      | ( v1_xboole_0 @ X9 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('55',plain,(
    ! [X7: $i,X8: $i,X9: $i,X11: $i,X13: $i,X14: $i] :
      ( ( v1_xboole_0 @ X9 )
      | ~ ( v1_funct_1 @ X11 )
      | ~ ( v1_funct_2 @ X11 @ X9 @ X7 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X7 ) ) )
      | ~ ( m1_subset_1 @ ( k7_funct_2 @ X9 @ X7 @ X11 @ X8 ) @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X7 ) ) )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X7 ) )
      | ~ ( zip_tseitin_0 @ X14 @ X13 @ X8 @ X11 @ X7 @ X9 )
      | ( r2_hidden @ X13 @ ( k7_funct_2 @ X9 @ X7 @ X11 @ X8 ) )
      | ~ ( m1_subset_1 @ X8 @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ X9 ) ) )
      | ( v1_xboole_0 @ X7 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ~ ( m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) )
      | ( r2_hidden @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_E @ sk_C_1 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) )
      | ~ ( m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) )
      | ~ ( v1_funct_2 @ sk_C_1 @ sk_A @ sk_B )
      | ~ ( v1_funct_1 @ sk_C_1 )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,(
    m1_subset_1 @ sk_E @ ( k1_zfmisc_1 @ ( k1_zfmisc_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('58',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    v1_funct_2 @ sk_C_1 @ sk_A @ sk_B ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    v1_funct_1 @ sk_C_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ sk_B )
      | ( r2_hidden @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) )
      | ~ ( zip_tseitin_0 @ X1 @ X0 @ sk_E @ sk_C_1 @ sk_B @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ sk_B ) )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference(demod,[status(thm)],['56','57','58','59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ~ ( m1_subset_1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( sk_G_1 @ ( sk_C @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_D @ sk_C_1 @ sk_B @ sk_A ) ) @ ( k1_zfmisc_1 @ sk_B ) )
      | ( r2_hidden @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( sk_G_1 @ ( sk_C @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_D @ sk_C_1 @ sk_B @ sk_A ) ) @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['46','61'])).

thf('63',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k7_relset_1 @ A @ B @ C @ D ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('64',plain,(
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X24 @ X25 ) ) )
      | ( m1_subset_1 @ ( k7_relset_1 @ X24 @ X25 @ X23 @ X26 ) @ ( k1_zfmisc_1 @ X25 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relset_1])).

thf('65',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ X0 ) @ ( k1_zfmisc_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( sk_G_1 @ ( sk_C @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_D @ sk_C_1 @ sk_B @ sk_A ) ) @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) )
      | ( v1_xboole_0 @ sk_B ) ) ),
    inference(demod,[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( k7_relset_1 @ sk_A @ sk_B @ sk_C_1 @ ( sk_G_1 @ ( sk_C @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ sk_D @ sk_C_1 @ sk_B @ sk_A ) ) @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_tarski @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ X0 ) ) ),
    inference(simplify,[status(thm)],['66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ ( sk_C @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) )
      | ( v1_xboole_0 @ sk_A )
      | ( v1_xboole_0 @ sk_B )
      | ( r1_tarski @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ X0 )
      | ( r1_tarski @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup+',[status(thm)],['31','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ X0 )
      | ( v1_xboole_0 @ sk_B )
      | ( v1_xboole_0 @ sk_A )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) ) @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) ) ) ),
    inference(simplify,[status(thm)],['68'])).

thf('70',plain,(
    ! [X16: $i,X18: $i] :
      ( ( r1_tarski @ X16 @ X18 )
      | ~ ( r2_hidden @ ( sk_C @ X18 @ X16 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('71',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B )
    | ( r1_tarski @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) )
    | ( r1_tarski @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( r1_tarski @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) )
    | ( v1_xboole_0 @ sk_B )
    | ( v1_xboole_0 @ sk_A ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    ~ ( r1_tarski @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_D ) @ ( k7_funct_2 @ sk_A @ sk_B @ sk_C_1 @ sk_E ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( v1_xboole_0 @ sk_A )
    | ( v1_xboole_0 @ sk_B ) ),
    inference(clc,[status(thm)],['72','73'])).

thf('75',plain,(
    ~ ( v1_xboole_0 @ sk_A ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    v1_xboole_0 @ sk_B ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,(
    $false ),
    inference(demod,[status(thm)],['0','76'])).


%------------------------------------------------------------------------------
