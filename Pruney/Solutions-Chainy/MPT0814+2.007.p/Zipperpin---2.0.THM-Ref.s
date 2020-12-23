%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RT2GxEOVDK

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:48:39 EST 2020

% Result     : Theorem 0.67s
% Output     : Refutation 0.72s
% Verified   : 
% Statistics : Number of formulae       :  121 (3096 expanded)
%              Number of leaves         :   30 ( 920 expanded)
%              Depth                    :   25
%              Number of atoms          :  821 (34041 expanded)
%              Number of equality atoms :   55 (1540 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r2_xboole_0_type,type,(
    r2_xboole_0: $i > $i > $o )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_E_2_type,type,(
    sk_E_2: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_F_2_type,type,(
    sk_F_2: $i > $i > $i > $i )).

thf(sk_F_type,type,(
    sk_F: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(t6_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
     => ~ ( ( r2_hidden @ A @ D )
          & ! [E: $i,F: $i] :
              ~ ( ( A
                  = ( k4_tarski @ E @ F ) )
                & ( r2_hidden @ E @ B )
                & ( r2_hidden @ F @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) )
       => ~ ( ( r2_hidden @ A @ D )
            & ! [E: $i,F: $i] :
                ~ ( ( A
                    = ( k4_tarski @ E @ F ) )
                  & ( r2_hidden @ E @ B )
                  & ( r2_hidden @ F @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t6_relset_1])).

thf('0',plain,(
    r2_hidden @ sk_A @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('2',plain,(
    ! [X30: $i,X31: $i] :
      ( ( r1_tarski @ X30 @ X31 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ X31 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('3',plain,(
    r1_tarski @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t65_subset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( r2_hidden @ D @ C )
        & ( r1_tarski @ C @ ( k2_zfmisc_1 @ A @ B ) )
        & ! [E: $i] :
            ( ( m1_subset_1 @ E @ A )
           => ! [F: $i] :
                ( ( m1_subset_1 @ F @ B )
               => ( D
                 != ( k4_tarski @ E @ F ) ) ) ) ) )).

thf('4',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ X24 @ ( k2_zfmisc_1 @ X25 @ X26 ) )
      | ( m1_subset_1 @ ( sk_F_2 @ X27 @ X26 @ X25 ) @ X26 )
      | ~ ( r2_hidden @ X27 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t65_subset_1])).

thf('5',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_D_1 )
      | ( m1_subset_1 @ ( sk_F_2 @ X0 @ sk_C_1 @ sk_B_1 ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ ( sk_F_2 @ sk_A @ sk_C_1 @ sk_B_1 ) @ sk_C_1 ),
    inference('sup-',[status(thm)],['0','5'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('7',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r2_hidden @ X28 @ X29 )
      | ( v1_xboole_0 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('8',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( r2_hidden @ ( sk_F_2 @ sk_A @ sk_C_1 @ sk_B_1 ) @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf('9',plain,(
    r2_hidden @ sk_A @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,(
    r1_tarski @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('11',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ X24 @ ( k2_zfmisc_1 @ X25 @ X26 ) )
      | ( X27
        = ( k4_tarski @ ( sk_E_2 @ X27 @ X26 @ X25 ) @ ( sk_F_2 @ X27 @ X26 @ X25 ) ) )
      | ~ ( r2_hidden @ X27 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t65_subset_1])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_D_1 )
      | ( X0
        = ( k4_tarski @ ( sk_E_2 @ X0 @ sk_C_1 @ sk_B_1 ) @ ( sk_F_2 @ X0 @ sk_C_1 @ sk_B_1 ) ) ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,
    ( sk_A
    = ( k4_tarski @ ( sk_E_2 @ sk_A @ sk_C_1 @ sk_B_1 ) @ ( sk_F_2 @ sk_A @ sk_C_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    r2_hidden @ sk_A @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    r1_tarski @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('16',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ~ ( r1_tarski @ X24 @ ( k2_zfmisc_1 @ X25 @ X26 ) )
      | ( m1_subset_1 @ ( sk_E_2 @ X27 @ X26 @ X25 ) @ X25 )
      | ~ ( r2_hidden @ X27 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t65_subset_1])).

thf('17',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ sk_D_1 )
      | ( m1_subset_1 @ ( sk_E_2 @ X0 @ sk_C_1 @ sk_B_1 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    m1_subset_1 @ ( sk_E_2 @ sk_A @ sk_C_1 @ sk_B_1 ) @ sk_B_1 ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X28: $i,X29: $i] :
      ( ( r2_hidden @ X28 @ X29 )
      | ( v1_xboole_0 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( r2_hidden @ ( sk_E_2 @ sk_A @ sk_C_1 @ sk_B_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X33: $i,X34: $i] :
      ( ~ ( r2_hidden @ X33 @ sk_B_1 )
      | ~ ( r2_hidden @ X34 @ sk_C_1 )
      | ( sk_A
       != ( k4_tarski @ X33 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ( sk_A
       != ( k4_tarski @ ( sk_E_2 @ sk_A @ sk_C_1 @ sk_B_1 ) @ X0 ) )
      | ~ ( r2_hidden @ X0 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,
    ( ( sk_A != sk_A )
    | ~ ( r2_hidden @ ( sk_F_2 @ sk_A @ sk_C_1 @ sk_B_1 ) @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['13','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ~ ( r2_hidden @ ( sk_F_2 @ sk_A @ sk_C_1 @ sk_B_1 ) @ sk_C_1 ) ),
    inference(simplify,[status(thm)],['23'])).

thf('25',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['8','24'])).

thf('26',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['8','24'])).

thf('27',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['8','24'])).

thf('28',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['8','24'])).

thf(d2_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( ( r2_hidden @ E @ A )
              & ( r2_hidden @ F @ B )
              & ( D
                = ( k4_tarski @ E @ F ) ) ) ) ) )).

thf(zf_stmt_1,type,(
    zip_tseitin_0: $i > $i > $i > $i > $i > $o )).

thf(zf_stmt_2,axiom,(
    ! [F: $i,E: $i,D: $i,B: $i,A: $i] :
      ( ( zip_tseitin_0 @ F @ E @ D @ B @ A )
    <=> ( ( D
          = ( k4_tarski @ E @ F ) )
        & ( r2_hidden @ F @ B )
        & ( r2_hidden @ E @ A ) ) ) )).

thf(zf_stmt_3,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_zfmisc_1 @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ? [E: $i,F: $i] :
              ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) )).

thf('29',plain,(
    ! [X17: $i,X18: $i,X21: $i] :
      ( ( X21
        = ( k2_zfmisc_1 @ X18 @ X17 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X21 @ X17 @ X18 ) @ ( sk_E @ X21 @ X17 @ X18 ) @ ( sk_D @ X21 @ X17 @ X18 ) @ X17 @ X18 )
      | ( r2_hidden @ ( sk_D @ X21 @ X17 @ X18 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('30',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X9 @ X11 )
      | ~ ( zip_tseitin_0 @ X9 @ X8 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('31',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_F @ X2 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_F @ X0 @ X2 @ X1 ) @ X2 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('35',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    r1_tarski @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d8_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_xboole_0 @ A @ B )
    <=> ( ( r1_tarski @ A @ B )
        & ( A != B ) ) ) )).

thf('37',plain,(
    ! [X3: $i,X5: $i] :
      ( ( r2_xboole_0 @ X3 @ X5 )
      | ( X3 = X5 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d8_xboole_0])).

thf('38',plain,
    ( ( sk_D_1
      = ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) )
    | ( r2_xboole_0 @ sk_D_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t6_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_xboole_0 @ A @ B )
        & ! [C: $i] :
            ~ ( ( r2_hidden @ C @ B )
              & ~ ( r2_hidden @ C @ A ) ) ) )).

thf('39',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( r2_xboole_0 @ X6 @ X7 )
      | ( r2_hidden @ ( sk_C @ X7 @ X6 ) @ X7 ) ) ),
    inference(cnf,[status(esa)],[t6_xboole_0])).

thf('40',plain,
    ( ( sk_D_1
      = ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) )
    | ( r2_hidden @ ( sk_C @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) @ sk_D_1 ) @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('42',plain,
    ( ( sk_D_1
      = ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_D_1
        = ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['35','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( sk_D_1
        = ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) )
      | ~ ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,
    ( ( sk_D_1
      = ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) )
    | ~ ( v1_xboole_0 @ sk_C_1 ) ),
    inference(condensation,[status(thm)],['44'])).

thf('46',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_D_1
      = ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['28','45'])).

thf('47',plain,(
    ! [X17: $i,X18: $i,X21: $i] :
      ( ( X21
        = ( k2_zfmisc_1 @ X18 @ X17 ) )
      | ( zip_tseitin_0 @ ( sk_F @ X21 @ X17 @ X18 ) @ ( sk_E @ X21 @ X17 @ X18 ) @ ( sk_D @ X21 @ X17 @ X18 ) @ X17 @ X18 )
      | ( r2_hidden @ ( sk_D @ X21 @ X17 @ X18 ) @ X21 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('48',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ( r2_hidden @ X8 @ X12 )
      | ~ ( zip_tseitin_0 @ X9 @ X8 @ X10 @ X11 @ X12 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_2])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X2 @ X1 @ X0 ) @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( sk_E @ X2 @ X1 @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('51',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_E @ X0 @ X2 @ X1 ) @ X1 )
      | ( X0
        = ( k2_zfmisc_1 @ X1 @ X2 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('53',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_D_1
      = ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( sk_D_1
        = ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i] :
      ( ( sk_D_1
        = ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) )
      | ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['55'])).

thf('57',plain,
    ( ( sk_D_1
      = ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) )
    | ~ ( v1_xboole_0 @ sk_B_1 ) ),
    inference(condensation,[status(thm)],['56'])).

thf('58',plain,
    ( sk_D_1
    = ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['46','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_D_1 )
      | ~ ( v1_xboole_0 @ sk_C_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X0 = sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['27','60'])).

thf('62',plain,
    ( sk_D_1
    = ( k2_zfmisc_1 @ sk_B_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['46','57'])).

thf('63',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_xboole_0 @ X2 )
      | ( X2
        = ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_D_1 )
      | ~ ( v1_xboole_0 @ sk_B_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup+',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_D_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['61','64'])).

thf('66',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C_1 = sk_D_1 ) ),
    inference('sup-',[status(thm)],['26','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_D_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['61','64'])).

thf('68',plain,
    ( ( sk_C_1 = sk_D_1 )
    | ( sk_B_1 = sk_D_1 ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['8','24'])).

thf('70',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( sk_B_1 = sk_D_1 )
    | ( v1_xboole_0 @ sk_B_1 ) ),
    inference('sup+',[status(thm)],['68','69'])).

thf('71',plain,(
    r2_hidden @ sk_A @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('72',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('73',plain,(
    ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_B_1 = sk_D_1 ) ),
    inference(clc,[status(thm)],['70','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_D_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['61','64'])).

thf('76',plain,(
    sk_B_1 = sk_D_1 ),
    inference(clc,[status(thm)],['74','75'])).

thf('77',plain,
    ( ( v1_xboole_0 @ sk_C_1 )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['25','76'])).

thf('78',plain,
    ( ( v1_xboole_0 @ sk_B_1 )
    | ( sk_C_1 = sk_D_1 ) ),
    inference('sup-',[status(thm)],['26','65'])).

thf('79',plain,(
    sk_B_1 = sk_D_1 ),
    inference(clc,[status(thm)],['74','75'])).

thf('80',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( sk_C_1 = sk_D_1 ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( X0 = sk_D_1 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['61','64'])).

thf('82',plain,(
    ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('83',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('85',plain,(
    sk_C_1 = sk_D_1 ),
    inference(clc,[status(thm)],['80','84'])).

thf('86',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( v1_xboole_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['77','85'])).

thf('87',plain,(
    v1_xboole_0 @ sk_D_1 ),
    inference(simplify,[status(thm)],['86'])).

thf('88',plain,(
    ! [X0: $i] :
      ~ ( v1_xboole_0 @ X0 ) ),
    inference(simplify,[status(thm)],['83'])).

thf('89',plain,(
    $false ),
    inference('sup-',[status(thm)],['87','88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.RT2GxEOVDK
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 18:44:42 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.34  % Running portfolio for 600 s
% 0.19/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.34  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.35  % Running in FO mode
% 0.67/0.89  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.67/0.89  % Solved by: fo/fo7.sh
% 0.67/0.89  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.67/0.89  % done 174 iterations in 0.395s
% 0.67/0.89  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.67/0.89  % SZS output start Refutation
% 0.67/0.89  thf(sk_E_type, type, sk_E: $i > $i > $i > $i).
% 0.67/0.89  thf(sk_A_type, type, sk_A: $i).
% 0.67/0.89  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.67/0.89  thf(r2_xboole_0_type, type, r2_xboole_0: $i > $i > $o).
% 0.67/0.89  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $i > $i > $i > $o).
% 0.67/0.89  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.67/0.89  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.67/0.89  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.67/0.89  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.67/0.89  thf(sk_E_2_type, type, sk_E_2: $i > $i > $i > $i).
% 0.67/0.89  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.67/0.89  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.67/0.89  thf(sk_F_2_type, type, sk_F_2: $i > $i > $i > $i).
% 0.67/0.89  thf(sk_F_type, type, sk_F: $i > $i > $i > $i).
% 0.67/0.89  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.67/0.89  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.67/0.89  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.67/0.89  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.67/0.89  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.67/0.89  thf(t6_relset_1, conjecture,
% 0.67/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.89     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.67/0.89       ( ~( ( r2_hidden @ A @ D ) & 
% 0.67/0.89            ( ![E:$i,F:$i]:
% 0.67/0.89              ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ E @ B ) & 
% 0.67/0.89                   ( r2_hidden @ F @ C ) ) ) ) ) ) ))).
% 0.67/0.89  thf(zf_stmt_0, negated_conjecture,
% 0.67/0.89    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.89        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) =>
% 0.67/0.89          ( ~( ( r2_hidden @ A @ D ) & 
% 0.67/0.89               ( ![E:$i,F:$i]:
% 0.67/0.89                 ( ~( ( ( A ) = ( k4_tarski @ E @ F ) ) & 
% 0.67/0.89                      ( r2_hidden @ E @ B ) & ( r2_hidden @ F @ C ) ) ) ) ) ) ) )),
% 0.67/0.89    inference('cnf.neg', [status(esa)], [t6_relset_1])).
% 0.67/0.89  thf('0', plain, ((r2_hidden @ sk_A @ sk_D_1)),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.89  thf('1', plain,
% 0.67/0.89      ((m1_subset_1 @ sk_D_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.89  thf(t3_subset, axiom,
% 0.67/0.89    (![A:$i,B:$i]:
% 0.67/0.89     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.67/0.89  thf('2', plain,
% 0.67/0.89      (![X30 : $i, X31 : $i]:
% 0.67/0.89         ((r1_tarski @ X30 @ X31) | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ X31)))),
% 0.67/0.89      inference('cnf', [status(esa)], [t3_subset])).
% 0.67/0.89  thf('3', plain, ((r1_tarski @ sk_D_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1))),
% 0.67/0.89      inference('sup-', [status(thm)], ['1', '2'])).
% 0.67/0.89  thf(t65_subset_1, axiom,
% 0.67/0.89    (![A:$i,B:$i,C:$i,D:$i]:
% 0.67/0.89     ( ~( ( r2_hidden @ D @ C ) & 
% 0.67/0.89          ( r1_tarski @ C @ ( k2_zfmisc_1 @ A @ B ) ) & 
% 0.67/0.89          ( ![E:$i]:
% 0.67/0.89            ( ( m1_subset_1 @ E @ A ) =>
% 0.67/0.89              ( ![F:$i]:
% 0.67/0.89                ( ( m1_subset_1 @ F @ B ) => ( ( D ) != ( k4_tarski @ E @ F ) ) ) ) ) ) ) ))).
% 0.67/0.89  thf('4', plain,
% 0.67/0.89      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.67/0.89         (~ (r1_tarski @ X24 @ (k2_zfmisc_1 @ X25 @ X26))
% 0.67/0.89          | (m1_subset_1 @ (sk_F_2 @ X27 @ X26 @ X25) @ X26)
% 0.67/0.89          | ~ (r2_hidden @ X27 @ X24))),
% 0.67/0.89      inference('cnf', [status(esa)], [t65_subset_1])).
% 0.67/0.89  thf('5', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         (~ (r2_hidden @ X0 @ sk_D_1)
% 0.67/0.89          | (m1_subset_1 @ (sk_F_2 @ X0 @ sk_C_1 @ sk_B_1) @ sk_C_1))),
% 0.67/0.89      inference('sup-', [status(thm)], ['3', '4'])).
% 0.67/0.89  thf('6', plain, ((m1_subset_1 @ (sk_F_2 @ sk_A @ sk_C_1 @ sk_B_1) @ sk_C_1)),
% 0.67/0.89      inference('sup-', [status(thm)], ['0', '5'])).
% 0.67/0.89  thf(t2_subset, axiom,
% 0.67/0.89    (![A:$i,B:$i]:
% 0.67/0.89     ( ( m1_subset_1 @ A @ B ) =>
% 0.67/0.89       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.67/0.89  thf('7', plain,
% 0.67/0.89      (![X28 : $i, X29 : $i]:
% 0.67/0.89         ((r2_hidden @ X28 @ X29)
% 0.67/0.89          | (v1_xboole_0 @ X29)
% 0.67/0.89          | ~ (m1_subset_1 @ X28 @ X29))),
% 0.67/0.89      inference('cnf', [status(esa)], [t2_subset])).
% 0.67/0.89  thf('8', plain,
% 0.67/0.89      (((v1_xboole_0 @ sk_C_1)
% 0.67/0.89        | (r2_hidden @ (sk_F_2 @ sk_A @ sk_C_1 @ sk_B_1) @ sk_C_1))),
% 0.67/0.89      inference('sup-', [status(thm)], ['6', '7'])).
% 0.67/0.89  thf('9', plain, ((r2_hidden @ sk_A @ sk_D_1)),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.89  thf('10', plain, ((r1_tarski @ sk_D_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1))),
% 0.67/0.89      inference('sup-', [status(thm)], ['1', '2'])).
% 0.67/0.89  thf('11', plain,
% 0.67/0.89      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.67/0.89         (~ (r1_tarski @ X24 @ (k2_zfmisc_1 @ X25 @ X26))
% 0.67/0.89          | ((X27)
% 0.67/0.89              = (k4_tarski @ (sk_E_2 @ X27 @ X26 @ X25) @ 
% 0.67/0.89                 (sk_F_2 @ X27 @ X26 @ X25)))
% 0.67/0.89          | ~ (r2_hidden @ X27 @ X24))),
% 0.67/0.89      inference('cnf', [status(esa)], [t65_subset_1])).
% 0.67/0.89  thf('12', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         (~ (r2_hidden @ X0 @ sk_D_1)
% 0.67/0.89          | ((X0)
% 0.67/0.89              = (k4_tarski @ (sk_E_2 @ X0 @ sk_C_1 @ sk_B_1) @ 
% 0.67/0.89                 (sk_F_2 @ X0 @ sk_C_1 @ sk_B_1))))),
% 0.67/0.89      inference('sup-', [status(thm)], ['10', '11'])).
% 0.67/0.89  thf('13', plain,
% 0.67/0.89      (((sk_A)
% 0.67/0.89         = (k4_tarski @ (sk_E_2 @ sk_A @ sk_C_1 @ sk_B_1) @ 
% 0.67/0.89            (sk_F_2 @ sk_A @ sk_C_1 @ sk_B_1)))),
% 0.67/0.89      inference('sup-', [status(thm)], ['9', '12'])).
% 0.67/0.89  thf('14', plain, ((r2_hidden @ sk_A @ sk_D_1)),
% 0.67/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.67/0.89  thf('15', plain, ((r1_tarski @ sk_D_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1))),
% 0.67/0.89      inference('sup-', [status(thm)], ['1', '2'])).
% 0.67/0.89  thf('16', plain,
% 0.67/0.89      (![X24 : $i, X25 : $i, X26 : $i, X27 : $i]:
% 0.67/0.89         (~ (r1_tarski @ X24 @ (k2_zfmisc_1 @ X25 @ X26))
% 0.67/0.89          | (m1_subset_1 @ (sk_E_2 @ X27 @ X26 @ X25) @ X25)
% 0.67/0.89          | ~ (r2_hidden @ X27 @ X24))),
% 0.67/0.89      inference('cnf', [status(esa)], [t65_subset_1])).
% 0.67/0.89  thf('17', plain,
% 0.67/0.89      (![X0 : $i]:
% 0.67/0.89         (~ (r2_hidden @ X0 @ sk_D_1)
% 0.67/0.89          | (m1_subset_1 @ (sk_E_2 @ X0 @ sk_C_1 @ sk_B_1) @ sk_B_1))),
% 0.67/0.89      inference('sup-', [status(thm)], ['15', '16'])).
% 0.67/0.89  thf('18', plain,
% 0.67/0.89      ((m1_subset_1 @ (sk_E_2 @ sk_A @ sk_C_1 @ sk_B_1) @ sk_B_1)),
% 0.67/0.89      inference('sup-', [status(thm)], ['14', '17'])).
% 0.67/0.89  thf('19', plain,
% 0.67/0.89      (![X28 : $i, X29 : $i]:
% 0.67/0.89         ((r2_hidden @ X28 @ X29)
% 0.67/0.89          | (v1_xboole_0 @ X29)
% 0.67/0.89          | ~ (m1_subset_1 @ X28 @ X29))),
% 0.67/0.89      inference('cnf', [status(esa)], [t2_subset])).
% 0.67/0.89  thf('20', plain,
% 0.67/0.89      (((v1_xboole_0 @ sk_B_1)
% 0.67/0.89        | (r2_hidden @ (sk_E_2 @ sk_A @ sk_C_1 @ sk_B_1) @ sk_B_1))),
% 0.72/0.89      inference('sup-', [status(thm)], ['18', '19'])).
% 0.72/0.89  thf('21', plain,
% 0.72/0.89      (![X33 : $i, X34 : $i]:
% 0.72/0.89         (~ (r2_hidden @ X33 @ sk_B_1)
% 0.72/0.89          | ~ (r2_hidden @ X34 @ sk_C_1)
% 0.72/0.89          | ((sk_A) != (k4_tarski @ X33 @ X34)))),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.89  thf('22', plain,
% 0.72/0.89      (![X0 : $i]:
% 0.72/0.89         ((v1_xboole_0 @ sk_B_1)
% 0.72/0.89          | ((sk_A) != (k4_tarski @ (sk_E_2 @ sk_A @ sk_C_1 @ sk_B_1) @ X0))
% 0.72/0.89          | ~ (r2_hidden @ X0 @ sk_C_1))),
% 0.72/0.89      inference('sup-', [status(thm)], ['20', '21'])).
% 0.72/0.89  thf('23', plain,
% 0.72/0.89      ((((sk_A) != (sk_A))
% 0.72/0.89        | ~ (r2_hidden @ (sk_F_2 @ sk_A @ sk_C_1 @ sk_B_1) @ sk_C_1)
% 0.72/0.89        | (v1_xboole_0 @ sk_B_1))),
% 0.72/0.89      inference('sup-', [status(thm)], ['13', '22'])).
% 0.72/0.89  thf('24', plain,
% 0.72/0.89      (((v1_xboole_0 @ sk_B_1)
% 0.72/0.89        | ~ (r2_hidden @ (sk_F_2 @ sk_A @ sk_C_1 @ sk_B_1) @ sk_C_1))),
% 0.72/0.89      inference('simplify', [status(thm)], ['23'])).
% 0.72/0.89  thf('25', plain, (((v1_xboole_0 @ sk_C_1) | (v1_xboole_0 @ sk_B_1))),
% 0.72/0.89      inference('sup-', [status(thm)], ['8', '24'])).
% 0.72/0.89  thf('26', plain, (((v1_xboole_0 @ sk_C_1) | (v1_xboole_0 @ sk_B_1))),
% 0.72/0.89      inference('sup-', [status(thm)], ['8', '24'])).
% 0.72/0.89  thf('27', plain, (((v1_xboole_0 @ sk_C_1) | (v1_xboole_0 @ sk_B_1))),
% 0.72/0.89      inference('sup-', [status(thm)], ['8', '24'])).
% 0.72/0.89  thf('28', plain, (((v1_xboole_0 @ sk_C_1) | (v1_xboole_0 @ sk_B_1))),
% 0.72/0.89      inference('sup-', [status(thm)], ['8', '24'])).
% 0.72/0.89  thf(d2_zfmisc_1, axiom,
% 0.72/0.89    (![A:$i,B:$i,C:$i]:
% 0.72/0.89     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.72/0.89       ( ![D:$i]:
% 0.72/0.89         ( ( r2_hidden @ D @ C ) <=>
% 0.72/0.89           ( ?[E:$i,F:$i]:
% 0.72/0.89             ( ( r2_hidden @ E @ A ) & ( r2_hidden @ F @ B ) & 
% 0.72/0.89               ( ( D ) = ( k4_tarski @ E @ F ) ) ) ) ) ) ))).
% 0.72/0.89  thf(zf_stmt_1, type, zip_tseitin_0 : $i > $i > $i > $i > $i > $o).
% 0.72/0.89  thf(zf_stmt_2, axiom,
% 0.72/0.89    (![F:$i,E:$i,D:$i,B:$i,A:$i]:
% 0.72/0.89     ( ( zip_tseitin_0 @ F @ E @ D @ B @ A ) <=>
% 0.72/0.89       ( ( ( D ) = ( k4_tarski @ E @ F ) ) & ( r2_hidden @ F @ B ) & 
% 0.72/0.89         ( r2_hidden @ E @ A ) ) ))).
% 0.72/0.89  thf(zf_stmt_3, axiom,
% 0.72/0.89    (![A:$i,B:$i,C:$i]:
% 0.72/0.89     ( ( ( C ) = ( k2_zfmisc_1 @ A @ B ) ) <=>
% 0.72/0.89       ( ![D:$i]:
% 0.72/0.89         ( ( r2_hidden @ D @ C ) <=>
% 0.72/0.89           ( ?[E:$i,F:$i]: ( zip_tseitin_0 @ F @ E @ D @ B @ A ) ) ) ) ))).
% 0.72/0.89  thf('29', plain,
% 0.72/0.89      (![X17 : $i, X18 : $i, X21 : $i]:
% 0.72/0.89         (((X21) = (k2_zfmisc_1 @ X18 @ X17))
% 0.72/0.89          | (zip_tseitin_0 @ (sk_F @ X21 @ X17 @ X18) @ 
% 0.72/0.89             (sk_E @ X21 @ X17 @ X18) @ (sk_D @ X21 @ X17 @ X18) @ X17 @ X18)
% 0.72/0.89          | (r2_hidden @ (sk_D @ X21 @ X17 @ X18) @ X21))),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.72/0.89  thf('30', plain,
% 0.72/0.89      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.72/0.89         ((r2_hidden @ X9 @ X11)
% 0.72/0.89          | ~ (zip_tseitin_0 @ X9 @ X8 @ X10 @ X11 @ X12))),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.72/0.89  thf('31', plain,
% 0.72/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.89         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.72/0.89          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.72/0.89          | (r2_hidden @ (sk_F @ X2 @ X1 @ X0) @ X1))),
% 0.72/0.89      inference('sup-', [status(thm)], ['29', '30'])).
% 0.72/0.89  thf(d1_xboole_0, axiom,
% 0.72/0.89    (![A:$i]:
% 0.72/0.89     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.72/0.89  thf('32', plain,
% 0.72/0.89      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.72/0.89      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.72/0.89  thf('33', plain,
% 0.72/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.89         ((r2_hidden @ (sk_F @ X0 @ X2 @ X1) @ X2)
% 0.72/0.89          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.72/0.89          | ~ (v1_xboole_0 @ X0))),
% 0.72/0.89      inference('sup-', [status(thm)], ['31', '32'])).
% 0.72/0.89  thf('34', plain,
% 0.72/0.89      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.72/0.89      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.72/0.89  thf('35', plain,
% 0.72/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.89         (~ (v1_xboole_0 @ X2)
% 0.72/0.89          | ((X2) = (k2_zfmisc_1 @ X1 @ X0))
% 0.72/0.89          | ~ (v1_xboole_0 @ X0))),
% 0.72/0.89      inference('sup-', [status(thm)], ['33', '34'])).
% 0.72/0.89  thf('36', plain, ((r1_tarski @ sk_D_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1))),
% 0.72/0.89      inference('sup-', [status(thm)], ['1', '2'])).
% 0.72/0.89  thf(d8_xboole_0, axiom,
% 0.72/0.89    (![A:$i,B:$i]:
% 0.72/0.89     ( ( r2_xboole_0 @ A @ B ) <=>
% 0.72/0.89       ( ( r1_tarski @ A @ B ) & ( ( A ) != ( B ) ) ) ))).
% 0.72/0.89  thf('37', plain,
% 0.72/0.89      (![X3 : $i, X5 : $i]:
% 0.72/0.89         ((r2_xboole_0 @ X3 @ X5) | ((X3) = (X5)) | ~ (r1_tarski @ X3 @ X5))),
% 0.72/0.89      inference('cnf', [status(esa)], [d8_xboole_0])).
% 0.72/0.89  thf('38', plain,
% 0.72/0.89      ((((sk_D_1) = (k2_zfmisc_1 @ sk_B_1 @ sk_C_1))
% 0.72/0.89        | (r2_xboole_0 @ sk_D_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.72/0.89      inference('sup-', [status(thm)], ['36', '37'])).
% 0.72/0.89  thf(t6_xboole_0, axiom,
% 0.72/0.89    (![A:$i,B:$i]:
% 0.72/0.89     ( ~( ( r2_xboole_0 @ A @ B ) & 
% 0.72/0.89          ( ![C:$i]:
% 0.72/0.89            ( ~( ( r2_hidden @ C @ B ) & ( ~( r2_hidden @ C @ A ) ) ) ) ) ) ))).
% 0.72/0.89  thf('39', plain,
% 0.72/0.89      (![X6 : $i, X7 : $i]:
% 0.72/0.89         (~ (r2_xboole_0 @ X6 @ X7) | (r2_hidden @ (sk_C @ X7 @ X6) @ X7))),
% 0.72/0.89      inference('cnf', [status(esa)], [t6_xboole_0])).
% 0.72/0.89  thf('40', plain,
% 0.72/0.89      ((((sk_D_1) = (k2_zfmisc_1 @ sk_B_1 @ sk_C_1))
% 0.72/0.89        | (r2_hidden @ (sk_C @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1) @ sk_D_1) @ 
% 0.72/0.89           (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.72/0.89      inference('sup-', [status(thm)], ['38', '39'])).
% 0.72/0.89  thf('41', plain,
% 0.72/0.89      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.72/0.89      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.72/0.89  thf('42', plain,
% 0.72/0.89      ((((sk_D_1) = (k2_zfmisc_1 @ sk_B_1 @ sk_C_1))
% 0.72/0.89        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.72/0.89      inference('sup-', [status(thm)], ['40', '41'])).
% 0.72/0.89  thf('43', plain,
% 0.72/0.89      (![X0 : $i]:
% 0.72/0.89         (~ (v1_xboole_0 @ X0)
% 0.72/0.89          | ~ (v1_xboole_0 @ sk_C_1)
% 0.72/0.89          | ~ (v1_xboole_0 @ X0)
% 0.72/0.89          | ((sk_D_1) = (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.72/0.89      inference('sup-', [status(thm)], ['35', '42'])).
% 0.72/0.89  thf('44', plain,
% 0.72/0.89      (![X0 : $i]:
% 0.72/0.89         (((sk_D_1) = (k2_zfmisc_1 @ sk_B_1 @ sk_C_1))
% 0.72/0.89          | ~ (v1_xboole_0 @ sk_C_1)
% 0.72/0.89          | ~ (v1_xboole_0 @ X0))),
% 0.72/0.89      inference('simplify', [status(thm)], ['43'])).
% 0.72/0.89  thf('45', plain,
% 0.72/0.89      ((((sk_D_1) = (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)) | ~ (v1_xboole_0 @ sk_C_1))),
% 0.72/0.89      inference('condensation', [status(thm)], ['44'])).
% 0.72/0.89  thf('46', plain,
% 0.72/0.89      (((v1_xboole_0 @ sk_B_1) | ((sk_D_1) = (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.72/0.89      inference('sup-', [status(thm)], ['28', '45'])).
% 0.72/0.89  thf('47', plain,
% 0.72/0.89      (![X17 : $i, X18 : $i, X21 : $i]:
% 0.72/0.89         (((X21) = (k2_zfmisc_1 @ X18 @ X17))
% 0.72/0.89          | (zip_tseitin_0 @ (sk_F @ X21 @ X17 @ X18) @ 
% 0.72/0.89             (sk_E @ X21 @ X17 @ X18) @ (sk_D @ X21 @ X17 @ X18) @ X17 @ X18)
% 0.72/0.89          | (r2_hidden @ (sk_D @ X21 @ X17 @ X18) @ X21))),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.72/0.89  thf('48', plain,
% 0.72/0.89      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i]:
% 0.72/0.89         ((r2_hidden @ X8 @ X12)
% 0.72/0.89          | ~ (zip_tseitin_0 @ X9 @ X8 @ X10 @ X11 @ X12))),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_2])).
% 0.72/0.89  thf('49', plain,
% 0.72/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.89         ((r2_hidden @ (sk_D @ X2 @ X1 @ X0) @ X2)
% 0.72/0.89          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.72/0.89          | (r2_hidden @ (sk_E @ X2 @ X1 @ X0) @ X0))),
% 0.72/0.89      inference('sup-', [status(thm)], ['47', '48'])).
% 0.72/0.89  thf('50', plain,
% 0.72/0.89      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.72/0.89      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.72/0.89  thf('51', plain,
% 0.72/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.89         ((r2_hidden @ (sk_E @ X0 @ X2 @ X1) @ X1)
% 0.72/0.89          | ((X0) = (k2_zfmisc_1 @ X1 @ X2))
% 0.72/0.89          | ~ (v1_xboole_0 @ X0))),
% 0.72/0.89      inference('sup-', [status(thm)], ['49', '50'])).
% 0.72/0.89  thf('52', plain,
% 0.72/0.89      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.72/0.89      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.72/0.89  thf('53', plain,
% 0.72/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.89         (~ (v1_xboole_0 @ X2)
% 0.72/0.89          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.72/0.89          | ~ (v1_xboole_0 @ X0))),
% 0.72/0.89      inference('sup-', [status(thm)], ['51', '52'])).
% 0.72/0.89  thf('54', plain,
% 0.72/0.89      ((((sk_D_1) = (k2_zfmisc_1 @ sk_B_1 @ sk_C_1))
% 0.72/0.89        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.72/0.89      inference('sup-', [status(thm)], ['40', '41'])).
% 0.72/0.89  thf('55', plain,
% 0.72/0.89      (![X0 : $i]:
% 0.72/0.89         (~ (v1_xboole_0 @ X0)
% 0.72/0.89          | ~ (v1_xboole_0 @ sk_B_1)
% 0.72/0.89          | ~ (v1_xboole_0 @ X0)
% 0.72/0.89          | ((sk_D_1) = (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)))),
% 0.72/0.89      inference('sup-', [status(thm)], ['53', '54'])).
% 0.72/0.89  thf('56', plain,
% 0.72/0.89      (![X0 : $i]:
% 0.72/0.89         (((sk_D_1) = (k2_zfmisc_1 @ sk_B_1 @ sk_C_1))
% 0.72/0.89          | ~ (v1_xboole_0 @ sk_B_1)
% 0.72/0.89          | ~ (v1_xboole_0 @ X0))),
% 0.72/0.89      inference('simplify', [status(thm)], ['55'])).
% 0.72/0.89  thf('57', plain,
% 0.72/0.89      ((((sk_D_1) = (k2_zfmisc_1 @ sk_B_1 @ sk_C_1)) | ~ (v1_xboole_0 @ sk_B_1))),
% 0.72/0.89      inference('condensation', [status(thm)], ['56'])).
% 0.72/0.89  thf('58', plain, (((sk_D_1) = (k2_zfmisc_1 @ sk_B_1 @ sk_C_1))),
% 0.72/0.89      inference('clc', [status(thm)], ['46', '57'])).
% 0.72/0.89  thf('59', plain,
% 0.72/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.89         (~ (v1_xboole_0 @ X2)
% 0.72/0.89          | ((X2) = (k2_zfmisc_1 @ X1 @ X0))
% 0.72/0.89          | ~ (v1_xboole_0 @ X0))),
% 0.72/0.89      inference('sup-', [status(thm)], ['33', '34'])).
% 0.72/0.89  thf('60', plain,
% 0.72/0.89      (![X0 : $i]:
% 0.72/0.89         (((X0) = (sk_D_1)) | ~ (v1_xboole_0 @ sk_C_1) | ~ (v1_xboole_0 @ X0))),
% 0.72/0.89      inference('sup+', [status(thm)], ['58', '59'])).
% 0.72/0.89  thf('61', plain,
% 0.72/0.89      (![X0 : $i]:
% 0.72/0.89         ((v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ X0) | ((X0) = (sk_D_1)))),
% 0.72/0.89      inference('sup-', [status(thm)], ['27', '60'])).
% 0.72/0.89  thf('62', plain, (((sk_D_1) = (k2_zfmisc_1 @ sk_B_1 @ sk_C_1))),
% 0.72/0.89      inference('clc', [status(thm)], ['46', '57'])).
% 0.72/0.89  thf('63', plain,
% 0.72/0.89      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.72/0.89         (~ (v1_xboole_0 @ X2)
% 0.72/0.89          | ((X2) = (k2_zfmisc_1 @ X0 @ X1))
% 0.72/0.89          | ~ (v1_xboole_0 @ X0))),
% 0.72/0.89      inference('sup-', [status(thm)], ['51', '52'])).
% 0.72/0.89  thf('64', plain,
% 0.72/0.89      (![X0 : $i]:
% 0.72/0.89         (((X0) = (sk_D_1)) | ~ (v1_xboole_0 @ sk_B_1) | ~ (v1_xboole_0 @ X0))),
% 0.72/0.89      inference('sup+', [status(thm)], ['62', '63'])).
% 0.72/0.89  thf('65', plain, (![X0 : $i]: (((X0) = (sk_D_1)) | ~ (v1_xboole_0 @ X0))),
% 0.72/0.89      inference('clc', [status(thm)], ['61', '64'])).
% 0.72/0.89  thf('66', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_C_1) = (sk_D_1)))),
% 0.72/0.89      inference('sup-', [status(thm)], ['26', '65'])).
% 0.72/0.89  thf('67', plain, (![X0 : $i]: (((X0) = (sk_D_1)) | ~ (v1_xboole_0 @ X0))),
% 0.72/0.89      inference('clc', [status(thm)], ['61', '64'])).
% 0.72/0.89  thf('68', plain, ((((sk_C_1) = (sk_D_1)) | ((sk_B_1) = (sk_D_1)))),
% 0.72/0.89      inference('sup-', [status(thm)], ['66', '67'])).
% 0.72/0.89  thf('69', plain, (((v1_xboole_0 @ sk_C_1) | (v1_xboole_0 @ sk_B_1))),
% 0.72/0.89      inference('sup-', [status(thm)], ['8', '24'])).
% 0.72/0.89  thf('70', plain,
% 0.72/0.89      (((v1_xboole_0 @ sk_D_1) | ((sk_B_1) = (sk_D_1)) | (v1_xboole_0 @ sk_B_1))),
% 0.72/0.89      inference('sup+', [status(thm)], ['68', '69'])).
% 0.72/0.89  thf('71', plain, ((r2_hidden @ sk_A @ sk_D_1)),
% 0.72/0.89      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.72/0.89  thf('72', plain,
% 0.72/0.89      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.72/0.89      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.72/0.89  thf('73', plain, (~ (v1_xboole_0 @ sk_D_1)),
% 0.72/0.89      inference('sup-', [status(thm)], ['71', '72'])).
% 0.72/0.89  thf('74', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_B_1) = (sk_D_1)))),
% 0.72/0.89      inference('clc', [status(thm)], ['70', '73'])).
% 0.72/0.89  thf('75', plain, (![X0 : $i]: (((X0) = (sk_D_1)) | ~ (v1_xboole_0 @ X0))),
% 0.72/0.89      inference('clc', [status(thm)], ['61', '64'])).
% 0.72/0.89  thf('76', plain, (((sk_B_1) = (sk_D_1))),
% 0.72/0.89      inference('clc', [status(thm)], ['74', '75'])).
% 0.72/0.89  thf('77', plain, (((v1_xboole_0 @ sk_C_1) | (v1_xboole_0 @ sk_D_1))),
% 0.72/0.89      inference('demod', [status(thm)], ['25', '76'])).
% 0.72/0.89  thf('78', plain, (((v1_xboole_0 @ sk_B_1) | ((sk_C_1) = (sk_D_1)))),
% 0.72/0.89      inference('sup-', [status(thm)], ['26', '65'])).
% 0.72/0.89  thf('79', plain, (((sk_B_1) = (sk_D_1))),
% 0.72/0.89      inference('clc', [status(thm)], ['74', '75'])).
% 0.72/0.89  thf('80', plain, (((v1_xboole_0 @ sk_D_1) | ((sk_C_1) = (sk_D_1)))),
% 0.72/0.89      inference('demod', [status(thm)], ['78', '79'])).
% 0.72/0.89  thf('81', plain, (![X0 : $i]: (((X0) = (sk_D_1)) | ~ (v1_xboole_0 @ X0))),
% 0.72/0.89      inference('clc', [status(thm)], ['61', '64'])).
% 0.72/0.89  thf('82', plain, (~ (v1_xboole_0 @ sk_D_1)),
% 0.72/0.89      inference('sup-', [status(thm)], ['71', '72'])).
% 0.72/0.89  thf('83', plain, (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X0))),
% 0.72/0.89      inference('sup-', [status(thm)], ['81', '82'])).
% 0.72/0.89  thf('84', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 0.72/0.89      inference('simplify', [status(thm)], ['83'])).
% 0.72/0.89  thf('85', plain, (((sk_C_1) = (sk_D_1))),
% 0.72/0.89      inference('clc', [status(thm)], ['80', '84'])).
% 0.72/0.89  thf('86', plain, (((v1_xboole_0 @ sk_D_1) | (v1_xboole_0 @ sk_D_1))),
% 0.72/0.89      inference('demod', [status(thm)], ['77', '85'])).
% 0.72/0.89  thf('87', plain, ((v1_xboole_0 @ sk_D_1)),
% 0.72/0.89      inference('simplify', [status(thm)], ['86'])).
% 0.72/0.89  thf('88', plain, (![X0 : $i]: ~ (v1_xboole_0 @ X0)),
% 0.72/0.89      inference('simplify', [status(thm)], ['83'])).
% 0.72/0.89  thf('89', plain, ($false), inference('sup-', [status(thm)], ['87', '88'])).
% 0.72/0.89  
% 0.72/0.89  % SZS output end Refutation
% 0.72/0.89  
% 0.72/0.90  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
