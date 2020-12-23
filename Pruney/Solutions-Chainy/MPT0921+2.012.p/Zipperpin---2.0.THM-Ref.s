%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PoJWNcoEJ3

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:14 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 247 expanded)
%              Number of leaves         :   23 (  86 expanded)
%              Depth                    :   10
%              Number of atoms          : 1039 (7261 expanded)
%              Number of equality atoms :  125 (1029 expanded)
%              Maximal formula depth    :   24 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(t81_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
      ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( ! [G: $i] :
            ( ( m1_subset_1 @ G @ A )
           => ! [H: $i] :
                ( ( m1_subset_1 @ H @ B )
               => ! [I: $i] :
                    ( ( m1_subset_1 @ I @ C )
                   => ! [J: $i] :
                        ( ( m1_subset_1 @ J @ D )
                       => ( ( F
                            = ( k4_mcart_1 @ G @ H @ I @ J ) )
                         => ( E = I ) ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D = k1_xboole_0 )
          | ( E
            = ( k10_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i,F: $i] :
        ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
       => ( ! [G: $i] :
              ( ( m1_subset_1 @ G @ A )
             => ! [H: $i] :
                  ( ( m1_subset_1 @ H @ B )
                 => ! [I: $i] :
                      ( ( m1_subset_1 @ I @ C )
                     => ! [J: $i] :
                          ( ( m1_subset_1 @ J @ D )
                         => ( ( F
                              = ( k4_mcart_1 @ G @ H @ I @ J ) )
                           => ( E = I ) ) ) ) ) )
         => ( ( A = k1_xboole_0 )
            | ( B = k1_xboole_0 )
            | ( C = k1_xboole_0 )
            | ( D = k1_xboole_0 )
            | ( E
              = ( k10_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t81_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t60_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 )
        & ~ ! [E: $i] :
              ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
             => ( E
                = ( k4_mcart_1 @ ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ ( k10_mcart_1 @ A @ B @ C @ D @ E ) @ ( k11_mcart_1 @ A @ B @ C @ D @ E ) ) ) ) ) )).

thf('1',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i,X24: $i] :
      ( ( X20 = k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( X22 = k1_xboole_0 )
      | ( X24
        = ( k4_mcart_1 @ ( k8_mcart_1 @ X20 @ X21 @ X22 @ X23 @ X24 ) @ ( k9_mcart_1 @ X20 @ X21 @ X22 @ X23 @ X24 ) @ ( k10_mcart_1 @ X20 @ X21 @ X22 @ X23 @ X24 ) @ ( k11_mcart_1 @ X20 @ X21 @ X22 @ X23 @ X24 ) ) )
      | ~ ( m1_subset_1 @ X24 @ ( k4_zfmisc_1 @ X20 @ X21 @ X22 @ X23 ) )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t60_mcart_1])).

thf('2',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_F
      = ( k4_mcart_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t61_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ( D != k1_xboole_0 )
        & ~ ! [E: $i] :
              ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
             => ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) )
                & ( ( k9_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) )
                & ( ( k10_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) )
                & ( ( k11_mcart_1 @ A @ B @ C @ D @ E )
                  = ( k2_mcart_1 @ E ) ) ) ) ) )).

thf('4',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( ( k8_mcart_1 @ X25 @ X26 @ X27 @ X29 @ X28 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X28 ) ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k4_zfmisc_1 @ X25 @ X26 @ X27 @ X29 ) )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('5',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('8',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('10',plain,
    ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['5','6','7','8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( ( k9_mcart_1 @ X25 @ X26 @ X27 @ X29 @ X28 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ X28 ) ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k4_zfmisc_1 @ X25 @ X26 @ X27 @ X29 ) )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('13',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['13','14','15','16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X25 @ X26 @ X27 @ X29 @ X28 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k4_zfmisc_1 @ X25 @ X26 @ X27 @ X29 ) )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('21',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ),
    inference('simplify_reflect-',[status(thm)],['21','22','23','24','25'])).

thf('27',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X25 = k1_xboole_0 )
      | ( X26 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( ( k11_mcart_1 @ X25 @ X26 @ X27 @ X29 @ X28 )
        = ( k2_mcart_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k4_zfmisc_1 @ X25 @ X26 @ X27 @ X29 ) )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t61_mcart_1])).

thf('29',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
      = ( k2_mcart_1 @ sk_F ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('34',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ sk_F ) ),
    inference('simplify_reflect-',[status(thm)],['29','30','31','32','33'])).

thf('35',plain,
    ( ( sk_D = k1_xboole_0 )
    | ( sk_F
      = ( k4_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) @ ( k2_mcart_1 @ sk_F ) ) )
    | ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['2','10','18','26','34'])).

thf('36',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('37',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('38',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('40',plain,
    ( sk_F
    = ( k4_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) @ ( k2_mcart_1 @ sk_F ) ) ),
    inference('simplify_reflect-',[status(thm)],['35','36','37','38','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k9_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ B ) ) )).

thf('42',plain,(
    ! [X15: $i,X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( m1_subset_1 @ ( k9_mcart_1 @ X15 @ X16 @ X17 @ X18 @ X19 ) @ X16 )
      | ~ ( m1_subset_1 @ X19 @ ( k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k9_mcart_1])).

thf('43',plain,(
    m1_subset_1 @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ sk_B ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X30: $i,X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X30 @ sk_B )
      | ~ ( m1_subset_1 @ X31 @ sk_D )
      | ( sk_F
       != ( k4_mcart_1 @ X32 @ X30 @ X33 @ X31 ) )
      | ( sk_E = X33 )
      | ~ ( m1_subset_1 @ X33 @ sk_C )
      | ~ ( m1_subset_1 @ X32 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E = X1 )
      | ( sk_F
       != ( k4_mcart_1 @ X0 @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['13','14','15','16','17'])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E = X1 )
      | ( sk_F
       != ( k4_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ sk_D ) ) ),
    inference(demod,[status(thm)],['45','46'])).

thf('48',plain,
    ( ( sk_F != sk_F )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_F ) @ sk_D )
    | ( sk_E
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['40','47'])).

thf('49',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k11_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k11_mcart_1 @ A @ B @ C @ D @ E ) @ D ) ) )).

thf('50',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k11_mcart_1 @ X5 @ X6 @ X7 @ X8 @ X9 ) @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k11_mcart_1])).

thf('51',plain,(
    m1_subset_1 @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ sk_D ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ sk_F ) ),
    inference('simplify_reflect-',[status(thm)],['29','30','31','32','33'])).

thf('53',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_F ) @ sk_D ),
    inference(demod,[status(thm)],['51','52'])).

thf('54',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k10_mcart_1 @ A @ B @ C @ D @ E ) @ C ) ) )).

thf('55',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k10_mcart_1 @ X0 @ X1 @ X2 @ X3 @ X4 ) @ X2 )
      | ~ ( m1_subset_1 @ X4 @ ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_mcart_1])).

thf('56',plain,(
    m1_subset_1 @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ sk_C ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ),
    inference('simplify_reflect-',[status(thm)],['21','22','23','24','25'])).

thf('58',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) @ sk_C ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ A ) ) )).

thf('60',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k8_mcart_1 @ X10 @ X11 @ X12 @ X13 @ X14 ) @ X10 )
      | ~ ( m1_subset_1 @ X14 @ ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_mcart_1])).

thf('61',plain,(
    m1_subset_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ sk_A ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,
    ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['5','6','7','8','9'])).

thf('63',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) @ sk_A ),
    inference(demod,[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_F != sk_F )
    | ( sk_E
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ),
    inference(demod,[status(thm)],['48','53','58','63'])).

thf('65',plain,
    ( sk_E
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ),
    inference(simplify,[status(thm)],['64'])).

thf('66',plain,(
    sk_E
 != ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ),
    inference('simplify_reflect-',[status(thm)],['21','22','23','24','25'])).

thf('68',plain,(
    sk_E
 != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['65','68'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.PoJWNcoEJ3
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:33:45 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  % Running portfolio for 600 s
% 0.15/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.15/0.35  % Number of cores: 8
% 0.15/0.36  % Python version: Python 3.6.8
% 0.15/0.36  % Running in FO mode
% 0.22/0.49  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.49  % Solved by: fo/fo7.sh
% 0.22/0.49  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.49  % done 30 iterations in 0.021s
% 0.22/0.49  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.49  % SZS output start Refutation
% 0.22/0.49  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.49  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.22/0.49  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.22/0.49  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.49  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.49  thf(sk_F_type, type, sk_F: $i).
% 0.22/0.49  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.22/0.49  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.22/0.49  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.22/0.49  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.22/0.49  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.49  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.49  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.49  thf(sk_E_type, type, sk_E: $i).
% 0.22/0.49  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.22/0.49  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.22/0.49  thf(t81_mcart_1, conjecture,
% 0.22/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.22/0.49       ( ( ![G:$i]:
% 0.22/0.49           ( ( m1_subset_1 @ G @ A ) =>
% 0.22/0.49             ( ![H:$i]:
% 0.22/0.49               ( ( m1_subset_1 @ H @ B ) =>
% 0.22/0.49                 ( ![I:$i]:
% 0.22/0.49                   ( ( m1_subset_1 @ I @ C ) =>
% 0.22/0.49                     ( ![J:$i]:
% 0.22/0.49                       ( ( m1_subset_1 @ J @ D ) =>
% 0.22/0.49                         ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.22/0.49                           ( ( E ) = ( I ) ) ) ) ) ) ) ) ) ) ) =>
% 0.22/0.49         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.22/0.49           ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.22/0.49           ( ( E ) = ( k10_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ))).
% 0.22/0.49  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.49    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.22/0.49        ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.22/0.49          ( ( ![G:$i]:
% 0.22/0.49              ( ( m1_subset_1 @ G @ A ) =>
% 0.22/0.49                ( ![H:$i]:
% 0.22/0.49                  ( ( m1_subset_1 @ H @ B ) =>
% 0.22/0.49                    ( ![I:$i]:
% 0.22/0.49                      ( ( m1_subset_1 @ I @ C ) =>
% 0.22/0.49                        ( ![J:$i]:
% 0.22/0.49                          ( ( m1_subset_1 @ J @ D ) =>
% 0.22/0.49                            ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.22/0.49                              ( ( E ) = ( I ) ) ) ) ) ) ) ) ) ) ) =>
% 0.22/0.49            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.22/0.49              ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.22/0.49              ( ( E ) = ( k10_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) )),
% 0.22/0.49    inference('cnf.neg', [status(esa)], [t81_mcart_1])).
% 0.22/0.49  thf('0', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t60_mcart_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49          ( ~( ![E:$i]:
% 0.22/0.49               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.22/0.49                 ( ( E ) =
% 0.22/0.49                   ( k4_mcart_1 @
% 0.22/0.49                     ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ 
% 0.22/0.49                     ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ 
% 0.22/0.49                     ( k10_mcart_1 @ A @ B @ C @ D @ E ) @ 
% 0.22/0.49                     ( k11_mcart_1 @ A @ B @ C @ D @ E ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf('1', plain,
% 0.22/0.49      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.22/0.49         (((X20) = (k1_xboole_0))
% 0.22/0.49          | ((X21) = (k1_xboole_0))
% 0.22/0.49          | ((X22) = (k1_xboole_0))
% 0.22/0.49          | ((X24)
% 0.22/0.49              = (k4_mcart_1 @ (k8_mcart_1 @ X20 @ X21 @ X22 @ X23 @ X24) @ 
% 0.22/0.49                 (k9_mcart_1 @ X20 @ X21 @ X22 @ X23 @ X24) @ 
% 0.22/0.49                 (k10_mcart_1 @ X20 @ X21 @ X22 @ X23 @ X24) @ 
% 0.22/0.49                 (k11_mcart_1 @ X20 @ X21 @ X22 @ X23 @ X24)))
% 0.22/0.49          | ~ (m1_subset_1 @ X24 @ (k4_zfmisc_1 @ X20 @ X21 @ X22 @ X23))
% 0.22/0.49          | ((X23) = (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t60_mcart_1])).
% 0.22/0.49  thf('2', plain,
% 0.22/0.49      ((((sk_D) = (k1_xboole_0))
% 0.22/0.49        | ((sk_F)
% 0.22/0.49            = (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.22/0.49               (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.22/0.49               (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.22/0.49               (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)))
% 0.22/0.49        | ((sk_C) = (k1_xboole_0))
% 0.22/0.49        | ((sk_B) = (k1_xboole_0))
% 0.22/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['0', '1'])).
% 0.22/0.49  thf('3', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(t61_mcart_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.49     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.22/0.49          ( ~( ![E:$i]:
% 0.22/0.49               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.22/0.49                 ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.22/0.49                     ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.22/0.49                   ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.22/0.49                     ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.22/0.49                   ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.22/0.49                     ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) ) & 
% 0.22/0.49                   ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( k2_mcart_1 @ E ) ) ) ) ) ) ) ))).
% 0.22/0.49  thf('4', plain,
% 0.22/0.49      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.22/0.49         (((X25) = (k1_xboole_0))
% 0.22/0.49          | ((X26) = (k1_xboole_0))
% 0.22/0.49          | ((X27) = (k1_xboole_0))
% 0.22/0.49          | ((k8_mcart_1 @ X25 @ X26 @ X27 @ X29 @ X28)
% 0.22/0.49              = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X28))))
% 0.22/0.49          | ~ (m1_subset_1 @ X28 @ (k4_zfmisc_1 @ X25 @ X26 @ X27 @ X29))
% 0.22/0.49          | ((X29) = (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.22/0.49  thf('5', plain,
% 0.22/0.49      ((((sk_D) = (k1_xboole_0))
% 0.22/0.49        | ((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.22/0.49            = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.22/0.49        | ((sk_C) = (k1_xboole_0))
% 0.22/0.49        | ((sk_B) = (k1_xboole_0))
% 0.22/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.49  thf('6', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('7', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('8', plain, (((sk_C) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('9', plain, (((sk_D) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('10', plain,
% 0.22/0.49      (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.22/0.49         = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['5', '6', '7', '8', '9'])).
% 0.22/0.49  thf('11', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('12', plain,
% 0.22/0.49      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.22/0.49         (((X25) = (k1_xboole_0))
% 0.22/0.49          | ((X26) = (k1_xboole_0))
% 0.22/0.49          | ((X27) = (k1_xboole_0))
% 0.22/0.49          | ((k9_mcart_1 @ X25 @ X26 @ X27 @ X29 @ X28)
% 0.22/0.49              = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X28))))
% 0.22/0.49          | ~ (m1_subset_1 @ X28 @ (k4_zfmisc_1 @ X25 @ X26 @ X27 @ X29))
% 0.22/0.49          | ((X29) = (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.22/0.49  thf('13', plain,
% 0.22/0.49      ((((sk_D) = (k1_xboole_0))
% 0.22/0.49        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.22/0.49            = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.22/0.49        | ((sk_C) = (k1_xboole_0))
% 0.22/0.49        | ((sk_B) = (k1_xboole_0))
% 0.22/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.49  thf('14', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('15', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('16', plain, (((sk_C) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('17', plain, (((sk_D) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('18', plain,
% 0.22/0.49      (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.22/0.49         = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)],
% 0.22/0.49                ['13', '14', '15', '16', '17'])).
% 0.22/0.49  thf('19', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('20', plain,
% 0.22/0.49      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.22/0.49         (((X25) = (k1_xboole_0))
% 0.22/0.49          | ((X26) = (k1_xboole_0))
% 0.22/0.49          | ((X27) = (k1_xboole_0))
% 0.22/0.49          | ((k10_mcart_1 @ X25 @ X26 @ X27 @ X29 @ X28)
% 0.22/0.49              = (k2_mcart_1 @ (k1_mcart_1 @ X28)))
% 0.22/0.49          | ~ (m1_subset_1 @ X28 @ (k4_zfmisc_1 @ X25 @ X26 @ X27 @ X29))
% 0.22/0.49          | ((X29) = (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.22/0.49  thf('21', plain,
% 0.22/0.49      ((((sk_D) = (k1_xboole_0))
% 0.22/0.49        | ((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.22/0.49            = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))
% 0.22/0.49        | ((sk_C) = (k1_xboole_0))
% 0.22/0.49        | ((sk_B) = (k1_xboole_0))
% 0.22/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['19', '20'])).
% 0.22/0.49  thf('22', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('23', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('24', plain, (((sk_C) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('25', plain, (((sk_D) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('26', plain,
% 0.22/0.49      (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.22/0.49         = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)],
% 0.22/0.49                ['21', '22', '23', '24', '25'])).
% 0.22/0.49  thf('27', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('28', plain,
% 0.22/0.49      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.22/0.49         (((X25) = (k1_xboole_0))
% 0.22/0.49          | ((X26) = (k1_xboole_0))
% 0.22/0.49          | ((X27) = (k1_xboole_0))
% 0.22/0.49          | ((k11_mcart_1 @ X25 @ X26 @ X27 @ X29 @ X28) = (k2_mcart_1 @ X28))
% 0.22/0.49          | ~ (m1_subset_1 @ X28 @ (k4_zfmisc_1 @ X25 @ X26 @ X27 @ X29))
% 0.22/0.49          | ((X29) = (k1_xboole_0)))),
% 0.22/0.49      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.22/0.49  thf('29', plain,
% 0.22/0.49      ((((sk_D) = (k1_xboole_0))
% 0.22/0.49        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.22/0.49            = (k2_mcart_1 @ sk_F))
% 0.22/0.49        | ((sk_C) = (k1_xboole_0))
% 0.22/0.49        | ((sk_B) = (k1_xboole_0))
% 0.22/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.49      inference('sup-', [status(thm)], ['27', '28'])).
% 0.22/0.49  thf('30', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('31', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('32', plain, (((sk_C) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('33', plain, (((sk_D) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('34', plain,
% 0.22/0.49      (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) = (k2_mcart_1 @ sk_F))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)],
% 0.22/0.49                ['29', '30', '31', '32', '33'])).
% 0.22/0.49  thf('35', plain,
% 0.22/0.49      ((((sk_D) = (k1_xboole_0))
% 0.22/0.49        | ((sk_F)
% 0.22/0.49            = (k4_mcart_1 @ 
% 0.22/0.49               (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))) @ 
% 0.22/0.49               (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))) @ 
% 0.22/0.49               (k2_mcart_1 @ (k1_mcart_1 @ sk_F)) @ (k2_mcart_1 @ sk_F)))
% 0.22/0.49        | ((sk_C) = (k1_xboole_0))
% 0.22/0.49        | ((sk_B) = (k1_xboole_0))
% 0.22/0.49        | ((sk_A) = (k1_xboole_0)))),
% 0.22/0.49      inference('demod', [status(thm)], ['2', '10', '18', '26', '34'])).
% 0.22/0.49  thf('36', plain, (((sk_A) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('37', plain, (((sk_B) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('38', plain, (((sk_C) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('39', plain, (((sk_D) != (k1_xboole_0))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('40', plain,
% 0.22/0.49      (((sk_F)
% 0.22/0.49         = (k4_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))) @ 
% 0.22/0.49            (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))) @ 
% 0.22/0.49            (k2_mcart_1 @ (k1_mcart_1 @ sk_F)) @ (k2_mcart_1 @ sk_F)))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)],
% 0.22/0.49                ['35', '36', '37', '38', '39'])).
% 0.22/0.49  thf('41', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(dt_k9_mcart_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.22/0.49       ( m1_subset_1 @ ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ B ) ))).
% 0.22/0.49  thf('42', plain,
% 0.22/0.49      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.22/0.49         ((m1_subset_1 @ (k9_mcart_1 @ X15 @ X16 @ X17 @ X18 @ X19) @ X16)
% 0.22/0.49          | ~ (m1_subset_1 @ X19 @ (k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18)))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_k9_mcart_1])).
% 0.22/0.49  thf('43', plain,
% 0.22/0.49      ((m1_subset_1 @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ sk_B)),
% 0.22/0.49      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.49  thf('44', plain,
% 0.22/0.49      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X30 @ sk_B)
% 0.22/0.49          | ~ (m1_subset_1 @ X31 @ sk_D)
% 0.22/0.49          | ((sk_F) != (k4_mcart_1 @ X32 @ X30 @ X33 @ X31))
% 0.22/0.49          | ((sk_E) = (X33))
% 0.22/0.49          | ~ (m1_subset_1 @ X33 @ sk_C)
% 0.22/0.49          | ~ (m1_subset_1 @ X32 @ sk_A))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('45', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.22/0.49          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.22/0.49          | ((sk_E) = (X1))
% 0.22/0.49          | ((sk_F)
% 0.22/0.49              != (k4_mcart_1 @ X0 @ 
% 0.22/0.49                  (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ X1 @ X2))
% 0.22/0.49          | ~ (m1_subset_1 @ X2 @ sk_D))),
% 0.22/0.49      inference('sup-', [status(thm)], ['43', '44'])).
% 0.22/0.49  thf('46', plain,
% 0.22/0.49      (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.22/0.49         = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)],
% 0.22/0.49                ['13', '14', '15', '16', '17'])).
% 0.22/0.49  thf('47', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.49         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.22/0.49          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.22/0.49          | ((sk_E) = (X1))
% 0.22/0.49          | ((sk_F)
% 0.22/0.49              != (k4_mcart_1 @ X0 @ 
% 0.22/0.49                  (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))) @ X1 @ X2))
% 0.22/0.49          | ~ (m1_subset_1 @ X2 @ sk_D))),
% 0.22/0.49      inference('demod', [status(thm)], ['45', '46'])).
% 0.22/0.49  thf('48', plain,
% 0.22/0.49      ((((sk_F) != (sk_F))
% 0.22/0.49        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_F) @ sk_D)
% 0.22/0.49        | ((sk_E) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))
% 0.22/0.49        | ~ (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_F)) @ sk_C)
% 0.22/0.49        | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))) @ 
% 0.22/0.49             sk_A))),
% 0.22/0.49      inference('sup-', [status(thm)], ['40', '47'])).
% 0.22/0.49  thf('49', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(dt_k11_mcart_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.22/0.49       ( m1_subset_1 @ ( k11_mcart_1 @ A @ B @ C @ D @ E ) @ D ) ))).
% 0.22/0.49  thf('50', plain,
% 0.22/0.49      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.22/0.49         ((m1_subset_1 @ (k11_mcart_1 @ X5 @ X6 @ X7 @ X8 @ X9) @ X8)
% 0.22/0.49          | ~ (m1_subset_1 @ X9 @ (k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8)))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_k11_mcart_1])).
% 0.22/0.49  thf('51', plain,
% 0.22/0.49      ((m1_subset_1 @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ sk_D)),
% 0.22/0.49      inference('sup-', [status(thm)], ['49', '50'])).
% 0.22/0.49  thf('52', plain,
% 0.22/0.49      (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) = (k2_mcart_1 @ sk_F))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)],
% 0.22/0.49                ['29', '30', '31', '32', '33'])).
% 0.22/0.49  thf('53', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_F) @ sk_D)),
% 0.22/0.49      inference('demod', [status(thm)], ['51', '52'])).
% 0.22/0.49  thf('54', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(dt_k10_mcart_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.22/0.49       ( m1_subset_1 @ ( k10_mcart_1 @ A @ B @ C @ D @ E ) @ C ) ))).
% 0.22/0.49  thf('55', plain,
% 0.22/0.49      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.22/0.49         ((m1_subset_1 @ (k10_mcart_1 @ X0 @ X1 @ X2 @ X3 @ X4) @ X2)
% 0.22/0.49          | ~ (m1_subset_1 @ X4 @ (k4_zfmisc_1 @ X0 @ X1 @ X2 @ X3)))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_k10_mcart_1])).
% 0.22/0.49  thf('56', plain,
% 0.22/0.49      ((m1_subset_1 @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ sk_C)),
% 0.22/0.49      inference('sup-', [status(thm)], ['54', '55'])).
% 0.22/0.49  thf('57', plain,
% 0.22/0.49      (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.22/0.49         = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)],
% 0.22/0.49                ['21', '22', '23', '24', '25'])).
% 0.22/0.49  thf('58', plain, ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_F)) @ sk_C)),
% 0.22/0.49      inference('demod', [status(thm)], ['56', '57'])).
% 0.22/0.49  thf('59', plain,
% 0.22/0.49      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf(dt_k8_mcart_1, axiom,
% 0.22/0.49    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.22/0.49     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.22/0.49       ( m1_subset_1 @ ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ A ) ))).
% 0.22/0.49  thf('60', plain,
% 0.22/0.49      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.49         ((m1_subset_1 @ (k8_mcart_1 @ X10 @ X11 @ X12 @ X13 @ X14) @ X10)
% 0.22/0.49          | ~ (m1_subset_1 @ X14 @ (k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)))),
% 0.22/0.49      inference('cnf', [status(esa)], [dt_k8_mcart_1])).
% 0.22/0.49  thf('61', plain,
% 0.22/0.49      ((m1_subset_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ sk_A)),
% 0.22/0.49      inference('sup-', [status(thm)], ['59', '60'])).
% 0.22/0.49  thf('62', plain,
% 0.22/0.49      (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.22/0.49         = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['5', '6', '7', '8', '9'])).
% 0.22/0.49  thf('63', plain,
% 0.22/0.49      ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))) @ sk_A)),
% 0.22/0.49      inference('demod', [status(thm)], ['61', '62'])).
% 0.22/0.49  thf('64', plain,
% 0.22/0.49      ((((sk_F) != (sk_F)) | ((sk_E) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.22/0.49      inference('demod', [status(thm)], ['48', '53', '58', '63'])).
% 0.22/0.49  thf('65', plain, (((sk_E) = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))),
% 0.22/0.49      inference('simplify', [status(thm)], ['64'])).
% 0.22/0.49  thf('66', plain,
% 0.22/0.49      (((sk_E) != (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))),
% 0.22/0.49      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.49  thf('67', plain,
% 0.22/0.49      (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.22/0.49         = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)],
% 0.22/0.49                ['21', '22', '23', '24', '25'])).
% 0.22/0.49  thf('68', plain, (((sk_E) != (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))),
% 0.22/0.49      inference('demod', [status(thm)], ['66', '67'])).
% 0.22/0.49  thf('69', plain, ($false),
% 0.22/0.49      inference('simplify_reflect-', [status(thm)], ['65', '68'])).
% 0.22/0.49  
% 0.22/0.49  % SZS output end Refutation
% 0.22/0.49  
% 0.22/0.50  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
