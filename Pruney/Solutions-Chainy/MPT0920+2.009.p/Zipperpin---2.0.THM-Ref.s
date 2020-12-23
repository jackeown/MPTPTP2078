%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.W6jANekIzW

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:12 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 227 expanded)
%              Number of leaves         :   23 (  80 expanded)
%              Depth                    :    9
%              Number of atoms          : 1032 (6634 expanded)
%              Number of equality atoms :  120 ( 932 expanded)
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

thf(t80_mcart_1,conjecture,(
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
                         => ( E = H ) ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D = k1_xboole_0 )
          | ( E
            = ( k9_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) )).

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
                           => ( E = H ) ) ) ) ) )
         => ( ( A = k1_xboole_0 )
            | ( B = k1_xboole_0 )
            | ( C = k1_xboole_0 )
            | ( D = k1_xboole_0 )
            | ( E
              = ( k9_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t80_mcart_1])).

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
      | ( sk_E = X30 )
      | ~ ( m1_subset_1 @ X33 @ sk_C )
      | ~ ( m1_subset_1 @ X32 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( sk_F
       != ( k4_mcart_1 @ X0 @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    sk_E
 != ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_F
       != ( k4_mcart_1 @ X0 @ ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ sk_D ) ) ),
    inference('simplify_reflect-',[status(thm)],['45','46'])).

thf('48',plain,
    ( ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['13','14','15','16','17'])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_F
       != ( k4_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) @ X1 @ X2 ) )
      | ~ ( m1_subset_1 @ X2 @ sk_D ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,
    ( ( sk_F != sk_F )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_F ) @ sk_D )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['40','49'])).

thf('51',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k11_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k11_mcart_1 @ A @ B @ C @ D @ E ) @ D ) ) )).

thf('52',plain,(
    ! [X5: $i,X6: $i,X7: $i,X8: $i,X9: $i] :
      ( ( m1_subset_1 @ ( k11_mcart_1 @ X5 @ X6 @ X7 @ X8 @ X9 ) @ X8 )
      | ~ ( m1_subset_1 @ X9 @ ( k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k11_mcart_1])).

thf('53',plain,(
    m1_subset_1 @ ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ sk_D ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ sk_F ) ),
    inference('simplify_reflect-',[status(thm)],['29','30','31','32','33'])).

thf('55',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_F ) @ sk_D ),
    inference(demod,[status(thm)],['53','54'])).

thf('56',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k10_mcart_1 @ A @ B @ C @ D @ E ) @ C ) ) )).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ( m1_subset_1 @ ( k10_mcart_1 @ X0 @ X1 @ X2 @ X3 @ X4 ) @ X2 )
      | ~ ( m1_subset_1 @ X4 @ ( k4_zfmisc_1 @ X0 @ X1 @ X2 @ X3 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k10_mcart_1])).

thf('58',plain,(
    m1_subset_1 @ ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ sk_C ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,
    ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ),
    inference('simplify_reflect-',[status(thm)],['21','22','23','24','25'])).

thf('60',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) @ sk_C ),
    inference(demod,[status(thm)],['58','59'])).

thf('61',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k8_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ( m1_subset_1 @ ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ A ) ) )).

thf('62',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k8_mcart_1 @ X10 @ X11 @ X12 @ X13 @ X14 ) @ X10 )
      | ~ ( m1_subset_1 @ X14 @ ( k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k8_mcart_1])).

thf('63',plain,(
    m1_subset_1 @ ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) @ sk_A ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['5','6','7','8','9'])).

thf('65',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_F ) ) ) @ sk_A ),
    inference(demod,[status(thm)],['63','64'])).

thf('66',plain,(
    sk_F != sk_F ),
    inference(demod,[status(thm)],['50','55','60','65'])).

thf('67',plain,(
    $false ),
    inference(simplify,[status(thm)],['66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.W6jANekIzW
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:18:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.47  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.20/0.47  % Solved by: fo/fo7.sh
% 0.20/0.47  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.47  % done 30 iterations in 0.020s
% 0.20/0.47  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.20/0.47  % SZS output start Refutation
% 0.20/0.47  thf(sk_B_type, type, sk_B: $i).
% 0.20/0.47  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.47  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.20/0.47  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.47  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.47  thf(sk_F_type, type, sk_F: $i).
% 0.20/0.47  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.47  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.47  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.20/0.47  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.20/0.47  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.47  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.47  thf(sk_D_type, type, sk_D: $i).
% 0.20/0.47  thf(sk_E_type, type, sk_E: $i).
% 0.20/0.47  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.20/0.47  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.20/0.47  thf(t80_mcart_1, conjecture,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.47       ( ( ![G:$i]:
% 0.20/0.47           ( ( m1_subset_1 @ G @ A ) =>
% 0.20/0.47             ( ![H:$i]:
% 0.20/0.47               ( ( m1_subset_1 @ H @ B ) =>
% 0.20/0.47                 ( ![I:$i]:
% 0.20/0.47                   ( ( m1_subset_1 @ I @ C ) =>
% 0.20/0.47                     ( ![J:$i]:
% 0.20/0.47                       ( ( m1_subset_1 @ J @ D ) =>
% 0.20/0.47                         ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.20/0.47                           ( ( E ) = ( H ) ) ) ) ) ) ) ) ) ) ) =>
% 0.20/0.47         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.47           ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.20/0.47           ( ( E ) = ( k9_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ))).
% 0.20/0.47  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.47    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.20/0.47        ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.47          ( ( ![G:$i]:
% 0.20/0.47              ( ( m1_subset_1 @ G @ A ) =>
% 0.20/0.47                ( ![H:$i]:
% 0.20/0.47                  ( ( m1_subset_1 @ H @ B ) =>
% 0.20/0.47                    ( ![I:$i]:
% 0.20/0.47                      ( ( m1_subset_1 @ I @ C ) =>
% 0.20/0.47                        ( ![J:$i]:
% 0.20/0.47                          ( ( m1_subset_1 @ J @ D ) =>
% 0.20/0.47                            ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.20/0.47                              ( ( E ) = ( H ) ) ) ) ) ) ) ) ) ) ) =>
% 0.20/0.47            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.20/0.47              ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.20/0.47              ( ( E ) = ( k9_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) )),
% 0.20/0.47    inference('cnf.neg', [status(esa)], [t80_mcart_1])).
% 0.20/0.47  thf('0', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t60_mcart_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.47          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.20/0.47          ( ~( ![E:$i]:
% 0.20/0.47               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.47                 ( ( E ) =
% 0.20/0.47                   ( k4_mcart_1 @
% 0.20/0.47                     ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ 
% 0.20/0.47                     ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ 
% 0.20/0.47                     ( k10_mcart_1 @ A @ B @ C @ D @ E ) @ 
% 0.20/0.47                     ( k11_mcart_1 @ A @ B @ C @ D @ E ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf('1', plain,
% 0.20/0.47      (![X20 : $i, X21 : $i, X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.47         (((X20) = (k1_xboole_0))
% 0.20/0.47          | ((X21) = (k1_xboole_0))
% 0.20/0.47          | ((X22) = (k1_xboole_0))
% 0.20/0.47          | ((X24)
% 0.20/0.47              = (k4_mcart_1 @ (k8_mcart_1 @ X20 @ X21 @ X22 @ X23 @ X24) @ 
% 0.20/0.47                 (k9_mcart_1 @ X20 @ X21 @ X22 @ X23 @ X24) @ 
% 0.20/0.47                 (k10_mcart_1 @ X20 @ X21 @ X22 @ X23 @ X24) @ 
% 0.20/0.47                 (k11_mcart_1 @ X20 @ X21 @ X22 @ X23 @ X24)))
% 0.20/0.47          | ~ (m1_subset_1 @ X24 @ (k4_zfmisc_1 @ X20 @ X21 @ X22 @ X23))
% 0.20/0.47          | ((X23) = (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t60_mcart_1])).
% 0.20/0.47  thf('2', plain,
% 0.20/0.47      ((((sk_D) = (k1_xboole_0))
% 0.20/0.47        | ((sk_F)
% 0.20/0.47            = (k4_mcart_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.20/0.47               (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.20/0.47               (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ 
% 0.20/0.47               (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)))
% 0.20/0.47        | ((sk_C) = (k1_xboole_0))
% 0.20/0.47        | ((sk_B) = (k1_xboole_0))
% 0.20/0.47        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['0', '1'])).
% 0.20/0.47  thf('3', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(t61_mcart_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.47     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.20/0.47          ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.20/0.47          ( ~( ![E:$i]:
% 0.20/0.47               ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.47                 ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.47                     ( k1_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.20/0.47                   ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.47                     ( k2_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ E ) ) ) ) & 
% 0.20/0.47                   ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) =
% 0.20/0.47                     ( k2_mcart_1 @ ( k1_mcart_1 @ E ) ) ) & 
% 0.20/0.47                   ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( k2_mcart_1 @ E ) ) ) ) ) ) ) ))).
% 0.20/0.47  thf('4', plain,
% 0.20/0.47      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.47         (((X25) = (k1_xboole_0))
% 0.20/0.47          | ((X26) = (k1_xboole_0))
% 0.20/0.47          | ((X27) = (k1_xboole_0))
% 0.20/0.47          | ((k8_mcart_1 @ X25 @ X26 @ X27 @ X29 @ X28)
% 0.20/0.47              = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X28))))
% 0.20/0.47          | ~ (m1_subset_1 @ X28 @ (k4_zfmisc_1 @ X25 @ X26 @ X27 @ X29))
% 0.20/0.47          | ((X29) = (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.20/0.47  thf('5', plain,
% 0.20/0.47      ((((sk_D) = (k1_xboole_0))
% 0.20/0.47        | ((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.20/0.47            = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.20/0.47        | ((sk_C) = (k1_xboole_0))
% 0.20/0.47        | ((sk_B) = (k1_xboole_0))
% 0.20/0.47        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['3', '4'])).
% 0.20/0.47  thf('6', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('7', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('8', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('9', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('10', plain,
% 0.20/0.47      (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.20/0.47         = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['5', '6', '7', '8', '9'])).
% 0.20/0.47  thf('11', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('12', plain,
% 0.20/0.47      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.47         (((X25) = (k1_xboole_0))
% 0.20/0.47          | ((X26) = (k1_xboole_0))
% 0.20/0.47          | ((X27) = (k1_xboole_0))
% 0.20/0.47          | ((k9_mcart_1 @ X25 @ X26 @ X27 @ X29 @ X28)
% 0.20/0.47              = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ X28))))
% 0.20/0.47          | ~ (m1_subset_1 @ X28 @ (k4_zfmisc_1 @ X25 @ X26 @ X27 @ X29))
% 0.20/0.47          | ((X29) = (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.20/0.47  thf('13', plain,
% 0.20/0.47      ((((sk_D) = (k1_xboole_0))
% 0.20/0.47        | ((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.20/0.47            = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))
% 0.20/0.47        | ((sk_C) = (k1_xboole_0))
% 0.20/0.47        | ((sk_B) = (k1_xboole_0))
% 0.20/0.47        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['11', '12'])).
% 0.20/0.47  thf('14', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('15', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('16', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('17', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('18', plain,
% 0.20/0.47      (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.20/0.47         = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)],
% 0.20/0.47                ['13', '14', '15', '16', '17'])).
% 0.20/0.47  thf('19', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('20', plain,
% 0.20/0.47      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.47         (((X25) = (k1_xboole_0))
% 0.20/0.47          | ((X26) = (k1_xboole_0))
% 0.20/0.47          | ((X27) = (k1_xboole_0))
% 0.20/0.47          | ((k10_mcart_1 @ X25 @ X26 @ X27 @ X29 @ X28)
% 0.20/0.47              = (k2_mcart_1 @ (k1_mcart_1 @ X28)))
% 0.20/0.47          | ~ (m1_subset_1 @ X28 @ (k4_zfmisc_1 @ X25 @ X26 @ X27 @ X29))
% 0.20/0.47          | ((X29) = (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.20/0.47  thf('21', plain,
% 0.20/0.47      ((((sk_D) = (k1_xboole_0))
% 0.20/0.47        | ((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.20/0.47            = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))
% 0.20/0.47        | ((sk_C) = (k1_xboole_0))
% 0.20/0.47        | ((sk_B) = (k1_xboole_0))
% 0.20/0.47        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['19', '20'])).
% 0.20/0.47  thf('22', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('23', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('24', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('25', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('26', plain,
% 0.20/0.47      (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.20/0.47         = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)],
% 0.20/0.47                ['21', '22', '23', '24', '25'])).
% 0.20/0.47  thf('27', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('28', plain,
% 0.20/0.47      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.20/0.47         (((X25) = (k1_xboole_0))
% 0.20/0.47          | ((X26) = (k1_xboole_0))
% 0.20/0.47          | ((X27) = (k1_xboole_0))
% 0.20/0.47          | ((k11_mcart_1 @ X25 @ X26 @ X27 @ X29 @ X28) = (k2_mcart_1 @ X28))
% 0.20/0.47          | ~ (m1_subset_1 @ X28 @ (k4_zfmisc_1 @ X25 @ X26 @ X27 @ X29))
% 0.20/0.47          | ((X29) = (k1_xboole_0)))),
% 0.20/0.47      inference('cnf', [status(esa)], [t61_mcart_1])).
% 0.20/0.47  thf('29', plain,
% 0.20/0.47      ((((sk_D) = (k1_xboole_0))
% 0.20/0.47        | ((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.20/0.47            = (k2_mcart_1 @ sk_F))
% 0.20/0.47        | ((sk_C) = (k1_xboole_0))
% 0.20/0.47        | ((sk_B) = (k1_xboole_0))
% 0.20/0.47        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.47      inference('sup-', [status(thm)], ['27', '28'])).
% 0.20/0.47  thf('30', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('31', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('32', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('33', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('34', plain,
% 0.20/0.47      (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) = (k2_mcart_1 @ sk_F))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)],
% 0.20/0.47                ['29', '30', '31', '32', '33'])).
% 0.20/0.47  thf('35', plain,
% 0.20/0.47      ((((sk_D) = (k1_xboole_0))
% 0.20/0.47        | ((sk_F)
% 0.20/0.47            = (k4_mcart_1 @ 
% 0.20/0.47               (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))) @ 
% 0.20/0.47               (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))) @ 
% 0.20/0.47               (k2_mcart_1 @ (k1_mcart_1 @ sk_F)) @ (k2_mcart_1 @ sk_F)))
% 0.20/0.47        | ((sk_C) = (k1_xboole_0))
% 0.20/0.47        | ((sk_B) = (k1_xboole_0))
% 0.20/0.47        | ((sk_A) = (k1_xboole_0)))),
% 0.20/0.47      inference('demod', [status(thm)], ['2', '10', '18', '26', '34'])).
% 0.20/0.47  thf('36', plain, (((sk_A) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('37', plain, (((sk_B) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('38', plain, (((sk_C) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('39', plain, (((sk_D) != (k1_xboole_0))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('40', plain,
% 0.20/0.47      (((sk_F)
% 0.20/0.47         = (k4_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))) @ 
% 0.20/0.47            (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))) @ 
% 0.20/0.47            (k2_mcart_1 @ (k1_mcart_1 @ sk_F)) @ (k2_mcart_1 @ sk_F)))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)],
% 0.20/0.47                ['35', '36', '37', '38', '39'])).
% 0.20/0.47  thf('41', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(dt_k9_mcart_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.47       ( m1_subset_1 @ ( k9_mcart_1 @ A @ B @ C @ D @ E ) @ B ) ))).
% 0.20/0.47  thf('42', plain,
% 0.20/0.47      (![X15 : $i, X16 : $i, X17 : $i, X18 : $i, X19 : $i]:
% 0.20/0.47         ((m1_subset_1 @ (k9_mcart_1 @ X15 @ X16 @ X17 @ X18 @ X19) @ X16)
% 0.20/0.47          | ~ (m1_subset_1 @ X19 @ (k4_zfmisc_1 @ X15 @ X16 @ X17 @ X18)))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k9_mcart_1])).
% 0.20/0.47  thf('43', plain,
% 0.20/0.47      ((m1_subset_1 @ (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ sk_B)),
% 0.20/0.47      inference('sup-', [status(thm)], ['41', '42'])).
% 0.20/0.47  thf('44', plain,
% 0.20/0.47      (![X30 : $i, X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X30 @ sk_B)
% 0.20/0.47          | ~ (m1_subset_1 @ X31 @ sk_D)
% 0.20/0.47          | ((sk_F) != (k4_mcart_1 @ X32 @ X30 @ X33 @ X31))
% 0.20/0.47          | ((sk_E) = (X30))
% 0.20/0.47          | ~ (m1_subset_1 @ X33 @ sk_C)
% 0.20/0.47          | ~ (m1_subset_1 @ X32 @ sk_A))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('45', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.47          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.20/0.47          | ((sk_E) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.20/0.47          | ((sk_F)
% 0.20/0.47              != (k4_mcart_1 @ X0 @ 
% 0.20/0.47                  (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ X1 @ X2))
% 0.20/0.47          | ~ (m1_subset_1 @ X2 @ sk_D))),
% 0.20/0.47      inference('sup-', [status(thm)], ['43', '44'])).
% 0.20/0.47  thf('46', plain,
% 0.20/0.47      (((sk_E) != (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf('47', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.47          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.20/0.47          | ((sk_F)
% 0.20/0.47              != (k4_mcart_1 @ X0 @ 
% 0.20/0.47                  (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ X1 @ X2))
% 0.20/0.47          | ~ (m1_subset_1 @ X2 @ sk_D))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['45', '46'])).
% 0.20/0.47  thf('48', plain,
% 0.20/0.47      (((k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.20/0.47         = (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)],
% 0.20/0.47                ['13', '14', '15', '16', '17'])).
% 0.20/0.47  thf('49', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.20/0.47         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.20/0.47          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.20/0.47          | ((sk_F)
% 0.20/0.47              != (k4_mcart_1 @ X0 @ 
% 0.20/0.47                  (k2_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))) @ X1 @ X2))
% 0.20/0.47          | ~ (m1_subset_1 @ X2 @ sk_D))),
% 0.20/0.47      inference('demod', [status(thm)], ['47', '48'])).
% 0.20/0.47  thf('50', plain,
% 0.20/0.47      ((((sk_F) != (sk_F))
% 0.20/0.47        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_F) @ sk_D)
% 0.20/0.47        | ~ (m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_F)) @ sk_C)
% 0.20/0.47        | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))) @ 
% 0.20/0.47             sk_A))),
% 0.20/0.47      inference('sup-', [status(thm)], ['40', '49'])).
% 0.20/0.47  thf('51', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(dt_k11_mcart_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.47       ( m1_subset_1 @ ( k11_mcart_1 @ A @ B @ C @ D @ E ) @ D ) ))).
% 0.20/0.47  thf('52', plain,
% 0.20/0.47      (![X5 : $i, X6 : $i, X7 : $i, X8 : $i, X9 : $i]:
% 0.20/0.47         ((m1_subset_1 @ (k11_mcart_1 @ X5 @ X6 @ X7 @ X8 @ X9) @ X8)
% 0.20/0.47          | ~ (m1_subset_1 @ X9 @ (k4_zfmisc_1 @ X5 @ X6 @ X7 @ X8)))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k11_mcart_1])).
% 0.20/0.47  thf('53', plain,
% 0.20/0.47      ((m1_subset_1 @ (k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ sk_D)),
% 0.20/0.47      inference('sup-', [status(thm)], ['51', '52'])).
% 0.20/0.47  thf('54', plain,
% 0.20/0.47      (((k11_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) = (k2_mcart_1 @ sk_F))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)],
% 0.20/0.47                ['29', '30', '31', '32', '33'])).
% 0.20/0.47  thf('55', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_F) @ sk_D)),
% 0.20/0.47      inference('demod', [status(thm)], ['53', '54'])).
% 0.20/0.47  thf('56', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(dt_k10_mcart_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.47       ( m1_subset_1 @ ( k10_mcart_1 @ A @ B @ C @ D @ E ) @ C ) ))).
% 0.20/0.47  thf('57', plain,
% 0.20/0.47      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.20/0.47         ((m1_subset_1 @ (k10_mcart_1 @ X0 @ X1 @ X2 @ X3 @ X4) @ X2)
% 0.20/0.47          | ~ (m1_subset_1 @ X4 @ (k4_zfmisc_1 @ X0 @ X1 @ X2 @ X3)))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k10_mcart_1])).
% 0.20/0.47  thf('58', plain,
% 0.20/0.47      ((m1_subset_1 @ (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ sk_C)),
% 0.20/0.47      inference('sup-', [status(thm)], ['56', '57'])).
% 0.20/0.47  thf('59', plain,
% 0.20/0.47      (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.20/0.47         = (k2_mcart_1 @ (k1_mcart_1 @ sk_F)))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)],
% 0.20/0.47                ['21', '22', '23', '24', '25'])).
% 0.20/0.47  thf('60', plain, ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_F)) @ sk_C)),
% 0.20/0.47      inference('demod', [status(thm)], ['58', '59'])).
% 0.20/0.47  thf('61', plain,
% 0.20/0.47      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.20/0.47      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.47  thf(dt_k8_mcart_1, axiom,
% 0.20/0.47    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.20/0.47     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.20/0.47       ( m1_subset_1 @ ( k8_mcart_1 @ A @ B @ C @ D @ E ) @ A ) ))).
% 0.20/0.47  thf('62', plain,
% 0.20/0.47      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.20/0.47         ((m1_subset_1 @ (k8_mcart_1 @ X10 @ X11 @ X12 @ X13 @ X14) @ X10)
% 0.20/0.47          | ~ (m1_subset_1 @ X14 @ (k4_zfmisc_1 @ X10 @ X11 @ X12 @ X13)))),
% 0.20/0.47      inference('cnf', [status(esa)], [dt_k8_mcart_1])).
% 0.20/0.47  thf('63', plain,
% 0.20/0.47      ((m1_subset_1 @ (k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) @ sk_A)),
% 0.20/0.47      inference('sup-', [status(thm)], ['61', '62'])).
% 0.20/0.47  thf('64', plain,
% 0.20/0.47      (((k8_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)
% 0.20/0.47         = (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))))),
% 0.20/0.47      inference('simplify_reflect-', [status(thm)], ['5', '6', '7', '8', '9'])).
% 0.20/0.47  thf('65', plain,
% 0.20/0.47      ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_F))) @ sk_A)),
% 0.20/0.47      inference('demod', [status(thm)], ['63', '64'])).
% 0.20/0.47  thf('66', plain, (((sk_F) != (sk_F))),
% 0.20/0.47      inference('demod', [status(thm)], ['50', '55', '60', '65'])).
% 0.20/0.47  thf('67', plain, ($false), inference('simplify', [status(thm)], ['66'])).
% 0.20/0.47  
% 0.20/0.47  % SZS output end Refutation
% 0.20/0.47  
% 0.20/0.48  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
