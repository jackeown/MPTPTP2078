%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1YbT6ObVqq

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:52:13 EST 2020

% Result     : Theorem 0.46s
% Output     : Refutation 0.46s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 586 expanded)
%              Number of leaves         :   21 ( 181 expanded)
%              Depth                    :   23
%              Number of atoms          : 1543 (19795 expanded)
%              Number of equality atoms :  180 (2675 expanded)
%              Maximal formula depth    :   27 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_F_type,type,(
    sk_F: $i )).

thf(k9_mcart_1_type,type,(
    k9_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_J_type,type,(
    sk_J: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_I_type,type,(
    sk_I: $i > $i > $i > $i > $i > $i > $i )).

thf(k10_mcart_1_type,type,(
    k10_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k4_zfmisc_1_type,type,(
    k4_zfmisc_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k8_mcart_1_type,type,(
    k8_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(k11_mcart_1_type,type,(
    k11_mcart_1: $i > $i > $i > $i > $i > $i )).

thf(sk_G_type,type,(
    sk_G: $i > $i > $i > $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_H_type,type,(
    sk_H: $i > $i > $i > $i > $i > $i > $i )).

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

thf(t80_mcart_1,axiom,(
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

thf('1',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X20 @ ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19 ) )
      | ( X21
        = ( k9_mcart_1 @ X16 @ X17 @ X18 @ X19 @ X20 ) )
      | ( m1_subset_1 @ ( sk_I @ X20 @ X21 @ X19 @ X18 @ X17 @ X16 ) @ X18 ) ) ),
    inference(cnf,[status(esa)],[t80_mcart_1])).

thf('2',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('9',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X20 @ ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19 ) )
      | ( X21
        = ( k9_mcart_1 @ X16 @ X17 @ X18 @ X19 @ X20 ) )
      | ( m1_subset_1 @ ( sk_G @ X20 @ X21 @ X19 @ X18 @ X17 @ X16 ) @ X16 ) ) ),
    inference(cnf,[status(esa)],[t80_mcart_1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['10','11','12','13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X20 @ ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19 ) )
      | ( X21
        = ( k9_mcart_1 @ X16 @ X17 @ X18 @ X19 @ X20 ) )
      | ( X20
        = ( k4_mcart_1 @ ( sk_G @ X20 @ X21 @ X19 @ X18 @ X17 @ X16 ) @ ( sk_H @ X20 @ X21 @ X19 @ X18 @ X17 @ X16 ) @ ( sk_I @ X20 @ X21 @ X19 @ X18 @ X17 @ X16 ) @ ( sk_J @ X20 @ X21 @ X19 @ X18 @ X17 @ X16 ) ) ) ) ),
    inference(cnf,[status(esa)],[t80_mcart_1])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( sk_F
        = ( k4_mcart_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,(
    ! [X0: $i] :
      ( ( sk_F
        = ( k4_mcart_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['18','19','20','21','22'])).

thf('24',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X20 @ ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19 ) )
      | ( X21
        = ( k9_mcart_1 @ X16 @ X17 @ X18 @ X19 @ X20 ) )
      | ( m1_subset_1 @ ( sk_H @ X20 @ X21 @ X19 @ X18 @ X17 @ X16 ) @ X17 ) ) ),
    inference(cnf,[status(esa)],[t80_mcart_1])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_B )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['26','27','28','29','30'])).

thf('32',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X22 @ sk_B )
      | ~ ( m1_subset_1 @ X23 @ sk_D )
      | ( sk_F
       != ( k4_mcart_1 @ X24 @ X22 @ X25 @ X23 ) )
      | ( sk_E = X25 )
      | ~ ( m1_subset_1 @ X25 @ sk_C )
      | ~ ( m1_subset_1 @ X24 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('33',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ~ ( m1_subset_1 @ X1 @ sk_A )
      | ~ ( m1_subset_1 @ X2 @ sk_C )
      | ( sk_E = X2 )
      | ( sk_F
       != ( k4_mcart_1 @ X1 @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ X2 @ X3 ) )
      | ~ ( m1_subset_1 @ X3 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,(
    ! [X0: $i] :
      ( ( sk_F != sk_F )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ~ ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( sk_E
        = ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ~ ( m1_subset_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['23','33'])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_A )
      | ~ ( m1_subset_1 @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( sk_E
        = ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ~ ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( sk_E
        = ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['15','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_C )
      | ( sk_E
        = ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ~ ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( sk_E
        = ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['7','37'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( sk_E
        = ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) )
      | ~ ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ( X16 = k1_xboole_0 )
      | ( X17 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X20 @ ( k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19 ) )
      | ( X21
        = ( k9_mcart_1 @ X16 @ X17 @ X18 @ X19 @ X20 ) )
      | ( m1_subset_1 @ ( sk_J @ X20 @ X21 @ X19 @ X18 @ X17 @ X16 ) @ X19 ) ) ),
    inference(cnf,[status(esa)],[t80_mcart_1])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( sk_D = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_A = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('44',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('46',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_D )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['42','43','44','45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( sk_E
        = ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ) ),
    inference(clc,[status(thm)],['39','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( sk_F
        = ( k4_mcart_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['18','19','20','21','22'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( sk_F
        = ( k4_mcart_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ) ) ),
    inference('sup+',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( sk_F
        = ( k4_mcart_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( sk_F
        = ( k4_mcart_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf(t78_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) )
     => ~ ( ( A != k1_xboole_0 )
          & ( B != k1_xboole_0 )
          & ( C != k1_xboole_0 )
          & ( D != k1_xboole_0 )
          & ? [F: $i,G: $i,H: $i,I: $i] :
              ( ~ ( ( ( k8_mcart_1 @ A @ B @ C @ D @ E )
                    = F )
                  & ( ( k9_mcart_1 @ A @ B @ C @ D @ E )
                    = G )
                  & ( ( k10_mcart_1 @ A @ B @ C @ D @ E )
                    = H )
                  & ( ( k11_mcart_1 @ A @ B @ C @ D @ E )
                    = I ) )
              & ( E
                = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) )).

thf('54',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X11: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( X7 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X10 = k1_xboole_0 )
      | ~ ( m1_subset_1 @ X11 @ ( k4_zfmisc_1 @ X10 @ X9 @ X8 @ X7 ) )
      | ( ( k10_mcart_1 @ X10 @ X9 @ X8 @ X7 @ X11 )
        = X15 )
      | ( X11
       != ( k4_mcart_1 @ X13 @ X14 @ X15 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t78_mcart_1])).

thf('55',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i,X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( ( k10_mcart_1 @ X10 @ X9 @ X8 @ X7 @ ( k4_mcart_1 @ X13 @ X14 @ X15 @ X12 ) )
        = X15 )
      | ~ ( m1_subset_1 @ ( k4_mcart_1 @ X13 @ X14 @ X15 @ X12 ) @ ( k4_zfmisc_1 @ X10 @ X9 @ X8 @ X7 ) )
      | ( X10 = k1_xboole_0 )
      | ( X9 = k1_xboole_0 )
      | ( X8 = k1_xboole_0 )
      | ( X7 = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i,X4: $i] :
      ( ~ ( m1_subset_1 @ sk_F @ ( k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0 ) )
      | ( X4
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( X0 = k1_xboole_0 )
      | ( X1 = k1_xboole_0 )
      | ( X2 = k1_xboole_0 )
      | ( X3 = k1_xboole_0 )
      | ( ( k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ ( k4_mcart_1 @ ( sk_G @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E @ ( sk_J @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
        = sk_E ) ) ),
    inference('sup-',[status(thm)],['53','55'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k4_mcart_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
        = sk_E )
      | ( sk_A = k1_xboole_0 )
      | ( sk_B = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 )
      | ( sk_D = k1_xboole_0 )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ) ) ),
    inference('sup-',[status(thm)],['52','56'])).

thf('58',plain,(
    sk_D != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('60',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ ( k4_mcart_1 @ ( sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ ( sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) @ sk_E @ ( sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A ) ) )
        = sk_E )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['57','58','59','60','61'])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
        = sk_E )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ) ) ),
    inference('sup+',[status(thm)],['51','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) )
      | ( ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F )
        = sk_E ) ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    sk_E
 != ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X0: $i] :
      ( X0
      = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ) ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X0: $i] :
      ( X0
      = ( k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ) ),
    inference('simplify_reflect-',[status(thm)],['64','65'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] : ( X1 = X0 ) ),
    inference('sup+',[status(thm)],['66','67'])).

thf('69',plain,(
    sk_E
 != ( k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('70',plain,(
    ! [X0: $i] : ( sk_E != X0 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    $false ),
    inference(simplify,[status(thm)],['70'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.1YbT6ObVqq
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:42:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.46/0.65  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.46/0.65  % Solved by: fo/fo7.sh
% 0.46/0.65  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.46/0.65  % done 99 iterations in 0.198s
% 0.46/0.65  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.46/0.65  % SZS output start Refutation
% 0.46/0.65  thf(sk_E_type, type, sk_E: $i).
% 0.46/0.65  thf(sk_F_type, type, sk_F: $i).
% 0.46/0.65  thf(k9_mcart_1_type, type, k9_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.46/0.65  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.46/0.65  thf(sk_C_type, type, sk_C: $i).
% 0.46/0.65  thf(sk_J_type, type, sk_J: $i > $i > $i > $i > $i > $i > $i).
% 0.46/0.65  thf(sk_I_type, type, sk_I: $i > $i > $i > $i > $i > $i > $i).
% 0.46/0.65  thf(k10_mcart_1_type, type, k10_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.46/0.65  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.46/0.65  thf(k4_zfmisc_1_type, type, k4_zfmisc_1: $i > $i > $i > $i > $i).
% 0.46/0.65  thf(sk_A_type, type, sk_A: $i).
% 0.46/0.65  thf(k8_mcart_1_type, type, k8_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.46/0.65  thf(k11_mcart_1_type, type, k11_mcart_1: $i > $i > $i > $i > $i > $i).
% 0.46/0.65  thf(sk_G_type, type, sk_G: $i > $i > $i > $i > $i > $i > $i).
% 0.46/0.65  thf(sk_B_type, type, sk_B: $i).
% 0.46/0.65  thf(sk_D_type, type, sk_D: $i).
% 0.46/0.65  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.46/0.65  thf(sk_H_type, type, sk_H: $i > $i > $i > $i > $i > $i > $i).
% 0.46/0.65  thf(t81_mcart_1, conjecture,
% 0.46/0.65    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.46/0.65       ( ( ![G:$i]:
% 0.46/0.65           ( ( m1_subset_1 @ G @ A ) =>
% 0.46/0.65             ( ![H:$i]:
% 0.46/0.65               ( ( m1_subset_1 @ H @ B ) =>
% 0.46/0.65                 ( ![I:$i]:
% 0.46/0.65                   ( ( m1_subset_1 @ I @ C ) =>
% 0.46/0.65                     ( ![J:$i]:
% 0.46/0.65                       ( ( m1_subset_1 @ J @ D ) =>
% 0.46/0.65                         ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.46/0.65                           ( ( E ) = ( I ) ) ) ) ) ) ) ) ) ) ) =>
% 0.46/0.65         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.46/0.65           ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.46/0.65           ( ( E ) = ( k10_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ))).
% 0.46/0.65  thf(zf_stmt_0, negated_conjecture,
% 0.46/0.65    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.46/0.65        ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.46/0.65          ( ( ![G:$i]:
% 0.46/0.65              ( ( m1_subset_1 @ G @ A ) =>
% 0.46/0.65                ( ![H:$i]:
% 0.46/0.65                  ( ( m1_subset_1 @ H @ B ) =>
% 0.46/0.65                    ( ![I:$i]:
% 0.46/0.65                      ( ( m1_subset_1 @ I @ C ) =>
% 0.46/0.65                        ( ![J:$i]:
% 0.46/0.65                          ( ( m1_subset_1 @ J @ D ) =>
% 0.46/0.65                            ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.46/0.65                              ( ( E ) = ( I ) ) ) ) ) ) ) ) ) ) ) =>
% 0.46/0.65            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.46/0.65              ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.46/0.65              ( ( E ) = ( k10_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ) )),
% 0.46/0.65    inference('cnf.neg', [status(esa)], [t81_mcart_1])).
% 0.46/0.65  thf('0', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf(t80_mcart_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i,D:$i,E:$i,F:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ F @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.46/0.65       ( ( ![G:$i]:
% 0.46/0.65           ( ( m1_subset_1 @ G @ A ) =>
% 0.46/0.65             ( ![H:$i]:
% 0.46/0.65               ( ( m1_subset_1 @ H @ B ) =>
% 0.46/0.65                 ( ![I:$i]:
% 0.46/0.65                   ( ( m1_subset_1 @ I @ C ) =>
% 0.46/0.65                     ( ![J:$i]:
% 0.46/0.65                       ( ( m1_subset_1 @ J @ D ) =>
% 0.46/0.65                         ( ( ( F ) = ( k4_mcart_1 @ G @ H @ I @ J ) ) =>
% 0.46/0.65                           ( ( E ) = ( H ) ) ) ) ) ) ) ) ) ) ) =>
% 0.46/0.65         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.46/0.65           ( ( C ) = ( k1_xboole_0 ) ) | ( ( D ) = ( k1_xboole_0 ) ) | 
% 0.46/0.65           ( ( E ) = ( k9_mcart_1 @ A @ B @ C @ D @ F ) ) ) ) ))).
% 0.46/0.65  thf('1', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.65         (((X16) = (k1_xboole_0))
% 0.46/0.65          | ((X17) = (k1_xboole_0))
% 0.46/0.65          | ((X18) = (k1_xboole_0))
% 0.46/0.65          | ((X19) = (k1_xboole_0))
% 0.46/0.65          | ~ (m1_subset_1 @ X20 @ (k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19))
% 0.46/0.65          | ((X21) = (k9_mcart_1 @ X16 @ X17 @ X18 @ X19 @ X20))
% 0.46/0.65          | (m1_subset_1 @ (sk_I @ X20 @ X21 @ X19 @ X18 @ X17 @ X16) @ X18))),
% 0.46/0.65      inference('cnf', [status(esa)], [t80_mcart_1])).
% 0.46/0.65  thf('2', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((m1_subset_1 @ (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.46/0.65          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.46/0.65          | ((sk_D) = (k1_xboole_0))
% 0.46/0.65          | ((sk_C) = (k1_xboole_0))
% 0.46/0.65          | ((sk_B) = (k1_xboole_0))
% 0.46/0.65          | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['0', '1'])).
% 0.46/0.65  thf('3', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('4', plain, (((sk_B) != (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('5', plain, (((sk_C) != (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('6', plain, (((sk_D) != (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('7', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((m1_subset_1 @ (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_C)
% 0.46/0.65          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)))),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5', '6'])).
% 0.46/0.65  thf('8', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('9', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.65         (((X16) = (k1_xboole_0))
% 0.46/0.65          | ((X17) = (k1_xboole_0))
% 0.46/0.65          | ((X18) = (k1_xboole_0))
% 0.46/0.65          | ((X19) = (k1_xboole_0))
% 0.46/0.65          | ~ (m1_subset_1 @ X20 @ (k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19))
% 0.46/0.65          | ((X21) = (k9_mcart_1 @ X16 @ X17 @ X18 @ X19 @ X20))
% 0.46/0.65          | (m1_subset_1 @ (sk_G @ X20 @ X21 @ X19 @ X18 @ X17 @ X16) @ X16))),
% 0.46/0.65      inference('cnf', [status(esa)], [t80_mcart_1])).
% 0.46/0.65  thf('10', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((m1_subset_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.46/0.65          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.46/0.65          | ((sk_D) = (k1_xboole_0))
% 0.46/0.65          | ((sk_C) = (k1_xboole_0))
% 0.46/0.65          | ((sk_B) = (k1_xboole_0))
% 0.46/0.65          | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['8', '9'])).
% 0.46/0.65  thf('11', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('12', plain, (((sk_B) != (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('13', plain, (((sk_C) != (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('14', plain, (((sk_D) != (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('15', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((m1_subset_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_A)
% 0.46/0.65          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)))),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)],
% 0.46/0.65                ['10', '11', '12', '13', '14'])).
% 0.46/0.65  thf('16', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('17', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.65         (((X16) = (k1_xboole_0))
% 0.46/0.65          | ((X17) = (k1_xboole_0))
% 0.46/0.65          | ((X18) = (k1_xboole_0))
% 0.46/0.65          | ((X19) = (k1_xboole_0))
% 0.46/0.65          | ~ (m1_subset_1 @ X20 @ (k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19))
% 0.46/0.65          | ((X21) = (k9_mcart_1 @ X16 @ X17 @ X18 @ X19 @ X20))
% 0.46/0.65          | ((X20)
% 0.46/0.65              = (k4_mcart_1 @ (sk_G @ X20 @ X21 @ X19 @ X18 @ X17 @ X16) @ 
% 0.46/0.65                 (sk_H @ X20 @ X21 @ X19 @ X18 @ X17 @ X16) @ 
% 0.46/0.65                 (sk_I @ X20 @ X21 @ X19 @ X18 @ X17 @ X16) @ 
% 0.46/0.65                 (sk_J @ X20 @ X21 @ X19 @ X18 @ X17 @ X16))))),
% 0.46/0.65      inference('cnf', [status(esa)], [t80_mcart_1])).
% 0.46/0.65  thf('18', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((sk_F)
% 0.46/0.65            = (k4_mcart_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.65               (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.65               (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.65               (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.46/0.65          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.46/0.65          | ((sk_D) = (k1_xboole_0))
% 0.46/0.65          | ((sk_C) = (k1_xboole_0))
% 0.46/0.65          | ((sk_B) = (k1_xboole_0))
% 0.46/0.65          | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['16', '17'])).
% 0.46/0.65  thf('19', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('20', plain, (((sk_B) != (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('21', plain, (((sk_C) != (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('22', plain, (((sk_D) != (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('23', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((sk_F)
% 0.46/0.65            = (k4_mcart_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.65               (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.65               (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.65               (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.46/0.65          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)))),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)],
% 0.46/0.65                ['18', '19', '20', '21', '22'])).
% 0.46/0.65  thf('24', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('25', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.65         (((X16) = (k1_xboole_0))
% 0.46/0.65          | ((X17) = (k1_xboole_0))
% 0.46/0.65          | ((X18) = (k1_xboole_0))
% 0.46/0.65          | ((X19) = (k1_xboole_0))
% 0.46/0.65          | ~ (m1_subset_1 @ X20 @ (k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19))
% 0.46/0.65          | ((X21) = (k9_mcart_1 @ X16 @ X17 @ X18 @ X19 @ X20))
% 0.46/0.65          | (m1_subset_1 @ (sk_H @ X20 @ X21 @ X19 @ X18 @ X17 @ X16) @ X17))),
% 0.46/0.65      inference('cnf', [status(esa)], [t80_mcart_1])).
% 0.46/0.65  thf('26', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((m1_subset_1 @ (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.46/0.65          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.46/0.65          | ((sk_D) = (k1_xboole_0))
% 0.46/0.65          | ((sk_C) = (k1_xboole_0))
% 0.46/0.65          | ((sk_B) = (k1_xboole_0))
% 0.46/0.65          | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['24', '25'])).
% 0.46/0.65  thf('27', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('28', plain, (((sk_B) != (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('29', plain, (((sk_C) != (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('30', plain, (((sk_D) != (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('31', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((m1_subset_1 @ (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_B)
% 0.46/0.65          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)))),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)],
% 0.46/0.65                ['26', '27', '28', '29', '30'])).
% 0.46/0.65  thf('32', plain,
% 0.46/0.65      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ X22 @ sk_B)
% 0.46/0.65          | ~ (m1_subset_1 @ X23 @ sk_D)
% 0.46/0.65          | ((sk_F) != (k4_mcart_1 @ X24 @ X22 @ X25 @ X23))
% 0.46/0.65          | ((sk_E) = (X25))
% 0.46/0.65          | ~ (m1_subset_1 @ X25 @ sk_C)
% 0.46/0.65          | ~ (m1_subset_1 @ X24 @ sk_A))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('33', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.46/0.65         (((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.46/0.65          | ~ (m1_subset_1 @ X1 @ sk_A)
% 0.46/0.65          | ~ (m1_subset_1 @ X2 @ sk_C)
% 0.46/0.65          | ((sk_E) = (X2))
% 0.46/0.65          | ((sk_F)
% 0.46/0.65              != (k4_mcart_1 @ X1 @ 
% 0.46/0.65                  (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ X2 @ X3))
% 0.46/0.65          | ~ (m1_subset_1 @ X3 @ sk_D))),
% 0.46/0.65      inference('sup-', [status(thm)], ['31', '32'])).
% 0.46/0.65  thf('34', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((sk_F) != (sk_F))
% 0.46/0.65          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.46/0.65          | ~ (m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.65               sk_D)
% 0.46/0.65          | ((sk_E) = (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.46/0.65          | ~ (m1_subset_1 @ (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.65               sk_C)
% 0.46/0.65          | ~ (m1_subset_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.65               sk_A)
% 0.46/0.65          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['23', '33'])).
% 0.46/0.65  thf('35', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.65             sk_A)
% 0.46/0.65          | ~ (m1_subset_1 @ (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.65               sk_C)
% 0.46/0.65          | ((sk_E) = (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.46/0.65          | ~ (m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.65               sk_D)
% 0.46/0.65          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['34'])).
% 0.46/0.65  thf('36', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.46/0.65          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.46/0.65          | ~ (m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.65               sk_D)
% 0.46/0.65          | ((sk_E) = (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.46/0.65          | ~ (m1_subset_1 @ (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.65               sk_C))),
% 0.46/0.65      inference('sup-', [status(thm)], ['15', '35'])).
% 0.46/0.65  thf('37', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.65             sk_C)
% 0.46/0.65          | ((sk_E) = (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.46/0.65          | ~ (m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.65               sk_D)
% 0.46/0.65          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['36'])).
% 0.46/0.65  thf('38', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.46/0.65          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.46/0.65          | ~ (m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.65               sk_D)
% 0.46/0.65          | ((sk_E) = (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['7', '37'])).
% 0.46/0.65  thf('39', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((sk_E) = (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))
% 0.46/0.65          | ~ (m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.65               sk_D)
% 0.46/0.65          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['38'])).
% 0.46/0.65  thf('40', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('41', plain,
% 0.46/0.65      (![X16 : $i, X17 : $i, X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.46/0.65         (((X16) = (k1_xboole_0))
% 0.46/0.65          | ((X17) = (k1_xboole_0))
% 0.46/0.65          | ((X18) = (k1_xboole_0))
% 0.46/0.65          | ((X19) = (k1_xboole_0))
% 0.46/0.65          | ~ (m1_subset_1 @ X20 @ (k4_zfmisc_1 @ X16 @ X17 @ X18 @ X19))
% 0.46/0.65          | ((X21) = (k9_mcart_1 @ X16 @ X17 @ X18 @ X19 @ X20))
% 0.46/0.65          | (m1_subset_1 @ (sk_J @ X20 @ X21 @ X19 @ X18 @ X17 @ X16) @ X19))),
% 0.46/0.65      inference('cnf', [status(esa)], [t80_mcart_1])).
% 0.46/0.65  thf('42', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.46/0.65          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.46/0.65          | ((sk_D) = (k1_xboole_0))
% 0.46/0.65          | ((sk_C) = (k1_xboole_0))
% 0.46/0.65          | ((sk_B) = (k1_xboole_0))
% 0.46/0.65          | ((sk_A) = (k1_xboole_0)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['40', '41'])).
% 0.46/0.65  thf('43', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('44', plain, (((sk_B) != (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('45', plain, (((sk_C) != (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('46', plain, (((sk_D) != (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('47', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         ((m1_subset_1 @ (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_D)
% 0.46/0.65          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)))),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)],
% 0.46/0.65                ['42', '43', '44', '45', '46'])).
% 0.46/0.65  thf('48', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.46/0.65          | ((sk_E) = (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))),
% 0.46/0.65      inference('clc', [status(thm)], ['39', '47'])).
% 0.46/0.65  thf('49', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((sk_F)
% 0.46/0.65            = (k4_mcart_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.65               (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.65               (sk_I @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.65               (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.46/0.65          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)))),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)],
% 0.46/0.65                ['18', '19', '20', '21', '22'])).
% 0.46/0.65  thf('50', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((sk_F)
% 0.46/0.65            = (k4_mcart_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.65               (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E @ 
% 0.46/0.65               (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.46/0.65          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.46/0.65          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['48', '49'])).
% 0.46/0.65  thf('51', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.46/0.65          | ((sk_F)
% 0.46/0.65              = (k4_mcart_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.65                 (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E @ 
% 0.46/0.65                 (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))))),
% 0.46/0.65      inference('simplify', [status(thm)], ['50'])).
% 0.46/0.65  thf('52', plain,
% 0.46/0.65      ((m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ sk_A @ sk_B @ sk_C @ sk_D))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('53', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.46/0.65          | ((sk_F)
% 0.46/0.65              = (k4_mcart_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.65                 (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E @ 
% 0.46/0.65                 (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A))))),
% 0.46/0.65      inference('simplify', [status(thm)], ['50'])).
% 0.46/0.65  thf(t78_mcart_1, axiom,
% 0.46/0.65    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.46/0.65     ( ( m1_subset_1 @ E @ ( k4_zfmisc_1 @ A @ B @ C @ D ) ) =>
% 0.46/0.65       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.46/0.65            ( ( C ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_xboole_0 ) ) & 
% 0.46/0.65            ( ?[F:$i,G:$i,H:$i,I:$i]:
% 0.46/0.65              ( ( ~( ( ( k8_mcart_1 @ A @ B @ C @ D @ E ) = ( F ) ) & 
% 0.46/0.65                     ( ( k9_mcart_1 @ A @ B @ C @ D @ E ) = ( G ) ) & 
% 0.46/0.65                     ( ( k10_mcart_1 @ A @ B @ C @ D @ E ) = ( H ) ) & 
% 0.46/0.65                     ( ( k11_mcart_1 @ A @ B @ C @ D @ E ) = ( I ) ) ) ) & 
% 0.46/0.65                ( ( E ) = ( k4_mcart_1 @ F @ G @ H @ I ) ) ) ) ) ) ))).
% 0.46/0.65  thf('54', plain,
% 0.46/0.65      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X11 : $i, X12 : $i, X13 : $i, 
% 0.46/0.65         X14 : $i, X15 : $i]:
% 0.46/0.65         (((X7) = (k1_xboole_0))
% 0.46/0.65          | ((X8) = (k1_xboole_0))
% 0.46/0.65          | ((X9) = (k1_xboole_0))
% 0.46/0.65          | ((X10) = (k1_xboole_0))
% 0.46/0.65          | ~ (m1_subset_1 @ X11 @ (k4_zfmisc_1 @ X10 @ X9 @ X8 @ X7))
% 0.46/0.65          | ((k10_mcart_1 @ X10 @ X9 @ X8 @ X7 @ X11) = (X15))
% 0.46/0.65          | ((X11) != (k4_mcart_1 @ X13 @ X14 @ X15 @ X12)))),
% 0.46/0.65      inference('cnf', [status(esa)], [t78_mcart_1])).
% 0.46/0.65  thf('55', plain,
% 0.46/0.65      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i, X12 : $i, X13 : $i, X14 : $i, 
% 0.46/0.65         X15 : $i]:
% 0.46/0.65         (((k10_mcart_1 @ X10 @ X9 @ X8 @ X7 @ 
% 0.46/0.65            (k4_mcart_1 @ X13 @ X14 @ X15 @ X12)) = (X15))
% 0.46/0.65          | ~ (m1_subset_1 @ (k4_mcart_1 @ X13 @ X14 @ X15 @ X12) @ 
% 0.46/0.65               (k4_zfmisc_1 @ X10 @ X9 @ X8 @ X7))
% 0.46/0.65          | ((X10) = (k1_xboole_0))
% 0.46/0.65          | ((X9) = (k1_xboole_0))
% 0.46/0.65          | ((X8) = (k1_xboole_0))
% 0.46/0.65          | ((X7) = (k1_xboole_0)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['54'])).
% 0.46/0.65  thf('56', plain,
% 0.46/0.65      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i, X4 : $i]:
% 0.46/0.65         (~ (m1_subset_1 @ sk_F @ (k4_zfmisc_1 @ X3 @ X2 @ X1 @ X0))
% 0.46/0.65          | ((X4) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.46/0.65          | ((X0) = (k1_xboole_0))
% 0.46/0.65          | ((X1) = (k1_xboole_0))
% 0.46/0.65          | ((X2) = (k1_xboole_0))
% 0.46/0.65          | ((X3) = (k1_xboole_0))
% 0.46/0.65          | ((k10_mcart_1 @ X3 @ X2 @ X1 @ X0 @ 
% 0.46/0.65              (k4_mcart_1 @ (sk_G @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.65               (sk_H @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E @ 
% 0.46/0.65               (sk_J @ sk_F @ X4 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.46/0.65              = (sk_E)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['53', '55'])).
% 0.46/0.65  thf('57', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 0.46/0.65            (k4_mcart_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.65             (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E @ 
% 0.46/0.65             (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.46/0.65            = (sk_E))
% 0.46/0.65          | ((sk_A) = (k1_xboole_0))
% 0.46/0.65          | ((sk_B) = (k1_xboole_0))
% 0.46/0.65          | ((sk_C) = (k1_xboole_0))
% 0.46/0.65          | ((sk_D) = (k1_xboole_0))
% 0.46/0.65          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)))),
% 0.46/0.65      inference('sup-', [status(thm)], ['52', '56'])).
% 0.46/0.65  thf('58', plain, (((sk_D) != (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('59', plain, (((sk_C) != (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('60', plain, (((sk_B) != (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('61', plain, (((sk_A) != (k1_xboole_0))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('62', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ 
% 0.46/0.65            (k4_mcart_1 @ (sk_G @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ 
% 0.46/0.65             (sk_H @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A) @ sk_E @ 
% 0.46/0.65             (sk_J @ sk_F @ X0 @ sk_D @ sk_C @ sk_B @ sk_A)))
% 0.46/0.65            = (sk_E))
% 0.46/0.65          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)))),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)],
% 0.46/0.65                ['57', '58', '59', '60', '61'])).
% 0.46/0.65  thf('63', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) = (sk_E))
% 0.46/0.65          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.46/0.65          | ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F)))),
% 0.46/0.65      inference('sup+', [status(thm)], ['51', '62'])).
% 0.46/0.65  thf('64', plain,
% 0.46/0.65      (![X0 : $i]:
% 0.46/0.65         (((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))
% 0.46/0.65          | ((k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F) = (sk_E)))),
% 0.46/0.65      inference('simplify', [status(thm)], ['63'])).
% 0.46/0.65  thf('65', plain,
% 0.46/0.65      (((sk_E) != (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('66', plain,
% 0.46/0.65      (![X0 : $i]: ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 0.46/0.65  thf('67', plain,
% 0.46/0.65      (![X0 : $i]: ((X0) = (k9_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))),
% 0.46/0.65      inference('simplify_reflect-', [status(thm)], ['64', '65'])).
% 0.46/0.65  thf('68', plain, (![X0 : $i, X1 : $i]: ((X1) = (X0))),
% 0.46/0.65      inference('sup+', [status(thm)], ['66', '67'])).
% 0.46/0.65  thf('69', plain,
% 0.46/0.65      (((sk_E) != (k10_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_D @ sk_F))),
% 0.46/0.65      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.46/0.65  thf('70', plain, (![X0 : $i]: ((sk_E) != (X0))),
% 0.46/0.65      inference('sup-', [status(thm)], ['68', '69'])).
% 0.46/0.65  thf('71', plain, ($false), inference('simplify', [status(thm)], ['70'])).
% 0.46/0.65  
% 0.46/0.65  % SZS output end Refutation
% 0.46/0.65  
% 0.46/0.66  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
