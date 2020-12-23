%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SvaolApkBo

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:51 EST 2020

% Result     : Theorem 0.90s
% Output     : Refutation 0.90s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 203 expanded)
%              Number of leaves         :   27 (  73 expanded)
%              Depth                    :   15
%              Number of atoms          :  938 (4073 expanded)
%              Number of equality atoms :  123 ( 584 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(t69_mcart_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
      ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( ! [F: $i] :
            ( ( m1_subset_1 @ F @ A )
           => ! [G: $i] :
                ( ( m1_subset_1 @ G @ B )
               => ! [H: $i] :
                    ( ( m1_subset_1 @ H @ C )
                   => ( ( E
                        = ( k3_mcart_1 @ F @ G @ H ) )
                     => ( D = F ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D
            = ( k5_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i,E: $i] :
        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) )
       => ( ! [F: $i] :
              ( ( m1_subset_1 @ F @ A )
             => ! [G: $i] :
                  ( ( m1_subset_1 @ G @ B )
                 => ! [H: $i] :
                      ( ( m1_subset_1 @ H @ C )
                     => ( ( E
                          = ( k3_mcart_1 @ F @ G @ H ) )
                       => ( D = F ) ) ) ) )
         => ( ( A = k1_xboole_0 )
            | ( B = k1_xboole_0 )
            | ( C = k1_xboole_0 )
            | ( D
              = ( k5_mcart_1 @ A @ B @ C @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t69_mcart_1])).

thf('0',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t48_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( D
                = ( k3_mcart_1 @ ( k5_mcart_1 @ A @ B @ C @ D ) @ ( k6_mcart_1 @ A @ B @ C @ D ) @ ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf('1',plain,(
    ! [X22: $i,X23: $i,X24: $i,X25: $i] :
      ( ( X22 = k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ( X25
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X22 @ X23 @ X24 @ X25 ) @ ( k6_mcart_1 @ X22 @ X23 @ X24 @ X25 ) @ ( k7_mcart_1 @ X22 @ X23 @ X24 @ X25 ) ) )
      | ~ ( m1_subset_1 @ X25 @ ( k3_zfmisc_1 @ X22 @ X23 @ X24 ) )
      | ( X24 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t48_mcart_1])).

thf('2',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_E
      = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
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

thf('6',plain,
    ( sk_E
    = ( k3_mcart_1 @ ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['2','3','4','5'])).

thf('7',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t50_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 )
        & ~ ! [D: $i] :
              ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
             => ( ( ( k5_mcart_1 @ A @ B @ C @ D )
                  = ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                & ( ( k6_mcart_1 @ A @ B @ C @ D )
                  = ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) )
                & ( ( k7_mcart_1 @ A @ B @ C @ D )
                  = ( k2_mcart_1 @ D ) ) ) ) ) )).

thf('8',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X26 @ X27 @ X29 @ X28 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k3_zfmisc_1 @ X26 @ X27 @ X29 ) )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('9',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('11',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('13',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['9','10','11','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('15',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X26 @ X27 @ X29 @ X28 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X28 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k3_zfmisc_1 @ X26 @ X27 @ X29 ) )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('16',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('18',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['16','17','18','19'])).

thf('21',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    ! [X26: $i,X27: $i,X28: $i,X29: $i] :
      ( ( X26 = k1_xboole_0 )
      | ( X27 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X26 @ X27 @ X29 @ X28 )
        = ( k2_mcart_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k3_zfmisc_1 @ X26 @ X27 @ X29 ) )
      | ( X29 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('23',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k2_mcart_1 @ sk_E ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('25',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('26',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['23','24','25','26'])).

thf('28',plain,
    ( sk_E
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['6','13','20','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('30',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r2_hidden @ X3 @ X4 )
      | ( v1_xboole_0 @ X4 )
      | ~ ( m1_subset_1 @ X3 @ X4 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('31',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('32',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( k3_zfmisc_1 @ X8 @ X9 @ X10 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X8 @ X9 ) @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('33',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X15 ) @ X16 )
      | ~ ( r2_hidden @ X15 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('36',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X15 ) @ X17 )
      | ~ ( r2_hidden @ X15 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('38',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('39',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('40',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k3_zfmisc_1 @ X18 @ X19 @ X20 )
       != k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('41',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf('42',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ) ),
    inference(simplify,[status(thm)],['41'])).

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
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['42','43','44','45'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('47',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('48',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( m1_subset_1 @ X30 @ sk_B )
      | ( sk_D = X31 )
      | ( sk_E
       != ( k3_mcart_1 @ X31 @ X30 @ X32 ) )
      | ~ ( m1_subset_1 @ X32 @ sk_C )
      | ~ ( m1_subset_1 @ X31 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 ) )
      | ( sk_D = X0 ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,
    ( ( sk_E != sk_E )
    | ( sk_D
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['28','50'])).

thf('52',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ) )).

thf('53',plain,(
    ! [X11: $i,X12: $i,X13: $i,X14: $i] :
      ( ( m1_subset_1 @ ( k7_mcart_1 @ X11 @ X12 @ X13 @ X14 ) @ X13 )
      | ~ ( m1_subset_1 @ X14 @ ( k3_zfmisc_1 @ X11 @ X12 @ X13 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_mcart_1])).

thf('54',plain,(
    m1_subset_1 @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_C ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['23','24','25','26'])).

thf('56',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['54','55'])).

thf('57',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['31','34'])).

thf('58',plain,(
    ! [X15: $i,X16: $i,X17: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X15 ) @ X16 )
      | ~ ( r2_hidden @ X15 @ ( k2_zfmisc_1 @ X16 @ X17 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('59',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('61',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
    | ( ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( ( k3_zfmisc_1 @ X18 @ X19 @ X20 )
       != k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ( X18 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('63',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference(simplify,[status(thm)],['63'])).

thf('65',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('67',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('68',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['64','65','66','67'])).

thf('69',plain,(
    ! [X1: $i,X2: $i] :
      ( ( m1_subset_1 @ X1 @ X2 )
      | ~ ( r2_hidden @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('70',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( sk_E != sk_E )
    | ( sk_D
      = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ),
    inference(demod,[status(thm)],['51','56','70'])).

thf('72',plain,
    ( sk_D
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    sk_D
 != ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,
    ( ( k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['9','10','11','12'])).

thf('75',plain,(
    sk_D
 != ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['73','74'])).

thf('76',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['72','75'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.SvaolApkBo
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:16:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.90/1.12  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.90/1.12  % Solved by: fo/fo7.sh
% 0.90/1.12  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.90/1.12  % done 931 iterations in 0.639s
% 0.90/1.12  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.90/1.12  % SZS output start Refutation
% 0.90/1.12  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.90/1.12  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.90/1.12  thf(sk_E_type, type, sk_E: $i).
% 0.90/1.12  thf(sk_A_type, type, sk_A: $i).
% 0.90/1.12  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.90/1.12  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.90/1.12  thf(sk_B_type, type, sk_B: $i).
% 0.90/1.12  thf(sk_C_type, type, sk_C: $i).
% 0.90/1.12  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.90/1.12  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.90/1.12  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.90/1.12  thf(sk_D_type, type, sk_D: $i).
% 0.90/1.12  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.90/1.12  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.90/1.12  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.90/1.12  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.90/1.12  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.90/1.12  thf(t69_mcart_1, conjecture,
% 0.90/1.12    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.90/1.12     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.90/1.12       ( ( ![F:$i]:
% 0.90/1.12           ( ( m1_subset_1 @ F @ A ) =>
% 0.90/1.12             ( ![G:$i]:
% 0.90/1.12               ( ( m1_subset_1 @ G @ B ) =>
% 0.90/1.12                 ( ![H:$i]:
% 0.90/1.12                   ( ( m1_subset_1 @ H @ C ) =>
% 0.90/1.12                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.90/1.12                       ( ( D ) = ( F ) ) ) ) ) ) ) ) ) =>
% 0.90/1.12         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.90/1.12           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.90/1.12           ( ( D ) = ( k5_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.90/1.12  thf(zf_stmt_0, negated_conjecture,
% 0.90/1.12    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.90/1.12        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.90/1.12          ( ( ![F:$i]:
% 0.90/1.12              ( ( m1_subset_1 @ F @ A ) =>
% 0.90/1.12                ( ![G:$i]:
% 0.90/1.12                  ( ( m1_subset_1 @ G @ B ) =>
% 0.90/1.12                    ( ![H:$i]:
% 0.90/1.12                      ( ( m1_subset_1 @ H @ C ) =>
% 0.90/1.12                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.90/1.12                          ( ( D ) = ( F ) ) ) ) ) ) ) ) ) =>
% 0.90/1.12            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.90/1.12              ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.90/1.12              ( ( D ) = ( k5_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 0.90/1.12    inference('cnf.neg', [status(esa)], [t69_mcart_1])).
% 0.90/1.12  thf('0', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf(t48_mcart_1, axiom,
% 0.90/1.12    (![A:$i,B:$i,C:$i]:
% 0.90/1.12     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.90/1.12          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.90/1.12          ( ~( ![D:$i]:
% 0.90/1.12               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.90/1.12                 ( ( D ) =
% 0.90/1.12                   ( k3_mcart_1 @
% 0.90/1.12                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.90/1.12                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.90/1.12                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.90/1.12  thf('1', plain,
% 0.90/1.12      (![X22 : $i, X23 : $i, X24 : $i, X25 : $i]:
% 0.90/1.12         (((X22) = (k1_xboole_0))
% 0.90/1.12          | ((X23) = (k1_xboole_0))
% 0.90/1.12          | ((X25)
% 0.90/1.12              = (k3_mcart_1 @ (k5_mcart_1 @ X22 @ X23 @ X24 @ X25) @ 
% 0.90/1.12                 (k6_mcart_1 @ X22 @ X23 @ X24 @ X25) @ 
% 0.90/1.12                 (k7_mcart_1 @ X22 @ X23 @ X24 @ X25)))
% 0.90/1.12          | ~ (m1_subset_1 @ X25 @ (k3_zfmisc_1 @ X22 @ X23 @ X24))
% 0.90/1.12          | ((X24) = (k1_xboole_0)))),
% 0.90/1.12      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.90/1.12  thf('2', plain,
% 0.90/1.12      ((((sk_C) = (k1_xboole_0))
% 0.90/1.12        | ((sk_E)
% 0.90/1.12            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.90/1.12               (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.90/1.12               (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 0.90/1.12        | ((sk_B) = (k1_xboole_0))
% 0.90/1.12        | ((sk_A) = (k1_xboole_0)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['0', '1'])).
% 0.90/1.12  thf('3', plain, (((sk_A) != (k1_xboole_0))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('4', plain, (((sk_B) != (k1_xboole_0))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('5', plain, (((sk_C) != (k1_xboole_0))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('6', plain,
% 0.90/1.12      (((sk_E)
% 0.90/1.12         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.90/1.12            (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.90/1.12            (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 0.90/1.12      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5'])).
% 0.90/1.12  thf('7', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf(t50_mcart_1, axiom,
% 0.90/1.12    (![A:$i,B:$i,C:$i]:
% 0.90/1.12     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.90/1.12          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.90/1.12          ( ~( ![D:$i]:
% 0.90/1.12               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.90/1.12                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.90/1.12                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.90/1.12                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.90/1.12                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.90/1.12                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.90/1.12  thf('8', plain,
% 0.90/1.12      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.90/1.12         (((X26) = (k1_xboole_0))
% 0.90/1.12          | ((X27) = (k1_xboole_0))
% 0.90/1.12          | ((k5_mcart_1 @ X26 @ X27 @ X29 @ X28)
% 0.90/1.12              = (k1_mcart_1 @ (k1_mcart_1 @ X28)))
% 0.90/1.12          | ~ (m1_subset_1 @ X28 @ (k3_zfmisc_1 @ X26 @ X27 @ X29))
% 0.90/1.12          | ((X29) = (k1_xboole_0)))),
% 0.90/1.12      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.90/1.12  thf('9', plain,
% 0.90/1.12      ((((sk_C) = (k1_xboole_0))
% 0.90/1.12        | ((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.90/1.12            = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.90/1.12        | ((sk_B) = (k1_xboole_0))
% 0.90/1.12        | ((sk_A) = (k1_xboole_0)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['7', '8'])).
% 0.90/1.12  thf('10', plain, (((sk_A) != (k1_xboole_0))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('11', plain, (((sk_B) != (k1_xboole_0))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('12', plain, (((sk_C) != (k1_xboole_0))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('13', plain,
% 0.90/1.12      (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.90/1.12         = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.90/1.12      inference('simplify_reflect-', [status(thm)], ['9', '10', '11', '12'])).
% 0.90/1.12  thf('14', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('15', plain,
% 0.90/1.12      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.90/1.12         (((X26) = (k1_xboole_0))
% 0.90/1.12          | ((X27) = (k1_xboole_0))
% 0.90/1.12          | ((k6_mcart_1 @ X26 @ X27 @ X29 @ X28)
% 0.90/1.12              = (k2_mcart_1 @ (k1_mcart_1 @ X28)))
% 0.90/1.12          | ~ (m1_subset_1 @ X28 @ (k3_zfmisc_1 @ X26 @ X27 @ X29))
% 0.90/1.12          | ((X29) = (k1_xboole_0)))),
% 0.90/1.12      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.90/1.12  thf('16', plain,
% 0.90/1.12      ((((sk_C) = (k1_xboole_0))
% 0.90/1.12        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.90/1.12            = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.90/1.12        | ((sk_B) = (k1_xboole_0))
% 0.90/1.12        | ((sk_A) = (k1_xboole_0)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['14', '15'])).
% 0.90/1.12  thf('17', plain, (((sk_A) != (k1_xboole_0))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('18', plain, (((sk_B) != (k1_xboole_0))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('19', plain, (((sk_C) != (k1_xboole_0))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('20', plain,
% 0.90/1.12      (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.90/1.12         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.90/1.12      inference('simplify_reflect-', [status(thm)], ['16', '17', '18', '19'])).
% 0.90/1.12  thf('21', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('22', plain,
% 0.90/1.12      (![X26 : $i, X27 : $i, X28 : $i, X29 : $i]:
% 0.90/1.12         (((X26) = (k1_xboole_0))
% 0.90/1.12          | ((X27) = (k1_xboole_0))
% 0.90/1.12          | ((k7_mcart_1 @ X26 @ X27 @ X29 @ X28) = (k2_mcart_1 @ X28))
% 0.90/1.12          | ~ (m1_subset_1 @ X28 @ (k3_zfmisc_1 @ X26 @ X27 @ X29))
% 0.90/1.12          | ((X29) = (k1_xboole_0)))),
% 0.90/1.12      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.90/1.12  thf('23', plain,
% 0.90/1.12      ((((sk_C) = (k1_xboole_0))
% 0.90/1.12        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))
% 0.90/1.12        | ((sk_B) = (k1_xboole_0))
% 0.90/1.12        | ((sk_A) = (k1_xboole_0)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['21', '22'])).
% 0.90/1.12  thf('24', plain, (((sk_A) != (k1_xboole_0))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('25', plain, (((sk_B) != (k1_xboole_0))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('26', plain, (((sk_C) != (k1_xboole_0))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('27', plain,
% 0.90/1.12      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 0.90/1.12      inference('simplify_reflect-', [status(thm)], ['23', '24', '25', '26'])).
% 0.90/1.12  thf('28', plain,
% 0.90/1.12      (((sk_E)
% 0.90/1.12         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.90/1.12            (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ (k2_mcart_1 @ sk_E)))),
% 0.90/1.12      inference('demod', [status(thm)], ['6', '13', '20', '27'])).
% 0.90/1.12  thf('29', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf(t2_subset, axiom,
% 0.90/1.12    (![A:$i,B:$i]:
% 0.90/1.12     ( ( m1_subset_1 @ A @ B ) =>
% 0.90/1.12       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.90/1.12  thf('30', plain,
% 0.90/1.12      (![X3 : $i, X4 : $i]:
% 0.90/1.12         ((r2_hidden @ X3 @ X4)
% 0.90/1.12          | (v1_xboole_0 @ X4)
% 0.90/1.12          | ~ (m1_subset_1 @ X3 @ X4))),
% 0.90/1.12      inference('cnf', [status(esa)], [t2_subset])).
% 0.90/1.12  thf('31', plain,
% 0.90/1.12      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.90/1.12        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['29', '30'])).
% 0.90/1.12  thf(d3_zfmisc_1, axiom,
% 0.90/1.12    (![A:$i,B:$i,C:$i]:
% 0.90/1.12     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.90/1.12       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.90/1.12  thf('32', plain,
% 0.90/1.12      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.90/1.12         ((k3_zfmisc_1 @ X8 @ X9 @ X10)
% 0.90/1.12           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X8 @ X9) @ X10))),
% 0.90/1.12      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.90/1.12  thf(t10_mcart_1, axiom,
% 0.90/1.12    (![A:$i,B:$i,C:$i]:
% 0.90/1.12     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.90/1.12       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.90/1.12         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.90/1.12  thf('33', plain,
% 0.90/1.12      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.90/1.12         ((r2_hidden @ (k1_mcart_1 @ X15) @ X16)
% 0.90/1.12          | ~ (r2_hidden @ X15 @ (k2_zfmisc_1 @ X16 @ X17)))),
% 0.90/1.12      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.90/1.12  thf('34', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.90/1.12         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.90/1.12          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['32', '33'])).
% 0.90/1.12  thf('35', plain,
% 0.90/1.12      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.90/1.12        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['31', '34'])).
% 0.90/1.12  thf('36', plain,
% 0.90/1.12      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.90/1.12         ((r2_hidden @ (k2_mcart_1 @ X15) @ X17)
% 0.90/1.12          | ~ (r2_hidden @ X15 @ (k2_zfmisc_1 @ X16 @ X17)))),
% 0.90/1.12      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.90/1.12  thf('37', plain,
% 0.90/1.12      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.90/1.12        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B))),
% 0.90/1.12      inference('sup-', [status(thm)], ['35', '36'])).
% 0.90/1.12  thf(l13_xboole_0, axiom,
% 0.90/1.12    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.90/1.12  thf('38', plain,
% 0.90/1.12      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.12      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.90/1.12  thf('39', plain,
% 0.90/1.12      (((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B)
% 0.90/1.12        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['37', '38'])).
% 0.90/1.12  thf(t35_mcart_1, axiom,
% 0.90/1.12    (![A:$i,B:$i,C:$i]:
% 0.90/1.12     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.90/1.12         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 0.90/1.12       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 0.90/1.12  thf('40', plain,
% 0.90/1.12      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.90/1.12         (((k3_zfmisc_1 @ X18 @ X19 @ X20) != (k1_xboole_0))
% 0.90/1.12          | ((X20) = (k1_xboole_0))
% 0.90/1.12          | ((X19) = (k1_xboole_0))
% 0.90/1.12          | ((X18) = (k1_xboole_0)))),
% 0.90/1.12      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.90/1.12  thf('41', plain,
% 0.90/1.12      ((((k1_xboole_0) != (k1_xboole_0))
% 0.90/1.12        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B)
% 0.90/1.12        | ((sk_A) = (k1_xboole_0))
% 0.90/1.12        | ((sk_B) = (k1_xboole_0))
% 0.90/1.12        | ((sk_C) = (k1_xboole_0)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['39', '40'])).
% 0.90/1.12  thf('42', plain,
% 0.90/1.12      ((((sk_C) = (k1_xboole_0))
% 0.90/1.12        | ((sk_B) = (k1_xboole_0))
% 0.90/1.12        | ((sk_A) = (k1_xboole_0))
% 0.90/1.12        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B))),
% 0.90/1.12      inference('simplify', [status(thm)], ['41'])).
% 0.90/1.12  thf('43', plain, (((sk_A) != (k1_xboole_0))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('44', plain, (((sk_B) != (k1_xboole_0))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('45', plain, (((sk_C) != (k1_xboole_0))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('46', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B)),
% 0.90/1.12      inference('simplify_reflect-', [status(thm)], ['42', '43', '44', '45'])).
% 0.90/1.12  thf(t1_subset, axiom,
% 0.90/1.12    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.90/1.12  thf('47', plain,
% 0.90/1.12      (![X1 : $i, X2 : $i]: ((m1_subset_1 @ X1 @ X2) | ~ (r2_hidden @ X1 @ X2))),
% 0.90/1.12      inference('cnf', [status(esa)], [t1_subset])).
% 0.90/1.12  thf('48', plain, ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B)),
% 0.90/1.12      inference('sup-', [status(thm)], ['46', '47'])).
% 0.90/1.12  thf('49', plain,
% 0.90/1.12      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.90/1.12         (~ (m1_subset_1 @ X30 @ sk_B)
% 0.90/1.12          | ((sk_D) = (X31))
% 0.90/1.12          | ((sk_E) != (k3_mcart_1 @ X31 @ X30 @ X32))
% 0.90/1.12          | ~ (m1_subset_1 @ X32 @ sk_C)
% 0.90/1.12          | ~ (m1_subset_1 @ X31 @ sk_A))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('50', plain,
% 0.90/1.12      (![X0 : $i, X1 : $i]:
% 0.90/1.12         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.90/1.12          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.90/1.12          | ((sk_E)
% 0.90/1.12              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1))
% 0.90/1.12          | ((sk_D) = (X0)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['48', '49'])).
% 0.90/1.12  thf('51', plain,
% 0.90/1.12      ((((sk_E) != (sk_E))
% 0.90/1.12        | ((sk_D) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.90/1.12        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)
% 0.90/1.12        | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.90/1.12      inference('sup-', [status(thm)], ['28', '50'])).
% 0.90/1.12  thf('52', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf(dt_k7_mcart_1, axiom,
% 0.90/1.12    (![A:$i,B:$i,C:$i,D:$i]:
% 0.90/1.12     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.90/1.12       ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ))).
% 0.90/1.12  thf('53', plain,
% 0.90/1.12      (![X11 : $i, X12 : $i, X13 : $i, X14 : $i]:
% 0.90/1.12         ((m1_subset_1 @ (k7_mcart_1 @ X11 @ X12 @ X13 @ X14) @ X13)
% 0.90/1.12          | ~ (m1_subset_1 @ X14 @ (k3_zfmisc_1 @ X11 @ X12 @ X13)))),
% 0.90/1.12      inference('cnf', [status(esa)], [dt_k7_mcart_1])).
% 0.90/1.12  thf('54', plain,
% 0.90/1.12      ((m1_subset_1 @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_C)),
% 0.90/1.12      inference('sup-', [status(thm)], ['52', '53'])).
% 0.90/1.12  thf('55', plain,
% 0.90/1.12      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 0.90/1.12      inference('simplify_reflect-', [status(thm)], ['23', '24', '25', '26'])).
% 0.90/1.12  thf('56', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)),
% 0.90/1.12      inference('demod', [status(thm)], ['54', '55'])).
% 0.90/1.12  thf('57', plain,
% 0.90/1.12      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.90/1.12        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['31', '34'])).
% 0.90/1.12  thf('58', plain,
% 0.90/1.12      (![X15 : $i, X16 : $i, X17 : $i]:
% 0.90/1.12         ((r2_hidden @ (k1_mcart_1 @ X15) @ X16)
% 0.90/1.12          | ~ (r2_hidden @ X15 @ (k2_zfmisc_1 @ X16 @ X17)))),
% 0.90/1.12      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.90/1.12  thf('59', plain,
% 0.90/1.12      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.90/1.12        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.90/1.12      inference('sup-', [status(thm)], ['57', '58'])).
% 0.90/1.12  thf('60', plain,
% 0.90/1.12      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.90/1.12      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.90/1.12  thf('61', plain,
% 0.90/1.12      (((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 0.90/1.12        | ((k3_zfmisc_1 @ sk_A @ sk_B @ sk_C) = (k1_xboole_0)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['59', '60'])).
% 0.90/1.12  thf('62', plain,
% 0.90/1.12      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.90/1.12         (((k3_zfmisc_1 @ X18 @ X19 @ X20) != (k1_xboole_0))
% 0.90/1.12          | ((X20) = (k1_xboole_0))
% 0.90/1.12          | ((X19) = (k1_xboole_0))
% 0.90/1.12          | ((X18) = (k1_xboole_0)))),
% 0.90/1.12      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.90/1.12  thf('63', plain,
% 0.90/1.12      ((((k1_xboole_0) != (k1_xboole_0))
% 0.90/1.12        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 0.90/1.12        | ((sk_A) = (k1_xboole_0))
% 0.90/1.12        | ((sk_B) = (k1_xboole_0))
% 0.90/1.12        | ((sk_C) = (k1_xboole_0)))),
% 0.90/1.12      inference('sup-', [status(thm)], ['61', '62'])).
% 0.90/1.12  thf('64', plain,
% 0.90/1.12      ((((sk_C) = (k1_xboole_0))
% 0.90/1.12        | ((sk_B) = (k1_xboole_0))
% 0.90/1.12        | ((sk_A) = (k1_xboole_0))
% 0.90/1.12        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.90/1.12      inference('simplify', [status(thm)], ['63'])).
% 0.90/1.12  thf('65', plain, (((sk_A) != (k1_xboole_0))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('66', plain, (((sk_B) != (k1_xboole_0))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('67', plain, (((sk_C) != (k1_xboole_0))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('68', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)),
% 0.90/1.12      inference('simplify_reflect-', [status(thm)], ['64', '65', '66', '67'])).
% 0.90/1.12  thf('69', plain,
% 0.90/1.12      (![X1 : $i, X2 : $i]: ((m1_subset_1 @ X1 @ X2) | ~ (r2_hidden @ X1 @ X2))),
% 0.90/1.12      inference('cnf', [status(esa)], [t1_subset])).
% 0.90/1.12  thf('70', plain, ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)),
% 0.90/1.12      inference('sup-', [status(thm)], ['68', '69'])).
% 0.90/1.12  thf('71', plain,
% 0.90/1.12      ((((sk_E) != (sk_E)) | ((sk_D) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.90/1.12      inference('demod', [status(thm)], ['51', '56', '70'])).
% 0.90/1.12  thf('72', plain, (((sk_D) = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.90/1.12      inference('simplify', [status(thm)], ['71'])).
% 0.90/1.12  thf('73', plain, (((sk_D) != (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E))),
% 0.90/1.12      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.90/1.12  thf('74', plain,
% 0.90/1.12      (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.90/1.12         = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.90/1.12      inference('simplify_reflect-', [status(thm)], ['9', '10', '11', '12'])).
% 0.90/1.12  thf('75', plain, (((sk_D) != (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.90/1.12      inference('demod', [status(thm)], ['73', '74'])).
% 0.90/1.12  thf('76', plain, ($false),
% 0.90/1.12      inference('simplify_reflect-', [status(thm)], ['72', '75'])).
% 0.90/1.12  
% 0.90/1.12  % SZS output end Refutation
% 0.90/1.12  
% 0.90/1.13  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
