%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9GLkS38W3f

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:51:54 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 211 expanded)
%              Number of leaves         :   28 (  75 expanded)
%              Depth                    :   15
%              Number of atoms          :  982 (4130 expanded)
%              Number of equality atoms :  124 ( 586 expanded)
%              Maximal formula depth    :   20 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_B_type,type,(
    sk_B: $i )).

thf(k3_zfmisc_1_type,type,(
    k3_zfmisc_1: $i > $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k3_mcart_1_type,type,(
    k3_mcart_1: $i > $i > $i > $i )).

thf(k5_mcart_1_type,type,(
    k5_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_mcart_1_type,type,(
    k2_mcart_1: $i > $i )).

thf(k7_mcart_1_type,type,(
    k7_mcart_1: $i > $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(sk_E_type,type,(
    sk_E: $i )).

thf(k1_mcart_1_type,type,(
    k1_mcart_1: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k6_mcart_1_type,type,(
    k6_mcart_1: $i > $i > $i > $i > $i )).

thf(t70_mcart_1,conjecture,(
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
                     => ( D = G ) ) ) ) )
       => ( ( A = k1_xboole_0 )
          | ( B = k1_xboole_0 )
          | ( C = k1_xboole_0 )
          | ( D
            = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )).

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
                       => ( D = G ) ) ) ) )
         => ( ( A = k1_xboole_0 )
            | ( B = k1_xboole_0 )
            | ( C = k1_xboole_0 )
            | ( D
              = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t70_mcart_1])).

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
    ! [X23: $i,X24: $i,X25: $i,X26: $i] :
      ( ( X23 = k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ( X26
        = ( k3_mcart_1 @ ( k5_mcart_1 @ X23 @ X24 @ X25 @ X26 ) @ ( k6_mcart_1 @ X23 @ X24 @ X25 @ X26 ) @ ( k7_mcart_1 @ X23 @ X24 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X26 @ ( k3_zfmisc_1 @ X23 @ X24 @ X25 ) )
      | ( X25 = k1_xboole_0 ) ) ),
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
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( X27 = k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ( ( k5_mcart_1 @ X27 @ X28 @ X30 @ X29 )
        = ( k1_mcart_1 @ ( k1_mcart_1 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k3_zfmisc_1 @ X27 @ X28 @ X30 ) )
      | ( X30 = k1_xboole_0 ) ) ),
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

thf('14',plain,
    ( sk_E
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['6','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( X27 = k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ( ( k6_mcart_1 @ X27 @ X28 @ X30 @ X29 )
        = ( k2_mcart_1 @ ( k1_mcart_1 @ X29 ) ) )
      | ~ ( m1_subset_1 @ X29 @ ( k3_zfmisc_1 @ X27 @ X28 @ X30 ) )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('17',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('21',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['17','18','19','20'])).

thf('22',plain,
    ( sk_E
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ) ),
    inference(demod,[status(thm)],['14','21'])).

thf('23',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('24',plain,(
    ! [X27: $i,X28: $i,X29: $i,X30: $i] :
      ( ( X27 = k1_xboole_0 )
      | ( X28 = k1_xboole_0 )
      | ( ( k7_mcart_1 @ X27 @ X28 @ X30 @ X29 )
        = ( k2_mcart_1 @ X29 ) )
      | ~ ( m1_subset_1 @ X29 @ ( k3_zfmisc_1 @ X27 @ X28 @ X30 ) )
      | ( X30 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t50_mcart_1])).

thf('25',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
      = ( k2_mcart_1 @ sk_E ) )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('29',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['25','26','27','28'])).

thf('30',plain,
    ( sk_E
    = ( k3_mcart_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ ( k2_mcart_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['22','29'])).

thf('31',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('32',plain,(
    ! [X4: $i,X5: $i] :
      ( ( r2_hidden @ X4 @ X5 )
      | ( v1_xboole_0 @ X5 )
      | ~ ( m1_subset_1 @ X4 @ X5 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf(d3_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( k3_zfmisc_1 @ A @ B @ C )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ) )).

thf('34',plain,(
    ! [X9: $i,X10: $i,X11: $i] :
      ( ( k3_zfmisc_1 @ X9 @ X10 @ X11 )
      = ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) @ X11 ) ) ),
    inference(cnf,[status(esa)],[d3_zfmisc_1])).

thf(t10_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) )
     => ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B )
        & ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ) )).

thf('35',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X16 ) @ X17 )
      | ~ ( r2_hidden @ X16 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('36',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k3_zfmisc_1 @ X2 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k1_mcart_1 @ X3 ) @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('38',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ ( k2_mcart_1 @ X16 ) @ X18 )
      | ~ ( r2_hidden @ X16 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('39',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('40',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('41',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 )
      | ( X0 = X1 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('42',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B )
    | ( k1_xboole_0
      = ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['39','42'])).

thf(t35_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ( C != k1_xboole_0 ) )
    <=> ( ( k3_zfmisc_1 @ A @ B @ C )
       != k1_xboole_0 ) ) )).

thf('44',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k3_zfmisc_1 @ X19 @ X20 @ X21 )
       != k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('45',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ) ),
    inference(simplify,[status(thm)],['45'])).

thf('47',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('48',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('49',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('50',plain,(
    r2_hidden @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ),
    inference('simplify_reflect-',[status(thm)],['46','47','48','49'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('51',plain,(
    ! [X2: $i,X3: $i] :
      ( ( m1_subset_1 @ X2 @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('52',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_B ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ~ ( m1_subset_1 @ X31 @ sk_B )
      | ( sk_D = X31 )
      | ( sk_E
       != ( k3_mcart_1 @ X32 @ X31 @ X33 ) )
      | ~ ( m1_subset_1 @ X33 @ sk_C )
      | ~ ( m1_subset_1 @ X32 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('54',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 ) )
      | ( sk_D
        = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    sk_D
 != ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ( k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference('simplify_reflect-',[status(thm)],['17','18','19','20'])).

thf('57',plain,(
    sk_D
 != ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) ),
    inference(demod,[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( m1_subset_1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X1 @ sk_C )
      | ( sk_E
       != ( k3_mcart_1 @ X0 @ ( k2_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ X1 ) ) ) ),
    inference('simplify_reflect-',[status(thm)],['54','57'])).

thf('59',plain,
    ( ( sk_E != sk_E )
    | ~ ( m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C )
    | ~ ( m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['30','58'])).

thf('60',plain,(
    m1_subset_1 @ sk_E @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(dt_k7_mcart_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) )
     => ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ) )).

thf('61',plain,(
    ! [X12: $i,X13: $i,X14: $i,X15: $i] :
      ( ( m1_subset_1 @ ( k7_mcart_1 @ X12 @ X13 @ X14 @ X15 ) @ X14 )
      | ~ ( m1_subset_1 @ X15 @ ( k3_zfmisc_1 @ X12 @ X13 @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_mcart_1])).

thf('62',plain,(
    m1_subset_1 @ ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E ) @ sk_C ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E )
    = ( k2_mcart_1 @ sk_E ) ),
    inference('simplify_reflect-',[status(thm)],['25','26','27','28'])).

thf('64',plain,(
    m1_subset_1 @ ( k2_mcart_1 @ sk_E ) @ sk_C ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ sk_E ) @ ( k2_zfmisc_1 @ sk_A @ sk_B ) ) ),
    inference('sup-',[status(thm)],['33','36'])).

thf('66',plain,(
    ! [X16: $i,X17: $i,X18: $i] :
      ( ( r2_hidden @ ( k1_mcart_1 @ X16 ) @ X17 )
      | ~ ( r2_hidden @ X16 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) ) ),
    inference(cnf,[status(esa)],[t10_mcart_1])).

thf('67',plain,
    ( ( v1_xboole_0 @ ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('69',plain,
    ( ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
    | ( k1_xboole_0
      = ( k3_zfmisc_1 @ sk_A @ sk_B @ sk_C ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ( ( k3_zfmisc_1 @ X19 @ X20 @ X21 )
       != k1_xboole_0 )
      | ( X21 = k1_xboole_0 )
      | ( X20 = k1_xboole_0 )
      | ( X19 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t35_mcart_1])).

thf('71',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A )
    | ( sk_A = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_C = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf('72',plain,
    ( ( sk_C = k1_xboole_0 )
    | ( sk_B = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 )
    | ( r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ) ),
    inference(simplify,[status(thm)],['71'])).

thf('73',plain,(
    sk_A != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('74',plain,(
    sk_B != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('75',plain,(
    sk_C != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('76',plain,(
    r2_hidden @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ),
    inference('simplify_reflect-',[status(thm)],['72','73','74','75'])).

thf('77',plain,(
    ! [X2: $i,X3: $i] :
      ( ( m1_subset_1 @ X2 @ X3 )
      | ~ ( r2_hidden @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('78',plain,(
    m1_subset_1 @ ( k1_mcart_1 @ ( k1_mcart_1 @ sk_E ) ) @ sk_A ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    sk_E != sk_E ),
    inference(demod,[status(thm)],['59','64','78'])).

thf('80',plain,(
    $false ),
    inference(simplify,[status(thm)],['79'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.9GLkS38W3f
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:57:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.59/0.85  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.85  % Solved by: fo/fo7.sh
% 0.59/0.85  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.85  % done 912 iterations in 0.390s
% 0.59/0.85  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.85  % SZS output start Refutation
% 0.59/0.85  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.85  thf(k3_zfmisc_1_type, type, k3_zfmisc_1: $i > $i > $i > $i).
% 0.59/0.85  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.85  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.59/0.85  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.85  thf(k3_mcart_1_type, type, k3_mcart_1: $i > $i > $i > $i).
% 0.59/0.85  thf(k5_mcart_1_type, type, k5_mcart_1: $i > $i > $i > $i > $i).
% 0.59/0.85  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.85  thf(k2_mcart_1_type, type, k2_mcart_1: $i > $i).
% 0.59/0.85  thf(k7_mcart_1_type, type, k7_mcart_1: $i > $i > $i > $i > $i).
% 0.59/0.85  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.85  thf(sk_D_type, type, sk_D: $i).
% 0.59/0.85  thf(sk_E_type, type, sk_E: $i).
% 0.59/0.85  thf(k1_mcart_1_type, type, k1_mcart_1: $i > $i).
% 0.59/0.85  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.85  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.59/0.85  thf(k6_mcart_1_type, type, k6_mcart_1: $i > $i > $i > $i > $i).
% 0.59/0.85  thf(t70_mcart_1, conjecture,
% 0.59/0.85    (![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.59/0.85     ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.59/0.85       ( ( ![F:$i]:
% 0.59/0.85           ( ( m1_subset_1 @ F @ A ) =>
% 0.59/0.85             ( ![G:$i]:
% 0.59/0.85               ( ( m1_subset_1 @ G @ B ) =>
% 0.59/0.85                 ( ![H:$i]:
% 0.59/0.85                   ( ( m1_subset_1 @ H @ C ) =>
% 0.59/0.85                     ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.59/0.85                       ( ( D ) = ( G ) ) ) ) ) ) ) ) ) =>
% 0.59/0.85         ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.59/0.85           ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.59/0.85           ( ( D ) = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ))).
% 0.59/0.85  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.85    (~( ![A:$i,B:$i,C:$i,D:$i,E:$i]:
% 0.59/0.85        ( ( m1_subset_1 @ E @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.59/0.85          ( ( ![F:$i]:
% 0.59/0.85              ( ( m1_subset_1 @ F @ A ) =>
% 0.59/0.85                ( ![G:$i]:
% 0.59/0.85                  ( ( m1_subset_1 @ G @ B ) =>
% 0.59/0.85                    ( ![H:$i]:
% 0.59/0.85                      ( ( m1_subset_1 @ H @ C ) =>
% 0.59/0.85                        ( ( ( E ) = ( k3_mcart_1 @ F @ G @ H ) ) =>
% 0.59/0.85                          ( ( D ) = ( G ) ) ) ) ) ) ) ) ) =>
% 0.59/0.85            ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) | 
% 0.59/0.85              ( ( C ) = ( k1_xboole_0 ) ) | 
% 0.59/0.85              ( ( D ) = ( k6_mcart_1 @ A @ B @ C @ E ) ) ) ) ) )),
% 0.59/0.85    inference('cnf.neg', [status(esa)], [t70_mcart_1])).
% 0.59/0.85  thf('0', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf(t48_mcart_1, axiom,
% 0.59/0.85    (![A:$i,B:$i,C:$i]:
% 0.59/0.85     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.59/0.85          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.59/0.85          ( ~( ![D:$i]:
% 0.59/0.85               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.59/0.85                 ( ( D ) =
% 0.59/0.85                   ( k3_mcart_1 @
% 0.59/0.85                     ( k5_mcart_1 @ A @ B @ C @ D ) @ 
% 0.59/0.85                     ( k6_mcart_1 @ A @ B @ C @ D ) @ 
% 0.59/0.85                     ( k7_mcart_1 @ A @ B @ C @ D ) ) ) ) ) ) ) ))).
% 0.59/0.85  thf('1', plain,
% 0.59/0.85      (![X23 : $i, X24 : $i, X25 : $i, X26 : $i]:
% 0.59/0.85         (((X23) = (k1_xboole_0))
% 0.59/0.85          | ((X24) = (k1_xboole_0))
% 0.59/0.85          | ((X26)
% 0.59/0.85              = (k3_mcart_1 @ (k5_mcart_1 @ X23 @ X24 @ X25 @ X26) @ 
% 0.59/0.85                 (k6_mcart_1 @ X23 @ X24 @ X25 @ X26) @ 
% 0.59/0.85                 (k7_mcart_1 @ X23 @ X24 @ X25 @ X26)))
% 0.59/0.85          | ~ (m1_subset_1 @ X26 @ (k3_zfmisc_1 @ X23 @ X24 @ X25))
% 0.59/0.85          | ((X25) = (k1_xboole_0)))),
% 0.59/0.85      inference('cnf', [status(esa)], [t48_mcart_1])).
% 0.59/0.85  thf('2', plain,
% 0.59/0.85      ((((sk_C) = (k1_xboole_0))
% 0.59/0.85        | ((sk_E)
% 0.59/0.85            = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.59/0.85               (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.59/0.85               (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)))
% 0.59/0.85        | ((sk_B) = (k1_xboole_0))
% 0.59/0.85        | ((sk_A) = (k1_xboole_0)))),
% 0.59/0.85      inference('sup-', [status(thm)], ['0', '1'])).
% 0.59/0.85  thf('3', plain, (((sk_A) != (k1_xboole_0))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('4', plain, (((sk_B) != (k1_xboole_0))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('5', plain, (((sk_C) != (k1_xboole_0))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('6', plain,
% 0.59/0.85      (((sk_E)
% 0.59/0.85         = (k3_mcart_1 @ (k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.59/0.85            (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.59/0.85            (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 0.59/0.85      inference('simplify_reflect-', [status(thm)], ['2', '3', '4', '5'])).
% 0.59/0.85  thf('7', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf(t50_mcart_1, axiom,
% 0.59/0.85    (![A:$i,B:$i,C:$i]:
% 0.59/0.85     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.59/0.85          ( ( C ) != ( k1_xboole_0 ) ) & 
% 0.59/0.85          ( ~( ![D:$i]:
% 0.59/0.85               ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.59/0.85                 ( ( ( k5_mcart_1 @ A @ B @ C @ D ) =
% 0.59/0.85                     ( k1_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.59/0.85                   ( ( k6_mcart_1 @ A @ B @ C @ D ) =
% 0.59/0.85                     ( k2_mcart_1 @ ( k1_mcart_1 @ D ) ) ) & 
% 0.59/0.85                   ( ( k7_mcart_1 @ A @ B @ C @ D ) = ( k2_mcart_1 @ D ) ) ) ) ) ) ) ))).
% 0.59/0.85  thf('8', plain,
% 0.59/0.85      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.59/0.85         (((X27) = (k1_xboole_0))
% 0.59/0.85          | ((X28) = (k1_xboole_0))
% 0.59/0.85          | ((k5_mcart_1 @ X27 @ X28 @ X30 @ X29)
% 0.59/0.85              = (k1_mcart_1 @ (k1_mcart_1 @ X29)))
% 0.59/0.85          | ~ (m1_subset_1 @ X29 @ (k3_zfmisc_1 @ X27 @ X28 @ X30))
% 0.59/0.85          | ((X30) = (k1_xboole_0)))),
% 0.59/0.85      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.59/0.85  thf('9', plain,
% 0.59/0.85      ((((sk_C) = (k1_xboole_0))
% 0.59/0.85        | ((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.59/0.85            = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.59/0.85        | ((sk_B) = (k1_xboole_0))
% 0.59/0.85        | ((sk_A) = (k1_xboole_0)))),
% 0.59/0.85      inference('sup-', [status(thm)], ['7', '8'])).
% 0.59/0.85  thf('10', plain, (((sk_A) != (k1_xboole_0))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('11', plain, (((sk_B) != (k1_xboole_0))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('12', plain, (((sk_C) != (k1_xboole_0))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('13', plain,
% 0.59/0.85      (((k5_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.59/0.85         = (k1_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.59/0.85      inference('simplify_reflect-', [status(thm)], ['9', '10', '11', '12'])).
% 0.59/0.85  thf('14', plain,
% 0.59/0.85      (((sk_E)
% 0.59/0.85         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.59/0.85            (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ 
% 0.59/0.85            (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 0.59/0.85      inference('demod', [status(thm)], ['6', '13'])).
% 0.59/0.85  thf('15', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('16', plain,
% 0.59/0.85      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.59/0.85         (((X27) = (k1_xboole_0))
% 0.59/0.85          | ((X28) = (k1_xboole_0))
% 0.59/0.85          | ((k6_mcart_1 @ X27 @ X28 @ X30 @ X29)
% 0.59/0.85              = (k2_mcart_1 @ (k1_mcart_1 @ X29)))
% 0.59/0.85          | ~ (m1_subset_1 @ X29 @ (k3_zfmisc_1 @ X27 @ X28 @ X30))
% 0.59/0.85          | ((X30) = (k1_xboole_0)))),
% 0.59/0.85      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.59/0.85  thf('17', plain,
% 0.59/0.85      ((((sk_C) = (k1_xboole_0))
% 0.59/0.85        | ((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.59/0.85            = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))
% 0.59/0.85        | ((sk_B) = (k1_xboole_0))
% 0.59/0.85        | ((sk_A) = (k1_xboole_0)))),
% 0.59/0.85      inference('sup-', [status(thm)], ['15', '16'])).
% 0.59/0.85  thf('18', plain, (((sk_A) != (k1_xboole_0))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('19', plain, (((sk_B) != (k1_xboole_0))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('20', plain, (((sk_C) != (k1_xboole_0))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('21', plain,
% 0.59/0.85      (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.59/0.85         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.59/0.85      inference('simplify_reflect-', [status(thm)], ['17', '18', '19', '20'])).
% 0.59/0.85  thf('22', plain,
% 0.59/0.85      (((sk_E)
% 0.59/0.85         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.59/0.85            (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.59/0.85            (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)))),
% 0.59/0.85      inference('demod', [status(thm)], ['14', '21'])).
% 0.59/0.85  thf('23', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('24', plain,
% 0.59/0.85      (![X27 : $i, X28 : $i, X29 : $i, X30 : $i]:
% 0.59/0.85         (((X27) = (k1_xboole_0))
% 0.59/0.85          | ((X28) = (k1_xboole_0))
% 0.59/0.85          | ((k7_mcart_1 @ X27 @ X28 @ X30 @ X29) = (k2_mcart_1 @ X29))
% 0.59/0.85          | ~ (m1_subset_1 @ X29 @ (k3_zfmisc_1 @ X27 @ X28 @ X30))
% 0.59/0.85          | ((X30) = (k1_xboole_0)))),
% 0.59/0.85      inference('cnf', [status(esa)], [t50_mcart_1])).
% 0.59/0.85  thf('25', plain,
% 0.59/0.85      ((((sk_C) = (k1_xboole_0))
% 0.59/0.85        | ((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))
% 0.59/0.85        | ((sk_B) = (k1_xboole_0))
% 0.59/0.85        | ((sk_A) = (k1_xboole_0)))),
% 0.59/0.85      inference('sup-', [status(thm)], ['23', '24'])).
% 0.59/0.85  thf('26', plain, (((sk_A) != (k1_xboole_0))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('27', plain, (((sk_B) != (k1_xboole_0))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('28', plain, (((sk_C) != (k1_xboole_0))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('29', plain,
% 0.59/0.85      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 0.59/0.85      inference('simplify_reflect-', [status(thm)], ['25', '26', '27', '28'])).
% 0.59/0.85  thf('30', plain,
% 0.59/0.85      (((sk_E)
% 0.59/0.85         = (k3_mcart_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ 
% 0.59/0.85            (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ (k2_mcart_1 @ sk_E)))),
% 0.59/0.85      inference('demod', [status(thm)], ['22', '29'])).
% 0.59/0.85  thf('31', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf(t2_subset, axiom,
% 0.59/0.85    (![A:$i,B:$i]:
% 0.59/0.85     ( ( m1_subset_1 @ A @ B ) =>
% 0.59/0.85       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.59/0.85  thf('32', plain,
% 0.59/0.85      (![X4 : $i, X5 : $i]:
% 0.59/0.85         ((r2_hidden @ X4 @ X5)
% 0.59/0.85          | (v1_xboole_0 @ X5)
% 0.59/0.85          | ~ (m1_subset_1 @ X4 @ X5))),
% 0.59/0.85      inference('cnf', [status(esa)], [t2_subset])).
% 0.59/0.85  thf('33', plain,
% 0.59/0.85      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.85        | (r2_hidden @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.59/0.85      inference('sup-', [status(thm)], ['31', '32'])).
% 0.59/0.85  thf(d3_zfmisc_1, axiom,
% 0.59/0.85    (![A:$i,B:$i,C:$i]:
% 0.59/0.85     ( ( k3_zfmisc_1 @ A @ B @ C ) =
% 0.59/0.85       ( k2_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) @ C ) ))).
% 0.59/0.85  thf('34', plain,
% 0.59/0.85      (![X9 : $i, X10 : $i, X11 : $i]:
% 0.59/0.85         ((k3_zfmisc_1 @ X9 @ X10 @ X11)
% 0.59/0.85           = (k2_zfmisc_1 @ (k2_zfmisc_1 @ X9 @ X10) @ X11))),
% 0.59/0.85      inference('cnf', [status(esa)], [d3_zfmisc_1])).
% 0.59/0.85  thf(t10_mcart_1, axiom,
% 0.59/0.85    (![A:$i,B:$i,C:$i]:
% 0.59/0.85     ( ( r2_hidden @ A @ ( k2_zfmisc_1 @ B @ C ) ) =>
% 0.59/0.85       ( ( r2_hidden @ ( k1_mcart_1 @ A ) @ B ) & 
% 0.59/0.85         ( r2_hidden @ ( k2_mcart_1 @ A ) @ C ) ) ))).
% 0.59/0.85  thf('35', plain,
% 0.59/0.85      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.59/0.85         ((r2_hidden @ (k1_mcart_1 @ X16) @ X17)
% 0.59/0.85          | ~ (r2_hidden @ X16 @ (k2_zfmisc_1 @ X17 @ X18)))),
% 0.59/0.85      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.59/0.85  thf('36', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.59/0.85         (~ (r2_hidden @ X3 @ (k3_zfmisc_1 @ X2 @ X1 @ X0))
% 0.59/0.85          | (r2_hidden @ (k1_mcart_1 @ X3) @ (k2_zfmisc_1 @ X2 @ X1)))),
% 0.59/0.85      inference('sup-', [status(thm)], ['34', '35'])).
% 0.59/0.85  thf('37', plain,
% 0.59/0.85      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.85        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.85      inference('sup-', [status(thm)], ['33', '36'])).
% 0.59/0.85  thf('38', plain,
% 0.59/0.85      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.59/0.85         ((r2_hidden @ (k2_mcart_1 @ X16) @ X18)
% 0.59/0.85          | ~ (r2_hidden @ X16 @ (k2_zfmisc_1 @ X17 @ X18)))),
% 0.59/0.85      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.59/0.85  thf('39', plain,
% 0.59/0.85      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.85        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B))),
% 0.59/0.85      inference('sup-', [status(thm)], ['37', '38'])).
% 0.59/0.85  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.59/0.85  thf('40', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.59/0.85      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.59/0.85  thf(t8_boole, axiom,
% 0.59/0.85    (![A:$i,B:$i]:
% 0.59/0.85     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.59/0.85  thf('41', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         (~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1) | ((X0) = (X1)))),
% 0.59/0.85      inference('cnf', [status(esa)], [t8_boole])).
% 0.59/0.85  thf('42', plain,
% 0.59/0.85      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.85      inference('sup-', [status(thm)], ['40', '41'])).
% 0.59/0.85  thf('43', plain,
% 0.59/0.85      (((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B)
% 0.59/0.85        | ((k1_xboole_0) = (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.59/0.85      inference('sup-', [status(thm)], ['39', '42'])).
% 0.59/0.85  thf(t35_mcart_1, axiom,
% 0.59/0.85    (![A:$i,B:$i,C:$i]:
% 0.59/0.85     ( ( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.59/0.85         ( ( C ) != ( k1_xboole_0 ) ) ) <=>
% 0.59/0.85       ( ( k3_zfmisc_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) ))).
% 0.59/0.85  thf('44', plain,
% 0.59/0.85      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.59/0.85         (((k3_zfmisc_1 @ X19 @ X20 @ X21) != (k1_xboole_0))
% 0.59/0.85          | ((X21) = (k1_xboole_0))
% 0.59/0.85          | ((X20) = (k1_xboole_0))
% 0.59/0.85          | ((X19) = (k1_xboole_0)))),
% 0.59/0.85      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.59/0.85  thf('45', plain,
% 0.59/0.85      ((((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.85        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B)
% 0.59/0.85        | ((sk_A) = (k1_xboole_0))
% 0.59/0.85        | ((sk_B) = (k1_xboole_0))
% 0.59/0.85        | ((sk_C) = (k1_xboole_0)))),
% 0.59/0.85      inference('sup-', [status(thm)], ['43', '44'])).
% 0.59/0.85  thf('46', plain,
% 0.59/0.85      ((((sk_C) = (k1_xboole_0))
% 0.59/0.85        | ((sk_B) = (k1_xboole_0))
% 0.59/0.85        | ((sk_A) = (k1_xboole_0))
% 0.59/0.85        | (r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B))),
% 0.59/0.85      inference('simplify', [status(thm)], ['45'])).
% 0.59/0.85  thf('47', plain, (((sk_A) != (k1_xboole_0))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('48', plain, (((sk_B) != (k1_xboole_0))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('49', plain, (((sk_C) != (k1_xboole_0))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('50', plain, ((r2_hidden @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B)),
% 0.59/0.85      inference('simplify_reflect-', [status(thm)], ['46', '47', '48', '49'])).
% 0.59/0.85  thf(t1_subset, axiom,
% 0.59/0.85    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.59/0.85  thf('51', plain,
% 0.59/0.85      (![X2 : $i, X3 : $i]: ((m1_subset_1 @ X2 @ X3) | ~ (r2_hidden @ X2 @ X3))),
% 0.59/0.85      inference('cnf', [status(esa)], [t1_subset])).
% 0.59/0.85  thf('52', plain, ((m1_subset_1 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_B)),
% 0.59/0.85      inference('sup-', [status(thm)], ['50', '51'])).
% 0.59/0.85  thf('53', plain,
% 0.59/0.85      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.59/0.85         (~ (m1_subset_1 @ X31 @ sk_B)
% 0.59/0.85          | ((sk_D) = (X31))
% 0.59/0.85          | ((sk_E) != (k3_mcart_1 @ X32 @ X31 @ X33))
% 0.59/0.85          | ~ (m1_subset_1 @ X33 @ sk_C)
% 0.59/0.85          | ~ (m1_subset_1 @ X32 @ sk_A))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('54', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.59/0.85          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.59/0.85          | ((sk_E)
% 0.59/0.85              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1))
% 0.59/0.85          | ((sk_D) = (k2_mcart_1 @ (k1_mcart_1 @ sk_E))))),
% 0.59/0.85      inference('sup-', [status(thm)], ['52', '53'])).
% 0.59/0.85  thf('55', plain, (((sk_D) != (k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('56', plain,
% 0.59/0.85      (((k6_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E)
% 0.59/0.85         = (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.59/0.85      inference('simplify_reflect-', [status(thm)], ['17', '18', '19', '20'])).
% 0.59/0.85  thf('57', plain, (((sk_D) != (k2_mcart_1 @ (k1_mcart_1 @ sk_E)))),
% 0.59/0.85      inference('demod', [status(thm)], ['55', '56'])).
% 0.59/0.85  thf('58', plain,
% 0.59/0.85      (![X0 : $i, X1 : $i]:
% 0.59/0.85         (~ (m1_subset_1 @ X0 @ sk_A)
% 0.59/0.85          | ~ (m1_subset_1 @ X1 @ sk_C)
% 0.59/0.85          | ((sk_E)
% 0.59/0.85              != (k3_mcart_1 @ X0 @ (k2_mcart_1 @ (k1_mcart_1 @ sk_E)) @ X1)))),
% 0.59/0.85      inference('simplify_reflect-', [status(thm)], ['54', '57'])).
% 0.59/0.85  thf('59', plain,
% 0.59/0.85      ((((sk_E) != (sk_E))
% 0.59/0.85        | ~ (m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)
% 0.59/0.85        | ~ (m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.59/0.85      inference('sup-', [status(thm)], ['30', '58'])).
% 0.59/0.85  thf('60', plain, ((m1_subset_1 @ sk_E @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf(dt_k7_mcart_1, axiom,
% 0.59/0.85    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.85     ( ( m1_subset_1 @ D @ ( k3_zfmisc_1 @ A @ B @ C ) ) =>
% 0.59/0.85       ( m1_subset_1 @ ( k7_mcart_1 @ A @ B @ C @ D ) @ C ) ))).
% 0.59/0.85  thf('61', plain,
% 0.59/0.85      (![X12 : $i, X13 : $i, X14 : $i, X15 : $i]:
% 0.59/0.85         ((m1_subset_1 @ (k7_mcart_1 @ X12 @ X13 @ X14 @ X15) @ X14)
% 0.59/0.85          | ~ (m1_subset_1 @ X15 @ (k3_zfmisc_1 @ X12 @ X13 @ X14)))),
% 0.59/0.85      inference('cnf', [status(esa)], [dt_k7_mcart_1])).
% 0.59/0.85  thf('62', plain,
% 0.59/0.85      ((m1_subset_1 @ (k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) @ sk_C)),
% 0.59/0.85      inference('sup-', [status(thm)], ['60', '61'])).
% 0.59/0.85  thf('63', plain,
% 0.59/0.85      (((k7_mcart_1 @ sk_A @ sk_B @ sk_C @ sk_E) = (k2_mcart_1 @ sk_E))),
% 0.59/0.85      inference('simplify_reflect-', [status(thm)], ['25', '26', '27', '28'])).
% 0.59/0.85  thf('64', plain, ((m1_subset_1 @ (k2_mcart_1 @ sk_E) @ sk_C)),
% 0.59/0.85      inference('demod', [status(thm)], ['62', '63'])).
% 0.59/0.85  thf('65', plain,
% 0.59/0.85      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.85        | (r2_hidden @ (k1_mcart_1 @ sk_E) @ (k2_zfmisc_1 @ sk_A @ sk_B)))),
% 0.59/0.85      inference('sup-', [status(thm)], ['33', '36'])).
% 0.59/0.85  thf('66', plain,
% 0.59/0.85      (![X16 : $i, X17 : $i, X18 : $i]:
% 0.59/0.85         ((r2_hidden @ (k1_mcart_1 @ X16) @ X17)
% 0.59/0.85          | ~ (r2_hidden @ X16 @ (k2_zfmisc_1 @ X17 @ X18)))),
% 0.59/0.85      inference('cnf', [status(esa)], [t10_mcart_1])).
% 0.59/0.85  thf('67', plain,
% 0.59/0.85      (((v1_xboole_0 @ (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C))
% 0.59/0.85        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.59/0.85      inference('sup-', [status(thm)], ['65', '66'])).
% 0.59/0.85  thf('68', plain,
% 0.59/0.85      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.59/0.85      inference('sup-', [status(thm)], ['40', '41'])).
% 0.59/0.85  thf('69', plain,
% 0.59/0.85      (((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 0.59/0.85        | ((k1_xboole_0) = (k3_zfmisc_1 @ sk_A @ sk_B @ sk_C)))),
% 0.59/0.85      inference('sup-', [status(thm)], ['67', '68'])).
% 0.59/0.85  thf('70', plain,
% 0.59/0.85      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.59/0.85         (((k3_zfmisc_1 @ X19 @ X20 @ X21) != (k1_xboole_0))
% 0.59/0.85          | ((X21) = (k1_xboole_0))
% 0.59/0.85          | ((X20) = (k1_xboole_0))
% 0.59/0.85          | ((X19) = (k1_xboole_0)))),
% 0.59/0.85      inference('cnf', [status(esa)], [t35_mcart_1])).
% 0.59/0.85  thf('71', plain,
% 0.59/0.85      ((((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.85        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)
% 0.59/0.85        | ((sk_A) = (k1_xboole_0))
% 0.59/0.85        | ((sk_B) = (k1_xboole_0))
% 0.59/0.85        | ((sk_C) = (k1_xboole_0)))),
% 0.59/0.85      inference('sup-', [status(thm)], ['69', '70'])).
% 0.59/0.85  thf('72', plain,
% 0.59/0.85      ((((sk_C) = (k1_xboole_0))
% 0.59/0.85        | ((sk_B) = (k1_xboole_0))
% 0.59/0.85        | ((sk_A) = (k1_xboole_0))
% 0.59/0.85        | (r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A))),
% 0.59/0.85      inference('simplify', [status(thm)], ['71'])).
% 0.59/0.85  thf('73', plain, (((sk_A) != (k1_xboole_0))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('74', plain, (((sk_B) != (k1_xboole_0))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('75', plain, (((sk_C) != (k1_xboole_0))),
% 0.59/0.85      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.85  thf('76', plain, ((r2_hidden @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)),
% 0.59/0.85      inference('simplify_reflect-', [status(thm)], ['72', '73', '74', '75'])).
% 0.59/0.85  thf('77', plain,
% 0.59/0.85      (![X2 : $i, X3 : $i]: ((m1_subset_1 @ X2 @ X3) | ~ (r2_hidden @ X2 @ X3))),
% 0.59/0.85      inference('cnf', [status(esa)], [t1_subset])).
% 0.59/0.85  thf('78', plain, ((m1_subset_1 @ (k1_mcart_1 @ (k1_mcart_1 @ sk_E)) @ sk_A)),
% 0.59/0.85      inference('sup-', [status(thm)], ['76', '77'])).
% 0.59/0.85  thf('79', plain, (((sk_E) != (sk_E))),
% 0.59/0.85      inference('demod', [status(thm)], ['59', '64', '78'])).
% 0.59/0.85  thf('80', plain, ($false), inference('simplify', [status(thm)], ['79'])).
% 0.59/0.85  
% 0.59/0.85  % SZS output end Refutation
% 0.59/0.85  
% 0.72/0.86  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
