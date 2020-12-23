%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.y1BGzeaTBh

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 365 expanded)
%              Number of leaves         :   36 ( 123 expanded)
%              Depth                    :   16
%              Number of atoms          :  628 (3541 expanded)
%              Number of equality atoms :   46 ( 170 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_C_2_type,type,(
    sk_C_2: $i )).

thf(r1_xboole_0_type,type,(
    r1_xboole_0: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(t49_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
             => ~ ( ( ( k1_relset_1 @ A @ B @ C )
                   != k1_xboole_0 )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ B )
                     => ~ ( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
               => ~ ( ( ( k1_relset_1 @ A @ B @ C )
                     != k1_xboole_0 )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ B )
                       => ~ ( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t49_relset_1])).

thf('1',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('2',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v4_relat_1 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('3',plain,(
    v4_relat_1 @ sk_C_2 @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('4',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v4_relat_1 @ X17 @ X18 )
      | ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('5',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('7',plain,(
    ! [X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( v1_relat_1 @ X15 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('8',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('10',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['8','9'])).

thf('11',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_2 ) @ sk_A ),
    inference(demod,[status(thm)],['5','10'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_A )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ ( k1_relat_1 @ sk_C_2 ) ) @ sk_A ) ),
    inference('sup-',[status(thm)],['0','13'])).

thf('15',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

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

thf('16',plain,(
    ! [X4: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X6 @ X7 )
      | ~ ( r1_xboole_0 @ X4 @ X7 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_0])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_xboole_0 @ X0 @ X1 )
      | ~ ( r2_hidden @ ( sk_B @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( ( k1_relat_1 @ sk_C_2 )
      = k1_xboole_0 )
    | ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_C_2 ) @ sk_A )
    | ( ( k1_relat_1 @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['14','17'])).

thf('19',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ sk_C_2 ) @ sk_A )
    | ( ( k1_relat_1 @ sk_C_2 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X8: $i] :
      ( ( X8 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X8 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf('21',plain,(
    ! [X37: $i] :
      ( ~ ( r2_hidden @ X37 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 ) )
      | ~ ( m1_subset_1 @ X37 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('23',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k2_relset_1 @ X35 @ X36 @ X34 )
        = ( k2_relat_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('24',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k2_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X37: $i] :
      ( ~ ( r2_hidden @ X37 @ ( k2_relat_1 @ sk_C_2 ) )
      | ~ ( m1_subset_1 @ X37 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['21','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v5_relat_1 @ X28 @ X30 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('28',plain,(
    v5_relat_1 @ sk_C_2 @ sk_B_1 ),
    inference('sup-',[status(thm)],['26','27'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('29',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v5_relat_1 @ X19 @ X20 )
      | ( r1_tarski @ ( k2_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('30',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['8','9'])).

thf('32',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_2 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['30','31'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('33',plain,(
    ! [X9: $i,X11: $i] :
      ( ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ X11 ) )
      | ~ ( r1_tarski @ X9 @ X11 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('34',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_2 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('35',plain,(
    ! [X12: $i,X13: $i,X14: $i] :
      ( ~ ( r2_hidden @ X12 @ X13 )
      | ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ X14 ) )
      | ( m1_subset_1 @ X12 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k2_relat_1 @ sk_C_2 ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    ! [X37: $i] :
      ~ ( r2_hidden @ X37 @ ( k2_relat_1 @ sk_C_2 ) ) ),
    inference(clc,[status(thm)],['25','36'])).

thf('38',plain,
    ( ( k2_relat_1 @ sk_C_2 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['20','37'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('39',plain,(
    ! [X25: $i] :
      ( ( ( k2_relat_1 @ X25 )
       != k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('40',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['8','9'])).

thf('42',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_C_2 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('45',plain,
    ( ~ ( r1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ sk_A )
    | ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['19','43','44'])).

thf('46',plain,(
    v4_relat_1 @ sk_C_2 @ sk_A ),
    inference('sup-',[status(thm)],['1','2'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('47',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X23
        = ( k7_relat_1 @ X23 @ X24 ) )
      | ~ ( v4_relat_1 @ X23 @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('48',plain,
    ( ~ ( v1_relat_1 @ sk_C_2 )
    | ( sk_C_2
      = ( k7_relat_1 @ sk_C_2 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['8','9'])).

thf('50',plain,
    ( sk_C_2
    = ( k7_relat_1 @ sk_C_2 @ sk_A ) ),
    inference(demod,[status(thm)],['48','49'])).

thf(t95_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( ( k7_relat_1 @ B @ A )
          = k1_xboole_0 )
      <=> ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('51',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k7_relat_1 @ X26 @ X27 )
       != k1_xboole_0 )
      | ( r1_xboole_0 @ ( k1_relat_1 @ X26 ) @ X27 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t95_relat_1])).

thf('52',plain,
    ( ( sk_C_2 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_2 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_C_2 ) @ sk_A ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_C_2 ),
    inference(demod,[status(thm)],['8','9'])).

thf('54',plain,
    ( ( sk_C_2 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ sk_C_2 ) @ sk_A ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('56',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('57',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( r1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ sk_A ) ),
    inference(demod,[status(thm)],['54','55','56'])).

thf('58',plain,(
    r1_xboole_0 @ ( k1_relat_1 @ k1_xboole_0 ) @ sk_A ),
    inference(simplify,[status(thm)],['57'])).

thf('59',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['45','58'])).

thf('60',plain,(
    ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('61',plain,(
    m1_subset_1 @ sk_C_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('62',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k1_relset_1 @ X32 @ X33 @ X31 )
        = ( k1_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('63',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2 )
    = ( k1_relat_1 @ sk_C_2 ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ( k1_relat_1 @ sk_C_2 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['60','63'])).

thf('65',plain,(
    sk_C_2 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('66',plain,(
    ( k1_relat_1 @ k1_xboole_0 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['64','65'])).

thf('67',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['59','66'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.y1BGzeaTBh
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:34:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.22/0.54  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.22/0.54  % Solved by: fo/fo7.sh
% 0.22/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.54  % done 233 iterations in 0.080s
% 0.22/0.54  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.22/0.54  % SZS output start Refutation
% 0.22/0.54  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.54  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.54  thf(sk_C_2_type, type, sk_C_2: $i).
% 0.22/0.54  thf(r1_xboole_0_type, type, r1_xboole_0: $i > $i > $o).
% 0.22/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.22/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.54  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.22/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.22/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.54  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.22/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.22/0.54  thf(t7_xboole_0, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.22/0.54          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.22/0.54  thf('0', plain,
% 0.22/0.54      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.22/0.54      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.54  thf(t49_relset_1, conjecture,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.54           ( ![C:$i]:
% 0.22/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.54               ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.22/0.54                    ( ![D:$i]:
% 0.22/0.54                      ( ( m1_subset_1 @ D @ B ) =>
% 0.22/0.54                        ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.22/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.54    (~( ![A:$i]:
% 0.22/0.54        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.22/0.54          ( ![B:$i]:
% 0.22/0.54            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.22/0.54              ( ![C:$i]:
% 0.22/0.54                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.54                  ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.22/0.54                       ( ![D:$i]:
% 0.22/0.54                         ( ( m1_subset_1 @ D @ B ) =>
% 0.22/0.54                           ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.22/0.54    inference('cnf.neg', [status(esa)], [t49_relset_1])).
% 0.22/0.54  thf('1', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(cc2_relset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.54       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.54  thf('2', plain,
% 0.22/0.54      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.22/0.54         ((v4_relat_1 @ X28 @ X29)
% 0.22/0.54          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.22/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.54  thf('3', plain, ((v4_relat_1 @ sk_C_2 @ sk_A)),
% 0.22/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.54  thf(d18_relat_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ B ) =>
% 0.22/0.54       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.54  thf('4', plain,
% 0.22/0.54      (![X17 : $i, X18 : $i]:
% 0.22/0.54         (~ (v4_relat_1 @ X17 @ X18)
% 0.22/0.54          | (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 0.22/0.54          | ~ (v1_relat_1 @ X17))),
% 0.22/0.54      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.22/0.54  thf('5', plain,
% 0.22/0.54      ((~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k1_relat_1 @ sk_C_2) @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.22/0.54  thf('6', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(cc2_relat_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ A ) =>
% 0.22/0.54       ( ![B:$i]:
% 0.22/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.22/0.54  thf('7', plain,
% 0.22/0.54      (![X15 : $i, X16 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.22/0.54          | (v1_relat_1 @ X15)
% 0.22/0.54          | ~ (v1_relat_1 @ X16))),
% 0.22/0.54      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.22/0.54  thf('8', plain,
% 0.22/0.54      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C_2))),
% 0.22/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.54  thf(fc6_relat_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.22/0.54  thf('9', plain,
% 0.22/0.54      (![X21 : $i, X22 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X21 @ X22))),
% 0.22/0.54      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.22/0.54  thf('10', plain, ((v1_relat_1 @ sk_C_2)),
% 0.22/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.54  thf('11', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_2) @ sk_A)),
% 0.22/0.54      inference('demod', [status(thm)], ['5', '10'])).
% 0.22/0.54  thf(d3_tarski, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( r1_tarski @ A @ B ) <=>
% 0.22/0.54       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.22/0.54  thf('12', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X0 @ X1)
% 0.22/0.54          | (r2_hidden @ X0 @ X2)
% 0.22/0.54          | ~ (r1_tarski @ X1 @ X2))),
% 0.22/0.54      inference('cnf', [status(esa)], [d3_tarski])).
% 0.22/0.54  thf('13', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((r2_hidden @ X0 @ sk_A) | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_2)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.54  thf('14', plain,
% 0.22/0.54      ((((k1_relat_1 @ sk_C_2) = (k1_xboole_0))
% 0.22/0.54        | (r2_hidden @ (sk_B @ (k1_relat_1 @ sk_C_2)) @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['0', '13'])).
% 0.22/0.54  thf('15', plain,
% 0.22/0.54      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.22/0.54      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.54  thf(t3_xboole_0, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ~( ( ?[C:$i]: ( ( r2_hidden @ C @ B ) & ( r2_hidden @ C @ A ) ) ) & 
% 0.22/0.54            ( r1_xboole_0 @ A @ B ) ) ) & 
% 0.22/0.54       ( ~( ( ~( r1_xboole_0 @ A @ B ) ) & 
% 0.22/0.54            ( ![C:$i]: ( ~( ( r2_hidden @ C @ A ) & ( r2_hidden @ C @ B ) ) ) ) ) ) ))).
% 0.22/0.54  thf('16', plain,
% 0.22/0.54      (![X4 : $i, X6 : $i, X7 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X6 @ X4)
% 0.22/0.54          | ~ (r2_hidden @ X6 @ X7)
% 0.22/0.54          | ~ (r1_xboole_0 @ X4 @ X7))),
% 0.22/0.54      inference('cnf', [status(esa)], [t3_xboole_0])).
% 0.22/0.54  thf('17', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]:
% 0.22/0.54         (((X0) = (k1_xboole_0))
% 0.22/0.54          | ~ (r1_xboole_0 @ X0 @ X1)
% 0.22/0.54          | ~ (r2_hidden @ (sk_B @ X0) @ X1))),
% 0.22/0.54      inference('sup-', [status(thm)], ['15', '16'])).
% 0.22/0.54  thf('18', plain,
% 0.22/0.54      ((((k1_relat_1 @ sk_C_2) = (k1_xboole_0))
% 0.22/0.54        | ~ (r1_xboole_0 @ (k1_relat_1 @ sk_C_2) @ sk_A)
% 0.22/0.54        | ((k1_relat_1 @ sk_C_2) = (k1_xboole_0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['14', '17'])).
% 0.22/0.54  thf('19', plain,
% 0.22/0.54      ((~ (r1_xboole_0 @ (k1_relat_1 @ sk_C_2) @ sk_A)
% 0.22/0.54        | ((k1_relat_1 @ sk_C_2) = (k1_xboole_0)))),
% 0.22/0.54      inference('simplify', [status(thm)], ['18'])).
% 0.22/0.54  thf('20', plain,
% 0.22/0.54      (![X8 : $i]: (((X8) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X8) @ X8))),
% 0.22/0.54      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.22/0.54  thf('21', plain,
% 0.22/0.54      (![X37 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X37 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2))
% 0.22/0.54          | ~ (m1_subset_1 @ X37 @ sk_B_1))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('22', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(redefinition_k2_relset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.54       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.22/0.54  thf('23', plain,
% 0.22/0.54      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.22/0.54         (((k2_relset_1 @ X35 @ X36 @ X34) = (k2_relat_1 @ X34))
% 0.22/0.54          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.22/0.54      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.22/0.54  thf('24', plain,
% 0.22/0.54      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k2_relat_1 @ sk_C_2))),
% 0.22/0.54      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.54  thf('25', plain,
% 0.22/0.54      (![X37 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X37 @ (k2_relat_1 @ sk_C_2))
% 0.22/0.54          | ~ (m1_subset_1 @ X37 @ sk_B_1))),
% 0.22/0.54      inference('demod', [status(thm)], ['21', '24'])).
% 0.22/0.54  thf('26', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('27', plain,
% 0.22/0.54      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.22/0.54         ((v5_relat_1 @ X28 @ X30)
% 0.22/0.54          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.22/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.54  thf('28', plain, ((v5_relat_1 @ sk_C_2 @ sk_B_1)),
% 0.22/0.54      inference('sup-', [status(thm)], ['26', '27'])).
% 0.22/0.54  thf(d19_relat_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ B ) =>
% 0.22/0.54       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.54  thf('29', plain,
% 0.22/0.54      (![X19 : $i, X20 : $i]:
% 0.22/0.54         (~ (v5_relat_1 @ X19 @ X20)
% 0.22/0.54          | (r1_tarski @ (k2_relat_1 @ X19) @ X20)
% 0.22/0.54          | ~ (v1_relat_1 @ X19))),
% 0.22/0.54      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.22/0.54  thf('30', plain,
% 0.22/0.54      ((~ (v1_relat_1 @ sk_C_2) | (r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B_1))),
% 0.22/0.54      inference('sup-', [status(thm)], ['28', '29'])).
% 0.22/0.54  thf('31', plain, ((v1_relat_1 @ sk_C_2)),
% 0.22/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.54  thf('32', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_2) @ sk_B_1)),
% 0.22/0.54      inference('demod', [status(thm)], ['30', '31'])).
% 0.22/0.54  thf(t3_subset, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.22/0.54  thf('33', plain,
% 0.22/0.54      (![X9 : $i, X11 : $i]:
% 0.22/0.54         ((m1_subset_1 @ X9 @ (k1_zfmisc_1 @ X11)) | ~ (r1_tarski @ X9 @ X11))),
% 0.22/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.22/0.54  thf('34', plain,
% 0.22/0.54      ((m1_subset_1 @ (k2_relat_1 @ sk_C_2) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.22/0.54      inference('sup-', [status(thm)], ['32', '33'])).
% 0.22/0.54  thf(t4_subset, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.22/0.54       ( m1_subset_1 @ A @ C ) ))).
% 0.22/0.54  thf('35', plain,
% 0.22/0.54      (![X12 : $i, X13 : $i, X14 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X12 @ X13)
% 0.22/0.54          | ~ (m1_subset_1 @ X13 @ (k1_zfmisc_1 @ X14))
% 0.22/0.54          | (m1_subset_1 @ X12 @ X14))),
% 0.22/0.54      inference('cnf', [status(esa)], [t4_subset])).
% 0.22/0.54  thf('36', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((m1_subset_1 @ X0 @ sk_B_1)
% 0.22/0.54          | ~ (r2_hidden @ X0 @ (k2_relat_1 @ sk_C_2)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['34', '35'])).
% 0.22/0.54  thf('37', plain, (![X37 : $i]: ~ (r2_hidden @ X37 @ (k2_relat_1 @ sk_C_2))),
% 0.22/0.54      inference('clc', [status(thm)], ['25', '36'])).
% 0.22/0.54  thf('38', plain, (((k2_relat_1 @ sk_C_2) = (k1_xboole_0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['20', '37'])).
% 0.22/0.54  thf(t64_relat_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ A ) =>
% 0.22/0.54       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.22/0.54           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.54         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.54  thf('39', plain,
% 0.22/0.54      (![X25 : $i]:
% 0.22/0.54         (((k2_relat_1 @ X25) != (k1_xboole_0))
% 0.22/0.54          | ((X25) = (k1_xboole_0))
% 0.22/0.54          | ~ (v1_relat_1 @ X25))),
% 0.22/0.54      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.22/0.54  thf('40', plain,
% 0.22/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.54        | ~ (v1_relat_1 @ sk_C_2)
% 0.22/0.54        | ((sk_C_2) = (k1_xboole_0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['38', '39'])).
% 0.22/0.54  thf('41', plain, ((v1_relat_1 @ sk_C_2)),
% 0.22/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.54  thf('42', plain,
% 0.22/0.54      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_C_2) = (k1_xboole_0)))),
% 0.22/0.54      inference('demod', [status(thm)], ['40', '41'])).
% 0.22/0.54  thf('43', plain, (((sk_C_2) = (k1_xboole_0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['42'])).
% 0.22/0.54  thf('44', plain, (((sk_C_2) = (k1_xboole_0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['42'])).
% 0.22/0.54  thf('45', plain,
% 0.22/0.54      ((~ (r1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ sk_A)
% 0.22/0.54        | ((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.22/0.54      inference('demod', [status(thm)], ['19', '43', '44'])).
% 0.22/0.54  thf('46', plain, ((v4_relat_1 @ sk_C_2 @ sk_A)),
% 0.22/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.54  thf(t209_relat_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.22/0.54       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.22/0.54  thf('47', plain,
% 0.22/0.54      (![X23 : $i, X24 : $i]:
% 0.22/0.54         (((X23) = (k7_relat_1 @ X23 @ X24))
% 0.22/0.54          | ~ (v4_relat_1 @ X23 @ X24)
% 0.22/0.54          | ~ (v1_relat_1 @ X23))),
% 0.22/0.54      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.22/0.54  thf('48', plain,
% 0.22/0.54      ((~ (v1_relat_1 @ sk_C_2) | ((sk_C_2) = (k7_relat_1 @ sk_C_2 @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.54  thf('49', plain, ((v1_relat_1 @ sk_C_2)),
% 0.22/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.54  thf('50', plain, (((sk_C_2) = (k7_relat_1 @ sk_C_2 @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['48', '49'])).
% 0.22/0.54  thf(t95_relat_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ B ) =>
% 0.22/0.54       ( ( ( k7_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) <=>
% 0.22/0.54         ( r1_xboole_0 @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.54  thf('51', plain,
% 0.22/0.54      (![X26 : $i, X27 : $i]:
% 0.22/0.54         (((k7_relat_1 @ X26 @ X27) != (k1_xboole_0))
% 0.22/0.54          | (r1_xboole_0 @ (k1_relat_1 @ X26) @ X27)
% 0.22/0.54          | ~ (v1_relat_1 @ X26))),
% 0.22/0.54      inference('cnf', [status(esa)], [t95_relat_1])).
% 0.22/0.54  thf('52', plain,
% 0.22/0.54      ((((sk_C_2) != (k1_xboole_0))
% 0.22/0.54        | ~ (v1_relat_1 @ sk_C_2)
% 0.22/0.54        | (r1_xboole_0 @ (k1_relat_1 @ sk_C_2) @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['50', '51'])).
% 0.22/0.54  thf('53', plain, ((v1_relat_1 @ sk_C_2)),
% 0.22/0.54      inference('demod', [status(thm)], ['8', '9'])).
% 0.22/0.54  thf('54', plain,
% 0.22/0.54      ((((sk_C_2) != (k1_xboole_0))
% 0.22/0.54        | (r1_xboole_0 @ (k1_relat_1 @ sk_C_2) @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['52', '53'])).
% 0.22/0.54  thf('55', plain, (((sk_C_2) = (k1_xboole_0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['42'])).
% 0.22/0.54  thf('56', plain, (((sk_C_2) = (k1_xboole_0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['42'])).
% 0.22/0.54  thf('57', plain,
% 0.22/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.54        | (r1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['54', '55', '56'])).
% 0.22/0.54  thf('58', plain, ((r1_xboole_0 @ (k1_relat_1 @ k1_xboole_0) @ sk_A)),
% 0.22/0.54      inference('simplify', [status(thm)], ['57'])).
% 0.22/0.54  thf('59', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.54      inference('demod', [status(thm)], ['45', '58'])).
% 0.22/0.54  thf('60', plain, (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) != (k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('61', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_C_2 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(redefinition_k1_relset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.22/0.54  thf('62', plain,
% 0.22/0.54      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.22/0.54         (((k1_relset_1 @ X32 @ X33 @ X31) = (k1_relat_1 @ X31))
% 0.22/0.54          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.22/0.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.22/0.54  thf('63', plain,
% 0.22/0.54      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_2) = (k1_relat_1 @ sk_C_2))),
% 0.22/0.54      inference('sup-', [status(thm)], ['61', '62'])).
% 0.22/0.54  thf('64', plain, (((k1_relat_1 @ sk_C_2) != (k1_xboole_0))),
% 0.22/0.54      inference('demod', [status(thm)], ['60', '63'])).
% 0.22/0.54  thf('65', plain, (((sk_C_2) = (k1_xboole_0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['42'])).
% 0.22/0.54  thf('66', plain, (((k1_relat_1 @ k1_xboole_0) != (k1_xboole_0))),
% 0.22/0.54      inference('demod', [status(thm)], ['64', '65'])).
% 0.22/0.54  thf('67', plain, ($false),
% 0.22/0.54      inference('simplify_reflect-', [status(thm)], ['59', '66'])).
% 0.22/0.54  
% 0.22/0.54  % SZS output end Refutation
% 0.22/0.54  
% 0.22/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
