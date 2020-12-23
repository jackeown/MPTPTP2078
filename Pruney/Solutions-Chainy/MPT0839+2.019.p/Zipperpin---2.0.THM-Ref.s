%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3kmhRj9Rkt

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 139 expanded)
%              Number of leaves         :   39 (  58 expanded)
%              Depth                    :   20
%              Number of atoms          :  580 (1082 expanded)
%              Number of equality atoms :   27 (  51 expanded)
%              Maximal formula depth    :   17 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(sk_A_1_type,type,(
    sk_A_1: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k2_subset_1_type,type,(
    k2_subset_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(fc4_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ) )).

thf('1',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ X4 )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ X4 @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[fc4_zfmisc_1])).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('2',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('3',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_xboole_0 @ X1 )
      | ( ( k2_zfmisc_1 @ X1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf(dt_k2_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ) )).

thf('4',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ ( k2_subset_1 @ X7 ) @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(cnf,[status(esa)],[dt_k2_subset_1])).

thf(d4_subset_1,axiom,(
    ! [A: $i] :
      ( ( k2_subset_1 @ A )
      = A ) )).

thf('5',plain,(
    ! [X6: $i] :
      ( ( k2_subset_1 @ X6 )
      = X6 ) ),
    inference(cnf,[status(esa)],[d4_subset_1])).

thf('6',plain,(
    ! [X7: $i] :
      ( m1_subset_1 @ X7 @ ( k1_zfmisc_1 @ X7 ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X10: $i,X11: $i] :
      ( ( r1_tarski @ X10 @ X11 )
      | ~ ( m1_subset_1 @ X10 @ ( k1_zfmisc_1 @ X11 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('8',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t50_relset_1,conjecture,(
    ! [A: $i] :
      ( ~ ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ~ ( v1_xboole_0 @ B )
         => ! [C: $i] :
              ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
             => ~ ( ( ( k2_relset_1 @ B @ A @ C )
                   != k1_xboole_0 )
                  & ! [D: $i] :
                      ( ( m1_subset_1 @ D @ B )
                     => ~ ( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i] :
        ( ~ ( v1_xboole_0 @ A )
       => ! [B: $i] :
            ( ~ ( v1_xboole_0 @ B )
           => ! [C: $i] :
                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
               => ~ ( ( ( k2_relset_1 @ B @ A @ C )
                     != k1_xboole_0 )
                    & ! [D: $i] :
                        ( ( m1_subset_1 @ D @ B )
                       => ~ ( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t50_relset_1])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t13_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B )
       => ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ) )).

thf('10',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X34 ) @ X35 )
      | ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[t13_relset_1])).

thf('11',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A_1 ) ) )
      | ~ ( r1_tarski @ ( k1_relat_1 @ sk_C ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('13',plain,(
    ! [X38: $i] :
      ( ~ ( r2_hidden @ X38 @ ( k1_relset_1 @ sk_B_1 @ sk_A_1 @ sk_C ) )
      | ~ ( m1_subset_1 @ X38 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( k1_relset_1 @ sk_B_1 @ sk_A_1 @ sk_C ) )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k1_relset_1 @ sk_B_1 @ sk_A_1 @ sk_C ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('16',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( ( k1_relset_1 @ X29 @ X30 @ X28 )
        = ( k1_relat_1 @ X28 ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('17',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_A_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_A_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('19',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k1_relat_1 @ sk_C ) ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['14','17','18'])).

thf('20',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('21',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('22',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ( v4_relat_1 @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('23',plain,(
    v4_relat_1 @ sk_C @ sk_B_1 ),
    inference('sup-',[status(thm)],['21','22'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('24',plain,(
    ! [X17: $i,X18: $i] :
      ( ( X17
        = ( k7_relat_1 @ X17 @ X18 ) )
      | ~ ( v4_relat_1 @ X17 @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('25',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( sk_C
      = ( k7_relat_1 @ sk_C @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('27',plain,(
    ! [X22: $i,X23: $i,X24: $i] :
      ( ( v1_relat_1 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('28',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,
    ( sk_C
    = ( k7_relat_1 @ sk_C @ sk_B_1 ) ),
    inference(demod,[status(thm)],['25','28'])).

thf(t86_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) )
      <=> ( ( r2_hidden @ A @ B )
          & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('30',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X19 @ ( k1_relat_1 @ ( k7_relat_1 @ X21 @ X20 ) ) )
      | ( r2_hidden @ X19 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t86_relat_1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C ) )
      | ~ ( v1_relat_1 @ sk_C )
      | ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_C ),
    inference('sup-',[status(thm)],['26','27'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C ) )
      | ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['31','32'])).

thf('34',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( r2_hidden @ ( sk_B @ ( k1_relat_1 @ sk_C ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['20','33'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('35',plain,(
    ! [X8: $i,X9: $i] :
      ( ( m1_subset_1 @ X8 @ X9 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('36',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C ) )
    | ( m1_subset_1 @ ( sk_B @ ( k1_relat_1 @ sk_C ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_xboole_0 @ ( k1_relat_1 @ sk_C ) ),
    inference(clc,[status(thm)],['19','36'])).

thf('38',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('39',plain,
    ( ( k1_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_A_1 ) ) )
      | ~ ( r1_tarski @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['11','39'])).

thf('41',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_A_1 ) ) ),
    inference('sup-',[status(thm)],['8','40'])).

thf('42',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
    | ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['3','41'])).

thf(rc1_xboole_0,axiom,(
    ? [A: $i] :
      ( v1_xboole_0 @ A ) )).

thf('43',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('44',plain,(
    v1_xboole_0 @ sk_A ),
    inference(cnf,[status(esa)],[rc1_xboole_0])).

thf('45',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('46',plain,(
    sk_A = k1_xboole_0 ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['43','46'])).

thf('48',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['42','47'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('49',plain,(
    ! [X13: $i,X14: $i,X15: $i] :
      ( ~ ( r2_hidden @ X13 @ X14 )
      | ~ ( v1_xboole_0 @ X15 )
      | ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('50',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['43','46'])).

thf('52',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_C ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,(
    v1_xboole_0 @ sk_C ),
    inference('sup-',[status(thm)],['0','52'])).

thf(fc11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ) )).

thf('54',plain,(
    ! [X16: $i] :
      ( ( v1_xboole_0 @ ( k2_relat_1 @ X16 ) )
      | ~ ( v1_xboole_0 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc11_relat_1])).

thf('55',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('56',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( k2_relat_1 @ sk_C )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','56'])).

thf('58',plain,(
    ( k2_relset_1 @ sk_B_1 @ sk_A_1 @ sk_C )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('59',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('60',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( ( k2_relset_1 @ X32 @ X33 @ X31 )
        = ( k2_relat_1 @ X31 ) )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('61',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A_1 @ sk_C )
    = ( k2_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ( k2_relat_1 @ sk_C )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['58','61'])).

thf('63',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['57','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.3kmhRj9Rkt
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:32:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.20/0.51  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.20/0.51  % Solved by: fo/fo7.sh
% 0.20/0.51  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.20/0.51  % done 117 iterations in 0.058s
% 0.20/0.51  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.20/0.51  % SZS output start Refutation
% 0.20/0.51  thf(sk_A_type, type, sk_A: $i).
% 0.20/0.51  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.20/0.51  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.20/0.51  thf(sk_B_type, type, sk_B: $i > $i).
% 0.20/0.51  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.20/0.51  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.20/0.51  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.20/0.51  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.20/0.51  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.20/0.51  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.20/0.51  thf(sk_C_type, type, sk_C: $i).
% 0.20/0.51  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.20/0.51  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.20/0.51  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.20/0.51  thf(sk_A_1_type, type, sk_A_1: $i).
% 0.20/0.51  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.20/0.51  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.20/0.51  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.20/0.51  thf(k2_subset_1_type, type, k2_subset_1: $i > $i).
% 0.20/0.51  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.20/0.51  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.20/0.51  thf(d1_xboole_0, axiom,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.20/0.51  thf('0', plain,
% 0.20/0.51      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.51  thf(fc4_zfmisc_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_zfmisc_1 @ A @ B ) ) ))).
% 0.20/0.51  thf('1', plain,
% 0.20/0.51      (![X4 : $i, X5 : $i]:
% 0.20/0.51         (~ (v1_xboole_0 @ X4) | (v1_xboole_0 @ (k2_zfmisc_1 @ X4 @ X5)))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc4_zfmisc_1])).
% 0.20/0.51  thf(l13_xboole_0, axiom,
% 0.20/0.51    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.20/0.51  thf('2', plain,
% 0.20/0.51      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.51  thf('3', plain,
% 0.20/0.51      (![X0 : $i, X1 : $i]:
% 0.20/0.51         (~ (v1_xboole_0 @ X1) | ((k2_zfmisc_1 @ X1 @ X0) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['1', '2'])).
% 0.20/0.51  thf(dt_k2_subset_1, axiom,
% 0.20/0.51    (![A:$i]: ( m1_subset_1 @ ( k2_subset_1 @ A ) @ ( k1_zfmisc_1 @ A ) ))).
% 0.20/0.51  thf('4', plain,
% 0.20/0.51      (![X7 : $i]: (m1_subset_1 @ (k2_subset_1 @ X7) @ (k1_zfmisc_1 @ X7))),
% 0.20/0.51      inference('cnf', [status(esa)], [dt_k2_subset_1])).
% 0.20/0.51  thf(d4_subset_1, axiom, (![A:$i]: ( ( k2_subset_1 @ A ) = ( A ) ))).
% 0.20/0.51  thf('5', plain, (![X6 : $i]: ((k2_subset_1 @ X6) = (X6))),
% 0.20/0.51      inference('cnf', [status(esa)], [d4_subset_1])).
% 0.20/0.51  thf('6', plain, (![X7 : $i]: (m1_subset_1 @ X7 @ (k1_zfmisc_1 @ X7))),
% 0.20/0.51      inference('demod', [status(thm)], ['4', '5'])).
% 0.20/0.51  thf(t3_subset, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.20/0.51  thf('7', plain,
% 0.20/0.51      (![X10 : $i, X11 : $i]:
% 0.20/0.51         ((r1_tarski @ X10 @ X11) | ~ (m1_subset_1 @ X10 @ (k1_zfmisc_1 @ X11)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t3_subset])).
% 0.20/0.51  thf('8', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.20/0.51      inference('sup-', [status(thm)], ['6', '7'])).
% 0.20/0.51  thf(t50_relset_1, conjecture,
% 0.20/0.51    (![A:$i]:
% 0.20/0.51     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.51       ( ![B:$i]:
% 0.20/0.51         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.51           ( ![C:$i]:
% 0.20/0.51             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.51               ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.51                    ( ![D:$i]:
% 0.20/0.51                      ( ( m1_subset_1 @ D @ B ) =>
% 0.20/0.51                        ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.20/0.51  thf(zf_stmt_0, negated_conjecture,
% 0.20/0.51    (~( ![A:$i]:
% 0.20/0.51        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.20/0.51          ( ![B:$i]:
% 0.20/0.51            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.20/0.51              ( ![C:$i]:
% 0.20/0.51                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.20/0.51                  ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.20/0.51                       ( ![D:$i]:
% 0.20/0.51                         ( ( m1_subset_1 @ D @ B ) =>
% 0.20/0.51                           ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.20/0.51    inference('cnf.neg', [status(esa)], [t50_relset_1])).
% 0.20/0.51  thf('9', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A_1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(t13_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i,D:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) ) =>
% 0.20/0.51       ( ( r1_tarski @ ( k1_relat_1 @ D ) @ B ) =>
% 0.20/0.51         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ))).
% 0.20/0.51  thf('10', plain,
% 0.20/0.51      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.20/0.51         (~ (r1_tarski @ (k1_relat_1 @ X34) @ X35)
% 0.20/0.51          | (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.20/0.51          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X36))))),
% 0.20/0.51      inference('cnf', [status(esa)], [t13_relset_1])).
% 0.20/0.51  thf('11', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A_1)))
% 0.20/0.51          | ~ (r1_tarski @ (k1_relat_1 @ sk_C) @ X0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['9', '10'])).
% 0.20/0.51  thf('12', plain,
% 0.20/0.51      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.51  thf('13', plain,
% 0.20/0.51      (![X38 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X38 @ (k1_relset_1 @ sk_B_1 @ sk_A_1 @ sk_C))
% 0.20/0.51          | ~ (m1_subset_1 @ X38 @ sk_B_1))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('14', plain,
% 0.20/0.51      (((v1_xboole_0 @ (k1_relset_1 @ sk_B_1 @ sk_A_1 @ sk_C))
% 0.20/0.51        | ~ (m1_subset_1 @ (sk_B @ (k1_relset_1 @ sk_B_1 @ sk_A_1 @ sk_C)) @ 
% 0.20/0.51             sk_B_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['12', '13'])).
% 0.20/0.51  thf('15', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A_1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(redefinition_k1_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.20/0.51  thf('16', plain,
% 0.20/0.51      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.20/0.51         (((k1_relset_1 @ X29 @ X30 @ X28) = (k1_relat_1 @ X28))
% 0.20/0.51          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.20/0.51  thf('17', plain,
% 0.20/0.51      (((k1_relset_1 @ sk_B_1 @ sk_A_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.51  thf('18', plain,
% 0.20/0.51      (((k1_relset_1 @ sk_B_1 @ sk_A_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['15', '16'])).
% 0.20/0.51  thf('19', plain,
% 0.20/0.51      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.20/0.51        | ~ (m1_subset_1 @ (sk_B @ (k1_relat_1 @ sk_C)) @ sk_B_1))),
% 0.20/0.51      inference('demod', [status(thm)], ['14', '17', '18'])).
% 0.20/0.51  thf('20', plain,
% 0.20/0.51      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.20/0.51      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.20/0.51  thf('21', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A_1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(cc2_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.20/0.51  thf('22', plain,
% 0.20/0.51      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.20/0.51         ((v4_relat_1 @ X25 @ X26)
% 0.20/0.51          | ~ (m1_subset_1 @ X25 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X26 @ X27))))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.20/0.51  thf('23', plain, ((v4_relat_1 @ sk_C @ sk_B_1)),
% 0.20/0.51      inference('sup-', [status(thm)], ['21', '22'])).
% 0.20/0.51  thf(t209_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i]:
% 0.20/0.51     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.20/0.51       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.20/0.51  thf('24', plain,
% 0.20/0.51      (![X17 : $i, X18 : $i]:
% 0.20/0.51         (((X17) = (k7_relat_1 @ X17 @ X18))
% 0.20/0.51          | ~ (v4_relat_1 @ X17 @ X18)
% 0.20/0.51          | ~ (v1_relat_1 @ X17))),
% 0.20/0.51      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.20/0.51  thf('25', plain,
% 0.20/0.51      ((~ (v1_relat_1 @ sk_C) | ((sk_C) = (k7_relat_1 @ sk_C @ sk_B_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['23', '24'])).
% 0.20/0.51  thf('26', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A_1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(cc1_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( v1_relat_1 @ C ) ))).
% 0.20/0.51  thf('27', plain,
% 0.20/0.51      (![X22 : $i, X23 : $i, X24 : $i]:
% 0.20/0.51         ((v1_relat_1 @ X22)
% 0.20/0.51          | ~ (m1_subset_1 @ X22 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X23 @ X24))))),
% 0.20/0.51      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.20/0.51  thf('28', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.51      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.51  thf('29', plain, (((sk_C) = (k7_relat_1 @ sk_C @ sk_B_1))),
% 0.20/0.51      inference('demod', [status(thm)], ['25', '28'])).
% 0.20/0.51  thf(t86_relat_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( v1_relat_1 @ C ) =>
% 0.20/0.51       ( ( r2_hidden @ A @ ( k1_relat_1 @ ( k7_relat_1 @ C @ B ) ) ) <=>
% 0.20/0.51         ( ( r2_hidden @ A @ B ) & ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) ) ) ))).
% 0.20/0.51  thf('30', plain,
% 0.20/0.51      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X19 @ (k1_relat_1 @ (k7_relat_1 @ X21 @ X20)))
% 0.20/0.51          | (r2_hidden @ X19 @ X20)
% 0.20/0.51          | ~ (v1_relat_1 @ X21))),
% 0.20/0.51      inference('cnf', [status(esa)], [t86_relat_1])).
% 0.20/0.51  thf('31', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C))
% 0.20/0.51          | ~ (v1_relat_1 @ sk_C)
% 0.20/0.51          | (r2_hidden @ X0 @ sk_B_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['29', '30'])).
% 0.20/0.51  thf('32', plain, ((v1_relat_1 @ sk_C)),
% 0.20/0.51      inference('sup-', [status(thm)], ['26', '27'])).
% 0.20/0.51  thf('33', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C)) | (r2_hidden @ X0 @ sk_B_1))),
% 0.20/0.51      inference('demod', [status(thm)], ['31', '32'])).
% 0.20/0.51  thf('34', plain,
% 0.20/0.51      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.20/0.51        | (r2_hidden @ (sk_B @ (k1_relat_1 @ sk_C)) @ sk_B_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['20', '33'])).
% 0.20/0.51  thf(t1_subset, axiom,
% 0.20/0.51    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.20/0.51  thf('35', plain,
% 0.20/0.51      (![X8 : $i, X9 : $i]: ((m1_subset_1 @ X8 @ X9) | ~ (r2_hidden @ X8 @ X9))),
% 0.20/0.51      inference('cnf', [status(esa)], [t1_subset])).
% 0.20/0.51  thf('36', plain,
% 0.20/0.51      (((v1_xboole_0 @ (k1_relat_1 @ sk_C))
% 0.20/0.51        | (m1_subset_1 @ (sk_B @ (k1_relat_1 @ sk_C)) @ sk_B_1))),
% 0.20/0.51      inference('sup-', [status(thm)], ['34', '35'])).
% 0.20/0.51  thf('37', plain, ((v1_xboole_0 @ (k1_relat_1 @ sk_C))),
% 0.20/0.51      inference('clc', [status(thm)], ['19', '36'])).
% 0.20/0.51  thf('38', plain,
% 0.20/0.51      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.51  thf('39', plain, (((k1_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['37', '38'])).
% 0.20/0.51  thf('40', plain,
% 0.20/0.51      (![X0 : $i]:
% 0.20/0.51         ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X0 @ sk_A_1)))
% 0.20/0.51          | ~ (r1_tarski @ k1_xboole_0 @ X0))),
% 0.20/0.51      inference('demod', [status(thm)], ['11', '39'])).
% 0.20/0.51  thf('41', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ 
% 0.20/0.51        (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_A_1)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['8', '40'])).
% 0.20/0.51  thf('42', plain,
% 0.20/0.51      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))
% 0.20/0.51        | ~ (v1_xboole_0 @ k1_xboole_0))),
% 0.20/0.51      inference('sup+', [status(thm)], ['3', '41'])).
% 0.20/0.51  thf(rc1_xboole_0, axiom, (?[A:$i]: ( v1_xboole_0 @ A ))).
% 0.20/0.51  thf('43', plain, ((v1_xboole_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.20/0.51  thf('44', plain, ((v1_xboole_0 @ sk_A)),
% 0.20/0.51      inference('cnf', [status(esa)], [rc1_xboole_0])).
% 0.20/0.51  thf('45', plain,
% 0.20/0.51      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.51  thf('46', plain, (((sk_A) = (k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['44', '45'])).
% 0.20/0.51  thf('47', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.51      inference('demod', [status(thm)], ['43', '46'])).
% 0.20/0.51  thf('48', plain, ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0))),
% 0.20/0.51      inference('demod', [status(thm)], ['42', '47'])).
% 0.20/0.51  thf(t5_subset, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ~( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) & 
% 0.20/0.51          ( v1_xboole_0 @ C ) ) ))).
% 0.20/0.51  thf('49', plain,
% 0.20/0.51      (![X13 : $i, X14 : $i, X15 : $i]:
% 0.20/0.51         (~ (r2_hidden @ X13 @ X14)
% 0.20/0.51          | ~ (v1_xboole_0 @ X15)
% 0.20/0.51          | ~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15)))),
% 0.20/0.51      inference('cnf', [status(esa)], [t5_subset])).
% 0.20/0.51  thf('50', plain,
% 0.20/0.51      (![X0 : $i]: (~ (v1_xboole_0 @ k1_xboole_0) | ~ (r2_hidden @ X0 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['48', '49'])).
% 0.20/0.51  thf('51', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.20/0.51      inference('demod', [status(thm)], ['43', '46'])).
% 0.20/0.51  thf('52', plain, (![X0 : $i]: ~ (r2_hidden @ X0 @ sk_C)),
% 0.20/0.51      inference('demod', [status(thm)], ['50', '51'])).
% 0.20/0.51  thf('53', plain, ((v1_xboole_0 @ sk_C)),
% 0.20/0.51      inference('sup-', [status(thm)], ['0', '52'])).
% 0.20/0.51  thf(fc11_relat_1, axiom,
% 0.20/0.51    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( v1_xboole_0 @ ( k2_relat_1 @ A ) ) ))).
% 0.20/0.51  thf('54', plain,
% 0.20/0.51      (![X16 : $i]:
% 0.20/0.51         ((v1_xboole_0 @ (k2_relat_1 @ X16)) | ~ (v1_xboole_0 @ X16))),
% 0.20/0.51      inference('cnf', [status(esa)], [fc11_relat_1])).
% 0.20/0.51  thf('55', plain,
% 0.20/0.51      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.20/0.51      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.20/0.51  thf('56', plain,
% 0.20/0.51      (![X0 : $i]: (~ (v1_xboole_0 @ X0) | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 0.20/0.51      inference('sup-', [status(thm)], ['54', '55'])).
% 0.20/0.51  thf('57', plain, (((k2_relat_1 @ sk_C) = (k1_xboole_0))),
% 0.20/0.51      inference('sup-', [status(thm)], ['53', '56'])).
% 0.20/0.51  thf('58', plain, (((k2_relset_1 @ sk_B_1 @ sk_A_1 @ sk_C) != (k1_xboole_0))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf('59', plain,
% 0.20/0.51      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A_1)))),
% 0.20/0.51      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.20/0.51  thf(redefinition_k2_relset_1, axiom,
% 0.20/0.51    (![A:$i,B:$i,C:$i]:
% 0.20/0.51     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.20/0.51       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.20/0.51  thf('60', plain,
% 0.20/0.51      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.20/0.51         (((k2_relset_1 @ X32 @ X33 @ X31) = (k2_relat_1 @ X31))
% 0.20/0.51          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.20/0.51      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.20/0.51  thf('61', plain,
% 0.20/0.51      (((k2_relset_1 @ sk_B_1 @ sk_A_1 @ sk_C) = (k2_relat_1 @ sk_C))),
% 0.20/0.51      inference('sup-', [status(thm)], ['59', '60'])).
% 0.20/0.51  thf('62', plain, (((k2_relat_1 @ sk_C) != (k1_xboole_0))),
% 0.20/0.51      inference('demod', [status(thm)], ['58', '61'])).
% 0.20/0.51  thf('63', plain, ($false),
% 0.20/0.51      inference('simplify_reflect-', [status(thm)], ['57', '62'])).
% 0.20/0.51  
% 0.20/0.51  % SZS output end Refutation
% 0.20/0.51  
% 0.20/0.52  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
