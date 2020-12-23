%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FNR8nYDuGu

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:17 EST 2020

% Result     : Theorem 0.54s
% Output     : Refutation 0.54s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 239 expanded)
%              Number of leaves         :   36 (  88 expanded)
%              Depth                    :   16
%              Number of atoms          :  815 (2244 expanded)
%              Number of equality atoms :   36 (  85 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_2_type,type,(
    sk_C_2: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_C_3_type,type,(
    sk_C_3: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

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

thf('0',plain,(
    ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('2',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k2_relset_1 @ X38 @ X39 @ X37 )
        = ( k2_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('3',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 )
    = ( k2_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ( k2_relat_1 @ sk_C_3 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['0','3'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ B )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ A )
         => ( r2_hidden @ C @ B ) ) ) )).

thf('5',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('6',plain,(
    ! [X40: $i] :
      ( ~ ( r2_hidden @ X40 @ ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 ) )
      | ~ ( m1_subset_1 @ X40 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 ) @ X0 )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 ) ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('9',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( ( k1_relset_1 @ X35 @ X36 @ X34 )
        = ( k1_relat_1 @ X34 ) )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('10',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_C_3 ) @ X0 )
      | ~ ( m1_subset_1 @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_C_3 ) ) @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['7','10','11'])).

thf('13',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('14',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('15',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v4_relat_1 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('16',plain,(
    v4_relat_1 @ sk_C_3 @ sk_B_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('17',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('18',plain,
    ( ~ ( v1_relat_1 @ sk_C_3 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_3 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('20',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( m1_subset_1 @ X14 @ ( k1_zfmisc_1 @ X15 ) )
      | ( v1_relat_1 @ X14 )
      | ~ ( v1_relat_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('21',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) )
    | ( v1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('22',plain,(
    ! [X25: $i,X26: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('23',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(demod,[status(thm)],['21','22'])).

thf('24',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_3 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['18','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('26',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ sk_B_1 )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_C_3 ) ) ) ),
    inference('sup-',[status(thm)],['24','25'])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_C_3 ) @ X0 )
      | ( r2_hidden @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_C_3 ) ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['13','26'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('28',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_C_3 ) @ X0 )
      | ( m1_subset_1 @ ( sk_C @ X0 @ ( k1_relat_1 @ sk_C_3 ) ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_C_3 ) @ X0 ) ),
    inference(clc,[status(thm)],['12','29'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('31',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('32',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','31'])).

thf(t56_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ! [B: $i,C: $i] :
            ~ ( r2_hidden @ ( k4_tarski @ B @ C ) @ A )
       => ( A = k1_xboole_0 ) ) ) )).

thf('33',plain,(
    ! [X27: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ X27 ) @ ( sk_C_2 @ X27 ) ) @ X27 )
      | ( X27 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf(d4_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k1_relat_1 @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) )).

thf('34',plain,(
    ! [X18: $i,X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ X20 )
      | ( r2_hidden @ X18 @ X21 )
      | ( X21
       != ( k1_relat_1 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[d4_relat_1])).

thf('35',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X18 @ ( k1_relat_1 @ X20 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ X20 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['33','35'])).

thf('37',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_3 ) @ k1_xboole_0 )
    | ( sk_C_3 = k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_3 ) ),
    inference('sup+',[status(thm)],['32','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(demod,[status(thm)],['21','22'])).

thf('39',plain,
    ( ( r2_hidden @ ( sk_B @ sk_C_3 ) @ k1_xboole_0 )
    | ( sk_C_3 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,(
    ! [X40: $i] :
      ( ~ ( r2_hidden @ X40 @ ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 ) )
      | ~ ( m1_subset_1 @ X40 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('41',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3 )
    = ( k1_relat_1 @ sk_C_3 ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('42',plain,(
    ! [X40: $i] :
      ( ~ ( r2_hidden @ X40 @ ( k1_relat_1 @ sk_C_3 ) )
      | ~ ( m1_subset_1 @ X40 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,
    ( ( k1_relat_1 @ sk_C_3 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['30','31'])).

thf('44',plain,(
    ! [X40: $i] :
      ( ~ ( r2_hidden @ X40 @ k1_xboole_0 )
      | ~ ( m1_subset_1 @ X40 @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['42','43'])).

thf('45',plain,
    ( ( sk_C_3 = k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( sk_B @ sk_C_3 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['39','44'])).

thf('46',plain,(
    ! [X27: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_B @ X27 ) @ ( sk_C_2 @ X27 ) ) @ X27 )
      | ( X27 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t56_relat_1])).

thf('47',plain,(
    m1_subset_1 @ sk_C_3 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('48',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('49',plain,(
    r1_tarski @ sk_C_3 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('51',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ X0 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_C_3 ) ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf('52',plain,
    ( ~ ( v1_relat_1 @ sk_C_3 )
    | ( sk_C_3 = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_C_3 ) @ ( sk_C_2 @ sk_C_3 ) ) @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['46','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_C_3 ),
    inference(demod,[status(thm)],['21','22'])).

thf('54',plain,
    ( ( sk_C_3 = k1_xboole_0 )
    | ( r2_hidden @ ( k4_tarski @ ( sk_B @ sk_C_3 ) @ ( sk_C_2 @ sk_C_3 ) ) @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X18 @ ( k1_relat_1 @ X20 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X18 @ X19 ) @ X20 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('56',plain,
    ( ( sk_C_3 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_C_3 ) @ ( k1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X1 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('58',plain,(
    ! [X1: $i,X3: $i] :
      ( ( r1_tarski @ X1 @ X3 )
      | ~ ( r2_hidden @ ( sk_C @ X3 @ X1 ) @ X3 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('59',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ X0 @ X0 )
      | ( r1_tarski @ X0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['57','58'])).

thf('60',plain,(
    ! [X0: $i] :
      ( r1_tarski @ X0 @ X0 ) ),
    inference(simplify,[status(thm)],['59'])).

thf('61',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('62',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v4_relat_1 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( v4_relat_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) @ X1 ) ),
    inference('sup-',[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) )
      | ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['64','65'])).

thf('67',plain,(
    ! [X25: $i,X26: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) @ X0 ) ),
    inference(demod,[status(thm)],['66','67'])).

thf('69',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ X0 @ X2 )
      | ~ ( r1_tarski @ X1 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf('70',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( r2_hidden @ X2 @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X0 @ X1 ) ) ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,
    ( ( sk_C_3 = k1_xboole_0 )
    | ( r2_hidden @ ( sk_B @ sk_C_3 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['56','70'])).

thf('72',plain,(
    ! [X9: $i,X10: $i] :
      ( ( m1_subset_1 @ X9 @ X10 )
      | ~ ( r2_hidden @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('73',plain,
    ( ( sk_C_3 = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_B @ sk_C_3 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['71','72'])).

thf('74',plain,(
    sk_C_3 = k1_xboole_0 ),
    inference(clc,[status(thm)],['45','73'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('75',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('76',plain,(
    ! [X11: $i,X13: $i] :
      ( ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X13 ) )
      | ~ ( r1_tarski @ X11 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('77',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf(dt_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ) )).

thf('78',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( m1_subset_1 @ ( k2_relset_1 @ X31 @ X32 @ X33 ) @ ( k1_zfmisc_1 @ X32 ) )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X31 @ X32 ) ) ) ) ),
    inference(cnf,[status(esa)],[dt_k2_relset_1])).

thf('79',plain,(
    ! [X0: $i,X1: $i] :
      ( m1_subset_1 @ ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['77','78'])).

thf('80',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','76'])).

thf('81',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k2_relset_1 @ X38 @ X39 @ X37 )
        = ( k2_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('82',plain,(
    ! [X0: $i,X1: $i] :
      ( ( k2_relset_1 @ X1 @ X0 @ k1_xboole_0 )
      = ( k2_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['80','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k2_relat_1 @ k1_xboole_0 ) @ ( k1_zfmisc_1 @ X0 ) ) ),
    inference(demod,[status(thm)],['79','82'])).

thf('84',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('85',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference('sup-',[status(thm)],['83','84'])).

thf('86',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('87',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['85','86'])).

thf('88',plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(demod,[status(thm)],['4','74','87'])).

thf('89',plain,(
    $false ),
    inference(simplify,[status(thm)],['88'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.FNR8nYDuGu
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % DateTime   : Tue Dec  1 17:17:53 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.19/0.35  % Running portfolio for 600 s
% 0.19/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.19/0.35  % Number of cores: 8
% 0.19/0.35  % Python version: Python 3.6.8
% 0.19/0.36  % Running in FO mode
% 0.54/0.73  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.54/0.73  % Solved by: fo/fo7.sh
% 0.54/0.73  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.54/0.73  % done 305 iterations in 0.240s
% 0.54/0.73  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.54/0.73  % SZS output start Refutation
% 0.54/0.73  thf(sk_C_2_type, type, sk_C_2: $i > $i).
% 0.54/0.73  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.54/0.73  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.54/0.73  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.54/0.73  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.54/0.73  thf(sk_B_type, type, sk_B: $i > $i).
% 0.54/0.73  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.54/0.73  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.54/0.73  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.54/0.73  thf(sk_C_3_type, type, sk_C_3: $i).
% 0.54/0.73  thf(sk_A_type, type, sk_A: $i).
% 0.54/0.73  thf(sk_C_type, type, sk_C: $i > $i > $i).
% 0.54/0.73  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.54/0.73  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.54/0.73  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.54/0.73  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.54/0.73  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.54/0.73  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.54/0.73  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.54/0.73  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.54/0.73  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.54/0.73  thf(t50_relset_1, conjecture,
% 0.54/0.73    (![A:$i]:
% 0.54/0.73     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.54/0.73       ( ![B:$i]:
% 0.54/0.73         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.54/0.73           ( ![C:$i]:
% 0.54/0.73             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.54/0.73               ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.54/0.73                    ( ![D:$i]:
% 0.54/0.73                      ( ( m1_subset_1 @ D @ B ) =>
% 0.54/0.73                        ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.54/0.73  thf(zf_stmt_0, negated_conjecture,
% 0.54/0.73    (~( ![A:$i]:
% 0.54/0.73        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.54/0.73          ( ![B:$i]:
% 0.54/0.73            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.54/0.73              ( ![C:$i]:
% 0.54/0.73                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.54/0.73                  ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.54/0.73                       ( ![D:$i]:
% 0.54/0.73                         ( ( m1_subset_1 @ D @ B ) =>
% 0.54/0.73                           ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.54/0.73    inference('cnf.neg', [status(esa)], [t50_relset_1])).
% 0.54/0.73  thf('0', plain, (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) != (k1_xboole_0))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('1', plain,
% 0.54/0.73      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf(redefinition_k2_relset_1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.73       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.54/0.73  thf('2', plain,
% 0.54/0.73      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.54/0.73         (((k2_relset_1 @ X38 @ X39 @ X37) = (k2_relat_1 @ X37))
% 0.54/0.73          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.54/0.73      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.54/0.73  thf('3', plain,
% 0.54/0.73      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) = (k2_relat_1 @ sk_C_3))),
% 0.54/0.73      inference('sup-', [status(thm)], ['1', '2'])).
% 0.54/0.73  thf('4', plain, (((k2_relat_1 @ sk_C_3) != (k1_xboole_0))),
% 0.54/0.73      inference('demod', [status(thm)], ['0', '3'])).
% 0.54/0.73  thf(d3_tarski, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( r1_tarski @ A @ B ) <=>
% 0.54/0.73       ( ![C:$i]: ( ( r2_hidden @ C @ A ) => ( r2_hidden @ C @ B ) ) ) ))).
% 0.54/0.73  thf('5', plain,
% 0.54/0.73      (![X1 : $i, X3 : $i]:
% 0.54/0.73         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.54/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.73  thf('6', plain,
% 0.54/0.73      (![X40 : $i]:
% 0.54/0.73         (~ (r2_hidden @ X40 @ (k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3))
% 0.54/0.73          | ~ (m1_subset_1 @ X40 @ sk_B_1))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('7', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         ((r1_tarski @ (k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) @ X0)
% 0.54/0.73          | ~ (m1_subset_1 @ 
% 0.54/0.73               (sk_C @ X0 @ (k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3)) @ sk_B_1))),
% 0.54/0.73      inference('sup-', [status(thm)], ['5', '6'])).
% 0.54/0.73  thf('8', plain,
% 0.54/0.73      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf(redefinition_k1_relset_1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.73       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.54/0.73  thf('9', plain,
% 0.54/0.73      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.54/0.73         (((k1_relset_1 @ X35 @ X36 @ X34) = (k1_relat_1 @ X34))
% 0.54/0.73          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.54/0.73      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.54/0.73  thf('10', plain,
% 0.54/0.73      (((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) = (k1_relat_1 @ sk_C_3))),
% 0.54/0.73      inference('sup-', [status(thm)], ['8', '9'])).
% 0.54/0.73  thf('11', plain,
% 0.54/0.73      (((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) = (k1_relat_1 @ sk_C_3))),
% 0.54/0.73      inference('sup-', [status(thm)], ['8', '9'])).
% 0.54/0.73  thf('12', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         ((r1_tarski @ (k1_relat_1 @ sk_C_3) @ X0)
% 0.54/0.73          | ~ (m1_subset_1 @ (sk_C @ X0 @ (k1_relat_1 @ sk_C_3)) @ sk_B_1))),
% 0.54/0.73      inference('demod', [status(thm)], ['7', '10', '11'])).
% 0.54/0.73  thf('13', plain,
% 0.54/0.73      (![X1 : $i, X3 : $i]:
% 0.54/0.73         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.54/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.73  thf('14', plain,
% 0.54/0.73      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf(cc2_relset_1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.73       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.54/0.73  thf('15', plain,
% 0.54/0.73      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.54/0.73         ((v4_relat_1 @ X28 @ X29)
% 0.54/0.73          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.54/0.73      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.73  thf('16', plain, ((v4_relat_1 @ sk_C_3 @ sk_B_1)),
% 0.54/0.73      inference('sup-', [status(thm)], ['14', '15'])).
% 0.54/0.73  thf(d18_relat_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( v1_relat_1 @ B ) =>
% 0.54/0.73       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.54/0.73  thf('17', plain,
% 0.54/0.73      (![X16 : $i, X17 : $i]:
% 0.54/0.73         (~ (v4_relat_1 @ X16 @ X17)
% 0.54/0.73          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 0.54/0.73          | ~ (v1_relat_1 @ X16))),
% 0.54/0.73      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.54/0.73  thf('18', plain,
% 0.54/0.73      ((~ (v1_relat_1 @ sk_C_3) | (r1_tarski @ (k1_relat_1 @ sk_C_3) @ sk_B_1))),
% 0.54/0.73      inference('sup-', [status(thm)], ['16', '17'])).
% 0.54/0.73  thf('19', plain,
% 0.54/0.73      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf(cc2_relat_1, axiom,
% 0.54/0.73    (![A:$i]:
% 0.54/0.73     ( ( v1_relat_1 @ A ) =>
% 0.54/0.73       ( ![B:$i]:
% 0.54/0.73         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.54/0.73  thf('20', plain,
% 0.54/0.73      (![X14 : $i, X15 : $i]:
% 0.54/0.73         (~ (m1_subset_1 @ X14 @ (k1_zfmisc_1 @ X15))
% 0.54/0.73          | (v1_relat_1 @ X14)
% 0.54/0.73          | ~ (v1_relat_1 @ X15))),
% 0.54/0.73      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.54/0.73  thf('21', plain,
% 0.54/0.73      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)) | (v1_relat_1 @ sk_C_3))),
% 0.54/0.73      inference('sup-', [status(thm)], ['19', '20'])).
% 0.54/0.73  thf(fc6_relat_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.54/0.73  thf('22', plain,
% 0.54/0.73      (![X25 : $i, X26 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X25 @ X26))),
% 0.54/0.73      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.54/0.73  thf('23', plain, ((v1_relat_1 @ sk_C_3)),
% 0.54/0.73      inference('demod', [status(thm)], ['21', '22'])).
% 0.54/0.73  thf('24', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_3) @ sk_B_1)),
% 0.54/0.73      inference('demod', [status(thm)], ['18', '23'])).
% 0.54/0.73  thf('25', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.73         (~ (r2_hidden @ X0 @ X1)
% 0.54/0.73          | (r2_hidden @ X0 @ X2)
% 0.54/0.73          | ~ (r1_tarski @ X1 @ X2))),
% 0.54/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.73  thf('26', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         ((r2_hidden @ X0 @ sk_B_1)
% 0.54/0.73          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_C_3)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['24', '25'])).
% 0.54/0.73  thf('27', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         ((r1_tarski @ (k1_relat_1 @ sk_C_3) @ X0)
% 0.54/0.73          | (r2_hidden @ (sk_C @ X0 @ (k1_relat_1 @ sk_C_3)) @ sk_B_1))),
% 0.54/0.73      inference('sup-', [status(thm)], ['13', '26'])).
% 0.54/0.73  thf(t1_subset, axiom,
% 0.54/0.73    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.54/0.73  thf('28', plain,
% 0.54/0.73      (![X9 : $i, X10 : $i]:
% 0.54/0.73         ((m1_subset_1 @ X9 @ X10) | ~ (r2_hidden @ X9 @ X10))),
% 0.54/0.73      inference('cnf', [status(esa)], [t1_subset])).
% 0.54/0.73  thf('29', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         ((r1_tarski @ (k1_relat_1 @ sk_C_3) @ X0)
% 0.54/0.73          | (m1_subset_1 @ (sk_C @ X0 @ (k1_relat_1 @ sk_C_3)) @ sk_B_1))),
% 0.54/0.73      inference('sup-', [status(thm)], ['27', '28'])).
% 0.54/0.73  thf('30', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ sk_C_3) @ X0)),
% 0.54/0.73      inference('clc', [status(thm)], ['12', '29'])).
% 0.54/0.73  thf(t3_xboole_1, axiom,
% 0.54/0.73    (![A:$i]:
% 0.54/0.73     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.54/0.73  thf('31', plain,
% 0.54/0.73      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ k1_xboole_0))),
% 0.54/0.73      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.54/0.73  thf('32', plain, (((k1_relat_1 @ sk_C_3) = (k1_xboole_0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['30', '31'])).
% 0.54/0.73  thf(t56_relat_1, axiom,
% 0.54/0.73    (![A:$i]:
% 0.54/0.73     ( ( v1_relat_1 @ A ) =>
% 0.54/0.73       ( ( ![B:$i,C:$i]: ( ~( r2_hidden @ ( k4_tarski @ B @ C ) @ A ) ) ) =>
% 0.54/0.73         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.54/0.73  thf('33', plain,
% 0.54/0.73      (![X27 : $i]:
% 0.54/0.73         ((r2_hidden @ (k4_tarski @ (sk_B @ X27) @ (sk_C_2 @ X27)) @ X27)
% 0.54/0.73          | ((X27) = (k1_xboole_0))
% 0.54/0.73          | ~ (v1_relat_1 @ X27))),
% 0.54/0.73      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.54/0.73  thf(d4_relat_1, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( ( B ) = ( k1_relat_1 @ A ) ) <=>
% 0.54/0.73       ( ![C:$i]:
% 0.54/0.73         ( ( r2_hidden @ C @ B ) <=>
% 0.54/0.73           ( ?[D:$i]: ( r2_hidden @ ( k4_tarski @ C @ D ) @ A ) ) ) ) ))).
% 0.54/0.73  thf('34', plain,
% 0.54/0.73      (![X18 : $i, X19 : $i, X20 : $i, X21 : $i]:
% 0.54/0.73         (~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ X20)
% 0.54/0.73          | (r2_hidden @ X18 @ X21)
% 0.54/0.73          | ((X21) != (k1_relat_1 @ X20)))),
% 0.54/0.73      inference('cnf', [status(esa)], [d4_relat_1])).
% 0.54/0.73  thf('35', plain,
% 0.54/0.73      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.54/0.73         ((r2_hidden @ X18 @ (k1_relat_1 @ X20))
% 0.54/0.73          | ~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ X20))),
% 0.54/0.73      inference('simplify', [status(thm)], ['34'])).
% 0.54/0.73  thf('36', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         (~ (v1_relat_1 @ X0)
% 0.54/0.73          | ((X0) = (k1_xboole_0))
% 0.54/0.73          | (r2_hidden @ (sk_B @ X0) @ (k1_relat_1 @ X0)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['33', '35'])).
% 0.54/0.73  thf('37', plain,
% 0.54/0.73      (((r2_hidden @ (sk_B @ sk_C_3) @ k1_xboole_0)
% 0.54/0.73        | ((sk_C_3) = (k1_xboole_0))
% 0.54/0.73        | ~ (v1_relat_1 @ sk_C_3))),
% 0.54/0.73      inference('sup+', [status(thm)], ['32', '36'])).
% 0.54/0.73  thf('38', plain, ((v1_relat_1 @ sk_C_3)),
% 0.54/0.73      inference('demod', [status(thm)], ['21', '22'])).
% 0.54/0.73  thf('39', plain,
% 0.54/0.73      (((r2_hidden @ (sk_B @ sk_C_3) @ k1_xboole_0)
% 0.54/0.73        | ((sk_C_3) = (k1_xboole_0)))),
% 0.54/0.73      inference('demod', [status(thm)], ['37', '38'])).
% 0.54/0.73  thf('40', plain,
% 0.54/0.73      (![X40 : $i]:
% 0.54/0.73         (~ (r2_hidden @ X40 @ (k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3))
% 0.54/0.73          | ~ (m1_subset_1 @ X40 @ sk_B_1))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf('41', plain,
% 0.54/0.73      (((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_3) = (k1_relat_1 @ sk_C_3))),
% 0.54/0.73      inference('sup-', [status(thm)], ['8', '9'])).
% 0.54/0.73  thf('42', plain,
% 0.54/0.73      (![X40 : $i]:
% 0.54/0.73         (~ (r2_hidden @ X40 @ (k1_relat_1 @ sk_C_3))
% 0.54/0.73          | ~ (m1_subset_1 @ X40 @ sk_B_1))),
% 0.54/0.73      inference('demod', [status(thm)], ['40', '41'])).
% 0.54/0.73  thf('43', plain, (((k1_relat_1 @ sk_C_3) = (k1_xboole_0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['30', '31'])).
% 0.54/0.73  thf('44', plain,
% 0.54/0.73      (![X40 : $i]:
% 0.54/0.73         (~ (r2_hidden @ X40 @ k1_xboole_0) | ~ (m1_subset_1 @ X40 @ sk_B_1))),
% 0.54/0.73      inference('demod', [status(thm)], ['42', '43'])).
% 0.54/0.73  thf('45', plain,
% 0.54/0.73      ((((sk_C_3) = (k1_xboole_0)) | ~ (m1_subset_1 @ (sk_B @ sk_C_3) @ sk_B_1))),
% 0.54/0.73      inference('sup-', [status(thm)], ['39', '44'])).
% 0.54/0.73  thf('46', plain,
% 0.54/0.73      (![X27 : $i]:
% 0.54/0.73         ((r2_hidden @ (k4_tarski @ (sk_B @ X27) @ (sk_C_2 @ X27)) @ X27)
% 0.54/0.73          | ((X27) = (k1_xboole_0))
% 0.54/0.73          | ~ (v1_relat_1 @ X27))),
% 0.54/0.73      inference('cnf', [status(esa)], [t56_relat_1])).
% 0.54/0.73  thf('47', plain,
% 0.54/0.73      ((m1_subset_1 @ sk_C_3 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.54/0.73      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.54/0.73  thf(t3_subset, axiom,
% 0.54/0.73    (![A:$i,B:$i]:
% 0.54/0.73     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.54/0.73  thf('48', plain,
% 0.54/0.73      (![X11 : $i, X12 : $i]:
% 0.54/0.73         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.54/0.73      inference('cnf', [status(esa)], [t3_subset])).
% 0.54/0.73  thf('49', plain, ((r1_tarski @ sk_C_3 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))),
% 0.54/0.73      inference('sup-', [status(thm)], ['47', '48'])).
% 0.54/0.73  thf('50', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.73         (~ (r2_hidden @ X0 @ X1)
% 0.54/0.73          | (r2_hidden @ X0 @ X2)
% 0.54/0.73          | ~ (r1_tarski @ X1 @ X2))),
% 0.54/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.73  thf('51', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         ((r2_hidden @ X0 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))
% 0.54/0.73          | ~ (r2_hidden @ X0 @ sk_C_3))),
% 0.54/0.73      inference('sup-', [status(thm)], ['49', '50'])).
% 0.54/0.73  thf('52', plain,
% 0.54/0.73      ((~ (v1_relat_1 @ sk_C_3)
% 0.54/0.73        | ((sk_C_3) = (k1_xboole_0))
% 0.54/0.73        | (r2_hidden @ (k4_tarski @ (sk_B @ sk_C_3) @ (sk_C_2 @ sk_C_3)) @ 
% 0.54/0.73           (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.54/0.73      inference('sup-', [status(thm)], ['46', '51'])).
% 0.54/0.73  thf('53', plain, ((v1_relat_1 @ sk_C_3)),
% 0.54/0.73      inference('demod', [status(thm)], ['21', '22'])).
% 0.54/0.73  thf('54', plain,
% 0.54/0.73      ((((sk_C_3) = (k1_xboole_0))
% 0.54/0.73        | (r2_hidden @ (k4_tarski @ (sk_B @ sk_C_3) @ (sk_C_2 @ sk_C_3)) @ 
% 0.54/0.73           (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.54/0.73      inference('demod', [status(thm)], ['52', '53'])).
% 0.54/0.73  thf('55', plain,
% 0.54/0.73      (![X18 : $i, X19 : $i, X20 : $i]:
% 0.54/0.73         ((r2_hidden @ X18 @ (k1_relat_1 @ X20))
% 0.54/0.73          | ~ (r2_hidden @ (k4_tarski @ X18 @ X19) @ X20))),
% 0.54/0.73      inference('simplify', [status(thm)], ['34'])).
% 0.54/0.73  thf('56', plain,
% 0.54/0.73      ((((sk_C_3) = (k1_xboole_0))
% 0.54/0.73        | (r2_hidden @ (sk_B @ sk_C_3) @ 
% 0.54/0.73           (k1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A))))),
% 0.54/0.73      inference('sup-', [status(thm)], ['54', '55'])).
% 0.54/0.73  thf('57', plain,
% 0.54/0.73      (![X1 : $i, X3 : $i]:
% 0.54/0.73         ((r1_tarski @ X1 @ X3) | (r2_hidden @ (sk_C @ X3 @ X1) @ X1))),
% 0.54/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.73  thf('58', plain,
% 0.54/0.73      (![X1 : $i, X3 : $i]:
% 0.54/0.73         ((r1_tarski @ X1 @ X3) | ~ (r2_hidden @ (sk_C @ X3 @ X1) @ X3))),
% 0.54/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.73  thf('59', plain,
% 0.54/0.73      (![X0 : $i]: ((r1_tarski @ X0 @ X0) | (r1_tarski @ X0 @ X0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['57', '58'])).
% 0.54/0.73  thf('60', plain, (![X0 : $i]: (r1_tarski @ X0 @ X0)),
% 0.54/0.73      inference('simplify', [status(thm)], ['59'])).
% 0.54/0.73  thf('61', plain,
% 0.54/0.73      (![X11 : $i, X13 : $i]:
% 0.54/0.73         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.54/0.73      inference('cnf', [status(esa)], [t3_subset])).
% 0.54/0.73  thf('62', plain, (![X0 : $i]: (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ X0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['60', '61'])).
% 0.54/0.73  thf('63', plain,
% 0.54/0.73      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.54/0.73         ((v4_relat_1 @ X28 @ X29)
% 0.54/0.73          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.54/0.73      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.54/0.73  thf('64', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]: (v4_relat_1 @ (k2_zfmisc_1 @ X1 @ X0) @ X1)),
% 0.54/0.73      inference('sup-', [status(thm)], ['62', '63'])).
% 0.54/0.73  thf('65', plain,
% 0.54/0.73      (![X16 : $i, X17 : $i]:
% 0.54/0.73         (~ (v4_relat_1 @ X16 @ X17)
% 0.54/0.73          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 0.54/0.73          | ~ (v1_relat_1 @ X16))),
% 0.54/0.73      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.54/0.73  thf('66', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         (~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))
% 0.54/0.73          | (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['64', '65'])).
% 0.54/0.73  thf('67', plain,
% 0.54/0.73      (![X25 : $i, X26 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X25 @ X26))),
% 0.54/0.73      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.54/0.73  thf('68', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1)) @ X0)),
% 0.54/0.73      inference('demod', [status(thm)], ['66', '67'])).
% 0.54/0.73  thf('69', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.73         (~ (r2_hidden @ X0 @ X1)
% 0.54/0.73          | (r2_hidden @ X0 @ X2)
% 0.54/0.73          | ~ (r1_tarski @ X1 @ X2))),
% 0.54/0.73      inference('cnf', [status(esa)], [d3_tarski])).
% 0.54/0.73  thf('70', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.54/0.73         ((r2_hidden @ X2 @ X0)
% 0.54/0.73          | ~ (r2_hidden @ X2 @ (k1_relat_1 @ (k2_zfmisc_1 @ X0 @ X1))))),
% 0.54/0.73      inference('sup-', [status(thm)], ['68', '69'])).
% 0.54/0.73  thf('71', plain,
% 0.54/0.73      ((((sk_C_3) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ sk_C_3) @ sk_B_1))),
% 0.54/0.73      inference('sup-', [status(thm)], ['56', '70'])).
% 0.54/0.73  thf('72', plain,
% 0.54/0.73      (![X9 : $i, X10 : $i]:
% 0.54/0.73         ((m1_subset_1 @ X9 @ X10) | ~ (r2_hidden @ X9 @ X10))),
% 0.54/0.73      inference('cnf', [status(esa)], [t1_subset])).
% 0.54/0.73  thf('73', plain,
% 0.54/0.73      ((((sk_C_3) = (k1_xboole_0)) | (m1_subset_1 @ (sk_B @ sk_C_3) @ sk_B_1))),
% 0.54/0.73      inference('sup-', [status(thm)], ['71', '72'])).
% 0.54/0.73  thf('74', plain, (((sk_C_3) = (k1_xboole_0))),
% 0.54/0.73      inference('clc', [status(thm)], ['45', '73'])).
% 0.54/0.73  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.54/0.73  thf('75', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.54/0.73      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.54/0.73  thf('76', plain,
% 0.54/0.73      (![X11 : $i, X13 : $i]:
% 0.54/0.73         ((m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X13)) | ~ (r1_tarski @ X11 @ X13))),
% 0.54/0.73      inference('cnf', [status(esa)], [t3_subset])).
% 0.54/0.73  thf('77', plain,
% 0.54/0.73      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['75', '76'])).
% 0.54/0.73  thf(dt_k2_relset_1, axiom,
% 0.54/0.73    (![A:$i,B:$i,C:$i]:
% 0.54/0.73     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.54/0.73       ( m1_subset_1 @ ( k2_relset_1 @ A @ B @ C ) @ ( k1_zfmisc_1 @ B ) ) ))).
% 0.54/0.73  thf('78', plain,
% 0.54/0.73      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.54/0.73         ((m1_subset_1 @ (k2_relset_1 @ X31 @ X32 @ X33) @ (k1_zfmisc_1 @ X32))
% 0.54/0.73          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X31 @ X32))))),
% 0.54/0.73      inference('cnf', [status(esa)], [dt_k2_relset_1])).
% 0.54/0.73  thf('79', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         (m1_subset_1 @ (k2_relset_1 @ X1 @ X0 @ k1_xboole_0) @ 
% 0.54/0.73          (k1_zfmisc_1 @ X0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['77', '78'])).
% 0.54/0.73  thf('80', plain,
% 0.54/0.73      (![X0 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['75', '76'])).
% 0.54/0.73  thf('81', plain,
% 0.54/0.73      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.54/0.73         (((k2_relset_1 @ X38 @ X39 @ X37) = (k2_relat_1 @ X37))
% 0.54/0.73          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.54/0.73      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.54/0.73  thf('82', plain,
% 0.54/0.73      (![X0 : $i, X1 : $i]:
% 0.54/0.73         ((k2_relset_1 @ X1 @ X0 @ k1_xboole_0) = (k2_relat_1 @ k1_xboole_0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['80', '81'])).
% 0.54/0.73  thf('83', plain,
% 0.54/0.73      (![X0 : $i]:
% 0.54/0.73         (m1_subset_1 @ (k2_relat_1 @ k1_xboole_0) @ (k1_zfmisc_1 @ X0))),
% 0.54/0.73      inference('demod', [status(thm)], ['79', '82'])).
% 0.54/0.73  thf('84', plain,
% 0.54/0.73      (![X11 : $i, X12 : $i]:
% 0.54/0.73         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.54/0.73      inference('cnf', [status(esa)], [t3_subset])).
% 0.54/0.73  thf('85', plain, (![X0 : $i]: (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ X0)),
% 0.54/0.73      inference('sup-', [status(thm)], ['83', '84'])).
% 0.54/0.73  thf('86', plain,
% 0.54/0.73      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ k1_xboole_0))),
% 0.54/0.73      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.54/0.73  thf('87', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.54/0.73      inference('sup-', [status(thm)], ['85', '86'])).
% 0.54/0.73  thf('88', plain, (((k1_xboole_0) != (k1_xboole_0))),
% 0.54/0.73      inference('demod', [status(thm)], ['4', '74', '87'])).
% 0.54/0.73  thf('89', plain, ($false), inference('simplify', [status(thm)], ['88'])).
% 0.54/0.73  
% 0.54/0.73  % SZS output end Refutation
% 0.54/0.73  
% 0.54/0.74  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
