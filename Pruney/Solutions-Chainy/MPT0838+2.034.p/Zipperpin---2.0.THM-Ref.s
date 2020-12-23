%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6zj3nrOdCC

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 127 expanded)
%              Number of leaves         :   40 (  52 expanded)
%              Depth                    :   16
%              Number of atoms          :  656 (1095 expanded)
%              Number of equality atoms :   50 (  69 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t7_xboole_0,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( r2_hidden @ B @ A ) ) )).

thf('0',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
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
    ! [X43: $i] :
      ( ~ ( r2_hidden @ X43 @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X43 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,
    ( ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['0','1'])).

thf('3',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('4',plain,(
    ! [X40: $i,X41: $i,X42: $i] :
      ( ( ( k2_relset_1 @ X41 @ X42 @ X40 )
        = ( k2_relat_1 @ X40 ) )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X41 @ X42 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('5',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('6',plain,
    ( ( k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['3','4'])).

thf('7',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['2','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('9',plain,(
    ! [X34: $i,X35: $i,X36: $i] :
      ( ( v5_relat_1 @ X34 @ X36 )
      | ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('10',plain,(
    v5_relat_1 @ sk_C_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['8','9'])).

thf(d19_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v5_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ) )).

thf('11',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( v5_relat_1 @ X24 @ X25 )
      | ( r1_tarski @ ( k2_relat_1 @ X24 ) @ X25 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[d19_relat_1])).

thf('12',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('14',plain,(
    ! [X20: $i,X21: $i] :
      ( ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ X21 ) )
      | ( v1_relat_1 @ X20 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('16',plain,(
    ! [X26: $i,X27: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X26 @ X27 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('17',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('18',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['12','17'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('19',plain,(
    ! [X17: $i,X19: $i] :
      ( ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ X19 ) )
      | ~ ( r1_tarski @ X17 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('20',plain,(
    m1_subset_1 @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X15: $i,X16: $i] :
      ( ( r2_hidden @ X15 @ X16 )
      | ( v1_xboole_0 @ X16 )
      | ~ ( m1_subset_1 @ X15 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('22',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ( r2_hidden @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('23',plain,(
    ! [X12: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('24',plain,(
    r2_hidden @ ( k2_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['22','23'])).

thf('25',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference(cnf,[status(esa)],[t7_xboole_0])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('26',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ~ ( r2_hidden @ X4 @ X5 )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ( r2_hidden @ X6 @ X7 )
      | ( X7
       != ( k3_tarski @ X5 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('27',plain,(
    ! [X4: $i,X5: $i,X6: $i] :
      ( ( r2_hidden @ X6 @ ( k3_tarski @ X5 ) )
      | ~ ( r2_hidden @ X6 @ X4 )
      | ~ ( r2_hidden @ X4 @ X5 ) ) ),
    inference(simplify,[status(thm)],['26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['25','27'])).

thf('29',plain,
    ( ( r2_hidden @ ( sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_B_1 ) ) )
    | ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','28'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('30',plain,(
    ! [X11: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X11 ) )
      = X11 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('31',plain,
    ( ( r2_hidden @ ( sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ sk_B_1 )
    | ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['29','30'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('32',plain,(
    ! [X13: $i,X14: $i] :
      ( ( m1_subset_1 @ X13 @ X14 )
      | ~ ( r2_hidden @ X13 @ X14 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('33',plain,
    ( ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 )
    | ( m1_subset_1 @ ( sk_B @ ( k2_relat_1 @ sk_C_1 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['31','32'])).

thf('34',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference(clc,[status(thm)],['7','33'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X1: $i,X2: $i] :
      ( ( r1_tarski @ X1 @ X2 )
      | ( X1 != X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('36',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['35'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('37',plain,(
    ! [X22: $i,X23: $i] :
      ( ~ ( r1_tarski @ ( k1_relat_1 @ X22 ) @ X23 )
      | ( v4_relat_1 @ X22 @ X23 )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('38',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( v4_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['36','37'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('39',plain,(
    ! [X32: $i,X33: $i] :
      ( ( X32
        = ( k7_relat_1 @ X32 @ X33 ) )
      | ~ ( v4_relat_1 @ X32 @ X33 )
      | ~ ( v1_relat_1 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('40',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    ! [X0: $i] :
      ( ( X0
        = ( k7_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['40'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('42',plain,(
    ! [X28: $i,X29: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X28 @ X29 ) )
        = ( k9_relat_1 @ X28 @ X29 ) )
      | ~ ( v1_relat_1 @ X28 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) ) ) ) ),
    inference(simplify,[status(thm)],['43'])).

thf('45',plain,(
    ! [X2: $i] :
      ( r1_tarski @ X2 @ X2 ) ),
    inference(simplify,[status(thm)],['35'])).

thf(t152_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k1_relat_1 @ B ) )
          & ( ( k9_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf('46',plain,(
    ! [X30: $i,X31: $i] :
      ( ( X30 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X31 )
      | ~ ( r1_tarski @ X30 @ ( k1_relat_1 @ X31 ) )
      | ( ( k9_relat_1 @ X31 @ X30 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t152_relat_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ X0 @ ( k1_relat_1 @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['34','49'])).

thf('51',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['15','16'])).

thf('52',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['50','51'])).

thf('53',plain,
    ( ( k1_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['52'])).

thf('54',plain,(
    ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('55',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('56',plain,(
    ! [X37: $i,X38: $i,X39: $i] :
      ( ( ( k1_relset_1 @ X38 @ X39 @ X37 )
        = ( k1_relat_1 @ X37 ) )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X38 @ X39 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('57',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ( k1_relat_1 @ sk_C_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['54','57'])).

thf('59',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['53','58'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.6zj3nrOdCC
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:06:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.21/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.54  % Solved by: fo/fo7.sh
% 0.21/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.54  % done 191 iterations in 0.084s
% 0.21/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.54  % SZS output start Refutation
% 0.21/0.54  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.21/0.54  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.54  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.21/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.54  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.54  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.54  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.54  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.54  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.54  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.54  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.21/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.54  thf(sk_B_type, type, sk_B: $i > $i).
% 0.21/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.54  thf(t7_xboole_0, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.54          ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ) ))).
% 0.21/0.54  thf('0', plain,
% 0.21/0.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.54  thf(t49_relset_1, conjecture,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.54           ( ![C:$i]:
% 0.21/0.54             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54               ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.54                    ( ![D:$i]:
% 0.21/0.54                      ( ( m1_subset_1 @ D @ B ) =>
% 0.21/0.54                        ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.21/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.54    (~( ![A:$i]:
% 0.21/0.54        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.21/0.54          ( ![B:$i]:
% 0.21/0.54            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.21/0.54              ( ![C:$i]:
% 0.21/0.54                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54                  ( ~( ( ( k1_relset_1 @ A @ B @ C ) != ( k1_xboole_0 ) ) & 
% 0.21/0.54                       ( ![D:$i]:
% 0.21/0.54                         ( ( m1_subset_1 @ D @ B ) =>
% 0.21/0.54                           ( ~( r2_hidden @ D @ ( k2_relset_1 @ A @ B @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.21/0.54    inference('cnf.neg', [status(esa)], [t49_relset_1])).
% 0.21/0.54  thf('1', plain,
% 0.21/0.54      (![X43 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X43 @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1))
% 0.21/0.54          | ~ (m1_subset_1 @ X43 @ sk_B_1))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('2', plain,
% 0.21/0.54      ((((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_xboole_0))
% 0.21/0.54        | ~ (m1_subset_1 @ (sk_B @ (k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1)) @ 
% 0.21/0.54             sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['0', '1'])).
% 0.21/0.54  thf('3', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(redefinition_k2_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.21/0.54  thf('4', plain,
% 0.21/0.54      (![X40 : $i, X41 : $i, X42 : $i]:
% 0.21/0.54         (((k2_relset_1 @ X41 @ X42 @ X40) = (k2_relat_1 @ X40))
% 0.21/0.54          | ~ (m1_subset_1 @ X40 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X41 @ X42))))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.21/0.54  thf('5', plain,
% 0.21/0.54      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.54  thf('6', plain,
% 0.21/0.54      (((k2_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['3', '4'])).
% 0.21/0.54  thf('7', plain,
% 0.21/0.54      ((((k2_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.21/0.54        | ~ (m1_subset_1 @ (sk_B @ (k2_relat_1 @ sk_C_1)) @ sk_B_1))),
% 0.21/0.54      inference('demod', [status(thm)], ['2', '5', '6'])).
% 0.21/0.54  thf('8', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(cc2_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.54  thf('9', plain,
% 0.21/0.54      (![X34 : $i, X35 : $i, X36 : $i]:
% 0.21/0.54         ((v5_relat_1 @ X34 @ X36)
% 0.21/0.54          | ~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36))))),
% 0.21/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.54  thf('10', plain, ((v5_relat_1 @ sk_C_1 @ sk_B_1)),
% 0.21/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.54  thf(d19_relat_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ B ) =>
% 0.21/0.54       ( ( v5_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k2_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.54  thf('11', plain,
% 0.21/0.54      (![X24 : $i, X25 : $i]:
% 0.21/0.54         (~ (v5_relat_1 @ X24 @ X25)
% 0.21/0.54          | (r1_tarski @ (k2_relat_1 @ X24) @ X25)
% 0.21/0.54          | ~ (v1_relat_1 @ X24))),
% 0.21/0.54      inference('cnf', [status(esa)], [d19_relat_1])).
% 0.21/0.54  thf('12', plain,
% 0.21/0.54      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['10', '11'])).
% 0.21/0.54  thf('13', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(cc2_relat_1, axiom,
% 0.21/0.54    (![A:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ A ) =>
% 0.21/0.54       ( ![B:$i]:
% 0.21/0.54         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.21/0.54  thf('14', plain,
% 0.21/0.54      (![X20 : $i, X21 : $i]:
% 0.21/0.54         (~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ X21))
% 0.21/0.54          | (v1_relat_1 @ X20)
% 0.21/0.54          | ~ (v1_relat_1 @ X21))),
% 0.21/0.54      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.21/0.54  thf('15', plain,
% 0.21/0.54      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)) | (v1_relat_1 @ sk_C_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['13', '14'])).
% 0.21/0.54  thf(fc6_relat_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.54  thf('16', plain,
% 0.21/0.54      (![X26 : $i, X27 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X26 @ X27))),
% 0.21/0.54      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.54  thf('17', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.54      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.54  thf('18', plain, ((r1_tarski @ (k2_relat_1 @ sk_C_1) @ sk_B_1)),
% 0.21/0.54      inference('demod', [status(thm)], ['12', '17'])).
% 0.21/0.54  thf(t3_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.54  thf('19', plain,
% 0.21/0.54      (![X17 : $i, X19 : $i]:
% 0.21/0.54         ((m1_subset_1 @ X17 @ (k1_zfmisc_1 @ X19)) | ~ (r1_tarski @ X17 @ X19))),
% 0.21/0.54      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.54  thf('20', plain,
% 0.21/0.54      ((m1_subset_1 @ (k2_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.21/0.54  thf(t2_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ A @ B ) =>
% 0.21/0.54       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.21/0.54  thf('21', plain,
% 0.21/0.54      (![X15 : $i, X16 : $i]:
% 0.21/0.54         ((r2_hidden @ X15 @ X16)
% 0.21/0.54          | (v1_xboole_0 @ X16)
% 0.21/0.54          | ~ (m1_subset_1 @ X15 @ X16))),
% 0.21/0.54      inference('cnf', [status(esa)], [t2_subset])).
% 0.21/0.54  thf('22', plain,
% 0.21/0.54      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.21/0.54        | (r2_hidden @ (k2_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B_1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['20', '21'])).
% 0.21/0.54  thf(fc1_subset_1, axiom,
% 0.21/0.54    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.21/0.54  thf('23', plain, (![X12 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.21/0.54      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.21/0.54  thf('24', plain,
% 0.21/0.54      ((r2_hidden @ (k2_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.21/0.54      inference('clc', [status(thm)], ['22', '23'])).
% 0.21/0.54  thf('25', plain,
% 0.21/0.54      (![X0 : $i]: (((X0) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X0) @ X0))),
% 0.21/0.54      inference('cnf', [status(esa)], [t7_xboole_0])).
% 0.21/0.54  thf(d4_tarski, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.21/0.54       ( ![C:$i]:
% 0.21/0.54         ( ( r2_hidden @ C @ B ) <=>
% 0.21/0.54           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.21/0.54  thf('26', plain,
% 0.21/0.54      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.21/0.54         (~ (r2_hidden @ X4 @ X5)
% 0.21/0.54          | ~ (r2_hidden @ X6 @ X4)
% 0.21/0.54          | (r2_hidden @ X6 @ X7)
% 0.21/0.54          | ((X7) != (k3_tarski @ X5)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d4_tarski])).
% 0.21/0.54  thf('27', plain,
% 0.21/0.54      (![X4 : $i, X5 : $i, X6 : $i]:
% 0.21/0.54         ((r2_hidden @ X6 @ (k3_tarski @ X5))
% 0.21/0.54          | ~ (r2_hidden @ X6 @ X4)
% 0.21/0.54          | ~ (r2_hidden @ X4 @ X5))),
% 0.21/0.54      inference('simplify', [status(thm)], ['26'])).
% 0.21/0.54  thf('28', plain,
% 0.21/0.54      (![X0 : $i, X1 : $i]:
% 0.21/0.54         (((X0) = (k1_xboole_0))
% 0.21/0.54          | ~ (r2_hidden @ X0 @ X1)
% 0.21/0.54          | (r2_hidden @ (sk_B @ X0) @ (k3_tarski @ X1)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['25', '27'])).
% 0.21/0.54  thf('29', plain,
% 0.21/0.54      (((r2_hidden @ (sk_B @ (k2_relat_1 @ sk_C_1)) @ 
% 0.21/0.54         (k3_tarski @ (k1_zfmisc_1 @ sk_B_1)))
% 0.21/0.54        | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['24', '28'])).
% 0.21/0.54  thf(t99_zfmisc_1, axiom,
% 0.21/0.54    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.21/0.54  thf('30', plain, (![X11 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X11)) = (X11))),
% 0.21/0.54      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.21/0.54  thf('31', plain,
% 0.21/0.54      (((r2_hidden @ (sk_B @ (k2_relat_1 @ sk_C_1)) @ sk_B_1)
% 0.21/0.54        | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['29', '30'])).
% 0.21/0.54  thf(t1_subset, axiom,
% 0.21/0.54    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.21/0.54  thf('32', plain,
% 0.21/0.54      (![X13 : $i, X14 : $i]:
% 0.21/0.54         ((m1_subset_1 @ X13 @ X14) | ~ (r2_hidden @ X13 @ X14))),
% 0.21/0.54      inference('cnf', [status(esa)], [t1_subset])).
% 0.21/0.54  thf('33', plain,
% 0.21/0.54      ((((k2_relat_1 @ sk_C_1) = (k1_xboole_0))
% 0.21/0.54        | (m1_subset_1 @ (sk_B @ (k2_relat_1 @ sk_C_1)) @ sk_B_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['31', '32'])).
% 0.21/0.54  thf('34', plain, (((k2_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.21/0.54      inference('clc', [status(thm)], ['7', '33'])).
% 0.21/0.54  thf(d10_xboole_0, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.21/0.54  thf('35', plain,
% 0.21/0.54      (![X1 : $i, X2 : $i]: ((r1_tarski @ X1 @ X2) | ((X1) != (X2)))),
% 0.21/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.21/0.54  thf('36', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.21/0.54      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.54  thf(d18_relat_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ B ) =>
% 0.21/0.54       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.54  thf('37', plain,
% 0.21/0.54      (![X22 : $i, X23 : $i]:
% 0.21/0.54         (~ (r1_tarski @ (k1_relat_1 @ X22) @ X23)
% 0.21/0.54          | (v4_relat_1 @ X22 @ X23)
% 0.21/0.54          | ~ (v1_relat_1 @ X22))),
% 0.21/0.54      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.21/0.54  thf('38', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0) | (v4_relat_1 @ X0 @ (k1_relat_1 @ X0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['36', '37'])).
% 0.21/0.54  thf(t209_relat_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.21/0.54       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.21/0.54  thf('39', plain,
% 0.21/0.54      (![X32 : $i, X33 : $i]:
% 0.21/0.54         (((X32) = (k7_relat_1 @ X32 @ X33))
% 0.21/0.54          | ~ (v4_relat_1 @ X32 @ X33)
% 0.21/0.54          | ~ (v1_relat_1 @ X32))),
% 0.21/0.54      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.21/0.54  thf('40', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.21/0.54      inference('sup-', [status(thm)], ['38', '39'])).
% 0.21/0.54  thf('41', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((X0) = (k7_relat_1 @ X0 @ (k1_relat_1 @ X0))) | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['40'])).
% 0.21/0.54  thf(t148_relat_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ B ) =>
% 0.21/0.54       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.21/0.54  thf('42', plain,
% 0.21/0.54      (![X28 : $i, X29 : $i]:
% 0.21/0.54         (((k2_relat_1 @ (k7_relat_1 @ X28 @ X29)) = (k9_relat_1 @ X28 @ X29))
% 0.21/0.54          | ~ (v1_relat_1 @ X28))),
% 0.21/0.54      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.54  thf('43', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0)))
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('sup+', [status(thm)], ['41', '42'])).
% 0.21/0.54  thf('44', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (~ (v1_relat_1 @ X0)
% 0.21/0.54          | ((k2_relat_1 @ X0) = (k9_relat_1 @ X0 @ (k1_relat_1 @ X0))))),
% 0.21/0.54      inference('simplify', [status(thm)], ['43'])).
% 0.21/0.54  thf('45', plain, (![X2 : $i]: (r1_tarski @ X2 @ X2)),
% 0.21/0.54      inference('simplify', [status(thm)], ['35'])).
% 0.21/0.54  thf(t152_relat_1, axiom,
% 0.21/0.54    (![A:$i,B:$i]:
% 0.21/0.54     ( ( v1_relat_1 @ B ) =>
% 0.21/0.54       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.21/0.54            ( r1_tarski @ A @ ( k1_relat_1 @ B ) ) & 
% 0.21/0.54            ( ( k9_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.21/0.54  thf('46', plain,
% 0.21/0.54      (![X30 : $i, X31 : $i]:
% 0.21/0.54         (((X30) = (k1_xboole_0))
% 0.21/0.54          | ~ (v1_relat_1 @ X31)
% 0.21/0.54          | ~ (r1_tarski @ X30 @ (k1_relat_1 @ X31))
% 0.21/0.54          | ((k9_relat_1 @ X31 @ X30) != (k1_xboole_0)))),
% 0.21/0.54      inference('cnf', [status(esa)], [t152_relat_1])).
% 0.21/0.54  thf('47', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k9_relat_1 @ X0 @ (k1_relat_1 @ X0)) != (k1_xboole_0))
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ((k1_relat_1 @ X0) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.54  thf('48', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k2_relat_1 @ X0) != (k1_xboole_0))
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ((k1_relat_1 @ X0) = (k1_xboole_0))
% 0.21/0.54          | ~ (v1_relat_1 @ X0))),
% 0.21/0.54      inference('sup-', [status(thm)], ['44', '47'])).
% 0.21/0.54  thf('49', plain,
% 0.21/0.54      (![X0 : $i]:
% 0.21/0.54         (((k1_relat_1 @ X0) = (k1_xboole_0))
% 0.21/0.54          | ~ (v1_relat_1 @ X0)
% 0.21/0.54          | ((k2_relat_1 @ X0) != (k1_xboole_0)))),
% 0.21/0.54      inference('simplify', [status(thm)], ['48'])).
% 0.21/0.54  thf('50', plain,
% 0.21/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.54        | ~ (v1_relat_1 @ sk_C_1)
% 0.21/0.54        | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.21/0.54      inference('sup-', [status(thm)], ['34', '49'])).
% 0.21/0.54  thf('51', plain, ((v1_relat_1 @ sk_C_1)),
% 0.21/0.54      inference('demod', [status(thm)], ['15', '16'])).
% 0.21/0.54  thf('52', plain,
% 0.21/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.54        | ((k1_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.21/0.54      inference('demod', [status(thm)], ['50', '51'])).
% 0.21/0.54  thf('53', plain, (((k1_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.21/0.54      inference('simplify', [status(thm)], ['52'])).
% 0.21/0.54  thf('54', plain, (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) != (k1_xboole_0))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf('55', plain,
% 0.21/0.54      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.54  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.54    (![A:$i,B:$i,C:$i]:
% 0.21/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.54       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.54  thf('56', plain,
% 0.21/0.54      (![X37 : $i, X38 : $i, X39 : $i]:
% 0.21/0.54         (((k1_relset_1 @ X38 @ X39 @ X37) = (k1_relat_1 @ X37))
% 0.21/0.54          | ~ (m1_subset_1 @ X37 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X38 @ X39))))),
% 0.21/0.54      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.54  thf('57', plain,
% 0.21/0.54      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.21/0.54      inference('sup-', [status(thm)], ['55', '56'])).
% 0.21/0.54  thf('58', plain, (((k1_relat_1 @ sk_C_1) != (k1_xboole_0))),
% 0.21/0.54      inference('demod', [status(thm)], ['54', '57'])).
% 0.21/0.54  thf('59', plain, ($false),
% 0.21/0.54      inference('simplify_reflect-', [status(thm)], ['53', '58'])).
% 0.21/0.54  
% 0.21/0.54  % SZS output end Refutation
% 0.21/0.54  
% 0.21/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
