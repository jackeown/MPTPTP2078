%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WGpBhf9Atw

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:50:15 EST 2020

% Result     : Theorem 0.47s
% Output     : Refutation 0.47s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 120 expanded)
%              Number of leaves         :   39 (  50 expanded)
%              Depth                    :   17
%              Number of atoms          :  586 (1009 expanded)
%              Number of equality atoms :   38 (  54 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k3_tarski_type,type,(
    k3_tarski: $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k2_relset_1_type,type,(
    k2_relset_1: $i > $i > $i > $i )).

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
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('1',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v4_relat_1 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('2',plain,(
    v4_relat_1 @ sk_C_1 @ sk_B_1 ),
    inference('sup-',[status(thm)],['0','1'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('3',plain,(
    ! [X26: $i,X27: $i] :
      ( ~ ( v4_relat_1 @ X26 @ X27 )
      | ( r1_tarski @ ( k1_relat_1 @ X26 ) @ X27 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('4',plain,
    ( ~ ( v1_relat_1 @ sk_C_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('6',plain,(
    ! [X24: $i,X25: $i] :
      ( ~ ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X25 ) )
      | ( v1_relat_1 @ X24 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('7',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) )
    | ( v1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('8',plain,(
    ! [X28: $i,X29: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X28 @ X29 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('9',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['7','8'])).

thf('10',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_C_1 ) @ sk_B_1 ),
    inference(demod,[status(thm)],['4','9'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('11',plain,(
    ! [X21: $i,X23: $i] :
      ( ( m1_subset_1 @ X21 @ ( k1_zfmisc_1 @ X23 ) )
      | ~ ( r1_tarski @ X21 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('12',plain,(
    m1_subset_1 @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('13',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r2_hidden @ X19 @ X20 )
      | ( v1_xboole_0 @ X20 )
      | ~ ( m1_subset_1 @ X19 @ X20 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('14',plain,
    ( ( v1_xboole_0 @ ( k1_zfmisc_1 @ sk_B_1 ) )
    | ( r2_hidden @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['12','13'])).

thf(fc1_subset_1,axiom,(
    ! [A: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('15',plain,(
    ! [X16: $i] :
      ~ ( v1_xboole_0 @ ( k1_zfmisc_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[fc1_subset_1])).

thf('16',plain,(
    r2_hidden @ ( k1_relat_1 @ sk_C_1 ) @ ( k1_zfmisc_1 @ sk_B_1 ) ),
    inference(clc,[status(thm)],['14','15'])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('17',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf(d4_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( B
        = ( k3_tarski @ A ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ C @ B )
        <=> ? [D: $i] :
              ( ( r2_hidden @ D @ A )
              & ( r2_hidden @ C @ D ) ) ) ) )).

thf('18',plain,(
    ! [X8: $i,X9: $i,X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ X8 @ X9 )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ( r2_hidden @ X10 @ X11 )
      | ( X11
       != ( k3_tarski @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[d4_tarski])).

thf('19',plain,(
    ! [X8: $i,X9: $i,X10: $i] :
      ( ( r2_hidden @ X10 @ ( k3_tarski @ X9 ) )
      | ~ ( r2_hidden @ X10 @ X8 )
      | ~ ( r2_hidden @ X8 @ X9 ) ) ),
    inference(simplify,[status(thm)],['18'])).

thf('20',plain,(
    ! [X0: $i,X1: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ~ ( r2_hidden @ X0 @ X1 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ ( k3_tarski @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['17','19'])).

thf('21',plain,
    ( ( r2_hidden @ ( sk_B @ ( k1_relat_1 @ sk_C_1 ) ) @ ( k3_tarski @ ( k1_zfmisc_1 @ sk_B_1 ) ) )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['16','20'])).

thf(t99_zfmisc_1,axiom,(
    ! [A: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) )
      = A ) )).

thf('22',plain,(
    ! [X15: $i] :
      ( ( k3_tarski @ ( k1_zfmisc_1 @ X15 ) )
      = X15 ) ),
    inference(cnf,[status(esa)],[t99_zfmisc_1])).

thf('23',plain,
    ( ( r2_hidden @ ( sk_B @ ( k1_relat_1 @ sk_C_1 ) ) @ sk_B_1 )
    | ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['21','22'])).

thf(t1_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( r2_hidden @ A @ B )
     => ( m1_subset_1 @ A @ B ) ) )).

thf('24',plain,(
    ! [X17: $i,X18: $i] :
      ( ( m1_subset_1 @ X17 @ X18 )
      | ~ ( r2_hidden @ X17 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t1_subset])).

thf('25',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) )
    | ( m1_subset_1 @ ( sk_B @ ( k1_relat_1 @ sk_C_1 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('27',plain,(
    ! [X42: $i] :
      ( ~ ( r2_hidden @ X42 @ ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_1 ) )
      | ~ ( m1_subset_1 @ X42 @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('28',plain,
    ( ( v1_xboole_0 @ ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_1 ) )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_1 ) ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf('29',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('30',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ( ( k1_relset_1 @ X37 @ X38 @ X36 )
        = ( k1_relat_1 @ X36 ) )
      | ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('31',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('32',plain,
    ( ( k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_1 )
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['29','30'])).

thf('33',plain,
    ( ( v1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) )
    | ~ ( m1_subset_1 @ ( sk_B @ ( k1_relat_1 @ sk_C_1 ) ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['28','31','32'])).

thf('34',plain,(
    v1_xboole_0 @ ( k1_relat_1 @ sk_C_1 ) ),
    inference(clc,[status(thm)],['25','33'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('35',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf(t8_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( v1_xboole_0 @ A )
        & ( A != B )
        & ( v1_xboole_0 @ B ) ) )).

thf('36',plain,(
    ! [X6: $i,X7: $i] :
      ( ~ ( v1_xboole_0 @ X6 )
      | ~ ( v1_xboole_0 @ X7 )
      | ( X6 = X7 ) ) ),
    inference(cnf,[status(esa)],[t8_boole])).

thf('37',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 = X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( k1_xboole_0
    = ( k1_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['34','37'])).

thf(t169_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) )
        = ( k1_relat_1 @ A ) ) ) )).

thf('39',plain,(
    ! [X30: $i] :
      ( ( ( k10_relat_1 @ X30 @ ( k2_relat_1 @ X30 ) )
        = ( k1_relat_1 @ X30 ) )
      | ~ ( v1_relat_1 @ X30 ) ) ),
    inference(cnf,[status(esa)],[t169_relat_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('40',plain,(
    ! [X3: $i,X4: $i] :
      ( ( r1_tarski @ X3 @ X4 )
      | ( X3 != X4 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('41',plain,(
    ! [X4: $i] :
      ( r1_tarski @ X4 @ X4 ) ),
    inference(simplify,[status(thm)],['40'])).

thf(t174_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ~ ( ( A != k1_xboole_0 )
          & ( r1_tarski @ A @ ( k2_relat_1 @ B ) )
          & ( ( k10_relat_1 @ B @ A )
            = k1_xboole_0 ) ) ) )).

thf('42',plain,(
    ! [X31: $i,X32: $i] :
      ( ( X31 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X32 )
      | ~ ( r1_tarski @ X31 @ ( k2_relat_1 @ X32 ) )
      | ( ( k10_relat_1 @ X32 @ X31 )
       != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t174_relat_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ( ( k10_relat_1 @ X0 @ ( k2_relat_1 @ X0 ) )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['39','43'])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ X0 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ( ( k1_relat_1 @ X0 )
       != k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['44'])).

thf('46',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_C_1 )
    | ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','45'])).

thf('47',plain,(
    v1_relat_1 @ sk_C_1 ),
    inference(demod,[status(thm)],['7','8'])).

thf('48',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_C_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['46','47'])).

thf('49',plain,
    ( ( k2_relat_1 @ sk_C_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['48'])).

thf('50',plain,(
    ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_1 )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('51',plain,(
    m1_subset_1 @ sk_C_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B_1 @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k2_relset_1 @ A @ B @ C )
        = ( k2_relat_1 @ C ) ) ) )).

thf('52',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ( ( k2_relset_1 @ X40 @ X41 @ X39 )
        = ( k2_relat_1 @ X39 ) )
      | ~ ( m1_subset_1 @ X39 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X40 @ X41 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k2_relset_1])).

thf('53',plain,
    ( ( k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_1 )
    = ( k2_relat_1 @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ( k2_relat_1 @ sk_C_1 )
 != k1_xboole_0 ),
    inference(demod,[status(thm)],['50','53'])).

thf('55',plain,(
    $false ),
    inference('simplify_reflect-',[status(thm)],['49','54'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WGpBhf9Atw
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:58:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.20/0.35  % Python version: Python 3.6.8
% 0.20/0.35  % Running in FO mode
% 0.47/0.68  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.47/0.68  % Solved by: fo/fo7.sh
% 0.47/0.68  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.47/0.68  % done 272 iterations in 0.231s
% 0.47/0.68  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.47/0.68  % SZS output start Refutation
% 0.47/0.68  thf(k3_tarski_type, type, k3_tarski: $i > $i).
% 0.47/0.68  thf(k10_relat_1_type, type, k10_relat_1: $i > $i > $i).
% 0.47/0.68  thf(sk_B_type, type, sk_B: $i > $i).
% 0.47/0.68  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.47/0.68  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.47/0.68  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.47/0.68  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.47/0.68  thf(sk_C_1_type, type, sk_C_1: $i).
% 0.47/0.68  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.47/0.68  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.47/0.68  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.47/0.68  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.47/0.68  thf(sk_A_type, type, sk_A: $i).
% 0.47/0.68  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.47/0.68  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.47/0.68  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.47/0.68  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.47/0.68  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.47/0.68  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.47/0.68  thf(k2_relset_1_type, type, k2_relset_1: $i > $i > $i > $i).
% 0.47/0.68  thf(t50_relset_1, conjecture,
% 0.47/0.68    (![A:$i]:
% 0.47/0.68     ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.47/0.68       ( ![B:$i]:
% 0.47/0.68         ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.47/0.68           ( ![C:$i]:
% 0.47/0.68             ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.47/0.68               ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.47/0.68                    ( ![D:$i]:
% 0.47/0.68                      ( ( m1_subset_1 @ D @ B ) =>
% 0.47/0.68                        ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ))).
% 0.47/0.68  thf(zf_stmt_0, negated_conjecture,
% 0.47/0.68    (~( ![A:$i]:
% 0.47/0.68        ( ( ~( v1_xboole_0 @ A ) ) =>
% 0.47/0.68          ( ![B:$i]:
% 0.47/0.68            ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.47/0.68              ( ![C:$i]:
% 0.47/0.68                ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) ) =>
% 0.47/0.68                  ( ~( ( ( k2_relset_1 @ B @ A @ C ) != ( k1_xboole_0 ) ) & 
% 0.47/0.68                       ( ![D:$i]:
% 0.47/0.68                         ( ( m1_subset_1 @ D @ B ) =>
% 0.47/0.68                           ( ~( r2_hidden @ D @ ( k1_relset_1 @ B @ A @ C ) ) ) ) ) ) ) ) ) ) ) ) )),
% 0.47/0.68    inference('cnf.neg', [status(esa)], [t50_relset_1])).
% 0.47/0.68  thf('0', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf(cc2_relset_1, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i]:
% 0.47/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.68       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.47/0.68  thf('1', plain,
% 0.47/0.68      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.47/0.68         ((v4_relat_1 @ X33 @ X34)
% 0.47/0.68          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.47/0.68      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.47/0.68  thf('2', plain, ((v4_relat_1 @ sk_C_1 @ sk_B_1)),
% 0.47/0.68      inference('sup-', [status(thm)], ['0', '1'])).
% 0.47/0.68  thf(d18_relat_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( v1_relat_1 @ B ) =>
% 0.47/0.68       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.47/0.68  thf('3', plain,
% 0.47/0.68      (![X26 : $i, X27 : $i]:
% 0.47/0.68         (~ (v4_relat_1 @ X26 @ X27)
% 0.47/0.68          | (r1_tarski @ (k1_relat_1 @ X26) @ X27)
% 0.47/0.68          | ~ (v1_relat_1 @ X26))),
% 0.47/0.68      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.47/0.68  thf('4', plain,
% 0.47/0.68      ((~ (v1_relat_1 @ sk_C_1) | (r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_B_1))),
% 0.47/0.68      inference('sup-', [status(thm)], ['2', '3'])).
% 0.47/0.68  thf('5', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf(cc2_relat_1, axiom,
% 0.47/0.68    (![A:$i]:
% 0.47/0.68     ( ( v1_relat_1 @ A ) =>
% 0.47/0.68       ( ![B:$i]:
% 0.47/0.68         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.47/0.68  thf('6', plain,
% 0.47/0.68      (![X24 : $i, X25 : $i]:
% 0.47/0.68         (~ (m1_subset_1 @ X24 @ (k1_zfmisc_1 @ X25))
% 0.47/0.68          | (v1_relat_1 @ X24)
% 0.47/0.68          | ~ (v1_relat_1 @ X25))),
% 0.47/0.68      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.47/0.68  thf('7', plain,
% 0.47/0.68      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)) | (v1_relat_1 @ sk_C_1))),
% 0.47/0.68      inference('sup-', [status(thm)], ['5', '6'])).
% 0.47/0.68  thf(fc6_relat_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.47/0.68  thf('8', plain,
% 0.47/0.68      (![X28 : $i, X29 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X28 @ X29))),
% 0.47/0.68      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.47/0.68  thf('9', plain, ((v1_relat_1 @ sk_C_1)),
% 0.47/0.68      inference('demod', [status(thm)], ['7', '8'])).
% 0.47/0.68  thf('10', plain, ((r1_tarski @ (k1_relat_1 @ sk_C_1) @ sk_B_1)),
% 0.47/0.68      inference('demod', [status(thm)], ['4', '9'])).
% 0.47/0.68  thf(t3_subset, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.47/0.68  thf('11', plain,
% 0.47/0.68      (![X21 : $i, X23 : $i]:
% 0.47/0.68         ((m1_subset_1 @ X21 @ (k1_zfmisc_1 @ X23)) | ~ (r1_tarski @ X21 @ X23))),
% 0.47/0.68      inference('cnf', [status(esa)], [t3_subset])).
% 0.47/0.68  thf('12', plain,
% 0.47/0.68      ((m1_subset_1 @ (k1_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.47/0.68      inference('sup-', [status(thm)], ['10', '11'])).
% 0.47/0.68  thf(t2_subset, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( m1_subset_1 @ A @ B ) =>
% 0.47/0.68       ( ( v1_xboole_0 @ B ) | ( r2_hidden @ A @ B ) ) ))).
% 0.47/0.68  thf('13', plain,
% 0.47/0.68      (![X19 : $i, X20 : $i]:
% 0.47/0.68         ((r2_hidden @ X19 @ X20)
% 0.47/0.68          | (v1_xboole_0 @ X20)
% 0.47/0.68          | ~ (m1_subset_1 @ X19 @ X20))),
% 0.47/0.68      inference('cnf', [status(esa)], [t2_subset])).
% 0.47/0.68  thf('14', plain,
% 0.47/0.68      (((v1_xboole_0 @ (k1_zfmisc_1 @ sk_B_1))
% 0.47/0.68        | (r2_hidden @ (k1_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B_1)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['12', '13'])).
% 0.47/0.68  thf(fc1_subset_1, axiom,
% 0.47/0.68    (![A:$i]: ( ~( v1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ))).
% 0.47/0.68  thf('15', plain, (![X16 : $i]: ~ (v1_xboole_0 @ (k1_zfmisc_1 @ X16))),
% 0.47/0.68      inference('cnf', [status(esa)], [fc1_subset_1])).
% 0.47/0.68  thf('16', plain,
% 0.47/0.68      ((r2_hidden @ (k1_relat_1 @ sk_C_1) @ (k1_zfmisc_1 @ sk_B_1))),
% 0.47/0.68      inference('clc', [status(thm)], ['14', '15'])).
% 0.47/0.68  thf(d1_xboole_0, axiom,
% 0.47/0.68    (![A:$i]:
% 0.47/0.68     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.47/0.68  thf('17', plain,
% 0.47/0.68      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.47/0.68      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.47/0.68  thf(d4_tarski, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( ( B ) = ( k3_tarski @ A ) ) <=>
% 0.47/0.68       ( ![C:$i]:
% 0.47/0.68         ( ( r2_hidden @ C @ B ) <=>
% 0.47/0.68           ( ?[D:$i]: ( ( r2_hidden @ D @ A ) & ( r2_hidden @ C @ D ) ) ) ) ) ))).
% 0.47/0.68  thf('18', plain,
% 0.47/0.68      (![X8 : $i, X9 : $i, X10 : $i, X11 : $i]:
% 0.47/0.68         (~ (r2_hidden @ X8 @ X9)
% 0.47/0.68          | ~ (r2_hidden @ X10 @ X8)
% 0.47/0.68          | (r2_hidden @ X10 @ X11)
% 0.47/0.68          | ((X11) != (k3_tarski @ X9)))),
% 0.47/0.68      inference('cnf', [status(esa)], [d4_tarski])).
% 0.47/0.68  thf('19', plain,
% 0.47/0.68      (![X8 : $i, X9 : $i, X10 : $i]:
% 0.47/0.68         ((r2_hidden @ X10 @ (k3_tarski @ X9))
% 0.47/0.68          | ~ (r2_hidden @ X10 @ X8)
% 0.47/0.68          | ~ (r2_hidden @ X8 @ X9))),
% 0.47/0.68      inference('simplify', [status(thm)], ['18'])).
% 0.47/0.68  thf('20', plain,
% 0.47/0.68      (![X0 : $i, X1 : $i]:
% 0.47/0.68         ((v1_xboole_0 @ X0)
% 0.47/0.68          | ~ (r2_hidden @ X0 @ X1)
% 0.47/0.68          | (r2_hidden @ (sk_B @ X0) @ (k3_tarski @ X1)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['17', '19'])).
% 0.47/0.68  thf('21', plain,
% 0.47/0.68      (((r2_hidden @ (sk_B @ (k1_relat_1 @ sk_C_1)) @ 
% 0.47/0.68         (k3_tarski @ (k1_zfmisc_1 @ sk_B_1)))
% 0.47/0.68        | (v1_xboole_0 @ (k1_relat_1 @ sk_C_1)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['16', '20'])).
% 0.47/0.68  thf(t99_zfmisc_1, axiom,
% 0.47/0.68    (![A:$i]: ( ( k3_tarski @ ( k1_zfmisc_1 @ A ) ) = ( A ) ))).
% 0.47/0.68  thf('22', plain, (![X15 : $i]: ((k3_tarski @ (k1_zfmisc_1 @ X15)) = (X15))),
% 0.47/0.68      inference('cnf', [status(esa)], [t99_zfmisc_1])).
% 0.47/0.68  thf('23', plain,
% 0.47/0.68      (((r2_hidden @ (sk_B @ (k1_relat_1 @ sk_C_1)) @ sk_B_1)
% 0.47/0.68        | (v1_xboole_0 @ (k1_relat_1 @ sk_C_1)))),
% 0.47/0.68      inference('demod', [status(thm)], ['21', '22'])).
% 0.47/0.68  thf(t1_subset, axiom,
% 0.47/0.68    (![A:$i,B:$i]: ( ( r2_hidden @ A @ B ) => ( m1_subset_1 @ A @ B ) ))).
% 0.47/0.68  thf('24', plain,
% 0.47/0.68      (![X17 : $i, X18 : $i]:
% 0.47/0.68         ((m1_subset_1 @ X17 @ X18) | ~ (r2_hidden @ X17 @ X18))),
% 0.47/0.68      inference('cnf', [status(esa)], [t1_subset])).
% 0.47/0.68  thf('25', plain,
% 0.47/0.68      (((v1_xboole_0 @ (k1_relat_1 @ sk_C_1))
% 0.47/0.68        | (m1_subset_1 @ (sk_B @ (k1_relat_1 @ sk_C_1)) @ sk_B_1))),
% 0.47/0.68      inference('sup-', [status(thm)], ['23', '24'])).
% 0.47/0.68  thf('26', plain,
% 0.47/0.68      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.47/0.68      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.47/0.68  thf('27', plain,
% 0.47/0.68      (![X42 : $i]:
% 0.47/0.68         (~ (r2_hidden @ X42 @ (k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_1))
% 0.47/0.68          | ~ (m1_subset_1 @ X42 @ sk_B_1))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('28', plain,
% 0.47/0.68      (((v1_xboole_0 @ (k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_1))
% 0.47/0.68        | ~ (m1_subset_1 @ (sk_B @ (k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_1)) @ 
% 0.47/0.68             sk_B_1))),
% 0.47/0.68      inference('sup-', [status(thm)], ['26', '27'])).
% 0.47/0.68  thf('29', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf(redefinition_k1_relset_1, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i]:
% 0.47/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.68       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.47/0.68  thf('30', plain,
% 0.47/0.68      (![X36 : $i, X37 : $i, X38 : $i]:
% 0.47/0.68         (((k1_relset_1 @ X37 @ X38 @ X36) = (k1_relat_1 @ X36))
% 0.47/0.68          | ~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38))))),
% 0.47/0.68      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.47/0.68  thf('31', plain,
% 0.47/0.68      (((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.47/0.68      inference('sup-', [status(thm)], ['29', '30'])).
% 0.47/0.68  thf('32', plain,
% 0.47/0.68      (((k1_relset_1 @ sk_B_1 @ sk_A @ sk_C_1) = (k1_relat_1 @ sk_C_1))),
% 0.47/0.68      inference('sup-', [status(thm)], ['29', '30'])).
% 0.47/0.68  thf('33', plain,
% 0.47/0.68      (((v1_xboole_0 @ (k1_relat_1 @ sk_C_1))
% 0.47/0.68        | ~ (m1_subset_1 @ (sk_B @ (k1_relat_1 @ sk_C_1)) @ sk_B_1))),
% 0.47/0.68      inference('demod', [status(thm)], ['28', '31', '32'])).
% 0.47/0.68  thf('34', plain, ((v1_xboole_0 @ (k1_relat_1 @ sk_C_1))),
% 0.47/0.68      inference('clc', [status(thm)], ['25', '33'])).
% 0.47/0.68  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.47/0.68  thf('35', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.47/0.68      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.47/0.68  thf(t8_boole, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ~( ( v1_xboole_0 @ A ) & ( ( A ) != ( B ) ) & ( v1_xboole_0 @ B ) ) ))).
% 0.47/0.68  thf('36', plain,
% 0.47/0.68      (![X6 : $i, X7 : $i]:
% 0.47/0.68         (~ (v1_xboole_0 @ X6) | ~ (v1_xboole_0 @ X7) | ((X6) = (X7)))),
% 0.47/0.68      inference('cnf', [status(esa)], [t8_boole])).
% 0.47/0.68  thf('37', plain,
% 0.47/0.68      (![X0 : $i]: (((k1_xboole_0) = (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['35', '36'])).
% 0.47/0.68  thf('38', plain, (((k1_xboole_0) = (k1_relat_1 @ sk_C_1))),
% 0.47/0.68      inference('sup-', [status(thm)], ['34', '37'])).
% 0.47/0.68  thf(t169_relat_1, axiom,
% 0.47/0.68    (![A:$i]:
% 0.47/0.68     ( ( v1_relat_1 @ A ) =>
% 0.47/0.68       ( ( k10_relat_1 @ A @ ( k2_relat_1 @ A ) ) = ( k1_relat_1 @ A ) ) ))).
% 0.47/0.68  thf('39', plain,
% 0.47/0.68      (![X30 : $i]:
% 0.47/0.68         (((k10_relat_1 @ X30 @ (k2_relat_1 @ X30)) = (k1_relat_1 @ X30))
% 0.47/0.68          | ~ (v1_relat_1 @ X30))),
% 0.47/0.68      inference('cnf', [status(esa)], [t169_relat_1])).
% 0.47/0.68  thf(d10_xboole_0, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.47/0.68  thf('40', plain,
% 0.47/0.68      (![X3 : $i, X4 : $i]: ((r1_tarski @ X3 @ X4) | ((X3) != (X4)))),
% 0.47/0.68      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.47/0.68  thf('41', plain, (![X4 : $i]: (r1_tarski @ X4 @ X4)),
% 0.47/0.68      inference('simplify', [status(thm)], ['40'])).
% 0.47/0.68  thf(t174_relat_1, axiom,
% 0.47/0.68    (![A:$i,B:$i]:
% 0.47/0.68     ( ( v1_relat_1 @ B ) =>
% 0.47/0.68       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.47/0.68            ( r1_tarski @ A @ ( k2_relat_1 @ B ) ) & 
% 0.47/0.68            ( ( k10_relat_1 @ B @ A ) = ( k1_xboole_0 ) ) ) ) ))).
% 0.47/0.68  thf('42', plain,
% 0.47/0.68      (![X31 : $i, X32 : $i]:
% 0.47/0.68         (((X31) = (k1_xboole_0))
% 0.47/0.68          | ~ (v1_relat_1 @ X32)
% 0.47/0.68          | ~ (r1_tarski @ X31 @ (k2_relat_1 @ X32))
% 0.47/0.68          | ((k10_relat_1 @ X32 @ X31) != (k1_xboole_0)))),
% 0.47/0.68      inference('cnf', [status(esa)], [t174_relat_1])).
% 0.47/0.68  thf('43', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (((k10_relat_1 @ X0 @ (k2_relat_1 @ X0)) != (k1_xboole_0))
% 0.47/0.68          | ~ (v1_relat_1 @ X0)
% 0.47/0.68          | ((k2_relat_1 @ X0) = (k1_xboole_0)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['41', '42'])).
% 0.47/0.68  thf('44', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (((k1_relat_1 @ X0) != (k1_xboole_0))
% 0.47/0.68          | ~ (v1_relat_1 @ X0)
% 0.47/0.68          | ((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.47/0.68          | ~ (v1_relat_1 @ X0))),
% 0.47/0.68      inference('sup-', [status(thm)], ['39', '43'])).
% 0.47/0.68  thf('45', plain,
% 0.47/0.68      (![X0 : $i]:
% 0.47/0.68         (((k2_relat_1 @ X0) = (k1_xboole_0))
% 0.47/0.68          | ~ (v1_relat_1 @ X0)
% 0.47/0.68          | ((k1_relat_1 @ X0) != (k1_xboole_0)))),
% 0.47/0.68      inference('simplify', [status(thm)], ['44'])).
% 0.47/0.68  thf('46', plain,
% 0.47/0.68      ((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.68        | ~ (v1_relat_1 @ sk_C_1)
% 0.47/0.68        | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.47/0.68      inference('sup-', [status(thm)], ['38', '45'])).
% 0.47/0.68  thf('47', plain, ((v1_relat_1 @ sk_C_1)),
% 0.47/0.68      inference('demod', [status(thm)], ['7', '8'])).
% 0.47/0.68  thf('48', plain,
% 0.47/0.68      ((((k1_xboole_0) != (k1_xboole_0))
% 0.47/0.68        | ((k2_relat_1 @ sk_C_1) = (k1_xboole_0)))),
% 0.47/0.68      inference('demod', [status(thm)], ['46', '47'])).
% 0.47/0.68  thf('49', plain, (((k2_relat_1 @ sk_C_1) = (k1_xboole_0))),
% 0.47/0.68      inference('simplify', [status(thm)], ['48'])).
% 0.47/0.68  thf('50', plain, (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_1) != (k1_xboole_0))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf('51', plain,
% 0.47/0.68      ((m1_subset_1 @ sk_C_1 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_B_1 @ sk_A)))),
% 0.47/0.68      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.47/0.68  thf(redefinition_k2_relset_1, axiom,
% 0.47/0.68    (![A:$i,B:$i,C:$i]:
% 0.47/0.68     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.47/0.68       ( ( k2_relset_1 @ A @ B @ C ) = ( k2_relat_1 @ C ) ) ))).
% 0.47/0.68  thf('52', plain,
% 0.47/0.68      (![X39 : $i, X40 : $i, X41 : $i]:
% 0.47/0.68         (((k2_relset_1 @ X40 @ X41 @ X39) = (k2_relat_1 @ X39))
% 0.47/0.68          | ~ (m1_subset_1 @ X39 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X40 @ X41))))),
% 0.47/0.68      inference('cnf', [status(esa)], [redefinition_k2_relset_1])).
% 0.47/0.68  thf('53', plain,
% 0.47/0.68      (((k2_relset_1 @ sk_B_1 @ sk_A @ sk_C_1) = (k2_relat_1 @ sk_C_1))),
% 0.47/0.68      inference('sup-', [status(thm)], ['51', '52'])).
% 0.47/0.68  thf('54', plain, (((k2_relat_1 @ sk_C_1) != (k1_xboole_0))),
% 0.47/0.68      inference('demod', [status(thm)], ['50', '53'])).
% 0.47/0.68  thf('55', plain, ($false),
% 0.47/0.68      inference('simplify_reflect-', [status(thm)], ['49', '54'])).
% 0.47/0.68  
% 0.47/0.68  % SZS output end Refutation
% 0.47/0.68  
% 0.47/0.69  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
