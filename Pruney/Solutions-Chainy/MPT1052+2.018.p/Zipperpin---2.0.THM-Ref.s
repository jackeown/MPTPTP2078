%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dAsD8S2gFh

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 495 expanded)
%              Number of leaves         :   42 ( 168 expanded)
%              Depth                    :   24
%              Number of atoms          :  868 (4227 expanded)
%              Number of equality atoms :   94 ( 360 expanded)
%              Maximal formula depth    :   12 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(zip_tseitin_0_type,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_relset_1_type,type,(
    k1_relset_1: $i > $i > $i > $i )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(zip_tseitin_1_type,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(l13_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('0',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('1',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf('2',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['0','1'])).

thf(t169_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
       => ( ( ( k1_relat_1 @ C )
            = A )
          & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_relat_1 @ C )
          & ( v1_funct_1 @ C ) )
       => ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
         => ( ( ( k1_relat_1 @ C )
              = A )
            & ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t169_funct_2])).

thf('3',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != sk_A )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('4',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != sk_A )
   <= ( ( k1_relat_1 @ sk_C )
     != sk_A ) ),
    inference(split,[status(esa)],['3'])).

thf('5',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf(t195_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ( B != k1_xboole_0 )
        & ~ ( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = A )
            & ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) )
              = B ) ) ) )).

thf('6',plain,(
    ! [X15: $i,X16: $i] :
      ( ( X15 = k1_xboole_0 )
      | ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X15 @ X16 ) )
        = X16 )
      | ( X16 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t195_relat_1])).

thf('7',plain,(
    r2_hidden @ sk_C @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t121_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('8',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) )
      | ~ ( r2_hidden @ X33 @ ( k1_funct_2 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t121_funct_2])).

thf('9',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('10',plain,(
    ! [X6: $i,X7: $i] :
      ( ( r1_tarski @ X6 @ X7 )
      | ~ ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('11',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf(t25_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( v1_relat_1 @ B )
         => ( ( r1_tarski @ A @ B )
           => ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) )
              & ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) )).

thf('12',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v1_relat_1 @ X17 )
      | ( r1_tarski @ ( k2_relat_1 @ X18 ) @ ( k2_relat_1 @ X17 ) )
      | ~ ( r1_tarski @ X18 @ X17 )
      | ~ ( v1_relat_1 @ X18 ) ) ),
    inference(cnf,[status(esa)],[t25_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ sk_C )
    | ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) )
    | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    v1_relat_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('15',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('16',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ ( k2_relat_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(demod,[status(thm)],['13','14','15'])).

thf('17',plain,
    ( ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 )
    | ( sk_B_1 = k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['6','16'])).

thf('18',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('19',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_B_1 = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf('20',plain,(
    r1_tarski @ sk_C @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('21',plain,(
    ! [X3: $i] :
      ( ( X3 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X3 ) ) ),
    inference(cnf,[status(esa)],[l13_xboole_0])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ A @ k1_xboole_0 )
     => ( A = k1_xboole_0 ) ) )).

thf('22',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( X1 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['21','22'])).

thf('24',plain,
    ( ( sk_C = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('25',plain,
    ( ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ k1_xboole_0 ) )
      | ( sk_A = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['19','24'])).

thf(t194_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ) )).

thf('26',plain,(
    ! [X13: $i,X14: $i] :
      ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ X13 @ X14 ) ) @ X14 ) ),
    inference(cnf,[status(esa)],[t194_relat_1])).

thf('27',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( k2_relat_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['26','27'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('29',plain,(
    ! [X19: $i] :
      ( ( ( k2_relat_1 @ X19 )
       != k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ X0 @ k1_xboole_0 ) )
      | ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('34',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('35',plain,
    ( ( ( sk_A = k1_xboole_0 )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['25','33','34'])).

thf('36',plain,
    ( ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('37',plain,
    ( ( ~ ( r1_tarski @ ( k2_relat_1 @ k1_xboole_0 ) @ sk_B_1 )
      | ( sk_A = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('38',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('39',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('40',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,
    ( ( sk_C = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf('42',plain,
    ( ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1 ) )
      | ( sk_C = k1_xboole_0 ) )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf(t193_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ) )).

thf('43',plain,(
    ! [X11: $i,X12: $i] :
      ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ X11 @ X12 ) ) @ X11 ) ),
    inference(cnf,[status(esa)],[t193_relat_1])).

thf('44',plain,(
    ! [X5: $i] :
      ( ( X5 = k1_xboole_0 )
      | ~ ( r1_tarski @ X5 @ k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('45',plain,(
    ! [X0: $i] :
      ( ( k1_relat_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['43','44'])).

thf('46',plain,(
    ! [X19: $i] :
      ( ( ( k1_relat_1 @ X19 )
       != k1_xboole_0 )
      | ( X19 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('47',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ X0 ) )
      | ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X9: $i,X10: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != k1_xboole_0 )
      | ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('52',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(demod,[status(thm)],['42','50','51'])).

thf('53',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('54',plain,(
    ! [X4: $i] :
      ( r1_tarski @ k1_xboole_0 @ X4 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('55',plain,(
    r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ),
    inference(demod,[status(thm)],['5','52','53','54'])).

thf('56',plain,
    ( ( ( k1_relat_1 @ sk_C )
     != sk_A )
    | ~ ( r1_tarski @ ( k2_relat_1 @ sk_C ) @ sk_B_1 ) ),
    inference(split,[status(esa)],['3'])).

thf('57',plain,(
    ( k1_relat_1 @ sk_C )
 != sk_A ),
    inference('sat_resolution*',[status(thm)],['55','56'])).

thf('58',plain,(
    ( k1_relat_1 @ sk_C )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['4','57'])).

thf('59',plain,
    ( ( sk_C = k1_xboole_0 )
    | ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','23'])).

thf(d1_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( B = k1_xboole_0 )
         => ( ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) )
            | ( A = k1_xboole_0 ) ) )
        & ( ( ( B = k1_xboole_0 )
           => ( A = k1_xboole_0 ) )
         => ( ( v1_funct_2 @ C @ A @ B )
          <=> ( A
              = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ) )).

thf(zf_stmt_1,axiom,(
    ! [B: $i,A: $i] :
      ( ( ( B = k1_xboole_0 )
       => ( A = k1_xboole_0 ) )
     => ( zip_tseitin_0 @ B @ A ) ) )).

thf('60',plain,(
    ! [X23: $i,X24: $i] :
      ( ( zip_tseitin_0 @ X23 @ X24 )
      | ( X23 = k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_1])).

thf('61',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(zf_stmt_2,type,(
    zip_tseitin_1: $i > $i > $i > $o )).

thf(zf_stmt_3,axiom,(
    ! [C: $i,B: $i,A: $i] :
      ( ( zip_tseitin_1 @ C @ B @ A )
     => ( ( v1_funct_2 @ C @ A @ B )
      <=> ( A
          = ( k1_relset_1 @ A @ B @ C ) ) ) ) )).

thf(zf_stmt_4,type,(
    zip_tseitin_0: $i > $i > $o )).

thf(zf_stmt_5,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( ( zip_tseitin_0 @ B @ A )
         => ( zip_tseitin_1 @ C @ B @ A ) )
        & ( ( B = k1_xboole_0 )
         => ( ( A = k1_xboole_0 )
            | ( ( v1_funct_2 @ C @ A @ B )
            <=> ( C = k1_xboole_0 ) ) ) ) ) ) )).

thf('62',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ~ ( zip_tseitin_0 @ X28 @ X29 )
      | ( zip_tseitin_1 @ X30 @ X28 @ X29 )
      | ~ ( m1_subset_1 @ X30 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_5])).

thf('63',plain,
    ( ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ~ ( zip_tseitin_0 @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A ) ),
    inference('sup-',[status(thm)],['60','63'])).

thf('65',plain,(
    r2_hidden @ sk_C @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('66',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v1_funct_2 @ X33 @ X34 @ X35 )
      | ~ ( r2_hidden @ X33 @ ( k1_funct_2 @ X34 @ X35 ) ) ) ),
    inference(cnf,[status(esa)],[t121_funct_2])).

thf('67',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_1 ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X25: $i,X26: $i,X27: $i] :
      ( ~ ( v1_funct_2 @ X27 @ X25 @ X26 )
      | ( X25
        = ( k1_relset_1 @ X25 @ X26 @ X27 ) )
      | ~ ( zip_tseitin_1 @ X27 @ X26 @ X25 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_3])).

thf('69',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf(redefinition_k1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k1_relset_1 @ A @ B @ C )
        = ( k1_relat_1 @ C ) ) ) )).

thf('71',plain,(
    ! [X20: $i,X21: $i,X22: $i] :
      ( ( ( k1_relset_1 @ X21 @ X22 @ X20 )
        = ( k1_relat_1 @ X20 ) )
      | ~ ( m1_subset_1 @ X20 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X21 @ X22 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k1_relset_1])).

thf('72',plain,
    ( ( k1_relset_1 @ sk_A @ sk_B_1 @ sk_C )
    = ( k1_relat_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['70','71'])).

thf('73',plain,
    ( ~ ( zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['69','72'])).

thf('74',plain,
    ( ( sk_B_1 = k1_xboole_0 )
    | ( sk_A
      = ( k1_relat_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['64','73'])).

thf('75',plain,(
    ( k1_relat_1 @ sk_C )
 != sk_A ),
    inference(simpl_trail,[status(thm)],['4','57'])).

thf('76',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i] :
      ( ( k2_zfmisc_1 @ X0 @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['32'])).

thf('78',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('79',plain,(
    sk_C = k1_xboole_0 ),
    inference(demod,[status(thm)],['59','76','77','78'])).

thf('80',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('81',plain,(
    k1_xboole_0 != sk_A ),
    inference(demod,[status(thm)],['58','79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ sk_A ) ) ),
    inference('sup-',[status(thm)],['2','81'])).

thf(fc3_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ( ~ ( v1_xboole_0 @ A )
        & ( v1_xboole_0 @ B ) )
     => ( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ) )).

thf('83',plain,(
    ! [X31: $i,X32: $i] :
      ( ( v1_xboole_0 @ X31 )
      | ~ ( v1_xboole_0 @ X32 )
      | ( v1_xboole_0 @ ( k1_funct_2 @ X31 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[fc3_funct_2])).

thf('84',plain,(
    r2_hidden @ sk_C @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('85',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('86',plain,(
    ~ ( v1_xboole_0 @ ( k1_funct_2 @ sk_A @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,
    ( ~ ( v1_xboole_0 @ sk_B_1 )
    | ( v1_xboole_0 @ sk_A ) ),
    inference('sup-',[status(thm)],['83','86'])).

thf('88',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('simplify_reflect-',[status(thm)],['74','75'])).

thf('89',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('90',plain,(
    v1_xboole_0 @ sk_A ),
    inference(demod,[status(thm)],['87','88','89'])).

thf('91',plain,(
    ! [X0: $i] :
      ( ( k1_xboole_0 != X0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['82','90'])).

thf('92',plain,(
    ~ ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['91'])).

thf('93',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('94',plain,(
    $false ),
    inference('simplify_reflect+',[status(thm)],['92','93'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.dAsD8S2gFh
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:04:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.36  % Running in FO mode
% 0.21/0.57  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.21/0.57  % Solved by: fo/fo7.sh
% 0.21/0.57  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.57  % done 196 iterations in 0.130s
% 0.21/0.57  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.21/0.57  % SZS output start Refutation
% 0.21/0.57  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.57  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.57  thf(zip_tseitin_0_type, type, zip_tseitin_0: $i > $i > $o).
% 0.21/0.57  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.21/0.57  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.57  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.57  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.57  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.21/0.57  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.57  thf(k1_relset_1_type, type, k1_relset_1: $i > $i > $i > $i).
% 0.21/0.57  thf(k1_funct_2_type, type, k1_funct_2: $i > $i > $i).
% 0.21/0.57  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.57  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.57  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.57  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.21/0.57  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.57  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.57  thf(zip_tseitin_1_type, type, zip_tseitin_1: $i > $i > $i > $o).
% 0.21/0.57  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.57  thf(l13_xboole_0, axiom,
% 0.21/0.57    (![A:$i]: ( ( v1_xboole_0 @ A ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.57  thf('0', plain,
% 0.21/0.57      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.21/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.57  thf('1', plain,
% 0.21/0.57      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.21/0.57      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.57  thf('2', plain,
% 0.21/0.57      (![X0 : $i, X1 : $i]:
% 0.21/0.57         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.57      inference('sup+', [status(thm)], ['0', '1'])).
% 0.21/0.57  thf(t169_funct_2, conjecture,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.57       ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.21/0.57         ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.21/0.57           ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ))).
% 0.21/0.57  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.57    (~( ![A:$i,B:$i,C:$i]:
% 0.21/0.57        ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.21/0.57          ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.21/0.57            ( ( ( k1_relat_1 @ C ) = ( A ) ) & 
% 0.21/0.57              ( r1_tarski @ ( k2_relat_1 @ C ) @ B ) ) ) ) )),
% 0.21/0.57    inference('cnf.neg', [status(esa)], [t169_funct_2])).
% 0.21/0.57  thf('3', plain,
% 0.21/0.57      ((((k1_relat_1 @ sk_C) != (sk_A))
% 0.21/0.57        | ~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf('4', plain,
% 0.21/0.57      ((((k1_relat_1 @ sk_C) != (sk_A)))
% 0.21/0.57         <= (~ (((k1_relat_1 @ sk_C) = (sk_A))))),
% 0.21/0.57      inference('split', [status(esa)], ['3'])).
% 0.21/0.57  thf('5', plain,
% 0.21/0.57      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))
% 0.21/0.57         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.21/0.57      inference('split', [status(esa)], ['3'])).
% 0.21/0.57  thf(t195_relat_1, axiom,
% 0.21/0.57    (![A:$i,B:$i]:
% 0.21/0.57     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( B ) != ( k1_xboole_0 ) ) & 
% 0.21/0.57          ( ~( ( ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( A ) ) & 
% 0.21/0.57               ( ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) = ( B ) ) ) ) ) ))).
% 0.21/0.57  thf('6', plain,
% 0.21/0.57      (![X15 : $i, X16 : $i]:
% 0.21/0.57         (((X15) = (k1_xboole_0))
% 0.21/0.57          | ((k2_relat_1 @ (k2_zfmisc_1 @ X15 @ X16)) = (X16))
% 0.21/0.57          | ((X16) = (k1_xboole_0)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t195_relat_1])).
% 0.21/0.57  thf('7', plain, ((r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.21/0.57      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.57  thf(t121_funct_2, axiom,
% 0.21/0.57    (![A:$i,B:$i,C:$i]:
% 0.21/0.57     ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) ) =>
% 0.21/0.57       ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.21/0.57         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ))).
% 0.21/0.57  thf('8', plain,
% 0.21/0.57      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.21/0.57         ((m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35)))
% 0.21/0.57          | ~ (r2_hidden @ X33 @ (k1_funct_2 @ X34 @ X35)))),
% 0.21/0.57      inference('cnf', [status(esa)], [t121_funct_2])).
% 0.21/0.57  thf('9', plain,
% 0.21/0.57      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.57      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.58  thf(t3_subset, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.58  thf('10', plain,
% 0.21/0.58      (![X6 : $i, X7 : $i]:
% 0.21/0.58         ((r1_tarski @ X6 @ X7) | ~ (m1_subset_1 @ X6 @ (k1_zfmisc_1 @ X7)))),
% 0.21/0.58      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.58  thf('11', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.58  thf(t25_relat_1, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( v1_relat_1 @ A ) =>
% 0.21/0.58       ( ![B:$i]:
% 0.21/0.58         ( ( v1_relat_1 @ B ) =>
% 0.21/0.58           ( ( r1_tarski @ A @ B ) =>
% 0.21/0.58             ( ( r1_tarski @ ( k1_relat_1 @ A ) @ ( k1_relat_1 @ B ) ) & 
% 0.21/0.58               ( r1_tarski @ ( k2_relat_1 @ A ) @ ( k2_relat_1 @ B ) ) ) ) ) ) ))).
% 0.21/0.58  thf('12', plain,
% 0.21/0.58      (![X17 : $i, X18 : $i]:
% 0.21/0.58         (~ (v1_relat_1 @ X17)
% 0.21/0.58          | (r1_tarski @ (k2_relat_1 @ X18) @ (k2_relat_1 @ X17))
% 0.21/0.58          | ~ (r1_tarski @ X18 @ X17)
% 0.21/0.58          | ~ (v1_relat_1 @ X18))),
% 0.21/0.58      inference('cnf', [status(esa)], [t25_relat_1])).
% 0.21/0.58  thf('13', plain,
% 0.21/0.58      ((~ (v1_relat_1 @ sk_C)
% 0.21/0.58        | (r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.21/0.58           (k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))
% 0.21/0.58        | ~ (v1_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.58  thf('14', plain, ((v1_relat_1 @ sk_C)),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(fc6_relat_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.21/0.58  thf('15', plain,
% 0.21/0.58      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.21/0.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.58  thf('16', plain,
% 0.21/0.58      ((r1_tarski @ (k2_relat_1 @ sk_C) @ 
% 0.21/0.58        (k2_relat_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.58      inference('demod', [status(thm)], ['13', '14', '15'])).
% 0.21/0.58  thf('17', plain,
% 0.21/0.58      (((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)
% 0.21/0.58        | ((sk_B_1) = (k1_xboole_0))
% 0.21/0.58        | ((sk_A) = (k1_xboole_0)))),
% 0.21/0.58      inference('sup+', [status(thm)], ['6', '16'])).
% 0.21/0.58  thf('18', plain,
% 0.21/0.58      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))
% 0.21/0.58         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.21/0.58      inference('split', [status(esa)], ['3'])).
% 0.21/0.58  thf('19', plain,
% 0.21/0.58      (((((sk_A) = (k1_xboole_0)) | ((sk_B_1) = (k1_xboole_0))))
% 0.21/0.58         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['17', '18'])).
% 0.21/0.58  thf('20', plain, ((r1_tarski @ sk_C @ (k2_zfmisc_1 @ sk_A @ sk_B_1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['9', '10'])).
% 0.21/0.58  thf('21', plain,
% 0.21/0.58      (![X3 : $i]: (((X3) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X3))),
% 0.21/0.58      inference('cnf', [status(esa)], [l13_xboole_0])).
% 0.21/0.58  thf(t3_xboole_1, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( r1_tarski @ A @ k1_xboole_0 ) => ( ( A ) = ( k1_xboole_0 ) ) ))).
% 0.21/0.58  thf('22', plain,
% 0.21/0.58      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ k1_xboole_0))),
% 0.21/0.58      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.21/0.58  thf('23', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]:
% 0.21/0.58         (~ (r1_tarski @ X1 @ X0)
% 0.21/0.58          | ~ (v1_xboole_0 @ X0)
% 0.21/0.58          | ((X1) = (k1_xboole_0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['21', '22'])).
% 0.21/0.58  thf('24', plain,
% 0.21/0.58      ((((sk_C) = (k1_xboole_0))
% 0.21/0.58        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['20', '23'])).
% 0.21/0.58  thf('25', plain,
% 0.21/0.58      (((~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ k1_xboole_0))
% 0.21/0.58         | ((sk_A) = (k1_xboole_0))
% 0.21/0.58         | ((sk_C) = (k1_xboole_0))))
% 0.21/0.58         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['19', '24'])).
% 0.21/0.58  thf(t194_relat_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]: ( r1_tarski @ ( k2_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ B ))).
% 0.21/0.58  thf('26', plain,
% 0.21/0.58      (![X13 : $i, X14 : $i]:
% 0.21/0.58         (r1_tarski @ (k2_relat_1 @ (k2_zfmisc_1 @ X13 @ X14)) @ X14)),
% 0.21/0.58      inference('cnf', [status(esa)], [t194_relat_1])).
% 0.21/0.58  thf('27', plain,
% 0.21/0.58      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ k1_xboole_0))),
% 0.21/0.58      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.21/0.58  thf('28', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((k2_relat_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0)) = (k1_xboole_0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['26', '27'])).
% 0.21/0.58  thf(t64_relat_1, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( v1_relat_1 @ A ) =>
% 0.21/0.58       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.58           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.58         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.58  thf('29', plain,
% 0.21/0.58      (![X19 : $i]:
% 0.21/0.58         (((k2_relat_1 @ X19) != (k1_xboole_0))
% 0.21/0.58          | ((X19) = (k1_xboole_0))
% 0.21/0.58          | ~ (v1_relat_1 @ X19))),
% 0.21/0.58      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.58  thf('30', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.58          | ~ (v1_relat_1 @ (k2_zfmisc_1 @ X0 @ k1_xboole_0))
% 0.21/0.58          | ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.58  thf('31', plain,
% 0.21/0.58      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.21/0.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.58  thf('32', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.58          | ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0)))),
% 0.21/0.58      inference('demod', [status(thm)], ['30', '31'])).
% 0.21/0.58  thf('33', plain,
% 0.21/0.58      (![X0 : $i]: ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.58      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.58  thf(fc1_xboole_0, axiom, (v1_xboole_0 @ k1_xboole_0)).
% 0.21/0.58  thf('34', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.58  thf('35', plain,
% 0.21/0.58      (((((sk_A) = (k1_xboole_0)) | ((sk_C) = (k1_xboole_0))))
% 0.21/0.58         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.21/0.58      inference('demod', [status(thm)], ['25', '33', '34'])).
% 0.21/0.58  thf('36', plain,
% 0.21/0.58      ((~ (r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))
% 0.21/0.58         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.21/0.58      inference('split', [status(esa)], ['3'])).
% 0.21/0.58  thf('37', plain,
% 0.21/0.58      (((~ (r1_tarski @ (k2_relat_1 @ k1_xboole_0) @ sk_B_1)
% 0.21/0.58         | ((sk_A) = (k1_xboole_0))))
% 0.21/0.58         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['35', '36'])).
% 0.21/0.58  thf(t60_relat_1, axiom,
% 0.21/0.58    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.58     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.58  thf('38', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.58      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.58  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.21/0.58  thf('39', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.21/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.58  thf('40', plain,
% 0.21/0.58      ((((sk_A) = (k1_xboole_0)))
% 0.21/0.58         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.21/0.58      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.21/0.58  thf('41', plain,
% 0.21/0.58      ((((sk_C) = (k1_xboole_0))
% 0.21/0.58        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['20', '23'])).
% 0.21/0.58  thf('42', plain,
% 0.21/0.58      (((~ (v1_xboole_0 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_1))
% 0.21/0.58         | ((sk_C) = (k1_xboole_0))))
% 0.21/0.58         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['40', '41'])).
% 0.21/0.58  thf(t193_relat_1, axiom,
% 0.21/0.58    (![A:$i,B:$i]: ( r1_tarski @ ( k1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) @ A ))).
% 0.21/0.58  thf('43', plain,
% 0.21/0.58      (![X11 : $i, X12 : $i]:
% 0.21/0.58         (r1_tarski @ (k1_relat_1 @ (k2_zfmisc_1 @ X11 @ X12)) @ X11)),
% 0.21/0.58      inference('cnf', [status(esa)], [t193_relat_1])).
% 0.21/0.58  thf('44', plain,
% 0.21/0.58      (![X5 : $i]: (((X5) = (k1_xboole_0)) | ~ (r1_tarski @ X5 @ k1_xboole_0))),
% 0.21/0.58      inference('cnf', [status(esa)], [t3_xboole_1])).
% 0.21/0.58  thf('45', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         ((k1_relat_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0)) = (k1_xboole_0))),
% 0.21/0.58      inference('sup-', [status(thm)], ['43', '44'])).
% 0.21/0.58  thf('46', plain,
% 0.21/0.58      (![X19 : $i]:
% 0.21/0.58         (((k1_relat_1 @ X19) != (k1_xboole_0))
% 0.21/0.58          | ((X19) = (k1_xboole_0))
% 0.21/0.58          | ~ (v1_relat_1 @ X19))),
% 0.21/0.58      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.58  thf('47', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.58          | ~ (v1_relat_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ X0))
% 0.21/0.58          | ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['45', '46'])).
% 0.21/0.58  thf('48', plain,
% 0.21/0.58      (![X9 : $i, X10 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X9 @ X10))),
% 0.21/0.58      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.21/0.58  thf('49', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.58          | ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0)))),
% 0.21/0.58      inference('demod', [status(thm)], ['47', '48'])).
% 0.21/0.58  thf('50', plain,
% 0.21/0.58      (![X0 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.21/0.58      inference('simplify', [status(thm)], ['49'])).
% 0.21/0.58  thf('51', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.58  thf('52', plain,
% 0.21/0.58      ((((sk_C) = (k1_xboole_0)))
% 0.21/0.58         <= (~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1)))),
% 0.21/0.58      inference('demod', [status(thm)], ['42', '50', '51'])).
% 0.21/0.58  thf('53', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.58      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.58  thf('54', plain, (![X4 : $i]: (r1_tarski @ k1_xboole_0 @ X4)),
% 0.21/0.58      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.21/0.58  thf('55', plain, (((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))),
% 0.21/0.58      inference('demod', [status(thm)], ['5', '52', '53', '54'])).
% 0.21/0.58  thf('56', plain,
% 0.21/0.58      (~ (((k1_relat_1 @ sk_C) = (sk_A))) | 
% 0.21/0.58       ~ ((r1_tarski @ (k2_relat_1 @ sk_C) @ sk_B_1))),
% 0.21/0.58      inference('split', [status(esa)], ['3'])).
% 0.21/0.58  thf('57', plain, (~ (((k1_relat_1 @ sk_C) = (sk_A)))),
% 0.21/0.58      inference('sat_resolution*', [status(thm)], ['55', '56'])).
% 0.21/0.58  thf('58', plain, (((k1_relat_1 @ sk_C) != (sk_A))),
% 0.21/0.58      inference('simpl_trail', [status(thm)], ['4', '57'])).
% 0.21/0.58  thf('59', plain,
% 0.21/0.58      ((((sk_C) = (k1_xboole_0))
% 0.21/0.58        | ~ (v1_xboole_0 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['20', '23'])).
% 0.21/0.58  thf(d1_funct_2, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.58       ( ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.58           ( ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) | 
% 0.21/0.58             ( ( A ) = ( k1_xboole_0 ) ) ) ) & 
% 0.21/0.58         ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.58           ( ( v1_funct_2 @ C @ A @ B ) <=>
% 0.21/0.58             ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ) ) ))).
% 0.21/0.58  thf(zf_stmt_1, axiom,
% 0.21/0.58    (![B:$i,A:$i]:
% 0.21/0.58     ( ( ( ( B ) = ( k1_xboole_0 ) ) => ( ( A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.58       ( zip_tseitin_0 @ B @ A ) ))).
% 0.21/0.58  thf('60', plain,
% 0.21/0.58      (![X23 : $i, X24 : $i]:
% 0.21/0.58         ((zip_tseitin_0 @ X23 @ X24) | ((X23) = (k1_xboole_0)))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_1])).
% 0.21/0.58  thf('61', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.58  thf(zf_stmt_2, type, zip_tseitin_1 : $i > $i > $i > $o).
% 0.21/0.58  thf(zf_stmt_3, axiom,
% 0.21/0.58    (![C:$i,B:$i,A:$i]:
% 0.21/0.58     ( ( zip_tseitin_1 @ C @ B @ A ) =>
% 0.21/0.58       ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( A ) = ( k1_relset_1 @ A @ B @ C ) ) ) ))).
% 0.21/0.58  thf(zf_stmt_4, type, zip_tseitin_0 : $i > $i > $o).
% 0.21/0.58  thf(zf_stmt_5, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.58       ( ( ( zip_tseitin_0 @ B @ A ) => ( zip_tseitin_1 @ C @ B @ A ) ) & 
% 0.21/0.58         ( ( ( B ) = ( k1_xboole_0 ) ) =>
% 0.21/0.58           ( ( ( A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.58             ( ( v1_funct_2 @ C @ A @ B ) <=> ( ( C ) = ( k1_xboole_0 ) ) ) ) ) ) ))).
% 0.21/0.58  thf('62', plain,
% 0.21/0.58      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.58         (~ (zip_tseitin_0 @ X28 @ X29)
% 0.21/0.58          | (zip_tseitin_1 @ X30 @ X28 @ X29)
% 0.21/0.58          | ~ (m1_subset_1 @ X30 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X28))))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_5])).
% 0.21/0.58  thf('63', plain,
% 0.21/0.58      (((zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.21/0.58        | ~ (zip_tseitin_0 @ sk_B_1 @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['61', '62'])).
% 0.21/0.58  thf('64', plain,
% 0.21/0.58      ((((sk_B_1) = (k1_xboole_0)) | (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['60', '63'])).
% 0.21/0.58  thf('65', plain, ((r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf('66', plain,
% 0.21/0.58      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.21/0.58         ((v1_funct_2 @ X33 @ X34 @ X35)
% 0.21/0.58          | ~ (r2_hidden @ X33 @ (k1_funct_2 @ X34 @ X35)))),
% 0.21/0.58      inference('cnf', [status(esa)], [t121_funct_2])).
% 0.21/0.58  thf('67', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_1)),
% 0.21/0.58      inference('sup-', [status(thm)], ['65', '66'])).
% 0.21/0.58  thf('68', plain,
% 0.21/0.58      (![X25 : $i, X26 : $i, X27 : $i]:
% 0.21/0.58         (~ (v1_funct_2 @ X27 @ X25 @ X26)
% 0.21/0.58          | ((X25) = (k1_relset_1 @ X25 @ X26 @ X27))
% 0.21/0.58          | ~ (zip_tseitin_1 @ X27 @ X26 @ X25))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_3])).
% 0.21/0.58  thf('69', plain,
% 0.21/0.58      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.21/0.58        | ((sk_A) = (k1_relset_1 @ sk_A @ sk_B_1 @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['67', '68'])).
% 0.21/0.58  thf('70', plain,
% 0.21/0.58      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_1)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['7', '8'])).
% 0.21/0.58  thf(redefinition_k1_relset_1, axiom,
% 0.21/0.58    (![A:$i,B:$i,C:$i]:
% 0.21/0.58     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.58       ( ( k1_relset_1 @ A @ B @ C ) = ( k1_relat_1 @ C ) ) ))).
% 0.21/0.58  thf('71', plain,
% 0.21/0.58      (![X20 : $i, X21 : $i, X22 : $i]:
% 0.21/0.58         (((k1_relset_1 @ X21 @ X22 @ X20) = (k1_relat_1 @ X20))
% 0.21/0.58          | ~ (m1_subset_1 @ X20 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X21 @ X22))))),
% 0.21/0.58      inference('cnf', [status(esa)], [redefinition_k1_relset_1])).
% 0.21/0.58  thf('72', plain,
% 0.21/0.58      (((k1_relset_1 @ sk_A @ sk_B_1 @ sk_C) = (k1_relat_1 @ sk_C))),
% 0.21/0.58      inference('sup-', [status(thm)], ['70', '71'])).
% 0.21/0.58  thf('73', plain,
% 0.21/0.58      ((~ (zip_tseitin_1 @ sk_C @ sk_B_1 @ sk_A)
% 0.21/0.58        | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.21/0.58      inference('demod', [status(thm)], ['69', '72'])).
% 0.21/0.58  thf('74', plain,
% 0.21/0.58      ((((sk_B_1) = (k1_xboole_0)) | ((sk_A) = (k1_relat_1 @ sk_C)))),
% 0.21/0.58      inference('sup-', [status(thm)], ['64', '73'])).
% 0.21/0.58  thf('75', plain, (((k1_relat_1 @ sk_C) != (sk_A))),
% 0.21/0.58      inference('simpl_trail', [status(thm)], ['4', '57'])).
% 0.21/0.58  thf('76', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.58      inference('simplify_reflect-', [status(thm)], ['74', '75'])).
% 0.21/0.58  thf('77', plain,
% 0.21/0.58      (![X0 : $i]: ((k2_zfmisc_1 @ X0 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.58      inference('simplify', [status(thm)], ['32'])).
% 0.21/0.58  thf('78', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.58  thf('79', plain, (((sk_C) = (k1_xboole_0))),
% 0.21/0.58      inference('demod', [status(thm)], ['59', '76', '77', '78'])).
% 0.21/0.58  thf('80', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.58      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.58  thf('81', plain, (((k1_xboole_0) != (sk_A))),
% 0.21/0.58      inference('demod', [status(thm)], ['58', '79', '80'])).
% 0.21/0.58  thf('82', plain,
% 0.21/0.58      (![X0 : $i]:
% 0.21/0.58         (((k1_xboole_0) != (X0))
% 0.21/0.58          | ~ (v1_xboole_0 @ X0)
% 0.21/0.58          | ~ (v1_xboole_0 @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['2', '81'])).
% 0.21/0.58  thf(fc3_funct_2, axiom,
% 0.21/0.58    (![A:$i,B:$i]:
% 0.21/0.58     ( ( ( ~( v1_xboole_0 @ A ) ) & ( v1_xboole_0 @ B ) ) =>
% 0.21/0.58       ( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ))).
% 0.21/0.58  thf('83', plain,
% 0.21/0.58      (![X31 : $i, X32 : $i]:
% 0.21/0.58         ((v1_xboole_0 @ X31)
% 0.21/0.58          | ~ (v1_xboole_0 @ X32)
% 0.21/0.58          | (v1_xboole_0 @ (k1_funct_2 @ X31 @ X32)))),
% 0.21/0.58      inference('cnf', [status(esa)], [fc3_funct_2])).
% 0.21/0.58  thf('84', plain, ((r2_hidden @ sk_C @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.21/0.58      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.58  thf(d1_xboole_0, axiom,
% 0.21/0.58    (![A:$i]:
% 0.21/0.58     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.21/0.58  thf('85', plain,
% 0.21/0.58      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.21/0.58      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.21/0.58  thf('86', plain, (~ (v1_xboole_0 @ (k1_funct_2 @ sk_A @ sk_B_1))),
% 0.21/0.58      inference('sup-', [status(thm)], ['84', '85'])).
% 0.21/0.58  thf('87', plain, ((~ (v1_xboole_0 @ sk_B_1) | (v1_xboole_0 @ sk_A))),
% 0.21/0.58      inference('sup-', [status(thm)], ['83', '86'])).
% 0.21/0.58  thf('88', plain, (((sk_B_1) = (k1_xboole_0))),
% 0.21/0.58      inference('simplify_reflect-', [status(thm)], ['74', '75'])).
% 0.21/0.58  thf('89', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.58  thf('90', plain, ((v1_xboole_0 @ sk_A)),
% 0.21/0.58      inference('demod', [status(thm)], ['87', '88', '89'])).
% 0.21/0.58  thf('91', plain,
% 0.21/0.58      (![X0 : $i]: (((k1_xboole_0) != (X0)) | ~ (v1_xboole_0 @ X0))),
% 0.21/0.58      inference('demod', [status(thm)], ['82', '90'])).
% 0.21/0.58  thf('92', plain, (~ (v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.58      inference('simplify', [status(thm)], ['91'])).
% 0.21/0.58  thf('93', plain, ((v1_xboole_0 @ k1_xboole_0)),
% 0.21/0.58      inference('cnf', [status(esa)], [fc1_xboole_0])).
% 0.21/0.58  thf('94', plain, ($false),
% 0.21/0.58      inference('simplify_reflect+', [status(thm)], ['92', '93'])).
% 0.21/0.58  
% 0.21/0.58  % SZS output end Refutation
% 0.21/0.58  
% 0.21/0.59  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
