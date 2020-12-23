%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1006+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.XpbQWkTHu8

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:11:05 EST 2020

% Result     : Theorem 43.94s
% Output     : Refutation 43.94s
% Verified   : 
% Statistics : Number of formulae       :   77 (  97 expanded)
%              Number of leaves         :   29 (  45 expanded)
%              Depth                    :    9
%              Number of atoms          :  339 ( 435 expanded)
%              Number of equality atoms :   43 (  63 expanded)
%              Maximal formula depth    :   13 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_16_type,type,(
    sk_A_16: $i )).

thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(sk_B_98_type,type,(
    sk_B_98: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k8_relset_1_type,type,(
    k8_relset_1: $i > $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_110_type,type,(
    sk_C_110: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(k10_relat_1_type,type,(
    k10_relat_1: $i > $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(t60_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ ( C @ ( k1_xboole_0 @ A ) ) )
        & ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_xboole_0 @ A ) ) ) ) ) )
     => ( ( k8_relset_1 @ ( k1_xboole_0 @ ( A @ ( C @ B ) ) ) )
        = k1_xboole_0 ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ ( C @ ( k1_xboole_0 @ A ) ) )
          & ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_xboole_0 @ A ) ) ) ) ) )
       => ( ( k8_relset_1 @ ( k1_xboole_0 @ ( A @ ( C @ B ) ) ) )
          = k1_xboole_0 ) ) ),
    inference('cnf.neg',[status(esa)],[t60_funct_2])).

thf('0',plain,(
    ( k8_relset_1 @ ( k1_xboole_0 @ ( sk_A_16 @ ( sk_C_110 @ sk_B_98 ) ) ) )
 != k1_xboole_0 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d2_xboole_0,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 )).

thf('1',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('2',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('3',plain,(
    ( k8_relset_1 @ ( o_0_0_xboole_0 @ ( sk_A_16 @ ( sk_C_110 @ sk_B_98 ) ) ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['0','1','2'])).

thf('4',plain,(
    m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_xboole_0 @ sk_A_16 ) ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('5',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('6',plain,(
    m1_subset_1 @ ( sk_C_110 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( o_0_0_xboole_0 @ sk_A_16 ) ) ) ) ),
    inference(demod,[status(thm)],['4','5'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ ( A @ B ) )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('7',plain,(
    ! [X1104: $i,X1105: $i] :
      ( ( ( k2_zfmisc_1 @ ( X1104 @ X1105 ) )
        = k1_xboole_0 )
      | ( X1104 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('8',plain,(
    ! [X1105: $i] :
      ( ( k2_zfmisc_1 @ ( k1_xboole_0 @ X1105 ) )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['7'])).

thf('9',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('10',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('11',plain,(
    ! [X1105: $i] :
      ( ( k2_zfmisc_1 @ ( o_0_0_xboole_0 @ X1105 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['8','9','10'])).

thf(t1_zfmisc_1,axiom,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) )).

thf('12',plain,
    ( ( k1_zfmisc_1 @ k1_xboole_0 )
    = ( k1_tarski @ k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t1_zfmisc_1])).

thf('13',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('14',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('15',plain,
    ( ( k1_zfmisc_1 @ o_0_0_xboole_0 )
    = ( k1_tarski @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf('16',plain,(
    m1_subset_1 @ ( sk_C_110 @ ( k1_tarski @ o_0_0_xboole_0 ) ) ),
    inference(demod,[status(thm)],['6','11','15'])).

thf('17',plain,
    ( ( k1_zfmisc_1 @ o_0_0_xboole_0 )
    = ( k1_tarski @ o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['12','13','14'])).

thf(cc1_subset_1,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ ( B @ ( k1_zfmisc_1 @ A ) ) )
         => ( v1_xboole_0 @ B ) ) ) )).

thf('18',plain,(
    ! [X1803: $i,X1804: $i] :
      ( ~ ( m1_subset_1 @ ( X1803 @ ( k1_zfmisc_1 @ X1804 ) ) )
      | ( v1_xboole_0 @ X1803 )
      | ~ ( v1_xboole_0 @ X1804 ) ) ),
    inference(cnf,[status(esa)],[cc1_subset_1])).

thf('19',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( X0 @ ( k1_tarski @ o_0_0_xboole_0 ) ) )
      | ~ ( v1_xboole_0 @ o_0_0_xboole_0 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(fc1_xboole_0,axiom,(
    v1_xboole_0 @ k1_xboole_0 )).

thf('20',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(cnf,[status(esa)],[fc1_xboole_0])).

thf('21',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('22',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['20','21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( ~ ( m1_subset_1 @ ( X0 @ ( k1_tarski @ o_0_0_xboole_0 ) ) )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['19','22'])).

thf('24',plain,(
    v1_xboole_0 @ sk_C_110 ),
    inference('sup-',[status(thm)],['16','23'])).

thf(d3_tarski,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( A @ B ) )
    <=> ! [C: $i] :
          ( ( r2_hidden @ ( C @ A ) )
         => ( r2_hidden @ ( C @ B ) ) ) ) )).

thf('25',plain,(
    ! [X14: $i,X16: $i] :
      ( ( r1_tarski @ ( X14 @ X16 ) )
      | ( r2_hidden @ ( sk_C @ ( X16 @ X14 ) @ X14 ) ) ) ),
    inference(cnf,[status(esa)],[d3_tarski])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ ( B @ A ) ) ) )).

thf('26',plain,(
    ! [X10: $i,X11: $i] :
      ( ~ ( r2_hidden @ ( X10 @ X11 ) )
      | ~ ( v1_xboole_0 @ X11 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( X0 @ X1 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf(t3_xboole_1,axiom,(
    ! [A: $i] :
      ( ( r1_tarski @ ( A @ k1_xboole_0 ) )
     => ( A = k1_xboole_0 ) ) )).

thf('28',plain,(
    ! [X245: $i] :
      ( ( X245 = k1_xboole_0 )
      | ~ ( r1_tarski @ ( X245 @ k1_xboole_0 ) ) ) ),
    inference(cnf,[status(esa)],[t3_xboole_1])).

thf('29',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('30',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('31',plain,(
    ! [X245: $i] :
      ( ( X245 = o_0_0_xboole_0 )
      | ~ ( r1_tarski @ ( X245 @ o_0_0_xboole_0 ) ) ) ),
    inference(demod,[status(thm)],['28','29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ X0 )
      | ( X0 = o_0_0_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['27','31'])).

thf('33',plain,(
    sk_C_110 = o_0_0_xboole_0 ),
    inference('sup-',[status(thm)],['24','32'])).

thf('34',plain,(
    ( k8_relset_1 @ ( o_0_0_xboole_0 @ ( sk_A_16 @ ( o_0_0_xboole_0 @ sk_B_98 ) ) ) )
 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['3','33'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ ( k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) ) )).

thf('35',plain,(
    ! [X1729: $i] :
      ( m1_subset_1 @ ( k1_xboole_0 @ ( k1_zfmisc_1 @ X1729 ) ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('36',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('37',plain,(
    ! [X1729: $i] :
      ( m1_subset_1 @ ( o_0_0_xboole_0 @ ( k1_zfmisc_1 @ X1729 ) ) ) ),
    inference(demod,[status(thm)],['35','36'])).

thf(redefinition_k8_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ ( C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( A @ B ) ) ) ) )
     => ( ( k8_relset_1 @ ( A @ ( B @ ( C @ D ) ) ) )
        = ( k10_relat_1 @ ( C @ D ) ) ) ) )).

thf('38',plain,(
    ! [X3622: $i,X3623: $i,X3624: $i,X3625: $i] :
      ( ~ ( m1_subset_1 @ ( X3622 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( X3623 @ X3624 ) ) ) ) )
      | ( ( k8_relset_1 @ ( X3623 @ ( X3624 @ ( X3622 @ X3625 ) ) ) )
        = ( k10_relat_1 @ ( X3622 @ X3625 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k8_relset_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relset_1 @ ( X1 @ ( X0 @ ( o_0_0_xboole_0 @ X2 ) ) ) )
      = ( k10_relat_1 @ ( o_0_0_xboole_0 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['37','38'])).

thf(t172_relat_1,axiom,(
    ! [A: $i] :
      ( ( k10_relat_1 @ ( k1_xboole_0 @ A ) )
      = k1_xboole_0 ) )).

thf('40',plain,(
    ! [X2359: $i] :
      ( ( k10_relat_1 @ ( k1_xboole_0 @ X2359 ) )
      = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[t172_relat_1])).

thf('41',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('42',plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[d2_xboole_0])).

thf('43',plain,(
    ! [X2359: $i] :
      ( ( k10_relat_1 @ ( o_0_0_xboole_0 @ X2359 ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41','42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k8_relset_1 @ ( X1 @ ( X0 @ ( o_0_0_xboole_0 @ X2 ) ) ) )
      = o_0_0_xboole_0 ) ),
    inference(demod,[status(thm)],['39','43'])).

thf('45',plain,(
    o_0_0_xboole_0 != o_0_0_xboole_0 ),
    inference(demod,[status(thm)],['34','44'])).

thf('46',plain,(
    $false ),
    inference(simplify,[status(thm)],['45'])).

%------------------------------------------------------------------------------
