%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9R3P1Ykd2V

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 209 expanded)
%              Number of leaves         :   37 (  78 expanded)
%              Depth                    :   18
%              Number of atoms          :  650 (2307 expanded)
%              Number of equality atoms :   67 ( 158 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(t64_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( v1_funct_1 @ D )
        & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
     => ( ( B != k1_xboole_0 )
       => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( ( v1_funct_1 @ D )
          & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B )
          & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) )
       => ( ( B != k1_xboole_0 )
         => ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t64_funct_2])).

thf('0',plain,(
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X34: $i,X35: $i,X36: $i,X37: $i] :
      ( ~ ( m1_subset_1 @ X34 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X35 @ X36 ) ) )
      | ( ( k7_relset_1 @ X35 @ X36 @ X34 @ X37 )
        = ( k9_relat_1 @ X34 @ X37 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D @ X0 )
      = ( k9_relat_1 @ sk_D @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X19 @ X20 ) @ ( k2_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('6',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v4_relat_1 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('8',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('9',plain,(
    ! [X17: $i,X18: $i] :
      ( ~ ( v4_relat_1 @ X17 @ X18 )
      | ( r1_tarski @ ( k1_relat_1 @ X17 ) @ X18 )
      | ~ ( v1_relat_1 @ X17 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('12',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['10','13'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('15',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(l45_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) )
    <=> ~ ( ( A != k1_xboole_0 )
          & ( A
           != ( k1_tarski @ B ) )
          & ( A
           != ( k1_tarski @ C ) )
          & ( A
           != ( k2_tarski @ B @ C ) ) ) ) )).

thf('16',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( X8
        = ( k2_tarski @ X6 @ X7 ) )
      | ( X8
        = ( k1_tarski @ X7 ) )
      | ( X8
        = ( k1_tarski @ X6 ) )
      | ( X8 = k1_xboole_0 )
      | ~ ( r1_tarski @ X8 @ ( k2_tarski @ X6 @ X7 ) ) ) ),
    inference(cnf,[status(esa)],[l45_zfmisc_1])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['17'])).

thf('19',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k2_tarski @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','18'])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( k2_tarski @ X0 @ X0 )
      = ( k1_tarski @ X0 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('21',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['19','20'])).

thf('22',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['21'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('23',plain,(
    ! [X26: $i,X27: $i] :
      ( ( ( k1_relat_1 @ X27 )
       != ( k1_tarski @ X26 ) )
      | ( ( k2_relat_1 @ X27 )
        = ( k1_tarski @ ( k1_funct_1 @ X27 @ X26 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['24'])).

thf('26',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('28',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['25','26','27'])).

thf('29',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('30',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','30'])).

thf('32',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('33',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['31','32'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('34',plain,(
    ! [X25: $i] :
      ( ( ( k1_relat_1 @ X25 )
       != k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('35',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('37',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['35','36'])).

thf('38',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('39',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('40',plain,(
    ! [X31: $i,X32: $i,X33: $i] :
      ( ( v4_relat_1 @ X31 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X32 @ X33 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('41',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['39','40'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('42',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X23
        = ( k7_relat_1 @ X23 @ X24 ) )
      | ~ ( v4_relat_1 @ X23 @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('43',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( k1_xboole_0
        = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('45',plain,(
    ! [X28: $i,X29: $i,X30: $i] :
      ( ( v1_relat_1 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X29 @ X30 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('46',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k7_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['43','46'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('48',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) )
        = ( k9_relat_1 @ X21 @ X22 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( ( k2_relat_1 @ k1_xboole_0 )
        = ( k9_relat_1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('50',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('51',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['44','45'])).

thf('52',plain,(
    ! [X0: $i] :
      ( k1_xboole_0
      = ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ),
    inference(demod,[status(thm)],['49','50','51'])).

thf('53',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['37'])).

thf('54',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('55',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('56',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['4','38','52','53','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.9R3P1Ykd2V
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:08:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.14/0.36  % Running in FO mode
% 0.21/0.60  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.21/0.60  % Solved by: fo/fo7.sh
% 0.21/0.60  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.21/0.60  % done 426 iterations in 0.132s
% 0.21/0.60  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.21/0.60  % SZS output start Refutation
% 0.21/0.60  thf(sk_A_type, type, sk_A: $i).
% 0.21/0.60  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.21/0.60  thf(sk_D_type, type, sk_D: $i).
% 0.21/0.60  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.21/0.60  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.21/0.60  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.21/0.60  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.21/0.60  thf(sk_B_type, type, sk_B: $i).
% 0.21/0.60  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.21/0.60  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.21/0.60  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.21/0.60  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.21/0.60  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.21/0.60  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.21/0.60  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.21/0.60  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.21/0.60  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.21/0.60  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.21/0.60  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.21/0.60  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.21/0.60  thf(sk_C_type, type, sk_C: $i).
% 0.21/0.60  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.21/0.60  thf(t64_funct_2, conjecture,
% 0.21/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.60     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.21/0.60         ( m1_subset_1 @
% 0.21/0.60           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.21/0.60       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.60         ( r1_tarski @
% 0.21/0.60           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.21/0.60           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.21/0.60  thf(zf_stmt_0, negated_conjecture,
% 0.21/0.60    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.60        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.21/0.60            ( m1_subset_1 @
% 0.21/0.60              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.21/0.60          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.21/0.60            ( r1_tarski @
% 0.21/0.60              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.21/0.60              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.21/0.60    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.21/0.60  thf('0', plain,
% 0.21/0.60      (~ (r1_tarski @ 
% 0.21/0.60          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.21/0.60          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('1', plain,
% 0.21/0.60      ((m1_subset_1 @ sk_D @ 
% 0.21/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf(redefinition_k7_relset_1, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i,D:$i]:
% 0.21/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.60       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.21/0.60  thf('2', plain,
% 0.21/0.60      (![X34 : $i, X35 : $i, X36 : $i, X37 : $i]:
% 0.21/0.60         (~ (m1_subset_1 @ X34 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X35 @ X36)))
% 0.21/0.60          | ((k7_relset_1 @ X35 @ X36 @ X34 @ X37) = (k9_relat_1 @ X34 @ X37)))),
% 0.21/0.60      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.21/0.60  thf('3', plain,
% 0.21/0.60      (![X0 : $i]:
% 0.21/0.60         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.21/0.60           = (k9_relat_1 @ sk_D @ X0))),
% 0.21/0.60      inference('sup-', [status(thm)], ['1', '2'])).
% 0.21/0.60  thf('4', plain,
% 0.21/0.60      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.21/0.60          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.21/0.60      inference('demod', [status(thm)], ['0', '3'])).
% 0.21/0.60  thf(t144_relat_1, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( v1_relat_1 @ B ) =>
% 0.21/0.60       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.21/0.60  thf('5', plain,
% 0.21/0.60      (![X19 : $i, X20 : $i]:
% 0.21/0.60         ((r1_tarski @ (k9_relat_1 @ X19 @ X20) @ (k2_relat_1 @ X19))
% 0.21/0.60          | ~ (v1_relat_1 @ X19))),
% 0.21/0.60      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.21/0.60  thf('6', plain,
% 0.21/0.60      ((m1_subset_1 @ sk_D @ 
% 0.21/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf(cc2_relset_1, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.60       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.21/0.60  thf('7', plain,
% 0.21/0.60      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.60         ((v4_relat_1 @ X31 @ X32)
% 0.21/0.60          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.21/0.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.60  thf('8', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.21/0.60      inference('sup-', [status(thm)], ['6', '7'])).
% 0.21/0.60  thf(d18_relat_1, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( v1_relat_1 @ B ) =>
% 0.21/0.60       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.21/0.60  thf('9', plain,
% 0.21/0.60      (![X17 : $i, X18 : $i]:
% 0.21/0.60         (~ (v4_relat_1 @ X17 @ X18)
% 0.21/0.60          | (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 0.21/0.60          | ~ (v1_relat_1 @ X17))),
% 0.21/0.60      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.21/0.60  thf('10', plain,
% 0.21/0.60      ((~ (v1_relat_1 @ sk_D)
% 0.21/0.60        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['8', '9'])).
% 0.21/0.60  thf('11', plain,
% 0.21/0.60      ((m1_subset_1 @ sk_D @ 
% 0.21/0.60        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf(cc1_relset_1, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.21/0.60       ( v1_relat_1 @ C ) ))).
% 0.21/0.60  thf('12', plain,
% 0.21/0.60      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.60         ((v1_relat_1 @ X28)
% 0.21/0.60          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.21/0.60      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.60  thf('13', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.60  thf('14', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.21/0.60      inference('demod', [status(thm)], ['10', '13'])).
% 0.21/0.60  thf(t69_enumset1, axiom,
% 0.21/0.60    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.21/0.60  thf('15', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.60  thf(l45_zfmisc_1, axiom,
% 0.21/0.60    (![A:$i,B:$i,C:$i]:
% 0.21/0.60     ( ( r1_tarski @ A @ ( k2_tarski @ B @ C ) ) <=>
% 0.21/0.60       ( ~( ( ( A ) != ( k1_xboole_0 ) ) & ( ( A ) != ( k1_tarski @ B ) ) & 
% 0.21/0.60            ( ( A ) != ( k1_tarski @ C ) ) & ( ( A ) != ( k2_tarski @ B @ C ) ) ) ) ))).
% 0.21/0.60  thf('16', plain,
% 0.21/0.60      (![X6 : $i, X7 : $i, X8 : $i]:
% 0.21/0.60         (((X8) = (k2_tarski @ X6 @ X7))
% 0.21/0.60          | ((X8) = (k1_tarski @ X7))
% 0.21/0.60          | ((X8) = (k1_tarski @ X6))
% 0.21/0.60          | ((X8) = (k1_xboole_0))
% 0.21/0.60          | ~ (r1_tarski @ X8 @ (k2_tarski @ X6 @ X7)))),
% 0.21/0.60      inference('cnf', [status(esa)], [l45_zfmisc_1])).
% 0.21/0.60  thf('17', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i]:
% 0.21/0.60         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.21/0.60          | ((X1) = (k1_xboole_0))
% 0.21/0.60          | ((X1) = (k1_tarski @ X0))
% 0.21/0.60          | ((X1) = (k1_tarski @ X0))
% 0.21/0.60          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['15', '16'])).
% 0.21/0.60  thf('18', plain,
% 0.21/0.60      (![X0 : $i, X1 : $i]:
% 0.21/0.60         (((X1) = (k2_tarski @ X0 @ X0))
% 0.21/0.60          | ((X1) = (k1_tarski @ X0))
% 0.21/0.60          | ((X1) = (k1_xboole_0))
% 0.21/0.60          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.21/0.60      inference('simplify', [status(thm)], ['17'])).
% 0.21/0.60  thf('19', plain,
% 0.21/0.60      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.21/0.60        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.21/0.60        | ((k1_relat_1 @ sk_D) = (k2_tarski @ sk_A @ sk_A)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['14', '18'])).
% 0.21/0.60  thf('20', plain, (![X0 : $i]: ((k2_tarski @ X0 @ X0) = (k1_tarski @ X0))),
% 0.21/0.60      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.21/0.60  thf('21', plain,
% 0.21/0.60      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.21/0.60        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.21/0.60        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.21/0.60      inference('demod', [status(thm)], ['19', '20'])).
% 0.21/0.60  thf('22', plain,
% 0.21/0.60      ((((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.21/0.60        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.21/0.60      inference('simplify', [status(thm)], ['21'])).
% 0.21/0.60  thf(t14_funct_1, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.21/0.60       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.21/0.60         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.21/0.60  thf('23', plain,
% 0.21/0.60      (![X26 : $i, X27 : $i]:
% 0.21/0.60         (((k1_relat_1 @ X27) != (k1_tarski @ X26))
% 0.21/0.60          | ((k2_relat_1 @ X27) = (k1_tarski @ (k1_funct_1 @ X27 @ X26)))
% 0.21/0.60          | ~ (v1_funct_1 @ X27)
% 0.21/0.60          | ~ (v1_relat_1 @ X27))),
% 0.21/0.60      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.21/0.60  thf('24', plain,
% 0.21/0.60      (![X0 : $i]:
% 0.21/0.60         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.21/0.60          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.21/0.60          | ~ (v1_relat_1 @ X0)
% 0.21/0.60          | ~ (v1_funct_1 @ X0)
% 0.21/0.60          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.21/0.60      inference('sup-', [status(thm)], ['22', '23'])).
% 0.21/0.60  thf('25', plain,
% 0.21/0.60      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.21/0.60        | ~ (v1_funct_1 @ sk_D)
% 0.21/0.60        | ~ (v1_relat_1 @ sk_D)
% 0.21/0.60        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.21/0.60      inference('eq_res', [status(thm)], ['24'])).
% 0.21/0.60  thf('26', plain, ((v1_funct_1 @ sk_D)),
% 0.21/0.60      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.21/0.60  thf('27', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.60  thf('28', plain,
% 0.21/0.60      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.21/0.60        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.21/0.60      inference('demod', [status(thm)], ['25', '26', '27'])).
% 0.21/0.60  thf('29', plain,
% 0.21/0.60      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.21/0.60          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.21/0.60      inference('demod', [status(thm)], ['0', '3'])).
% 0.21/0.60  thf('30', plain,
% 0.21/0.60      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.21/0.60        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['28', '29'])).
% 0.21/0.60  thf('31', plain,
% 0.21/0.60      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['5', '30'])).
% 0.21/0.60  thf('32', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.60  thf('33', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.21/0.60      inference('demod', [status(thm)], ['31', '32'])).
% 0.21/0.60  thf(t64_relat_1, axiom,
% 0.21/0.60    (![A:$i]:
% 0.21/0.60     ( ( v1_relat_1 @ A ) =>
% 0.21/0.60       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.21/0.60           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.21/0.60         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.21/0.60  thf('34', plain,
% 0.21/0.60      (![X25 : $i]:
% 0.21/0.60         (((k1_relat_1 @ X25) != (k1_xboole_0))
% 0.21/0.60          | ((X25) = (k1_xboole_0))
% 0.21/0.60          | ~ (v1_relat_1 @ X25))),
% 0.21/0.60      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.21/0.60  thf('35', plain,
% 0.21/0.60      ((((k1_xboole_0) != (k1_xboole_0))
% 0.21/0.60        | ~ (v1_relat_1 @ sk_D)
% 0.21/0.60        | ((sk_D) = (k1_xboole_0)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['33', '34'])).
% 0.21/0.60  thf('36', plain, ((v1_relat_1 @ sk_D)),
% 0.21/0.60      inference('sup-', [status(thm)], ['11', '12'])).
% 0.21/0.60  thf('37', plain,
% 0.21/0.60      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 0.21/0.60      inference('demod', [status(thm)], ['35', '36'])).
% 0.21/0.60  thf('38', plain, (((sk_D) = (k1_xboole_0))),
% 0.21/0.60      inference('simplify', [status(thm)], ['37'])).
% 0.21/0.60  thf(t4_subset_1, axiom,
% 0.21/0.60    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.21/0.60  thf('39', plain,
% 0.21/0.60      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.21/0.60      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.60  thf('40', plain,
% 0.21/0.60      (![X31 : $i, X32 : $i, X33 : $i]:
% 0.21/0.60         ((v4_relat_1 @ X31 @ X32)
% 0.21/0.60          | ~ (m1_subset_1 @ X31 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X32 @ X33))))),
% 0.21/0.60      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.21/0.60  thf('41', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 0.21/0.60      inference('sup-', [status(thm)], ['39', '40'])).
% 0.21/0.60  thf(t209_relat_1, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.21/0.60       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.21/0.60  thf('42', plain,
% 0.21/0.60      (![X23 : $i, X24 : $i]:
% 0.21/0.60         (((X23) = (k7_relat_1 @ X23 @ X24))
% 0.21/0.60          | ~ (v4_relat_1 @ X23 @ X24)
% 0.21/0.60          | ~ (v1_relat_1 @ X23))),
% 0.21/0.60      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.21/0.60  thf('43', plain,
% 0.21/0.60      (![X0 : $i]:
% 0.21/0.60         (~ (v1_relat_1 @ k1_xboole_0)
% 0.21/0.60          | ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0)))),
% 0.21/0.60      inference('sup-', [status(thm)], ['41', '42'])).
% 0.21/0.60  thf('44', plain,
% 0.21/0.60      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.21/0.60      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.60  thf('45', plain,
% 0.21/0.60      (![X28 : $i, X29 : $i, X30 : $i]:
% 0.21/0.60         ((v1_relat_1 @ X28)
% 0.21/0.60          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X29 @ X30))))),
% 0.21/0.60      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.21/0.60  thf('46', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.60      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.60  thf('47', plain,
% 0.21/0.60      (![X0 : $i]: ((k1_xboole_0) = (k7_relat_1 @ k1_xboole_0 @ X0))),
% 0.21/0.60      inference('demod', [status(thm)], ['43', '46'])).
% 0.21/0.60  thf(t148_relat_1, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( v1_relat_1 @ B ) =>
% 0.21/0.60       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.21/0.60  thf('48', plain,
% 0.21/0.60      (![X21 : $i, X22 : $i]:
% 0.21/0.60         (((k2_relat_1 @ (k7_relat_1 @ X21 @ X22)) = (k9_relat_1 @ X21 @ X22))
% 0.21/0.60          | ~ (v1_relat_1 @ X21))),
% 0.21/0.60      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.21/0.60  thf('49', plain,
% 0.21/0.60      (![X0 : $i]:
% 0.21/0.60         (((k2_relat_1 @ k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))
% 0.21/0.60          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.21/0.60      inference('sup+', [status(thm)], ['47', '48'])).
% 0.21/0.60  thf(t60_relat_1, axiom,
% 0.21/0.60    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.21/0.60     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.21/0.60  thf('50', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.21/0.60      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.21/0.60  thf('51', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.21/0.60      inference('sup-', [status(thm)], ['44', '45'])).
% 0.21/0.60  thf('52', plain,
% 0.21/0.60      (![X0 : $i]: ((k1_xboole_0) = (k9_relat_1 @ k1_xboole_0 @ X0))),
% 0.21/0.60      inference('demod', [status(thm)], ['49', '50', '51'])).
% 0.21/0.60  thf('53', plain, (((sk_D) = (k1_xboole_0))),
% 0.21/0.60      inference('simplify', [status(thm)], ['37'])).
% 0.21/0.60  thf('54', plain,
% 0.21/0.60      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.21/0.60      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.21/0.60  thf(t3_subset, axiom,
% 0.21/0.60    (![A:$i,B:$i]:
% 0.21/0.60     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.21/0.60  thf('55', plain,
% 0.21/0.60      (![X11 : $i, X12 : $i]:
% 0.21/0.60         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.21/0.60      inference('cnf', [status(esa)], [t3_subset])).
% 0.21/0.60  thf('56', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.21/0.60      inference('sup-', [status(thm)], ['54', '55'])).
% 0.21/0.60  thf('57', plain, ($false),
% 0.21/0.60      inference('demod', [status(thm)], ['4', '38', '52', '53', '56'])).
% 0.21/0.60  
% 0.21/0.60  % SZS output end Refutation
% 0.21/0.60  
% 0.43/0.61  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
