%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Z6HNTfQC1E

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:51 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 313 expanded)
%              Number of leaves         :   40 ( 111 expanded)
%              Depth                    :   19
%              Number of atoms          :  705 (3464 expanded)
%              Number of equality atoms :   60 ( 186 expanded)
%              Maximal formula depth    :   15 (   5 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

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
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( ( k7_relset_1 @ X36 @ X37 @ X35 @ X38 )
        = ( k9_relat_1 @ X35 @ X38 ) ) ) ),
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
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v4_relat_1 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
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
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v1_relat_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('13',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['10','13'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('15',plain,(
    ! [X10: $i,X11: $i] :
      ( ( X11
        = ( k1_tarski @ X10 ) )
      | ( X11 = k1_xboole_0 )
      | ~ ( r1_tarski @ X11 @ ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('16',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','15'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ X0 @ X1 )
      | ( X0 != X1 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('18',plain,(
    ! [X1: $i] :
      ( r1_tarski @ X1 @ X1 ) ),
    inference(simplify,[status(thm)],['17'])).

thf(l1_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ ( k1_tarski @ A ) @ B )
    <=> ( r2_hidden @ A @ B ) ) )).

thf('19',plain,(
    ! [X7: $i,X8: $i] :
      ( ( r2_hidden @ X7 @ X8 )
      | ~ ( r1_tarski @ ( k1_tarski @ X7 ) @ X8 ) ) ),
    inference(cnf,[status(esa)],[l1_zfmisc_1])).

thf('20',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','20'])).

thf('22',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['16','20'])).

thf(t118_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) )
       => ( ( k9_relat_1 @ C @ ( k2_tarski @ A @ B ) )
          = ( k2_tarski @ ( k1_funct_1 @ C @ A ) @ ( k1_funct_1 @ C @ B ) ) ) ) ) )).

thf('23',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X26 @ ( k1_relat_1 @ X27 ) )
      | ~ ( r2_hidden @ X28 @ ( k1_relat_1 @ X27 ) )
      | ( ( k9_relat_1 @ X27 @ ( k2_tarski @ X26 @ X28 ) )
        = ( k2_tarski @ ( k1_funct_1 @ X27 @ X26 ) @ ( k1_funct_1 @ X27 @ X28 ) ) )
      | ~ ( v1_funct_1 @ X27 )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t118_funct_1])).

thf('24',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D )
      | ~ ( v1_funct_1 @ sk_D )
      | ( ( k9_relat_1 @ sk_D @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference('sup-',[status(thm)],['22','23'])).

thf('25',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('26',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ( ( k9_relat_1 @ sk_D @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) @ ( k1_funct_1 @ sk_D @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D ) ) ) ),
    inference(demod,[status(thm)],['24','25','26'])).

thf('28',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k9_relat_1 @ sk_D @ ( k2_tarski @ sk_A @ sk_A ) )
      = ( k2_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['21','27'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('29',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('30',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(t209_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v4_relat_1 @ B @ A ) )
     => ( B
        = ( k7_relat_1 @ B @ A ) ) ) )).

thf('31',plain,(
    ! [X23: $i,X24: $i] :
      ( ( X23
        = ( k7_relat_1 @ X23 @ X24 ) )
      | ~ ( v4_relat_1 @ X23 @ X24 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t209_relat_1])).

thf('32',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( sk_D
      = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('34',plain,
    ( sk_D
    = ( k7_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['32','33'])).

thf(t148_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) )
        = ( k9_relat_1 @ B @ A ) ) ) )).

thf('35',plain,(
    ! [X21: $i,X22: $i] :
      ( ( ( k2_relat_1 @ ( k7_relat_1 @ X21 @ X22 ) )
        = ( k9_relat_1 @ X21 @ X22 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t148_relat_1])).

thf('36',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k9_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) )
    | ~ ( v1_relat_1 @ sk_D ) ),
    inference('sup+',[status(thm)],['34','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('38',plain,
    ( ( k2_relat_1 @ sk_D )
    = ( k9_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['36','37'])).

thf('39',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('40',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['28','29','38','39'])).

thf('41',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['40'])).

thf('42',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('43',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('46',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['44','45'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('47',plain,(
    ! [X25: $i] :
      ( ( ( k1_relat_1 @ X25 )
       != k1_xboole_0 )
      | ( X25 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('48',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['11','12'])).

thf('50',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['50'])).

thf(t60_relat_1,axiom,
    ( ( ( k2_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 )
    & ( ( k1_relat_1 @ k1_xboole_0 )
      = k1_xboole_0 ) )).

thf('52',plain,
    ( ( k2_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference(cnf,[status(esa)],[t60_relat_1])).

thf('53',plain,(
    ! [X19: $i,X20: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X19 @ X20 ) @ ( k2_relat_1 @ X19 ) )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('54',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['52','53'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('55',plain,(
    ! [X13: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X13 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('56',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v1_relat_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('57',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','57'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('59',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('61',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['50'])).

thf('64',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('65',plain,(
    $false ),
    inference(demod,[status(thm)],['4','51','62','63','64'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.15  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.Z6HNTfQC1E
% 0.15/0.36  % Computer   : n007.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 11:30:06 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.36  % Running portfolio for 600 s
% 0.15/0.36  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.15/0.36  % Number of cores: 8
% 0.15/0.37  % Python version: Python 3.6.8
% 0.15/0.37  % Running in FO mode
% 0.22/0.54  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.22/0.54  % Solved by: fo/fo7.sh
% 0.22/0.54  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.22/0.54  % done 173 iterations in 0.066s
% 0.22/0.54  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.22/0.54  % SZS output start Refutation
% 0.22/0.54  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.22/0.54  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.22/0.54  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.22/0.54  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.22/0.54  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.22/0.54  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.22/0.54  thf(sk_D_type, type, sk_D: $i).
% 0.22/0.54  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.22/0.54  thf(sk_C_type, type, sk_C: $i).
% 0.22/0.54  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.22/0.54  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.22/0.54  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.22/0.54  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.22/0.54  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.22/0.54  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.22/0.54  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.22/0.54  thf(sk_A_type, type, sk_A: $i).
% 0.22/0.54  thf(k7_relat_1_type, type, k7_relat_1: $i > $i > $i).
% 0.22/0.54  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.22/0.54  thf(sk_B_type, type, sk_B: $i).
% 0.22/0.54  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.22/0.54  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.22/0.54  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.22/0.54  thf(t64_funct_2, conjecture,
% 0.22/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.54     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.22/0.54         ( m1_subset_1 @
% 0.22/0.54           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.22/0.54       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.22/0.54         ( r1_tarski @
% 0.22/0.54           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.22/0.54           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.22/0.54  thf(zf_stmt_0, negated_conjecture,
% 0.22/0.54    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.54        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.22/0.54            ( m1_subset_1 @
% 0.22/0.54              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.22/0.54          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.22/0.54            ( r1_tarski @
% 0.22/0.54              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.22/0.54              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.22/0.54    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.22/0.54  thf('0', plain,
% 0.22/0.54      (~ (r1_tarski @ 
% 0.22/0.54          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.22/0.54          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('1', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_D @ 
% 0.22/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(redefinition_k7_relset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i,D:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.54       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.22/0.54  thf('2', plain,
% 0.22/0.54      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.22/0.54         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.22/0.54          | ((k7_relset_1 @ X36 @ X37 @ X35 @ X38) = (k9_relat_1 @ X35 @ X38)))),
% 0.22/0.54      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.22/0.54  thf('3', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.22/0.54           = (k9_relat_1 @ sk_D @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['1', '2'])).
% 0.22/0.54  thf('4', plain,
% 0.22/0.54      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.22/0.54          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.22/0.54      inference('demod', [status(thm)], ['0', '3'])).
% 0.22/0.54  thf(t144_relat_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ B ) =>
% 0.22/0.54       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.22/0.54  thf('5', plain,
% 0.22/0.54      (![X19 : $i, X20 : $i]:
% 0.22/0.54         ((r1_tarski @ (k9_relat_1 @ X19 @ X20) @ (k2_relat_1 @ X19))
% 0.22/0.54          | ~ (v1_relat_1 @ X19))),
% 0.22/0.54      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.22/0.54  thf('6', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_D @ 
% 0.22/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(cc2_relset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.54       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.22/0.54  thf('7', plain,
% 0.22/0.54      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.22/0.54         ((v4_relat_1 @ X32 @ X33)
% 0.22/0.54          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.22/0.54      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.22/0.54  thf('8', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.54  thf(d18_relat_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ B ) =>
% 0.22/0.54       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.22/0.54  thf('9', plain,
% 0.22/0.54      (![X17 : $i, X18 : $i]:
% 0.22/0.54         (~ (v4_relat_1 @ X17 @ X18)
% 0.22/0.54          | (r1_tarski @ (k1_relat_1 @ X17) @ X18)
% 0.22/0.54          | ~ (v1_relat_1 @ X17))),
% 0.22/0.54      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.22/0.54  thf('10', plain,
% 0.22/0.54      ((~ (v1_relat_1 @ sk_D)
% 0.22/0.54        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['8', '9'])).
% 0.22/0.54  thf('11', plain,
% 0.22/0.54      ((m1_subset_1 @ sk_D @ 
% 0.22/0.54        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf(cc1_relset_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.22/0.54       ( v1_relat_1 @ C ) ))).
% 0.22/0.54  thf('12', plain,
% 0.22/0.54      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.22/0.54         ((v1_relat_1 @ X29)
% 0.22/0.54          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.22/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.54  thf('13', plain, ((v1_relat_1 @ sk_D)),
% 0.22/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.54  thf('14', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.22/0.54      inference('demod', [status(thm)], ['10', '13'])).
% 0.22/0.54  thf(l3_zfmisc_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.22/0.54       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.22/0.54  thf('15', plain,
% 0.22/0.54      (![X10 : $i, X11 : $i]:
% 0.22/0.54         (((X11) = (k1_tarski @ X10))
% 0.22/0.54          | ((X11) = (k1_xboole_0))
% 0.22/0.54          | ~ (r1_tarski @ X11 @ (k1_tarski @ X10)))),
% 0.22/0.54      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.22/0.54  thf('16', plain,
% 0.22/0.54      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.22/0.54        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['14', '15'])).
% 0.22/0.54  thf(d10_xboole_0, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.22/0.54  thf('17', plain,
% 0.22/0.54      (![X0 : $i, X1 : $i]: ((r1_tarski @ X0 @ X1) | ((X0) != (X1)))),
% 0.22/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.54  thf('18', plain, (![X1 : $i]: (r1_tarski @ X1 @ X1)),
% 0.22/0.54      inference('simplify', [status(thm)], ['17'])).
% 0.22/0.54  thf(l1_zfmisc_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( r1_tarski @ ( k1_tarski @ A ) @ B ) <=> ( r2_hidden @ A @ B ) ))).
% 0.22/0.54  thf('19', plain,
% 0.22/0.54      (![X7 : $i, X8 : $i]:
% 0.22/0.54         ((r2_hidden @ X7 @ X8) | ~ (r1_tarski @ (k1_tarski @ X7) @ X8))),
% 0.22/0.54      inference('cnf', [status(esa)], [l1_zfmisc_1])).
% 0.22/0.54  thf('20', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['18', '19'])).
% 0.22/0.54  thf('21', plain,
% 0.22/0.54      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D))
% 0.22/0.54        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.22/0.54      inference('sup+', [status(thm)], ['16', '20'])).
% 0.22/0.54  thf('22', plain,
% 0.22/0.54      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D))
% 0.22/0.54        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.22/0.54      inference('sup+', [status(thm)], ['16', '20'])).
% 0.22/0.54  thf(t118_funct_1, axiom,
% 0.22/0.54    (![A:$i,B:$i,C:$i]:
% 0.22/0.54     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.22/0.54       ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.22/0.54           ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) ) =>
% 0.22/0.54         ( ( k9_relat_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 0.22/0.54           ( k2_tarski @ ( k1_funct_1 @ C @ A ) @ ( k1_funct_1 @ C @ B ) ) ) ) ))).
% 0.22/0.54  thf('23', plain,
% 0.22/0.54      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.22/0.54         (~ (r2_hidden @ X26 @ (k1_relat_1 @ X27))
% 0.22/0.54          | ~ (r2_hidden @ X28 @ (k1_relat_1 @ X27))
% 0.22/0.54          | ((k9_relat_1 @ X27 @ (k2_tarski @ X26 @ X28))
% 0.22/0.54              = (k2_tarski @ (k1_funct_1 @ X27 @ X26) @ 
% 0.22/0.54                 (k1_funct_1 @ X27 @ X28)))
% 0.22/0.54          | ~ (v1_funct_1 @ X27)
% 0.22/0.54          | ~ (v1_relat_1 @ X27))),
% 0.22/0.54      inference('cnf', [status(esa)], [t118_funct_1])).
% 0.22/0.54  thf('24', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.22/0.54          | ~ (v1_relat_1 @ sk_D)
% 0.22/0.54          | ~ (v1_funct_1 @ sk_D)
% 0.22/0.54          | ((k9_relat_1 @ sk_D @ (k2_tarski @ sk_A @ X0))
% 0.22/0.54              = (k2_tarski @ (k1_funct_1 @ sk_D @ sk_A) @ 
% 0.22/0.54                 (k1_funct_1 @ sk_D @ X0)))
% 0.22/0.54          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['22', '23'])).
% 0.22/0.54  thf('25', plain, ((v1_relat_1 @ sk_D)),
% 0.22/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.54  thf('26', plain, ((v1_funct_1 @ sk_D)),
% 0.22/0.54      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.22/0.54  thf('27', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         (((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.22/0.54          | ((k9_relat_1 @ sk_D @ (k2_tarski @ sk_A @ X0))
% 0.22/0.54              = (k2_tarski @ (k1_funct_1 @ sk_D @ sk_A) @ 
% 0.22/0.54                 (k1_funct_1 @ sk_D @ X0)))
% 0.22/0.54          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D)))),
% 0.22/0.54      inference('demod', [status(thm)], ['24', '25', '26'])).
% 0.22/0.54  thf('28', plain,
% 0.22/0.54      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.22/0.54        | ((k9_relat_1 @ sk_D @ (k2_tarski @ sk_A @ sk_A))
% 0.22/0.54            = (k2_tarski @ (k1_funct_1 @ sk_D @ sk_A) @ 
% 0.22/0.54               (k1_funct_1 @ sk_D @ sk_A)))
% 0.22/0.54        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['21', '27'])).
% 0.22/0.54  thf(t69_enumset1, axiom,
% 0.22/0.54    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.22/0.54  thf('29', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.22/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.54  thf('30', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.22/0.54      inference('sup-', [status(thm)], ['6', '7'])).
% 0.22/0.54  thf(t209_relat_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( ( v1_relat_1 @ B ) & ( v4_relat_1 @ B @ A ) ) =>
% 0.22/0.54       ( ( B ) = ( k7_relat_1 @ B @ A ) ) ))).
% 0.22/0.54  thf('31', plain,
% 0.22/0.54      (![X23 : $i, X24 : $i]:
% 0.22/0.54         (((X23) = (k7_relat_1 @ X23 @ X24))
% 0.22/0.54          | ~ (v4_relat_1 @ X23 @ X24)
% 0.22/0.54          | ~ (v1_relat_1 @ X23))),
% 0.22/0.54      inference('cnf', [status(esa)], [t209_relat_1])).
% 0.22/0.54  thf('32', plain,
% 0.22/0.54      ((~ (v1_relat_1 @ sk_D)
% 0.22/0.54        | ((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A))))),
% 0.22/0.54      inference('sup-', [status(thm)], ['30', '31'])).
% 0.22/0.54  thf('33', plain, ((v1_relat_1 @ sk_D)),
% 0.22/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.54  thf('34', plain, (((sk_D) = (k7_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.22/0.54      inference('demod', [status(thm)], ['32', '33'])).
% 0.22/0.54  thf(t148_relat_1, axiom,
% 0.22/0.54    (![A:$i,B:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ B ) =>
% 0.22/0.54       ( ( k2_relat_1 @ ( k7_relat_1 @ B @ A ) ) = ( k9_relat_1 @ B @ A ) ) ))).
% 0.22/0.54  thf('35', plain,
% 0.22/0.54      (![X21 : $i, X22 : $i]:
% 0.22/0.54         (((k2_relat_1 @ (k7_relat_1 @ X21 @ X22)) = (k9_relat_1 @ X21 @ X22))
% 0.22/0.54          | ~ (v1_relat_1 @ X21))),
% 0.22/0.54      inference('cnf', [status(esa)], [t148_relat_1])).
% 0.22/0.54  thf('36', plain,
% 0.22/0.54      ((((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ (k1_tarski @ sk_A)))
% 0.22/0.54        | ~ (v1_relat_1 @ sk_D))),
% 0.22/0.54      inference('sup+', [status(thm)], ['34', '35'])).
% 0.22/0.54  thf('37', plain, ((v1_relat_1 @ sk_D)),
% 0.22/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.54  thf('38', plain,
% 0.22/0.54      (((k2_relat_1 @ sk_D) = (k9_relat_1 @ sk_D @ (k1_tarski @ sk_A)))),
% 0.22/0.54      inference('demod', [status(thm)], ['36', '37'])).
% 0.22/0.54  thf('39', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.22/0.54      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.22/0.54  thf('40', plain,
% 0.22/0.54      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.22/0.54        | ((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.22/0.54        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.22/0.54      inference('demod', [status(thm)], ['28', '29', '38', '39'])).
% 0.22/0.54  thf('41', plain,
% 0.22/0.54      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.22/0.54        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.22/0.54      inference('simplify', [status(thm)], ['40'])).
% 0.22/0.54  thf('42', plain,
% 0.22/0.54      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.22/0.54          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.22/0.54      inference('demod', [status(thm)], ['0', '3'])).
% 0.22/0.54  thf('43', plain,
% 0.22/0.54      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.22/0.54        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['41', '42'])).
% 0.22/0.54  thf('44', plain,
% 0.22/0.54      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['5', '43'])).
% 0.22/0.54  thf('45', plain, ((v1_relat_1 @ sk_D)),
% 0.22/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.54  thf('46', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.22/0.54      inference('demod', [status(thm)], ['44', '45'])).
% 0.22/0.54  thf(t64_relat_1, axiom,
% 0.22/0.54    (![A:$i]:
% 0.22/0.54     ( ( v1_relat_1 @ A ) =>
% 0.22/0.54       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.22/0.54           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.22/0.54         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.22/0.54  thf('47', plain,
% 0.22/0.54      (![X25 : $i]:
% 0.22/0.54         (((k1_relat_1 @ X25) != (k1_xboole_0))
% 0.22/0.54          | ((X25) = (k1_xboole_0))
% 0.22/0.54          | ~ (v1_relat_1 @ X25))),
% 0.22/0.54      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.22/0.54  thf('48', plain,
% 0.22/0.54      ((((k1_xboole_0) != (k1_xboole_0))
% 0.22/0.54        | ~ (v1_relat_1 @ sk_D)
% 0.22/0.54        | ((sk_D) = (k1_xboole_0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['46', '47'])).
% 0.22/0.54  thf('49', plain, ((v1_relat_1 @ sk_D)),
% 0.22/0.54      inference('sup-', [status(thm)], ['11', '12'])).
% 0.22/0.54  thf('50', plain,
% 0.22/0.54      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 0.22/0.54      inference('demod', [status(thm)], ['48', '49'])).
% 0.22/0.54  thf('51', plain, (((sk_D) = (k1_xboole_0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['50'])).
% 0.22/0.54  thf(t60_relat_1, axiom,
% 0.22/0.54    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.22/0.54     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.22/0.54  thf('52', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.22/0.54      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.22/0.54  thf('53', plain,
% 0.22/0.54      (![X19 : $i, X20 : $i]:
% 0.22/0.54         ((r1_tarski @ (k9_relat_1 @ X19 @ X20) @ (k2_relat_1 @ X19))
% 0.22/0.54          | ~ (v1_relat_1 @ X19))),
% 0.22/0.54      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.22/0.54  thf('54', plain,
% 0.22/0.54      (![X0 : $i]:
% 0.22/0.54         ((r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.22/0.54          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.22/0.54      inference('sup+', [status(thm)], ['52', '53'])).
% 0.22/0.54  thf(t4_subset_1, axiom,
% 0.22/0.54    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.22/0.54  thf('55', plain,
% 0.22/0.54      (![X13 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X13))),
% 0.22/0.54      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.22/0.54  thf('56', plain,
% 0.22/0.54      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.22/0.54         ((v1_relat_1 @ X29)
% 0.22/0.54          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.22/0.54      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.22/0.54  thf('57', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.22/0.54      inference('sup-', [status(thm)], ['55', '56'])).
% 0.22/0.54  thf('58', plain,
% 0.22/0.54      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)),
% 0.22/0.54      inference('demod', [status(thm)], ['54', '57'])).
% 0.22/0.54  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.22/0.54  thf('59', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.22/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.54  thf('60', plain,
% 0.22/0.54      (![X0 : $i, X2 : $i]:
% 0.22/0.54         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.22/0.54      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.22/0.54  thf('61', plain,
% 0.22/0.54      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.22/0.54      inference('sup-', [status(thm)], ['59', '60'])).
% 0.22/0.54  thf('62', plain,
% 0.22/0.54      (![X0 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.22/0.54      inference('sup-', [status(thm)], ['58', '61'])).
% 0.22/0.54  thf('63', plain, (((sk_D) = (k1_xboole_0))),
% 0.22/0.54      inference('simplify', [status(thm)], ['50'])).
% 0.22/0.54  thf('64', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.22/0.54      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.22/0.54  thf('65', plain, ($false),
% 0.22/0.54      inference('demod', [status(thm)], ['4', '51', '62', '63', '64'])).
% 0.22/0.54  
% 0.22/0.54  % SZS output end Refutation
% 0.22/0.54  
% 0.22/0.55  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
