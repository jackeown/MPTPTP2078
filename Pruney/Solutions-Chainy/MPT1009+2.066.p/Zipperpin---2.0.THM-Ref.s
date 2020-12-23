%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rHTa9Ymlsz

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:58 EST 2020

% Result     : Theorem 0.59s
% Output     : Refutation 0.59s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 230 expanded)
%              Number of leaves         :   37 (  83 expanded)
%              Depth                    :   22
%              Number of atoms          :  855 (2862 expanded)
%              Number of equality atoms :   98 ( 248 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

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
    ! [X32: $i,X33: $i,X34: $i,X35: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( ( k7_relset_1 @ X33 @ X34 @ X32 @ X35 )
        = ( k9_relat_1 @ X32 @ X35 ) ) ) ),
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
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X21 @ X22 ) @ ( k2_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('6',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('7',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf(t142_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) )
    <=> ~ ( ( D != k1_xboole_0 )
          & ( D
           != ( k1_tarski @ A ) )
          & ( D
           != ( k1_tarski @ B ) )
          & ( D
           != ( k1_tarski @ C ) )
          & ( D
           != ( k2_tarski @ A @ B ) )
          & ( D
           != ( k2_tarski @ B @ C ) )
          & ( D
           != ( k2_tarski @ A @ C ) )
          & ( D
           != ( k1_enumset1 @ A @ B @ C ) ) ) ) )).

thf('8',plain,(
    ! [X10: $i,X11: $i,X12: $i,X14: $i] :
      ( ( r1_tarski @ X14 @ ( k1_enumset1 @ X10 @ X11 @ X12 ) )
      | ( X14
       != ( k1_tarski @ X10 ) ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('9',plain,(
    ! [X10: $i,X11: $i,X12: $i] :
      ( r1_tarski @ ( k1_tarski @ X10 ) @ ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ),
    inference(simplify,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k1_tarski @ X1 ) @ ( k2_tarski @ X1 @ X0 ) ) ),
    inference('sup+',[status(thm)],['7','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('12',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v4_relat_1 @ X29 @ X30 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('13',plain,(
    v4_relat_1 @ sk_D @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('14',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( v4_relat_1 @ X19 @ X20 )
      | ( r1_tarski @ ( k1_relat_1 @ X19 ) @ X20 )
      | ~ ( v1_relat_1 @ X19 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('15',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['13','14'])).

thf('16',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('17',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('18',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['15','18'])).

thf(t1_xboole_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ C ) )
     => ( r1_tarski @ A @ C ) ) )).

thf('20',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ X0 )
      | ~ ( r1_tarski @ ( k1_tarski @ sk_A ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ sk_D ) @ ( k2_tarski @ sk_A @ X0 ) ) ),
    inference('sup-',[status(thm)],['10','21'])).

thf('23',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('24',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ( X13
        = ( k1_enumset1 @ X10 @ X11 @ X12 ) )
      | ( X13
        = ( k2_tarski @ X10 @ X12 ) )
      | ( X13
        = ( k2_tarski @ X11 @ X12 ) )
      | ( X13
        = ( k2_tarski @ X10 @ X11 ) )
      | ( X13
        = ( k1_tarski @ X12 ) )
      | ( X13
        = ( k1_tarski @ X11 ) )
      | ( X13
        = ( k1_tarski @ X10 ) )
      | ( X13 = k1_xboole_0 )
      | ~ ( r1_tarski @ X13 @ ( k1_enumset1 @ X10 @ X11 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k1_tarski @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X1 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k1_enumset1 @ X1 @ X1 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X5: $i,X6: $i] :
      ( ( k1_enumset1 @ X5 @ X5 @ X6 )
      = ( k2_tarski @ X5 @ X6 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('27',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X2 @ ( k2_tarski @ X1 @ X0 ) )
      | ( X2 = k1_xboole_0 )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2
        = ( k1_tarski @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X1 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( X2
        = ( k2_tarski @ X1 @ X0 ) )
      | ( X2
        = ( k2_tarski @ X1 @ X1 ) )
      | ( X2
        = ( k1_tarski @ X0 ) )
      | ( X2
        = ( k1_tarski @ X1 ) )
      | ( X2 = k1_xboole_0 )
      | ~ ( r1_tarski @ X2 @ ( k2_tarski @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_D )
        = ( k1_tarski @ sk_A ) )
      | ( ( k1_relat_1 @ sk_D )
        = ( k1_tarski @ X0 ) )
      | ( ( k1_relat_1 @ sk_D )
        = ( k2_tarski @ sk_A @ sk_A ) )
      | ( ( k1_relat_1 @ sk_D )
        = ( k2_tarski @ sk_A @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['22','28'])).

thf('30',plain,(
    ! [X4: $i] :
      ( ( k2_tarski @ X4 @ X4 )
      = ( k1_tarski @ X4 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('31',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ( ( k1_relat_1 @ sk_D )
        = ( k1_tarski @ sk_A ) )
      | ( ( k1_relat_1 @ sk_D )
        = ( k1_tarski @ X0 ) )
      | ( ( k1_relat_1 @ sk_D )
        = ( k1_tarski @ sk_A ) )
      | ( ( k1_relat_1 @ sk_D )
        = ( k2_tarski @ sk_A @ X0 ) ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D )
        = ( k2_tarski @ sk_A @ X0 ) )
      | ( ( k1_relat_1 @ sk_D )
        = ( k1_tarski @ X0 ) )
      | ( ( k1_relat_1 @ sk_D )
        = ( k1_tarski @ sk_A ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup+',[status(thm)],['6','32'])).

thf('34',plain,
    ( ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D )
      = ( k1_tarski @ sk_A ) ) ),
    inference(simplify,[status(thm)],['33'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('35',plain,(
    ! [X24: $i,X25: $i] :
      ( ( ( k1_relat_1 @ X25 )
       != ( k1_tarski @ X24 ) )
      | ( ( k2_relat_1 @ X25 )
        = ( k1_tarski @ ( k1_funct_1 @ X25 @ X24 ) ) )
      | ~ ( v1_funct_1 @ X25 )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D ) )
      | ( ( k1_relat_1 @ sk_D )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['34','35'])).

thf('37',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['36'])).

thf('38',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('39',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['16','17'])).

thf('40',plain,
    ( ( ( k2_relat_1 @ sk_D )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['37','38','39'])).

thf('41',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('42',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D @ sk_C ) @ ( k2_relat_1 @ sk_D ) )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,
    ( ~ ( v1_relat_1 @ sk_D )
    | ( ( k1_relat_1 @ sk_D )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','42'])).

thf('44',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['16','17'])).

thf('45',plain,
    ( ( k1_relat_1 @ sk_D )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['43','44'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('46',plain,(
    ! [X23: $i] :
      ( ( ( k1_relat_1 @ X23 )
       != k1_xboole_0 )
      | ( X23 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('47',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D )
    | ( sk_D = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    v1_relat_1 @ sk_D ),
    inference('sup-',[status(thm)],['16','17'])).

thf('49',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_D = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['47','48'])).

thf('50',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['49'])).

thf('51',plain,(
    sk_D = k1_xboole_0 ),
    inference(simplify,[status(thm)],['49'])).

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
    ! [X21: $i,X22: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X21 @ X22 ) @ ( k2_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
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
    ! [X15: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X15 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('56',plain,(
    ! [X26: $i,X27: $i,X28: $i] :
      ( ( v1_relat_1 @ X26 )
      | ~ ( m1_subset_1 @ X26 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X27 @ X28 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('57',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['55','56'])).

thf('58',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['54','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r1_tarski @ X0 @ X1 )
      | ~ ( r1_tarski @ X1 @ X2 )
      | ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[t1_xboole_1])).

thf('60',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ X1 )
      | ~ ( r1_tarski @ k1_xboole_0 @ X1 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('61',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) @ X1 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    $false ),
    inference(demod,[status(thm)],['4','50','51','62'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.rHTa9Ymlsz
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:26:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running portfolio for 600 s
% 0.14/0.35  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.14/0.35  % Number of cores: 8
% 0.14/0.36  % Python version: Python 3.6.8
% 0.22/0.36  % Running in FO mode
% 0.59/0.78  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.59/0.78  % Solved by: fo/fo7.sh
% 0.59/0.78  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.59/0.78  % done 365 iterations in 0.291s
% 0.59/0.78  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.59/0.78  % SZS output start Refutation
% 0.59/0.78  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.59/0.78  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.59/0.78  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.59/0.78  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.59/0.78  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.59/0.78  thf(sk_B_type, type, sk_B: $i).
% 0.59/0.78  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.59/0.78  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.59/0.78  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.59/0.78  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.59/0.78  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.59/0.78  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.59/0.78  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.59/0.78  thf(sk_C_type, type, sk_C: $i).
% 0.59/0.78  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.59/0.78  thf(sk_D_type, type, sk_D: $i).
% 0.59/0.78  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.59/0.78  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.59/0.78  thf(sk_A_type, type, sk_A: $i).
% 0.59/0.78  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.59/0.78  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.59/0.78  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.59/0.78  thf(t64_funct_2, conjecture,
% 0.59/0.78    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.78     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.59/0.78         ( m1_subset_1 @
% 0.59/0.78           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.59/0.78       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.59/0.78         ( r1_tarski @
% 0.59/0.78           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.59/0.78           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.59/0.78  thf(zf_stmt_0, negated_conjecture,
% 0.59/0.78    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.78        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.59/0.78            ( m1_subset_1 @
% 0.59/0.78              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.59/0.78          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.59/0.78            ( r1_tarski @
% 0.59/0.78              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.59/0.78              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.59/0.78    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.59/0.78  thf('0', plain,
% 0.59/0.78      (~ (r1_tarski @ 
% 0.59/0.78          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ sk_C) @ 
% 0.59/0.78          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('1', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_D @ 
% 0.59/0.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(redefinition_k7_relset_1, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.78       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.59/0.78  thf('2', plain,
% 0.59/0.78      (![X32 : $i, X33 : $i, X34 : $i, X35 : $i]:
% 0.59/0.78         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.59/0.78          | ((k7_relset_1 @ X33 @ X34 @ X32 @ X35) = (k9_relat_1 @ X32 @ X35)))),
% 0.59/0.78      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.59/0.78  thf('3', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D @ X0)
% 0.59/0.78           = (k9_relat_1 @ sk_D @ X0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['1', '2'])).
% 0.59/0.78  thf('4', plain,
% 0.59/0.78      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.59/0.78          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.59/0.78      inference('demod', [status(thm)], ['0', '3'])).
% 0.59/0.78  thf(t144_relat_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( v1_relat_1 @ B ) =>
% 0.59/0.78       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.59/0.78  thf('5', plain,
% 0.59/0.78      (![X21 : $i, X22 : $i]:
% 0.59/0.78         ((r1_tarski @ (k9_relat_1 @ X21 @ X22) @ (k2_relat_1 @ X21))
% 0.59/0.78          | ~ (v1_relat_1 @ X21))),
% 0.59/0.78      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.59/0.78  thf(t69_enumset1, axiom,
% 0.59/0.78    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.59/0.78  thf('6', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.59/0.78      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.59/0.78  thf(t70_enumset1, axiom,
% 0.59/0.78    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.59/0.78  thf('7', plain,
% 0.59/0.78      (![X5 : $i, X6 : $i]:
% 0.59/0.78         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 0.59/0.78      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.59/0.78  thf(t142_zfmisc_1, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i,D:$i]:
% 0.59/0.78     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.59/0.78       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 0.59/0.78            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 0.59/0.78            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 0.59/0.78            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 0.59/0.78            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 0.59/0.78            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 0.59/0.78  thf('8', plain,
% 0.59/0.78      (![X10 : $i, X11 : $i, X12 : $i, X14 : $i]:
% 0.59/0.78         ((r1_tarski @ X14 @ (k1_enumset1 @ X10 @ X11 @ X12))
% 0.59/0.78          | ((X14) != (k1_tarski @ X10)))),
% 0.59/0.78      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 0.59/0.78  thf('9', plain,
% 0.59/0.78      (![X10 : $i, X11 : $i, X12 : $i]:
% 0.59/0.78         (r1_tarski @ (k1_tarski @ X10) @ (k1_enumset1 @ X10 @ X11 @ X12))),
% 0.59/0.78      inference('simplify', [status(thm)], ['8'])).
% 0.59/0.78  thf('10', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         (r1_tarski @ (k1_tarski @ X1) @ (k2_tarski @ X1 @ X0))),
% 0.59/0.78      inference('sup+', [status(thm)], ['7', '9'])).
% 0.59/0.78  thf('11', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_D @ 
% 0.59/0.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(cc2_relset_1, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i]:
% 0.59/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.78       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.59/0.78  thf('12', plain,
% 0.59/0.78      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.59/0.78         ((v4_relat_1 @ X29 @ X30)
% 0.59/0.78          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.59/0.78      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.59/0.78  thf('13', plain, ((v4_relat_1 @ sk_D @ (k1_tarski @ sk_A))),
% 0.59/0.78      inference('sup-', [status(thm)], ['11', '12'])).
% 0.59/0.78  thf(d18_relat_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( v1_relat_1 @ B ) =>
% 0.59/0.78       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.59/0.78  thf('14', plain,
% 0.59/0.78      (![X19 : $i, X20 : $i]:
% 0.59/0.78         (~ (v4_relat_1 @ X19 @ X20)
% 0.59/0.78          | (r1_tarski @ (k1_relat_1 @ X19) @ X20)
% 0.59/0.78          | ~ (v1_relat_1 @ X19))),
% 0.59/0.78      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.59/0.78  thf('15', plain,
% 0.59/0.78      ((~ (v1_relat_1 @ sk_D)
% 0.59/0.78        | (r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['13', '14'])).
% 0.59/0.78  thf('16', plain,
% 0.59/0.78      ((m1_subset_1 @ sk_D @ 
% 0.59/0.78        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf(cc1_relset_1, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i]:
% 0.59/0.78     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.59/0.78       ( v1_relat_1 @ C ) ))).
% 0.59/0.78  thf('17', plain,
% 0.59/0.78      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.59/0.78         ((v1_relat_1 @ X26)
% 0.59/0.78          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.59/0.78      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.59/0.78  thf('18', plain, ((v1_relat_1 @ sk_D)),
% 0.59/0.78      inference('sup-', [status(thm)], ['16', '17'])).
% 0.59/0.78  thf('19', plain, ((r1_tarski @ (k1_relat_1 @ sk_D) @ (k1_tarski @ sk_A))),
% 0.59/0.78      inference('demod', [status(thm)], ['15', '18'])).
% 0.59/0.78  thf(t1_xboole_1, axiom,
% 0.59/0.78    (![A:$i,B:$i,C:$i]:
% 0.59/0.78     ( ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ C ) ) =>
% 0.59/0.78       ( r1_tarski @ A @ C ) ))).
% 0.59/0.78  thf('20', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.78         (~ (r1_tarski @ X0 @ X1)
% 0.59/0.78          | ~ (r1_tarski @ X1 @ X2)
% 0.59/0.78          | (r1_tarski @ X0 @ X2))),
% 0.59/0.78      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.59/0.78  thf('21', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((r1_tarski @ (k1_relat_1 @ sk_D) @ X0)
% 0.59/0.78          | ~ (r1_tarski @ (k1_tarski @ sk_A) @ X0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['19', '20'])).
% 0.59/0.78  thf('22', plain,
% 0.59/0.78      (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ sk_D) @ (k2_tarski @ sk_A @ X0))),
% 0.59/0.78      inference('sup-', [status(thm)], ['10', '21'])).
% 0.59/0.78  thf('23', plain,
% 0.59/0.78      (![X5 : $i, X6 : $i]:
% 0.59/0.78         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 0.59/0.78      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.59/0.78  thf('24', plain,
% 0.59/0.78      (![X10 : $i, X11 : $i, X12 : $i, X13 : $i]:
% 0.59/0.78         (((X13) = (k1_enumset1 @ X10 @ X11 @ X12))
% 0.59/0.78          | ((X13) = (k2_tarski @ X10 @ X12))
% 0.59/0.78          | ((X13) = (k2_tarski @ X11 @ X12))
% 0.59/0.78          | ((X13) = (k2_tarski @ X10 @ X11))
% 0.59/0.78          | ((X13) = (k1_tarski @ X12))
% 0.59/0.78          | ((X13) = (k1_tarski @ X11))
% 0.59/0.78          | ((X13) = (k1_tarski @ X10))
% 0.59/0.78          | ((X13) = (k1_xboole_0))
% 0.59/0.78          | ~ (r1_tarski @ X13 @ (k1_enumset1 @ X10 @ X11 @ X12)))),
% 0.59/0.78      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 0.59/0.78  thf('25', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.78         (~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0))
% 0.59/0.78          | ((X2) = (k1_xboole_0))
% 0.59/0.78          | ((X2) = (k1_tarski @ X1))
% 0.59/0.78          | ((X2) = (k1_tarski @ X1))
% 0.59/0.78          | ((X2) = (k1_tarski @ X0))
% 0.59/0.78          | ((X2) = (k2_tarski @ X1 @ X1))
% 0.59/0.78          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.59/0.78          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.59/0.78          | ((X2) = (k1_enumset1 @ X1 @ X1 @ X0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['23', '24'])).
% 0.59/0.78  thf('26', plain,
% 0.59/0.78      (![X5 : $i, X6 : $i]:
% 0.59/0.78         ((k1_enumset1 @ X5 @ X5 @ X6) = (k2_tarski @ X5 @ X6))),
% 0.59/0.78      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.59/0.78  thf('27', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.78         (~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0))
% 0.59/0.78          | ((X2) = (k1_xboole_0))
% 0.59/0.78          | ((X2) = (k1_tarski @ X1))
% 0.59/0.78          | ((X2) = (k1_tarski @ X1))
% 0.59/0.78          | ((X2) = (k1_tarski @ X0))
% 0.59/0.78          | ((X2) = (k2_tarski @ X1 @ X1))
% 0.59/0.78          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.59/0.78          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.59/0.78          | ((X2) = (k2_tarski @ X1 @ X0)))),
% 0.59/0.78      inference('demod', [status(thm)], ['25', '26'])).
% 0.59/0.78  thf('28', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.78         (((X2) = (k2_tarski @ X1 @ X0))
% 0.59/0.78          | ((X2) = (k2_tarski @ X1 @ X1))
% 0.59/0.78          | ((X2) = (k1_tarski @ X0))
% 0.59/0.78          | ((X2) = (k1_tarski @ X1))
% 0.59/0.78          | ((X2) = (k1_xboole_0))
% 0.59/0.78          | ~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0)))),
% 0.59/0.78      inference('simplify', [status(thm)], ['27'])).
% 0.59/0.78  thf('29', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.59/0.78          | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.59/0.78          | ((k1_relat_1 @ sk_D) = (k1_tarski @ X0))
% 0.59/0.78          | ((k1_relat_1 @ sk_D) = (k2_tarski @ sk_A @ sk_A))
% 0.59/0.78          | ((k1_relat_1 @ sk_D) = (k2_tarski @ sk_A @ X0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['22', '28'])).
% 0.59/0.78  thf('30', plain, (![X4 : $i]: ((k2_tarski @ X4 @ X4) = (k1_tarski @ X4))),
% 0.59/0.78      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.59/0.78  thf('31', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.59/0.78          | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.59/0.78          | ((k1_relat_1 @ sk_D) = (k1_tarski @ X0))
% 0.59/0.78          | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.59/0.78          | ((k1_relat_1 @ sk_D) = (k2_tarski @ sk_A @ X0)))),
% 0.59/0.78      inference('demod', [status(thm)], ['29', '30'])).
% 0.59/0.78  thf('32', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (((k1_relat_1 @ sk_D) = (k2_tarski @ sk_A @ X0))
% 0.59/0.78          | ((k1_relat_1 @ sk_D) = (k1_tarski @ X0))
% 0.59/0.78          | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.59/0.78          | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.59/0.78      inference('simplify', [status(thm)], ['31'])).
% 0.59/0.78  thf('33', plain,
% 0.59/0.78      ((((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.59/0.78        | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.59/0.78        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A))
% 0.59/0.78        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.59/0.78      inference('sup+', [status(thm)], ['6', '32'])).
% 0.59/0.78  thf('34', plain,
% 0.59/0.78      ((((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.59/0.78        | ((k1_relat_1 @ sk_D) = (k1_tarski @ sk_A)))),
% 0.59/0.78      inference('simplify', [status(thm)], ['33'])).
% 0.59/0.78  thf(t14_funct_1, axiom,
% 0.59/0.78    (![A:$i,B:$i]:
% 0.59/0.78     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.59/0.78       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.59/0.78         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.59/0.78  thf('35', plain,
% 0.59/0.78      (![X24 : $i, X25 : $i]:
% 0.59/0.78         (((k1_relat_1 @ X25) != (k1_tarski @ X24))
% 0.59/0.78          | ((k2_relat_1 @ X25) = (k1_tarski @ (k1_funct_1 @ X25 @ X24)))
% 0.59/0.78          | ~ (v1_funct_1 @ X25)
% 0.59/0.78          | ~ (v1_relat_1 @ X25))),
% 0.59/0.78      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.59/0.78  thf('36', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D))
% 0.59/0.78          | ((k1_relat_1 @ sk_D) = (k1_xboole_0))
% 0.59/0.78          | ~ (v1_relat_1 @ X0)
% 0.59/0.78          | ~ (v1_funct_1 @ X0)
% 0.59/0.78          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.59/0.78      inference('sup-', [status(thm)], ['34', '35'])).
% 0.59/0.78  thf('37', plain,
% 0.59/0.78      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.59/0.78        | ~ (v1_funct_1 @ sk_D)
% 0.59/0.78        | ~ (v1_relat_1 @ sk_D)
% 0.59/0.78        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.59/0.78      inference('eq_res', [status(thm)], ['36'])).
% 0.59/0.78  thf('38', plain, ((v1_funct_1 @ sk_D)),
% 0.59/0.78      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.59/0.78  thf('39', plain, ((v1_relat_1 @ sk_D)),
% 0.59/0.78      inference('sup-', [status(thm)], ['16', '17'])).
% 0.59/0.78  thf('40', plain,
% 0.59/0.78      ((((k2_relat_1 @ sk_D) = (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))
% 0.59/0.78        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.59/0.78      inference('demod', [status(thm)], ['37', '38', '39'])).
% 0.59/0.78  thf('41', plain,
% 0.59/0.78      (~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ 
% 0.59/0.78          (k1_tarski @ (k1_funct_1 @ sk_D @ sk_A)))),
% 0.59/0.78      inference('demod', [status(thm)], ['0', '3'])).
% 0.59/0.78  thf('42', plain,
% 0.59/0.78      ((~ (r1_tarski @ (k9_relat_1 @ sk_D @ sk_C) @ (k2_relat_1 @ sk_D))
% 0.59/0.78        | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['40', '41'])).
% 0.59/0.78  thf('43', plain,
% 0.59/0.78      ((~ (v1_relat_1 @ sk_D) | ((k1_relat_1 @ sk_D) = (k1_xboole_0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['5', '42'])).
% 0.59/0.78  thf('44', plain, ((v1_relat_1 @ sk_D)),
% 0.59/0.78      inference('sup-', [status(thm)], ['16', '17'])).
% 0.59/0.78  thf('45', plain, (((k1_relat_1 @ sk_D) = (k1_xboole_0))),
% 0.59/0.78      inference('demod', [status(thm)], ['43', '44'])).
% 0.59/0.78  thf(t64_relat_1, axiom,
% 0.59/0.78    (![A:$i]:
% 0.59/0.78     ( ( v1_relat_1 @ A ) =>
% 0.59/0.78       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.59/0.78           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.59/0.78         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.59/0.78  thf('46', plain,
% 0.59/0.78      (![X23 : $i]:
% 0.59/0.78         (((k1_relat_1 @ X23) != (k1_xboole_0))
% 0.59/0.78          | ((X23) = (k1_xboole_0))
% 0.59/0.78          | ~ (v1_relat_1 @ X23))),
% 0.59/0.78      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.59/0.78  thf('47', plain,
% 0.59/0.78      ((((k1_xboole_0) != (k1_xboole_0))
% 0.59/0.78        | ~ (v1_relat_1 @ sk_D)
% 0.59/0.78        | ((sk_D) = (k1_xboole_0)))),
% 0.59/0.78      inference('sup-', [status(thm)], ['45', '46'])).
% 0.59/0.78  thf('48', plain, ((v1_relat_1 @ sk_D)),
% 0.59/0.78      inference('sup-', [status(thm)], ['16', '17'])).
% 0.59/0.78  thf('49', plain,
% 0.59/0.78      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_D) = (k1_xboole_0)))),
% 0.59/0.78      inference('demod', [status(thm)], ['47', '48'])).
% 0.59/0.78  thf('50', plain, (((sk_D) = (k1_xboole_0))),
% 0.59/0.78      inference('simplify', [status(thm)], ['49'])).
% 0.59/0.78  thf('51', plain, (((sk_D) = (k1_xboole_0))),
% 0.59/0.78      inference('simplify', [status(thm)], ['49'])).
% 0.59/0.78  thf(t60_relat_1, axiom,
% 0.59/0.78    (( ( k2_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ) & 
% 0.59/0.78     ( ( k1_relat_1 @ k1_xboole_0 ) = ( k1_xboole_0 ) ))).
% 0.59/0.78  thf('52', plain, (((k2_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.59/0.78      inference('cnf', [status(esa)], [t60_relat_1])).
% 0.59/0.78  thf('53', plain,
% 0.59/0.78      (![X21 : $i, X22 : $i]:
% 0.59/0.78         ((r1_tarski @ (k9_relat_1 @ X21 @ X22) @ (k2_relat_1 @ X21))
% 0.59/0.78          | ~ (v1_relat_1 @ X21))),
% 0.59/0.78      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.59/0.78  thf('54', plain,
% 0.59/0.78      (![X0 : $i]:
% 0.59/0.78         ((r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)
% 0.59/0.78          | ~ (v1_relat_1 @ k1_xboole_0))),
% 0.59/0.78      inference('sup+', [status(thm)], ['52', '53'])).
% 0.59/0.78  thf(t4_subset_1, axiom,
% 0.59/0.78    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.59/0.78  thf('55', plain,
% 0.59/0.78      (![X15 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X15))),
% 0.59/0.78      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.59/0.78  thf('56', plain,
% 0.59/0.78      (![X26 : $i, X27 : $i, X28 : $i]:
% 0.59/0.78         ((v1_relat_1 @ X26)
% 0.59/0.78          | ~ (m1_subset_1 @ X26 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X27 @ X28))))),
% 0.59/0.78      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.59/0.78  thf('57', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.59/0.78      inference('sup-', [status(thm)], ['55', '56'])).
% 0.59/0.78  thf('58', plain,
% 0.59/0.78      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ k1_xboole_0)),
% 0.59/0.78      inference('demod', [status(thm)], ['54', '57'])).
% 0.59/0.78  thf('59', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.59/0.78         (~ (r1_tarski @ X0 @ X1)
% 0.59/0.78          | ~ (r1_tarski @ X1 @ X2)
% 0.59/0.78          | (r1_tarski @ X0 @ X2))),
% 0.59/0.78      inference('cnf', [status(esa)], [t1_xboole_1])).
% 0.59/0.78  thf('60', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]:
% 0.59/0.78         ((r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ X1)
% 0.59/0.78          | ~ (r1_tarski @ k1_xboole_0 @ X1))),
% 0.59/0.78      inference('sup-', [status(thm)], ['58', '59'])).
% 0.59/0.78  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.59/0.78  thf('61', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.59/0.78      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.59/0.78  thf('62', plain,
% 0.59/0.78      (![X0 : $i, X1 : $i]: (r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ X0) @ X1)),
% 0.59/0.78      inference('demod', [status(thm)], ['60', '61'])).
% 0.59/0.78  thf('63', plain, ($false),
% 0.59/0.78      inference('demod', [status(thm)], ['4', '50', '51', '62'])).
% 0.59/0.78  
% 0.59/0.78  % SZS output end Refutation
% 0.59/0.78  
% 0.59/0.78  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
