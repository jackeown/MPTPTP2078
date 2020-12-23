%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.95gQFAjSyq

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:57:05 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 197 expanded)
%              Number of leaves         :   37 (  75 expanded)
%              Depth                    :   24
%              Number of atoms          :  680 (1992 expanded)
%              Number of equality atoms :   57 ( 107 expanded)
%              Maximal formula depth    :   15 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

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
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k7_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k7_relset_1 @ A @ B @ C @ D )
        = ( k9_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X36: $i,X37: $i,X38: $i,X39: $i] :
      ( ~ ( m1_subset_1 @ X36 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X37 @ X38 ) ) )
      | ( ( k7_relset_1 @ X37 @ X38 @ X36 @ X39 )
        = ( k9_relat_1 @ X36 @ X39 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t147_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ) )).

thf('5',plain,(
    ! [X27: $i,X28: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X27 @ X28 ) @ ( k9_relat_1 @ X27 @ ( k1_relat_1 @ X27 ) ) )
      | ~ ( v1_relat_1 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t147_relat_1])).

thf('6',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( v4_relat_1 @ C @ A )
        & ( v5_relat_1 @ C @ B ) ) ) )).

thf('7',plain,(
    ! [X33: $i,X34: $i,X35: $i] :
      ( ( v4_relat_1 @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X34 @ X35 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('8',plain,(
    v4_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('9',plain,(
    ! [X21: $i,X22: $i] :
      ( ~ ( v4_relat_1 @ X21 @ X22 )
      | ( r1_tarski @ ( k1_relat_1 @ X21 ) @ X22 )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc2_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) )
         => ( v1_relat_1 @ B ) ) ) )).

thf('12',plain,(
    ! [X19: $i,X20: $i] :
      ( ~ ( m1_subset_1 @ X19 @ ( k1_zfmisc_1 @ X20 ) )
      | ( v1_relat_1 @ X19 )
      | ~ ( v1_relat_1 @ X20 ) ) ),
    inference(cnf,[status(esa)],[cc2_relat_1])).

thf('13',plain,
    ( ~ ( v1_relat_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B ) )
    | ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf(fc6_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ) )).

thf('14',plain,(
    ! [X23: $i,X24: $i] :
      ( v1_relat_1 @ ( k2_zfmisc_1 @ X23 @ X24 ) ) ),
    inference(cnf,[status(esa)],[fc6_relat_1])).

thf('15',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('16',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['10','15'])).

thf(l3_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( r1_tarski @ A @ ( k1_tarski @ B ) )
    <=> ( ( A = k1_xboole_0 )
        | ( A
          = ( k1_tarski @ B ) ) ) ) )).

thf('17',plain,(
    ! [X16: $i,X17: $i] :
      ( ( X17
        = ( k1_tarski @ X16 ) )
      | ( X17 = k1_xboole_0 )
      | ~ ( r1_tarski @ X17 @ ( k1_tarski @ X16 ) ) ) ),
    inference(cnf,[status(esa)],[l3_zfmisc_1])).

thf('18',plain,
    ( ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,
    ( ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['16','17'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('20',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(d2_tarski,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( C
        = ( k2_tarski @ A @ B ) )
    <=> ! [D: $i] :
          ( ( r2_hidden @ D @ C )
        <=> ( ( D = A )
            | ( D = B ) ) ) ) )).

thf('21',plain,(
    ! [X4: $i,X5: $i,X6: $i,X7: $i] :
      ( ( X5 != X4 )
      | ( r2_hidden @ X5 @ X6 )
      | ( X6
       != ( k2_tarski @ X7 @ X4 ) ) ) ),
    inference(cnf,[status(esa)],[d2_tarski])).

thf('22',plain,(
    ! [X4: $i,X7: $i] :
      ( r2_hidden @ X4 @ ( k2_tarski @ X7 @ X4 ) ) ),
    inference(simplify,[status(thm)],['21'])).

thf('23',plain,(
    ! [X0: $i] :
      ( r2_hidden @ X0 @ ( k1_tarski @ X0 ) ) ),
    inference('sup+',[status(thm)],['20','22'])).

thf('24',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_1 ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','23'])).

thf('25',plain,
    ( ( r2_hidden @ sk_A @ ( k1_relat_1 @ sk_D_1 ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['19','23'])).

thf(t118_funct_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_relat_1 @ C )
        & ( v1_funct_1 @ C ) )
     => ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) )
          & ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) )
       => ( ( k9_relat_1 @ C @ ( k2_tarski @ A @ B ) )
          = ( k2_tarski @ ( k1_funct_1 @ C @ A ) @ ( k1_funct_1 @ C @ B ) ) ) ) ) )).

thf('26',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X30 @ ( k1_relat_1 @ X31 ) )
      | ~ ( r2_hidden @ X32 @ ( k1_relat_1 @ X31 ) )
      | ( ( k9_relat_1 @ X31 @ ( k2_tarski @ X30 @ X32 ) )
        = ( k2_tarski @ ( k1_funct_1 @ X31 @ X30 ) @ ( k1_funct_1 @ X31 @ X32 ) ) )
      | ~ ( v1_funct_1 @ X31 )
      | ~ ( v1_relat_1 @ X31 ) ) ),
    inference(cnf,[status(esa)],[t118_funct_1])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D_1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D_1 )
      | ~ ( v1_funct_1 @ sk_D_1 )
      | ( ( k9_relat_1 @ sk_D_1 @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) @ ( k1_funct_1 @ sk_D_1 @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('29',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ sk_D_1 )
        = k1_xboole_0 )
      | ( ( k9_relat_1 @ sk_D_1 @ ( k2_tarski @ sk_A @ X0 ) )
        = ( k2_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) @ ( k1_funct_1 @ sk_D_1 @ X0 ) ) )
      | ~ ( r2_hidden @ X0 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference(demod,[status(thm)],['27','28','29'])).

thf('31',plain,
    ( ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( k9_relat_1 @ sk_D_1 @ ( k2_tarski @ sk_A @ sk_A ) )
      = ( k2_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['24','30'])).

thf('32',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('33',plain,(
    ! [X10: $i] :
      ( ( k2_tarski @ X10 @ X10 )
      = ( k1_tarski @ X10 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('34',plain,
    ( ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( k9_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['31','32','33'])).

thf('35',plain,
    ( ( ( k9_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('37',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k9_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['35','36'])).

thf('38',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k9_relat_1 @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['18','37'])).

thf('39',plain,
    ( ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 )
    | ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k9_relat_1 @ sk_D_1 @ ( k1_relat_1 @ sk_D_1 ) ) ) ),
    inference(simplify,[status(thm)],['38'])).

thf('40',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('42',plain,
    ( ( k1_relat_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['40','41'])).

thf(t65_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( k1_relat_1 @ A )
          = k1_xboole_0 )
      <=> ( ( k2_relat_1 @ A )
          = k1_xboole_0 ) ) ) )).

thf('43',plain,(
    ! [X29: $i] :
      ( ( ( k1_relat_1 @ X29 )
       != k1_xboole_0 )
      | ( ( k2_relat_1 @ X29 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t65_relat_1])).

thf('44',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ( ( k2_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['42','43'])).

thf('45',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('46',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( ( k2_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['44','45'])).

thf('47',plain,
    ( ( k2_relat_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference(simplify,[status(thm)],['46'])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('48',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X25 @ X26 ) @ ( k2_relat_1 @ X25 ) )
      | ~ ( v1_relat_1 @ X25 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('49',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ X0 ) @ k1_xboole_0 )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup+',[status(thm)],['47','48'])).

thf('50',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['13','14'])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ X0 ) @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','50'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('52',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('53',plain,(
    ! [X0: $i,X2: $i] :
      ( ( X0 = X2 )
      | ~ ( r1_tarski @ X2 @ X0 )
      | ~ ( r1_tarski @ X0 @ X2 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('54',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ sk_D_1 @ X0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['51','54'])).

thf('56',plain,(
    ! [X3: $i] :
      ( r1_tarski @ k1_xboole_0 @ X3 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('57',plain,(
    $false ),
    inference(demod,[status(thm)],['4','55','56'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.95gQFAjSyq
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:33:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.34  % Running in FO mode
% 0.19/0.50  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.19/0.50  % Solved by: fo/fo7.sh
% 0.19/0.50  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.19/0.50  % done 124 iterations in 0.052s
% 0.19/0.50  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.19/0.50  % SZS output start Refutation
% 0.19/0.50  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.19/0.50  thf(sk_B_type, type, sk_B: $i).
% 0.19/0.50  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.19/0.50  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.19/0.50  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.19/0.50  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.19/0.50  thf(sk_A_type, type, sk_A: $i).
% 0.19/0.50  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.19/0.50  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.19/0.50  thf(sk_C_type, type, sk_C: $i).
% 0.19/0.50  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.19/0.50  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.19/0.50  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.19/0.50  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.19/0.50  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.19/0.50  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.19/0.50  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.19/0.50  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.19/0.50  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.19/0.50  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.19/0.50  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.19/0.50  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.19/0.50  thf(t64_funct_2, conjecture,
% 0.19/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.50     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.19/0.50         ( m1_subset_1 @
% 0.19/0.50           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.19/0.50       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.19/0.50         ( r1_tarski @
% 0.19/0.50           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.19/0.50           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.19/0.50  thf(zf_stmt_0, negated_conjecture,
% 0.19/0.50    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.50        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.19/0.50            ( m1_subset_1 @
% 0.19/0.50              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.19/0.50          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.19/0.50            ( r1_tarski @
% 0.19/0.50              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.19/0.50              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.19/0.50    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.19/0.50  thf('0', plain,
% 0.19/0.50      (~ (r1_tarski @ 
% 0.19/0.50          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ sk_C) @ 
% 0.19/0.50          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('1', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_D_1 @ 
% 0.19/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(redefinition_k7_relset_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i,D:$i]:
% 0.19/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.50       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.19/0.50  thf('2', plain,
% 0.19/0.50      (![X36 : $i, X37 : $i, X38 : $i, X39 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X36 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X37 @ X38)))
% 0.19/0.50          | ((k7_relset_1 @ X37 @ X38 @ X36 @ X39) = (k9_relat_1 @ X36 @ X39)))),
% 0.19/0.50      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.19/0.50  thf('3', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B @ sk_D_1 @ X0)
% 0.19/0.50           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['1', '2'])).
% 0.19/0.50  thf('4', plain,
% 0.19/0.50      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ 
% 0.19/0.50          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.19/0.50      inference('demod', [status(thm)], ['0', '3'])).
% 0.19/0.50  thf(t147_relat_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ B ) =>
% 0.19/0.50       ( r1_tarski @
% 0.19/0.50         ( k9_relat_1 @ B @ A ) @ ( k9_relat_1 @ B @ ( k1_relat_1 @ B ) ) ) ))).
% 0.19/0.50  thf('5', plain,
% 0.19/0.50      (![X27 : $i, X28 : $i]:
% 0.19/0.50         ((r1_tarski @ (k9_relat_1 @ X27 @ X28) @ 
% 0.19/0.50           (k9_relat_1 @ X27 @ (k1_relat_1 @ X27)))
% 0.19/0.50          | ~ (v1_relat_1 @ X27))),
% 0.19/0.50      inference('cnf', [status(esa)], [t147_relat_1])).
% 0.19/0.50  thf('6', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_D_1 @ 
% 0.19/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(cc2_relset_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.19/0.50       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.19/0.50  thf('7', plain,
% 0.19/0.50      (![X33 : $i, X34 : $i, X35 : $i]:
% 0.19/0.50         ((v4_relat_1 @ X33 @ X34)
% 0.19/0.50          | ~ (m1_subset_1 @ X33 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X34 @ X35))))),
% 0.19/0.50      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.19/0.50  thf('8', plain, ((v4_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A))),
% 0.19/0.50      inference('sup-', [status(thm)], ['6', '7'])).
% 0.19/0.50  thf(d18_relat_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ B ) =>
% 0.19/0.50       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.19/0.50  thf('9', plain,
% 0.19/0.50      (![X21 : $i, X22 : $i]:
% 0.19/0.50         (~ (v4_relat_1 @ X21 @ X22)
% 0.19/0.50          | (r1_tarski @ (k1_relat_1 @ X21) @ X22)
% 0.19/0.50          | ~ (v1_relat_1 @ X21))),
% 0.19/0.50      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.19/0.50  thf('10', plain,
% 0.19/0.50      ((~ (v1_relat_1 @ sk_D_1)
% 0.19/0.50        | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ (k1_tarski @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['8', '9'])).
% 0.19/0.50  thf('11', plain,
% 0.19/0.50      ((m1_subset_1 @ sk_D_1 @ 
% 0.19/0.50        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B)))),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf(cc2_relat_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ A ) =>
% 0.19/0.50       ( ![B:$i]:
% 0.19/0.50         ( ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ A ) ) => ( v1_relat_1 @ B ) ) ) ))).
% 0.19/0.50  thf('12', plain,
% 0.19/0.50      (![X19 : $i, X20 : $i]:
% 0.19/0.50         (~ (m1_subset_1 @ X19 @ (k1_zfmisc_1 @ X20))
% 0.19/0.50          | (v1_relat_1 @ X19)
% 0.19/0.50          | ~ (v1_relat_1 @ X20))),
% 0.19/0.50      inference('cnf', [status(esa)], [cc2_relat_1])).
% 0.19/0.50  thf('13', plain,
% 0.19/0.50      ((~ (v1_relat_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B))
% 0.19/0.50        | (v1_relat_1 @ sk_D_1))),
% 0.19/0.50      inference('sup-', [status(thm)], ['11', '12'])).
% 0.19/0.50  thf(fc6_relat_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]: ( v1_relat_1 @ ( k2_zfmisc_1 @ A @ B ) ))).
% 0.19/0.50  thf('14', plain,
% 0.19/0.50      (![X23 : $i, X24 : $i]: (v1_relat_1 @ (k2_zfmisc_1 @ X23 @ X24))),
% 0.19/0.50      inference('cnf', [status(esa)], [fc6_relat_1])).
% 0.19/0.50  thf('15', plain, ((v1_relat_1 @ sk_D_1)),
% 0.19/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.50  thf('16', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ (k1_tarski @ sk_A))),
% 0.19/0.50      inference('demod', [status(thm)], ['10', '15'])).
% 0.19/0.50  thf(l3_zfmisc_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( r1_tarski @ A @ ( k1_tarski @ B ) ) <=>
% 0.19/0.50       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( A ) = ( k1_tarski @ B ) ) ) ))).
% 0.19/0.50  thf('17', plain,
% 0.19/0.50      (![X16 : $i, X17 : $i]:
% 0.19/0.50         (((X17) = (k1_tarski @ X16))
% 0.19/0.50          | ((X17) = (k1_xboole_0))
% 0.19/0.50          | ~ (r1_tarski @ X17 @ (k1_tarski @ X16)))),
% 0.19/0.50      inference('cnf', [status(esa)], [l3_zfmisc_1])).
% 0.19/0.50  thf('18', plain,
% 0.19/0.50      ((((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.19/0.50        | ((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.50  thf('19', plain,
% 0.19/0.50      ((((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.19/0.50        | ((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['16', '17'])).
% 0.19/0.50  thf(t69_enumset1, axiom,
% 0.19/0.50    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.19/0.50  thf('20', plain,
% 0.19/0.50      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 0.19/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.50  thf(d2_tarski, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( ( C ) = ( k2_tarski @ A @ B ) ) <=>
% 0.19/0.50       ( ![D:$i]:
% 0.19/0.50         ( ( r2_hidden @ D @ C ) <=> ( ( ( D ) = ( A ) ) | ( ( D ) = ( B ) ) ) ) ) ))).
% 0.19/0.50  thf('21', plain,
% 0.19/0.50      (![X4 : $i, X5 : $i, X6 : $i, X7 : $i]:
% 0.19/0.50         (((X5) != (X4))
% 0.19/0.50          | (r2_hidden @ X5 @ X6)
% 0.19/0.50          | ((X6) != (k2_tarski @ X7 @ X4)))),
% 0.19/0.50      inference('cnf', [status(esa)], [d2_tarski])).
% 0.19/0.50  thf('22', plain,
% 0.19/0.50      (![X4 : $i, X7 : $i]: (r2_hidden @ X4 @ (k2_tarski @ X7 @ X4))),
% 0.19/0.50      inference('simplify', [status(thm)], ['21'])).
% 0.19/0.50  thf('23', plain, (![X0 : $i]: (r2_hidden @ X0 @ (k1_tarski @ X0))),
% 0.19/0.50      inference('sup+', [status(thm)], ['20', '22'])).
% 0.19/0.50  thf('24', plain,
% 0.19/0.50      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_1))
% 0.19/0.50        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['19', '23'])).
% 0.19/0.50  thf('25', plain,
% 0.19/0.50      (((r2_hidden @ sk_A @ (k1_relat_1 @ sk_D_1))
% 0.19/0.50        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup+', [status(thm)], ['19', '23'])).
% 0.19/0.50  thf(t118_funct_1, axiom,
% 0.19/0.50    (![A:$i,B:$i,C:$i]:
% 0.19/0.50     ( ( ( v1_relat_1 @ C ) & ( v1_funct_1 @ C ) ) =>
% 0.19/0.50       ( ( ( r2_hidden @ A @ ( k1_relat_1 @ C ) ) & 
% 0.19/0.50           ( r2_hidden @ B @ ( k1_relat_1 @ C ) ) ) =>
% 0.19/0.50         ( ( k9_relat_1 @ C @ ( k2_tarski @ A @ B ) ) =
% 0.19/0.50           ( k2_tarski @ ( k1_funct_1 @ C @ A ) @ ( k1_funct_1 @ C @ B ) ) ) ) ))).
% 0.19/0.50  thf('26', plain,
% 0.19/0.50      (![X30 : $i, X31 : $i, X32 : $i]:
% 0.19/0.50         (~ (r2_hidden @ X30 @ (k1_relat_1 @ X31))
% 0.19/0.50          | ~ (r2_hidden @ X32 @ (k1_relat_1 @ X31))
% 0.19/0.50          | ((k9_relat_1 @ X31 @ (k2_tarski @ X30 @ X32))
% 0.19/0.50              = (k2_tarski @ (k1_funct_1 @ X31 @ X30) @ 
% 0.19/0.50                 (k1_funct_1 @ X31 @ X32)))
% 0.19/0.50          | ~ (v1_funct_1 @ X31)
% 0.19/0.50          | ~ (v1_relat_1 @ X31))),
% 0.19/0.50      inference('cnf', [status(esa)], [t118_funct_1])).
% 0.19/0.50  thf('27', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.19/0.50          | ~ (v1_relat_1 @ sk_D_1)
% 0.19/0.50          | ~ (v1_funct_1 @ sk_D_1)
% 0.19/0.50          | ((k9_relat_1 @ sk_D_1 @ (k2_tarski @ sk_A @ X0))
% 0.19/0.50              = (k2_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A) @ 
% 0.19/0.50                 (k1_funct_1 @ sk_D_1 @ X0)))
% 0.19/0.50          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['25', '26'])).
% 0.19/0.50  thf('28', plain, ((v1_relat_1 @ sk_D_1)),
% 0.19/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.50  thf('29', plain, ((v1_funct_1 @ sk_D_1)),
% 0.19/0.50      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.19/0.50  thf('30', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         (((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.19/0.50          | ((k9_relat_1 @ sk_D_1 @ (k2_tarski @ sk_A @ X0))
% 0.19/0.50              = (k2_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A) @ 
% 0.19/0.50                 (k1_funct_1 @ sk_D_1 @ X0)))
% 0.19/0.50          | ~ (r2_hidden @ X0 @ (k1_relat_1 @ sk_D_1)))),
% 0.19/0.50      inference('demod', [status(thm)], ['27', '28', '29'])).
% 0.19/0.50  thf('31', plain,
% 0.19/0.50      ((((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.19/0.50        | ((k9_relat_1 @ sk_D_1 @ (k2_tarski @ sk_A @ sk_A))
% 0.19/0.50            = (k2_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A) @ 
% 0.19/0.50               (k1_funct_1 @ sk_D_1 @ sk_A)))
% 0.19/0.50        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['24', '30'])).
% 0.19/0.50  thf('32', plain,
% 0.19/0.50      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 0.19/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.50  thf('33', plain,
% 0.19/0.50      (![X10 : $i]: ((k2_tarski @ X10 @ X10) = (k1_tarski @ X10))),
% 0.19/0.50      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.19/0.50  thf('34', plain,
% 0.19/0.50      ((((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.19/0.50        | ((k9_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A))
% 0.19/0.50            = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))
% 0.19/0.50        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.19/0.50      inference('demod', [status(thm)], ['31', '32', '33'])).
% 0.19/0.50  thf('35', plain,
% 0.19/0.50      ((((k9_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A))
% 0.19/0.50          = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))
% 0.19/0.50        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.19/0.50      inference('simplify', [status(thm)], ['34'])).
% 0.19/0.50  thf('36', plain,
% 0.19/0.50      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ 
% 0.19/0.50          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.19/0.50      inference('demod', [status(thm)], ['0', '3'])).
% 0.19/0.50  thf('37', plain,
% 0.19/0.50      ((~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ 
% 0.19/0.50           (k9_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A)))
% 0.19/0.50        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['35', '36'])).
% 0.19/0.50  thf('38', plain,
% 0.19/0.50      ((~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ 
% 0.19/0.50           (k9_relat_1 @ sk_D_1 @ (k1_relat_1 @ sk_D_1)))
% 0.19/0.50        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.19/0.50        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['18', '37'])).
% 0.19/0.50  thf('39', plain,
% 0.19/0.50      ((((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.19/0.50        | ~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ 
% 0.19/0.50             (k9_relat_1 @ sk_D_1 @ (k1_relat_1 @ sk_D_1))))),
% 0.19/0.50      inference('simplify', [status(thm)], ['38'])).
% 0.19/0.50  thf('40', plain,
% 0.19/0.50      ((~ (v1_relat_1 @ sk_D_1) | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['5', '39'])).
% 0.19/0.50  thf('41', plain, ((v1_relat_1 @ sk_D_1)),
% 0.19/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.50  thf('42', plain, (((k1_relat_1 @ sk_D_1) = (k1_xboole_0))),
% 0.19/0.50      inference('demod', [status(thm)], ['40', '41'])).
% 0.19/0.50  thf(t65_relat_1, axiom,
% 0.19/0.50    (![A:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ A ) =>
% 0.19/0.50       ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) <=>
% 0.19/0.50         ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) ))).
% 0.19/0.50  thf('43', plain,
% 0.19/0.50      (![X29 : $i]:
% 0.19/0.50         (((k1_relat_1 @ X29) != (k1_xboole_0))
% 0.19/0.50          | ((k2_relat_1 @ X29) = (k1_xboole_0))
% 0.19/0.50          | ~ (v1_relat_1 @ X29))),
% 0.19/0.50      inference('cnf', [status(esa)], [t65_relat_1])).
% 0.19/0.50  thf('44', plain,
% 0.19/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.50        | ~ (v1_relat_1 @ sk_D_1)
% 0.19/0.50        | ((k2_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['42', '43'])).
% 0.19/0.50  thf('45', plain, ((v1_relat_1 @ sk_D_1)),
% 0.19/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.50  thf('46', plain,
% 0.19/0.50      ((((k1_xboole_0) != (k1_xboole_0))
% 0.19/0.50        | ((k2_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.19/0.50      inference('demod', [status(thm)], ['44', '45'])).
% 0.19/0.50  thf('47', plain, (((k2_relat_1 @ sk_D_1) = (k1_xboole_0))),
% 0.19/0.50      inference('simplify', [status(thm)], ['46'])).
% 0.19/0.50  thf(t144_relat_1, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( v1_relat_1 @ B ) =>
% 0.19/0.50       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.19/0.50  thf('48', plain,
% 0.19/0.50      (![X25 : $i, X26 : $i]:
% 0.19/0.50         ((r1_tarski @ (k9_relat_1 @ X25 @ X26) @ (k2_relat_1 @ X25))
% 0.19/0.50          | ~ (v1_relat_1 @ X25))),
% 0.19/0.50      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.19/0.50  thf('49', plain,
% 0.19/0.50      (![X0 : $i]:
% 0.19/0.50         ((r1_tarski @ (k9_relat_1 @ sk_D_1 @ X0) @ k1_xboole_0)
% 0.19/0.50          | ~ (v1_relat_1 @ sk_D_1))),
% 0.19/0.50      inference('sup+', [status(thm)], ['47', '48'])).
% 0.19/0.50  thf('50', plain, ((v1_relat_1 @ sk_D_1)),
% 0.19/0.50      inference('demod', [status(thm)], ['13', '14'])).
% 0.19/0.50  thf('51', plain,
% 0.19/0.50      (![X0 : $i]: (r1_tarski @ (k9_relat_1 @ sk_D_1 @ X0) @ k1_xboole_0)),
% 0.19/0.50      inference('demod', [status(thm)], ['49', '50'])).
% 0.19/0.50  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.19/0.50  thf('52', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.19/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.50  thf(d10_xboole_0, axiom,
% 0.19/0.50    (![A:$i,B:$i]:
% 0.19/0.50     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.19/0.50  thf('53', plain,
% 0.19/0.50      (![X0 : $i, X2 : $i]:
% 0.19/0.50         (((X0) = (X2)) | ~ (r1_tarski @ X2 @ X0) | ~ (r1_tarski @ X0 @ X2))),
% 0.19/0.50      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.19/0.50  thf('54', plain,
% 0.19/0.50      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.19/0.50      inference('sup-', [status(thm)], ['52', '53'])).
% 0.19/0.50  thf('55', plain, (![X0 : $i]: ((k9_relat_1 @ sk_D_1 @ X0) = (k1_xboole_0))),
% 0.19/0.50      inference('sup-', [status(thm)], ['51', '54'])).
% 0.19/0.50  thf('56', plain, (![X3 : $i]: (r1_tarski @ k1_xboole_0 @ X3)),
% 0.19/0.50      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.19/0.50  thf('57', plain, ($false),
% 0.19/0.50      inference('demod', [status(thm)], ['4', '55', '56'])).
% 0.19/0.50  
% 0.19/0.50  % SZS output end Refutation
% 0.19/0.50  
% 0.19/0.51  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
