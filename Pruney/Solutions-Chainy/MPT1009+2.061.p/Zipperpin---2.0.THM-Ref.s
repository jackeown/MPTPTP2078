%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.T6O6sfdYda

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:56:57 EST 2020

% Result     : Theorem 0.49s
% Output     : Refutation 0.49s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 250 expanded)
%              Number of leaves         :   43 (  94 expanded)
%              Depth                    :   20
%              Number of atoms          :  971 (2912 expanded)
%              Number of equality atoms :  101 ( 232 expanded)
%              Maximal formula depth    :   19 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(k1_enumset1_type,type,(
    k1_enumset1: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k2_tarski_type,type,(
    k2_tarski: $i > $i > $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(v5_relat_1_type,type,(
    v5_relat_1: $i > $i > $o )).

thf(k9_relat_1_type,type,(
    k9_relat_1: $i > $i > $i )).

thf(k2_relat_1_type,type,(
    k2_relat_1: $i > $i )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k7_relset_1_type,type,(
    k7_relset_1: $i > $i > $i > $i > $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(v4_relat_1_type,type,(
    v4_relat_1: $i > $i > $o )).

thf(k1_funct_1_type,type,(
    k1_funct_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k4_mcart_1_type,type,(
    k4_mcart_1: $i > $i > $i > $i > $i )).

thf(k1_relat_1_type,type,(
    k1_relat_1: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_tarski_type,type,(
    k1_tarski: $i > $i )).

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
    ~ ( r1_tarski @ ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
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
      ( ( k7_relset_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 @ sk_D_1 @ X0 )
      = ( k9_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(t144_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ) )).

thf('5',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r1_tarski @ ( k9_relat_1 @ X22 @ X23 ) @ ( k2_relat_1 @ X22 ) )
      | ~ ( v1_relat_1 @ X22 ) ) ),
    inference(cnf,[status(esa)],[t144_relat_1])).

thf('6',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
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
    v4_relat_1 @ sk_D_1 @ ( k1_tarski @ sk_A ) ),
    inference('sup-',[status(thm)],['6','7'])).

thf(d18_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ( ( v4_relat_1 @ B @ A )
      <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ) )).

thf('9',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('10',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_tarski @ sk_A ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ sk_A ) @ sk_B_1 ) ) ),
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
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    r1_tarski @ ( k1_relat_1 @ sk_D_1 ) @ ( k1_tarski @ sk_A ) ),
    inference(demod,[status(thm)],['10','13'])).

thf(t69_enumset1,axiom,(
    ! [A: $i] :
      ( ( k2_tarski @ A @ A )
      = ( k1_tarski @ A ) ) )).

thf('15',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf(t70_enumset1,axiom,(
    ! [A: $i,B: $i] :
      ( ( k1_enumset1 @ A @ A @ B )
      = ( k2_tarski @ A @ B ) ) )).

thf('16',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_enumset1 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
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

thf('17',plain,(
    ! [X7: $i,X8: $i,X9: $i,X10: $i] :
      ( ( X10
        = ( k1_enumset1 @ X7 @ X8 @ X9 ) )
      | ( X10
        = ( k2_tarski @ X7 @ X9 ) )
      | ( X10
        = ( k2_tarski @ X8 @ X9 ) )
      | ( X10
        = ( k2_tarski @ X7 @ X8 ) )
      | ( X10
        = ( k1_tarski @ X9 ) )
      | ( X10
        = ( k1_tarski @ X8 ) )
      | ( X10
        = ( k1_tarski @ X7 ) )
      | ( X10 = k1_xboole_0 )
      | ~ ( r1_tarski @ X10 @ ( k1_enumset1 @ X7 @ X8 @ X9 ) ) ) ),
    inference(cnf,[status(esa)],[t142_zfmisc_1])).

thf('18',plain,(
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
    inference('sup-',[status(thm)],['16','17'])).

thf('19',plain,(
    ! [X2: $i,X3: $i] :
      ( ( k1_enumset1 @ X2 @ X2 @ X3 )
      = ( k2_tarski @ X2 @ X3 ) ) ),
    inference(cnf,[status(esa)],[t70_enumset1])).

thf('20',plain,(
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
    inference(demod,[status(thm)],['18','19'])).

thf('21',plain,(
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
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k2_tarski @ X0 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['15','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1
        = ( k2_tarski @ X0 @ X0 ) )
      | ( X1
        = ( k1_tarski @ X0 ) )
      | ( X1 = k1_xboole_0 )
      | ~ ( r1_tarski @ X1 @ ( k1_tarski @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,
    ( ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = ( k2_tarski @ sk_A @ sk_A ) ) ),
    inference('sup-',[status(thm)],['14','23'])).

thf('25',plain,(
    ! [X1: $i] :
      ( ( k2_tarski @ X1 @ X1 )
      = ( k1_tarski @ X1 ) ) ),
    inference(cnf,[status(esa)],[t69_enumset1])).

thf('26',plain,
    ( ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = ( k1_tarski @ sk_A ) ) ),
    inference(demod,[status(thm)],['24','25'])).

thf('27',plain,
    ( ( ( k1_relat_1 @ sk_D_1 )
      = ( k1_tarski @ sk_A ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['26'])).

thf(t14_funct_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( v1_relat_1 @ B )
        & ( v1_funct_1 @ B ) )
     => ( ( ( k1_relat_1 @ B )
          = ( k1_tarski @ A ) )
       => ( ( k2_relat_1 @ B )
          = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ) )).

thf('28',plain,(
    ! [X25: $i,X26: $i] :
      ( ( ( k1_relat_1 @ X26 )
       != ( k1_tarski @ X25 ) )
      | ( ( k2_relat_1 @ X26 )
        = ( k1_tarski @ ( k1_funct_1 @ X26 @ X25 ) ) )
      | ~ ( v1_funct_1 @ X26 )
      | ~ ( v1_relat_1 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t14_funct_1])).

thf('29',plain,(
    ! [X0: $i] :
      ( ( ( k1_relat_1 @ X0 )
       != ( k1_relat_1 @ sk_D_1 ) )
      | ( ( k1_relat_1 @ sk_D_1 )
        = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X0 )
      | ~ ( v1_funct_1 @ X0 )
      | ( ( k2_relat_1 @ X0 )
        = ( k1_tarski @ ( k1_funct_1 @ X0 @ sk_A ) ) ) ) ),
    inference('sup-',[status(thm)],['27','28'])).

thf('30',plain,
    ( ( ( k2_relat_1 @ sk_D_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) )
    | ~ ( v1_funct_1 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference(eq_res,[status(thm)],['29'])).

thf('31',plain,(
    v1_funct_1 @ sk_D_1 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('33',plain,
    ( ( ( k2_relat_1 @ sk_D_1 )
      = ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['30','31','32'])).

thf('34',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ sk_D_1 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('35',plain,
    ( ~ ( r1_tarski @ ( k9_relat_1 @ sk_D_1 @ sk_C ) @ ( k2_relat_1 @ sk_D_1 ) )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,
    ( ~ ( v1_relat_1 @ sk_D_1 )
    | ( ( k1_relat_1 @ sk_D_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['5','35'])).

thf('37',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('38',plain,
    ( ( k1_relat_1 @ sk_D_1 )
    = k1_xboole_0 ),
    inference(demod,[status(thm)],['36','37'])).

thf(t64_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ( ( ( ( k1_relat_1 @ A )
            = k1_xboole_0 )
          | ( ( k2_relat_1 @ A )
            = k1_xboole_0 ) )
       => ( A = k1_xboole_0 ) ) ) )).

thf('39',plain,(
    ! [X24: $i] :
      ( ( ( k1_relat_1 @ X24 )
       != k1_xboole_0 )
      | ( X24 = k1_xboole_0 )
      | ~ ( v1_relat_1 @ X24 ) ) ),
    inference(cnf,[status(esa)],[t64_relat_1])).

thf('40',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['38','39'])).

thf('41',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['11','12'])).

thf('42',plain,
    ( ( k1_xboole_0 != k1_xboole_0 )
    | ( sk_D_1 = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['40','41'])).

thf('43',plain,(
    sk_D_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    sk_D_1 = k1_xboole_0 ),
    inference(simplify,[status(thm)],['42'])).

thf('45',plain,(
    ~ ( r1_tarski @ ( k9_relat_1 @ k1_xboole_0 @ sk_C ) @ ( k1_tarski @ ( k1_funct_1 @ k1_xboole_0 @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['4','43','44'])).

thf(t34_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i,E: $i,F: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) )).

thf('46',plain,(
    ! [X39: $i] :
      ( ( X39 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X39 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('47',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('48',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( ( k7_relset_1 @ X36 @ X37 @ X35 @ X38 )
        = ( k9_relat_1 @ X35 @ X38 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k7_relset_1])).

thf('49',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k9_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2 )
      = ( k9_relat_1 @ k1_xboole_0 @ X2 ) ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf(t143_relat_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( v1_relat_1 @ C )
     => ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) )
      <=> ? [D: $i] :
            ( ( r2_hidden @ D @ B )
            & ( r2_hidden @ ( k4_tarski @ D @ A ) @ C )
            & ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) )).

thf('51',plain,(
    ! [X19: $i,X20: $i,X21: $i] :
      ( ~ ( r2_hidden @ X20 @ ( k9_relat_1 @ X21 @ X19 ) )
      | ( r2_hidden @ ( sk_D @ X21 @ X19 @ X20 ) @ ( k1_relat_1 @ X21 ) )
      | ~ ( v1_relat_1 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t143_relat_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k7_relset_1 @ X2 @ X1 @ k1_xboole_0 @ X0 ) )
      | ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X3 ) @ ( k1_relat_1 @ k1_xboole_0 ) ) ) ),
    inference('sup-',[status(thm)],['50','51'])).

thf('53',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('54',plain,(
    ! [X29: $i,X30: $i,X31: $i] :
      ( ( v1_relat_1 @ X29 )
      | ~ ( m1_subset_1 @ X29 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X30 @ X31 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('55',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X12: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X12 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('57',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ( v4_relat_1 @ X32 @ X33 )
      | ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc2_relset_1])).

thf('58',plain,(
    ! [X1: $i] :
      ( v4_relat_1 @ k1_xboole_0 @ X1 ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X16: $i,X17: $i] :
      ( ~ ( v4_relat_1 @ X16 @ X17 )
      | ( r1_tarski @ ( k1_relat_1 @ X16 ) @ X17 )
      | ~ ( v1_relat_1 @ X16 ) ) ),
    inference(cnf,[status(esa)],[d18_relat_1])).

thf('60',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ k1_xboole_0 )
      | ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    v1_relat_1 @ k1_xboole_0 ),
    inference('sup-',[status(thm)],['53','54'])).

thf('62',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k1_relat_1 @ k1_xboole_0 ) @ X0 ) ),
    inference(demod,[status(thm)],['60','61'])).

thf('63',plain,(
    ! [X39: $i] :
      ( ( X39 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B @ X39 ) @ X39 ) ) ),
    inference(cnf,[status(esa)],[t34_mcart_1])).

thf(t7_ordinal1,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( r1_tarski @ B @ A ) ) )).

thf('64',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( r1_tarski @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('65',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( r1_tarski @ X0 @ ( sk_B @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,
    ( ( k1_relat_1 @ k1_xboole_0 )
    = k1_xboole_0 ),
    inference('sup-',[status(thm)],['62','65'])).

thf('67',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k7_relset_1 @ X2 @ X1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X3 ) @ k1_xboole_0 ) ) ),
    inference(demod,[status(thm)],['52','55','66'])).

thf('68',plain,(
    ! [X0: $i,X3: $i] :
      ( ~ ( r2_hidden @ X3 @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ X3 ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['49','67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ( r2_hidden @ ( sk_D @ k1_xboole_0 @ X0 @ ( sk_B @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ) @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['46','68'])).

thf('70',plain,(
    ! [X27: $i,X28: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( r1_tarski @ X28 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t7_ordinal1])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
        = k1_xboole_0 )
      | ~ ( r1_tarski @ k1_xboole_0 @ ( sk_D @ k1_xboole_0 @ X0 @ ( sk_B @ ( k9_relat_1 @ k1_xboole_0 @ X0 ) ) ) ) ) ),
    inference('sup-',[status(thm)],['69','70'])).

thf(t2_xboole_1,axiom,(
    ! [A: $i] :
      ( r1_tarski @ k1_xboole_0 @ A ) )).

thf('72',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( k9_relat_1 @ k1_xboole_0 @ X0 )
      = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference(cnf,[status(esa)],[t2_xboole_1])).

thf('75',plain,(
    $false ),
    inference(demod,[status(thm)],['45','73','74'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.T6O6sfdYda
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:28:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running portfolio for 600 s
% 0.13/0.35  % File         : /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.13/0.35  % Number of cores: 8
% 0.13/0.35  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.49/0.70  % Running /export/starexec/sandbox2/solver/bin/fo/fo7.sh for 78
% 0.49/0.70  % Solved by: fo/fo7.sh
% 0.49/0.70  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.49/0.70  % done 400 iterations in 0.232s
% 0.49/0.70  % SZS status Theorem for '/export/starexec/sandbox2/benchmark/theBenchmark.p'
% 0.49/0.70  % SZS output start Refutation
% 0.49/0.70  thf(k1_enumset1_type, type, k1_enumset1: $i > $i > $i > $i).
% 0.49/0.70  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.49/0.70  thf(sk_D_1_type, type, sk_D_1: $i).
% 0.49/0.70  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.49/0.70  thf(k2_tarski_type, type, k2_tarski: $i > $i > $i).
% 0.49/0.70  thf(sk_D_type, type, sk_D: $i > $i > $i > $i).
% 0.49/0.70  thf(v5_relat_1_type, type, v5_relat_1: $i > $i > $o).
% 0.49/0.70  thf(k9_relat_1_type, type, k9_relat_1: $i > $i > $i).
% 0.49/0.70  thf(k2_relat_1_type, type, k2_relat_1: $i > $i).
% 0.49/0.70  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.49/0.70  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.49/0.70  thf(sk_C_type, type, sk_C: $i).
% 0.49/0.70  thf(sk_B_type, type, sk_B: $i > $i).
% 0.49/0.70  thf(k7_relset_1_type, type, k7_relset_1: $i > $i > $i > $i > $i).
% 0.49/0.70  thf(sk_B_1_type, type, sk_B_1: $i).
% 0.49/0.70  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.49/0.70  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.49/0.70  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.49/0.70  thf(v1_relat_1_type, type, v1_relat_1: $i > $o).
% 0.49/0.70  thf(v4_relat_1_type, type, v4_relat_1: $i > $i > $o).
% 0.49/0.70  thf(k1_funct_1_type, type, k1_funct_1: $i > $i > $i).
% 0.49/0.70  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.49/0.70  thf(sk_A_type, type, sk_A: $i).
% 0.49/0.70  thf(k4_mcart_1_type, type, k4_mcart_1: $i > $i > $i > $i > $i).
% 0.49/0.70  thf(k1_relat_1_type, type, k1_relat_1: $i > $i).
% 0.49/0.70  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.49/0.70  thf(k1_tarski_type, type, k1_tarski: $i > $i).
% 0.49/0.70  thf(t64_funct_2, conjecture,
% 0.49/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.70     ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.49/0.70         ( m1_subset_1 @
% 0.49/0.70           D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.49/0.70       ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.49/0.70         ( r1_tarski @
% 0.49/0.70           ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.49/0.70           ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ))).
% 0.49/0.70  thf(zf_stmt_0, negated_conjecture,
% 0.49/0.70    (~( ![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.70        ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ ( k1_tarski @ A ) @ B ) & 
% 0.49/0.70            ( m1_subset_1 @
% 0.49/0.70              D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ ( k1_tarski @ A ) @ B ) ) ) ) =>
% 0.49/0.70          ( ( ( B ) != ( k1_xboole_0 ) ) =>
% 0.49/0.70            ( r1_tarski @
% 0.49/0.70              ( k7_relset_1 @ ( k1_tarski @ A ) @ B @ D @ C ) @ 
% 0.49/0.70              ( k1_tarski @ ( k1_funct_1 @ D @ A ) ) ) ) ) )),
% 0.49/0.70    inference('cnf.neg', [status(esa)], [t64_funct_2])).
% 0.49/0.70  thf('0', plain,
% 0.49/0.70      (~ (r1_tarski @ 
% 0.49/0.70          (k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_D_1 @ sk_C) @ 
% 0.49/0.70          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('1', plain,
% 0.49/0.70      ((m1_subset_1 @ sk_D_1 @ 
% 0.49/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf(redefinition_k7_relset_1, axiom,
% 0.49/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.70       ( ( k7_relset_1 @ A @ B @ C @ D ) = ( k9_relat_1 @ C @ D ) ) ))).
% 0.49/0.70  thf('2', plain,
% 0.49/0.70      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.49/0.70         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.49/0.70          | ((k7_relset_1 @ X36 @ X37 @ X35 @ X38) = (k9_relat_1 @ X35 @ X38)))),
% 0.49/0.70      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.49/0.70  thf('3', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         ((k7_relset_1 @ (k1_tarski @ sk_A) @ sk_B_1 @ sk_D_1 @ X0)
% 0.49/0.70           = (k9_relat_1 @ sk_D_1 @ X0))),
% 0.49/0.70      inference('sup-', [status(thm)], ['1', '2'])).
% 0.49/0.70  thf('4', plain,
% 0.49/0.70      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ 
% 0.49/0.70          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.49/0.70      inference('demod', [status(thm)], ['0', '3'])).
% 0.49/0.70  thf(t144_relat_1, axiom,
% 0.49/0.70    (![A:$i,B:$i]:
% 0.49/0.70     ( ( v1_relat_1 @ B ) =>
% 0.49/0.70       ( r1_tarski @ ( k9_relat_1 @ B @ A ) @ ( k2_relat_1 @ B ) ) ))).
% 0.49/0.70  thf('5', plain,
% 0.49/0.70      (![X22 : $i, X23 : $i]:
% 0.49/0.70         ((r1_tarski @ (k9_relat_1 @ X22 @ X23) @ (k2_relat_1 @ X22))
% 0.49/0.70          | ~ (v1_relat_1 @ X22))),
% 0.49/0.70      inference('cnf', [status(esa)], [t144_relat_1])).
% 0.49/0.70  thf('6', plain,
% 0.49/0.70      ((m1_subset_1 @ sk_D_1 @ 
% 0.49/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf(cc2_relset_1, axiom,
% 0.49/0.70    (![A:$i,B:$i,C:$i]:
% 0.49/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.70       ( ( v4_relat_1 @ C @ A ) & ( v5_relat_1 @ C @ B ) ) ))).
% 0.49/0.70  thf('7', plain,
% 0.49/0.70      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.49/0.70         ((v4_relat_1 @ X32 @ X33)
% 0.49/0.70          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.49/0.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.49/0.70  thf('8', plain, ((v4_relat_1 @ sk_D_1 @ (k1_tarski @ sk_A))),
% 0.49/0.70      inference('sup-', [status(thm)], ['6', '7'])).
% 0.49/0.70  thf(d18_relat_1, axiom,
% 0.49/0.70    (![A:$i,B:$i]:
% 0.49/0.70     ( ( v1_relat_1 @ B ) =>
% 0.49/0.70       ( ( v4_relat_1 @ B @ A ) <=> ( r1_tarski @ ( k1_relat_1 @ B ) @ A ) ) ))).
% 0.49/0.70  thf('9', plain,
% 0.49/0.70      (![X16 : $i, X17 : $i]:
% 0.49/0.70         (~ (v4_relat_1 @ X16 @ X17)
% 0.49/0.70          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 0.49/0.70          | ~ (v1_relat_1 @ X16))),
% 0.49/0.70      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.49/0.70  thf('10', plain,
% 0.49/0.70      ((~ (v1_relat_1 @ sk_D_1)
% 0.49/0.70        | (r1_tarski @ (k1_relat_1 @ sk_D_1) @ (k1_tarski @ sk_A)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['8', '9'])).
% 0.49/0.70  thf('11', plain,
% 0.49/0.70      ((m1_subset_1 @ sk_D_1 @ 
% 0.49/0.70        (k1_zfmisc_1 @ (k2_zfmisc_1 @ (k1_tarski @ sk_A) @ sk_B_1)))),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf(cc1_relset_1, axiom,
% 0.49/0.70    (![A:$i,B:$i,C:$i]:
% 0.49/0.70     ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.49/0.70       ( v1_relat_1 @ C ) ))).
% 0.49/0.70  thf('12', plain,
% 0.49/0.70      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.49/0.70         ((v1_relat_1 @ X29)
% 0.49/0.70          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.49/0.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.49/0.70  thf('13', plain, ((v1_relat_1 @ sk_D_1)),
% 0.49/0.70      inference('sup-', [status(thm)], ['11', '12'])).
% 0.49/0.70  thf('14', plain, ((r1_tarski @ (k1_relat_1 @ sk_D_1) @ (k1_tarski @ sk_A))),
% 0.49/0.70      inference('demod', [status(thm)], ['10', '13'])).
% 0.49/0.70  thf(t69_enumset1, axiom,
% 0.49/0.70    (![A:$i]: ( ( k2_tarski @ A @ A ) = ( k1_tarski @ A ) ))).
% 0.49/0.70  thf('15', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.49/0.70      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.49/0.70  thf(t70_enumset1, axiom,
% 0.49/0.70    (![A:$i,B:$i]: ( ( k1_enumset1 @ A @ A @ B ) = ( k2_tarski @ A @ B ) ))).
% 0.49/0.70  thf('16', plain,
% 0.49/0.70      (![X2 : $i, X3 : $i]:
% 0.49/0.70         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 0.49/0.70      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.49/0.70  thf(t142_zfmisc_1, axiom,
% 0.49/0.70    (![A:$i,B:$i,C:$i,D:$i]:
% 0.49/0.70     ( ( r1_tarski @ D @ ( k1_enumset1 @ A @ B @ C ) ) <=>
% 0.49/0.70       ( ~( ( ( D ) != ( k1_xboole_0 ) ) & ( ( D ) != ( k1_tarski @ A ) ) & 
% 0.49/0.70            ( ( D ) != ( k1_tarski @ B ) ) & ( ( D ) != ( k1_tarski @ C ) ) & 
% 0.49/0.70            ( ( D ) != ( k2_tarski @ A @ B ) ) & 
% 0.49/0.70            ( ( D ) != ( k2_tarski @ B @ C ) ) & 
% 0.49/0.70            ( ( D ) != ( k2_tarski @ A @ C ) ) & 
% 0.49/0.70            ( ( D ) != ( k1_enumset1 @ A @ B @ C ) ) ) ) ))).
% 0.49/0.70  thf('17', plain,
% 0.49/0.70      (![X7 : $i, X8 : $i, X9 : $i, X10 : $i]:
% 0.49/0.70         (((X10) = (k1_enumset1 @ X7 @ X8 @ X9))
% 0.49/0.70          | ((X10) = (k2_tarski @ X7 @ X9))
% 0.49/0.70          | ((X10) = (k2_tarski @ X8 @ X9))
% 0.49/0.70          | ((X10) = (k2_tarski @ X7 @ X8))
% 0.49/0.70          | ((X10) = (k1_tarski @ X9))
% 0.49/0.70          | ((X10) = (k1_tarski @ X8))
% 0.49/0.70          | ((X10) = (k1_tarski @ X7))
% 0.49/0.70          | ((X10) = (k1_xboole_0))
% 0.49/0.70          | ~ (r1_tarski @ X10 @ (k1_enumset1 @ X7 @ X8 @ X9)))),
% 0.49/0.70      inference('cnf', [status(esa)], [t142_zfmisc_1])).
% 0.49/0.70  thf('18', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         (~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0))
% 0.49/0.70          | ((X2) = (k1_xboole_0))
% 0.49/0.70          | ((X2) = (k1_tarski @ X1))
% 0.49/0.70          | ((X2) = (k1_tarski @ X1))
% 0.49/0.70          | ((X2) = (k1_tarski @ X0))
% 0.49/0.70          | ((X2) = (k2_tarski @ X1 @ X1))
% 0.49/0.70          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.49/0.70          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.49/0.70          | ((X2) = (k1_enumset1 @ X1 @ X1 @ X0)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['16', '17'])).
% 0.49/0.70  thf('19', plain,
% 0.49/0.70      (![X2 : $i, X3 : $i]:
% 0.49/0.70         ((k1_enumset1 @ X2 @ X2 @ X3) = (k2_tarski @ X2 @ X3))),
% 0.49/0.70      inference('cnf', [status(esa)], [t70_enumset1])).
% 0.49/0.70  thf('20', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         (~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0))
% 0.49/0.70          | ((X2) = (k1_xboole_0))
% 0.49/0.70          | ((X2) = (k1_tarski @ X1))
% 0.49/0.70          | ((X2) = (k1_tarski @ X1))
% 0.49/0.70          | ((X2) = (k1_tarski @ X0))
% 0.49/0.70          | ((X2) = (k2_tarski @ X1 @ X1))
% 0.49/0.70          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.49/0.70          | ((X2) = (k2_tarski @ X1 @ X0))
% 0.49/0.70          | ((X2) = (k2_tarski @ X1 @ X0)))),
% 0.49/0.70      inference('demod', [status(thm)], ['18', '19'])).
% 0.49/0.70  thf('21', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         (((X2) = (k2_tarski @ X1 @ X0))
% 0.49/0.70          | ((X2) = (k2_tarski @ X1 @ X1))
% 0.49/0.70          | ((X2) = (k1_tarski @ X0))
% 0.49/0.70          | ((X2) = (k1_tarski @ X1))
% 0.49/0.70          | ((X2) = (k1_xboole_0))
% 0.49/0.70          | ~ (r1_tarski @ X2 @ (k2_tarski @ X1 @ X0)))),
% 0.49/0.70      inference('simplify', [status(thm)], ['20'])).
% 0.49/0.70  thf('22', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         (~ (r1_tarski @ X1 @ (k1_tarski @ X0))
% 0.49/0.70          | ((X1) = (k1_xboole_0))
% 0.49/0.70          | ((X1) = (k1_tarski @ X0))
% 0.49/0.70          | ((X1) = (k1_tarski @ X0))
% 0.49/0.70          | ((X1) = (k2_tarski @ X0 @ X0))
% 0.49/0.70          | ((X1) = (k2_tarski @ X0 @ X0)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['15', '21'])).
% 0.49/0.70  thf('23', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i]:
% 0.49/0.70         (((X1) = (k2_tarski @ X0 @ X0))
% 0.49/0.70          | ((X1) = (k1_tarski @ X0))
% 0.49/0.70          | ((X1) = (k1_xboole_0))
% 0.49/0.70          | ~ (r1_tarski @ X1 @ (k1_tarski @ X0)))),
% 0.49/0.70      inference('simplify', [status(thm)], ['22'])).
% 0.49/0.70  thf('24', plain,
% 0.49/0.70      ((((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.49/0.70        | ((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A))
% 0.49/0.70        | ((k1_relat_1 @ sk_D_1) = (k2_tarski @ sk_A @ sk_A)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['14', '23'])).
% 0.49/0.70  thf('25', plain, (![X1 : $i]: ((k2_tarski @ X1 @ X1) = (k1_tarski @ X1))),
% 0.49/0.70      inference('cnf', [status(esa)], [t69_enumset1])).
% 0.49/0.70  thf('26', plain,
% 0.49/0.70      ((((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.49/0.70        | ((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A))
% 0.49/0.70        | ((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A)))),
% 0.49/0.70      inference('demod', [status(thm)], ['24', '25'])).
% 0.49/0.70  thf('27', plain,
% 0.49/0.70      ((((k1_relat_1 @ sk_D_1) = (k1_tarski @ sk_A))
% 0.49/0.70        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.49/0.70      inference('simplify', [status(thm)], ['26'])).
% 0.49/0.70  thf(t14_funct_1, axiom,
% 0.49/0.70    (![A:$i,B:$i]:
% 0.49/0.70     ( ( ( v1_relat_1 @ B ) & ( v1_funct_1 @ B ) ) =>
% 0.49/0.70       ( ( ( k1_relat_1 @ B ) = ( k1_tarski @ A ) ) =>
% 0.49/0.70         ( ( k2_relat_1 @ B ) = ( k1_tarski @ ( k1_funct_1 @ B @ A ) ) ) ) ))).
% 0.49/0.70  thf('28', plain,
% 0.49/0.70      (![X25 : $i, X26 : $i]:
% 0.49/0.70         (((k1_relat_1 @ X26) != (k1_tarski @ X25))
% 0.49/0.70          | ((k2_relat_1 @ X26) = (k1_tarski @ (k1_funct_1 @ X26 @ X25)))
% 0.49/0.70          | ~ (v1_funct_1 @ X26)
% 0.49/0.70          | ~ (v1_relat_1 @ X26))),
% 0.49/0.70      inference('cnf', [status(esa)], [t14_funct_1])).
% 0.49/0.70  thf('29', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (((k1_relat_1 @ X0) != (k1_relat_1 @ sk_D_1))
% 0.49/0.70          | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0))
% 0.49/0.70          | ~ (v1_relat_1 @ X0)
% 0.49/0.70          | ~ (v1_funct_1 @ X0)
% 0.49/0.70          | ((k2_relat_1 @ X0) = (k1_tarski @ (k1_funct_1 @ X0 @ sk_A))))),
% 0.49/0.70      inference('sup-', [status(thm)], ['27', '28'])).
% 0.49/0.70  thf('30', plain,
% 0.49/0.70      ((((k2_relat_1 @ sk_D_1) = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))
% 0.49/0.70        | ~ (v1_funct_1 @ sk_D_1)
% 0.49/0.70        | ~ (v1_relat_1 @ sk_D_1)
% 0.49/0.70        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.49/0.70      inference('eq_res', [status(thm)], ['29'])).
% 0.49/0.70  thf('31', plain, ((v1_funct_1 @ sk_D_1)),
% 0.49/0.70      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.49/0.70  thf('32', plain, ((v1_relat_1 @ sk_D_1)),
% 0.49/0.70      inference('sup-', [status(thm)], ['11', '12'])).
% 0.49/0.70  thf('33', plain,
% 0.49/0.70      ((((k2_relat_1 @ sk_D_1) = (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))
% 0.49/0.70        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.49/0.70      inference('demod', [status(thm)], ['30', '31', '32'])).
% 0.49/0.70  thf('34', plain,
% 0.49/0.70      (~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ 
% 0.49/0.70          (k1_tarski @ (k1_funct_1 @ sk_D_1 @ sk_A)))),
% 0.49/0.70      inference('demod', [status(thm)], ['0', '3'])).
% 0.49/0.70  thf('35', plain,
% 0.49/0.70      ((~ (r1_tarski @ (k9_relat_1 @ sk_D_1 @ sk_C) @ (k2_relat_1 @ sk_D_1))
% 0.49/0.70        | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['33', '34'])).
% 0.49/0.70  thf('36', plain,
% 0.49/0.70      ((~ (v1_relat_1 @ sk_D_1) | ((k1_relat_1 @ sk_D_1) = (k1_xboole_0)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['5', '35'])).
% 0.49/0.70  thf('37', plain, ((v1_relat_1 @ sk_D_1)),
% 0.49/0.70      inference('sup-', [status(thm)], ['11', '12'])).
% 0.49/0.70  thf('38', plain, (((k1_relat_1 @ sk_D_1) = (k1_xboole_0))),
% 0.49/0.70      inference('demod', [status(thm)], ['36', '37'])).
% 0.49/0.70  thf(t64_relat_1, axiom,
% 0.49/0.70    (![A:$i]:
% 0.49/0.70     ( ( v1_relat_1 @ A ) =>
% 0.49/0.70       ( ( ( ( k1_relat_1 @ A ) = ( k1_xboole_0 ) ) | 
% 0.49/0.70           ( ( k2_relat_1 @ A ) = ( k1_xboole_0 ) ) ) =>
% 0.49/0.70         ( ( A ) = ( k1_xboole_0 ) ) ) ))).
% 0.49/0.70  thf('39', plain,
% 0.49/0.70      (![X24 : $i]:
% 0.49/0.70         (((k1_relat_1 @ X24) != (k1_xboole_0))
% 0.49/0.70          | ((X24) = (k1_xboole_0))
% 0.49/0.70          | ~ (v1_relat_1 @ X24))),
% 0.49/0.70      inference('cnf', [status(esa)], [t64_relat_1])).
% 0.49/0.70  thf('40', plain,
% 0.49/0.70      ((((k1_xboole_0) != (k1_xboole_0))
% 0.49/0.70        | ~ (v1_relat_1 @ sk_D_1)
% 0.49/0.70        | ((sk_D_1) = (k1_xboole_0)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['38', '39'])).
% 0.49/0.70  thf('41', plain, ((v1_relat_1 @ sk_D_1)),
% 0.49/0.70      inference('sup-', [status(thm)], ['11', '12'])).
% 0.49/0.70  thf('42', plain,
% 0.49/0.70      ((((k1_xboole_0) != (k1_xboole_0)) | ((sk_D_1) = (k1_xboole_0)))),
% 0.49/0.70      inference('demod', [status(thm)], ['40', '41'])).
% 0.49/0.70  thf('43', plain, (((sk_D_1) = (k1_xboole_0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['42'])).
% 0.49/0.70  thf('44', plain, (((sk_D_1) = (k1_xboole_0))),
% 0.49/0.70      inference('simplify', [status(thm)], ['42'])).
% 0.49/0.70  thf('45', plain,
% 0.49/0.70      (~ (r1_tarski @ (k9_relat_1 @ k1_xboole_0 @ sk_C) @ 
% 0.49/0.70          (k1_tarski @ (k1_funct_1 @ k1_xboole_0 @ sk_A)))),
% 0.49/0.70      inference('demod', [status(thm)], ['4', '43', '44'])).
% 0.49/0.70  thf(t34_mcart_1, axiom,
% 0.49/0.70    (![A:$i]:
% 0.49/0.70     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.49/0.70          ( ![B:$i]:
% 0.49/0.70            ( ~( ( r2_hidden @ B @ A ) & 
% 0.49/0.70                 ( ![C:$i,D:$i,E:$i,F:$i]:
% 0.49/0.70                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.49/0.70                        ( ( B ) = ( k4_mcart_1 @ C @ D @ E @ F ) ) ) ) ) ) ) ) ) ))).
% 0.49/0.70  thf('46', plain,
% 0.49/0.70      (![X39 : $i]:
% 0.49/0.70         (((X39) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X39) @ X39))),
% 0.49/0.70      inference('cnf', [status(esa)], [t34_mcart_1])).
% 0.49/0.70  thf(t4_subset_1, axiom,
% 0.49/0.70    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.49/0.70  thf('47', plain,
% 0.49/0.70      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.49/0.70      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.49/0.70  thf('48', plain,
% 0.49/0.70      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.49/0.70         (~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.49/0.70          | ((k7_relset_1 @ X36 @ X37 @ X35 @ X38) = (k9_relat_1 @ X35 @ X38)))),
% 0.49/0.70      inference('cnf', [status(esa)], [redefinition_k7_relset_1])).
% 0.49/0.70  thf('49', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         ((k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 0.49/0.70           = (k9_relat_1 @ k1_xboole_0 @ X2))),
% 0.49/0.70      inference('sup-', [status(thm)], ['47', '48'])).
% 0.49/0.70  thf('50', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.49/0.70         ((k7_relset_1 @ X1 @ X0 @ k1_xboole_0 @ X2)
% 0.49/0.70           = (k9_relat_1 @ k1_xboole_0 @ X2))),
% 0.49/0.70      inference('sup-', [status(thm)], ['47', '48'])).
% 0.49/0.70  thf(t143_relat_1, axiom,
% 0.49/0.70    (![A:$i,B:$i,C:$i]:
% 0.49/0.70     ( ( v1_relat_1 @ C ) =>
% 0.49/0.70       ( ( r2_hidden @ A @ ( k9_relat_1 @ C @ B ) ) <=>
% 0.49/0.70         ( ?[D:$i]:
% 0.49/0.70           ( ( r2_hidden @ D @ B ) & 
% 0.49/0.70             ( r2_hidden @ ( k4_tarski @ D @ A ) @ C ) & 
% 0.49/0.70             ( r2_hidden @ D @ ( k1_relat_1 @ C ) ) ) ) ) ))).
% 0.49/0.70  thf('51', plain,
% 0.49/0.70      (![X19 : $i, X20 : $i, X21 : $i]:
% 0.49/0.70         (~ (r2_hidden @ X20 @ (k9_relat_1 @ X21 @ X19))
% 0.49/0.70          | (r2_hidden @ (sk_D @ X21 @ X19 @ X20) @ (k1_relat_1 @ X21))
% 0.49/0.70          | ~ (v1_relat_1 @ X21))),
% 0.49/0.70      inference('cnf', [status(esa)], [t143_relat_1])).
% 0.49/0.70  thf('52', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.70         (~ (r2_hidden @ X3 @ (k7_relset_1 @ X2 @ X1 @ k1_xboole_0 @ X0))
% 0.49/0.70          | ~ (v1_relat_1 @ k1_xboole_0)
% 0.49/0.70          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X3) @ 
% 0.49/0.70             (k1_relat_1 @ k1_xboole_0)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['50', '51'])).
% 0.49/0.70  thf('53', plain,
% 0.49/0.70      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.49/0.70      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.49/0.70  thf('54', plain,
% 0.49/0.70      (![X29 : $i, X30 : $i, X31 : $i]:
% 0.49/0.70         ((v1_relat_1 @ X29)
% 0.49/0.70          | ~ (m1_subset_1 @ X29 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X30 @ X31))))),
% 0.49/0.70      inference('cnf', [status(esa)], [cc1_relset_1])).
% 0.49/0.70  thf('55', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.49/0.70      inference('sup-', [status(thm)], ['53', '54'])).
% 0.49/0.70  thf('56', plain,
% 0.49/0.70      (![X12 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X12))),
% 0.49/0.70      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.49/0.70  thf('57', plain,
% 0.49/0.70      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.49/0.70         ((v4_relat_1 @ X32 @ X33)
% 0.49/0.70          | ~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34))))),
% 0.49/0.70      inference('cnf', [status(esa)], [cc2_relset_1])).
% 0.49/0.70  thf('58', plain, (![X1 : $i]: (v4_relat_1 @ k1_xboole_0 @ X1)),
% 0.49/0.70      inference('sup-', [status(thm)], ['56', '57'])).
% 0.49/0.70  thf('59', plain,
% 0.49/0.70      (![X16 : $i, X17 : $i]:
% 0.49/0.70         (~ (v4_relat_1 @ X16 @ X17)
% 0.49/0.70          | (r1_tarski @ (k1_relat_1 @ X16) @ X17)
% 0.49/0.70          | ~ (v1_relat_1 @ X16))),
% 0.49/0.70      inference('cnf', [status(esa)], [d18_relat_1])).
% 0.49/0.70  thf('60', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (~ (v1_relat_1 @ k1_xboole_0)
% 0.49/0.70          | (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0))),
% 0.49/0.70      inference('sup-', [status(thm)], ['58', '59'])).
% 0.49/0.70  thf('61', plain, ((v1_relat_1 @ k1_xboole_0)),
% 0.49/0.70      inference('sup-', [status(thm)], ['53', '54'])).
% 0.49/0.70  thf('62', plain, (![X0 : $i]: (r1_tarski @ (k1_relat_1 @ k1_xboole_0) @ X0)),
% 0.49/0.70      inference('demod', [status(thm)], ['60', '61'])).
% 0.49/0.70  thf('63', plain,
% 0.49/0.70      (![X39 : $i]:
% 0.49/0.70         (((X39) = (k1_xboole_0)) | (r2_hidden @ (sk_B @ X39) @ X39))),
% 0.49/0.70      inference('cnf', [status(esa)], [t34_mcart_1])).
% 0.49/0.70  thf(t7_ordinal1, axiom,
% 0.49/0.70    (![A:$i,B:$i]: ( ~( ( r2_hidden @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.49/0.70  thf('64', plain,
% 0.49/0.70      (![X27 : $i, X28 : $i]:
% 0.49/0.70         (~ (r2_hidden @ X27 @ X28) | ~ (r1_tarski @ X28 @ X27))),
% 0.49/0.70      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.49/0.70  thf('65', plain,
% 0.49/0.70      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (r1_tarski @ X0 @ (sk_B @ X0)))),
% 0.49/0.70      inference('sup-', [status(thm)], ['63', '64'])).
% 0.49/0.70  thf('66', plain, (((k1_relat_1 @ k1_xboole_0) = (k1_xboole_0))),
% 0.49/0.70      inference('sup-', [status(thm)], ['62', '65'])).
% 0.49/0.70  thf('67', plain,
% 0.49/0.70      (![X0 : $i, X1 : $i, X2 : $i, X3 : $i]:
% 0.49/0.70         (~ (r2_hidden @ X3 @ (k7_relset_1 @ X2 @ X1 @ k1_xboole_0 @ X0))
% 0.49/0.70          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X3) @ k1_xboole_0))),
% 0.49/0.70      inference('demod', [status(thm)], ['52', '55', '66'])).
% 0.49/0.70  thf('68', plain,
% 0.49/0.70      (![X0 : $i, X3 : $i]:
% 0.49/0.70         (~ (r2_hidden @ X3 @ (k9_relat_1 @ k1_xboole_0 @ X0))
% 0.49/0.70          | (r2_hidden @ (sk_D @ k1_xboole_0 @ X0 @ X3) @ k1_xboole_0))),
% 0.49/0.70      inference('sup-', [status(thm)], ['49', '67'])).
% 0.49/0.70  thf('69', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.49/0.70          | (r2_hidden @ 
% 0.49/0.70             (sk_D @ k1_xboole_0 @ X0 @ 
% 0.49/0.70              (sk_B @ (k9_relat_1 @ k1_xboole_0 @ X0))) @ 
% 0.49/0.70             k1_xboole_0))),
% 0.49/0.70      inference('sup-', [status(thm)], ['46', '68'])).
% 0.49/0.70  thf('70', plain,
% 0.49/0.70      (![X27 : $i, X28 : $i]:
% 0.49/0.70         (~ (r2_hidden @ X27 @ X28) | ~ (r1_tarski @ X28 @ X27))),
% 0.49/0.70      inference('cnf', [status(esa)], [t7_ordinal1])).
% 0.49/0.70  thf('71', plain,
% 0.49/0.70      (![X0 : $i]:
% 0.49/0.70         (((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))
% 0.49/0.70          | ~ (r1_tarski @ k1_xboole_0 @ 
% 0.49/0.70               (sk_D @ k1_xboole_0 @ X0 @ 
% 0.49/0.70                (sk_B @ (k9_relat_1 @ k1_xboole_0 @ X0)))))),
% 0.49/0.70      inference('sup-', [status(thm)], ['69', '70'])).
% 0.49/0.70  thf(t2_xboole_1, axiom, (![A:$i]: ( r1_tarski @ k1_xboole_0 @ A ))).
% 0.49/0.70  thf('72', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.49/0.70      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.49/0.70  thf('73', plain,
% 0.49/0.70      (![X0 : $i]: ((k9_relat_1 @ k1_xboole_0 @ X0) = (k1_xboole_0))),
% 0.49/0.70      inference('demod', [status(thm)], ['71', '72'])).
% 0.49/0.70  thf('74', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.49/0.70      inference('cnf', [status(esa)], [t2_xboole_1])).
% 0.49/0.70  thf('75', plain, ($false),
% 0.49/0.70      inference('demod', [status(thm)], ['45', '73', '74'])).
% 0.49/0.70  
% 0.49/0.70  % SZS output end Refutation
% 0.49/0.70  
% 0.49/0.70  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
