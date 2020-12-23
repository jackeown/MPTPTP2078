%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0833+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bVXCcmossm

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:33 EST 2020

% Result     : Theorem 35.81s
% Output     : Refutation 35.81s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 767 expanded)
%              Number of leaves         :   34 ( 229 expanded)
%              Depth                    :   27
%              Number of atoms          : 1123 (8925 expanded)
%              Number of equality atoms :   53 ( 256 expanded)
%              Maximal formula depth    :   16 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(o_0_0_xboole_0_type,type,(
    o_0_0_xboole_0: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k6_relset_1_type,type,(
    k6_relset_1: $i > $i > $i > $i > $i )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_B_1_type,type,(
    sk_B_1: $i )).

thf(k8_relat_1_type,type,(
    k8_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t36_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( r1_tarski @ B @ C )
       => ( r2_relset_1 @ A @ B @ ( k6_relset_1 @ A @ B @ C @ D ) @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
       => ( ( r1_tarski @ B @ C )
         => ( r2_relset_1 @ A @ B @ ( k6_relset_1 @ A @ B @ C @ D ) @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t36_relset_1])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ ( k6_relset_1 @ sk_A @ sk_B_1 @ sk_C @ sk_D_1 ) @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k6_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k6_relset_1 @ A @ B @ C @ D )
        = ( k8_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ( ( k6_relset_1 @ X18 @ X19 @ X16 @ X17 )
        = ( k8_relat_1 @ X16 @ X17 ) )
      | ~ ( m1_subset_1 @ X17 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X18 @ X19 ) ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k6_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k6_relset_1 @ sk_A @ sk_B_1 @ X0 @ sk_D_1 )
      = ( k8_relat_1 @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ ( k8_relat_1 @ sk_C @ sk_D_1 ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(existence_m1_subset_1,axiom,(
    ! [A: $i] :
    ? [B: $i] :
      ( m1_subset_1 @ B @ A ) )).

thf('5',plain,(
    ! [X15: $i] :
      ( m1_subset_1 @ ( sk_B @ X15 ) @ X15 ) ),
    inference(cnf,[status(esa)],[existence_m1_subset_1])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r2_hidden @ X31 @ X32 )
      | ( v1_xboole_0 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('7',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf(d12_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ B )
     => ! [C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( C
              = ( k8_relat_1 @ A @ B ) )
          <=> ! [D: $i,E: $i] :
                ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
              <=> ( ( r2_hidden @ E @ A )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ B ) ) ) ) ) ) )).

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X5 @ X4 ) @ ( sk_E @ X3 @ X5 @ X4 ) ) @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X5 @ X4 ) @ ( sk_E @ X3 @ X5 @ X4 ) ) @ X5 )
      | ( X3
        = ( k8_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X0 @ X1 ) @ ( sk_E @ X0 @ X0 @ X1 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X0 @ X1 ) @ ( sk_E @ X0 @ X0 @ X1 ) ) @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('12',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ( m1_subset_1 @ X36 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['11','12'])).

thf('14',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( sk_D_1
        = ( k8_relat_1 @ X0 @ sk_D_1 ) )
      | ( m1_subset_1 @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_D_1 @ X0 ) @ ( sk_E @ sk_D_1 @ sk_D_1 @ X0 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['10','13'])).

thf('15',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('17',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i] :
      ( ( sk_D_1
        = ( k8_relat_1 @ X0 @ sk_D_1 ) )
      | ( m1_subset_1 @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_D_1 @ X0 ) @ ( sk_E @ sk_D_1 @ sk_D_1 @ X0 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference(demod,[status(thm)],['14','17'])).

thf('19',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r2_hidden @ X31 @ X32 )
      | ( v1_xboole_0 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('20',plain,(
    ! [X0: $i] :
      ( ( sk_D_1
        = ( k8_relat_1 @ X0 @ sk_D_1 ) )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ sk_D_1 @ X0 ) @ ( sk_E @ sk_D_1 @ sk_D_1 @ X0 ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(t106_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('21',plain,(
    ! [X24: $i,X25: $i,X26: $i,X27: $i] :
      ( ( r2_hidden @ X26 @ X27 )
      | ~ ( r2_hidden @ ( k4_tarski @ X24 @ X26 ) @ ( k2_zfmisc_1 @ X25 @ X27 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('22',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ( sk_D_1
        = ( k8_relat_1 @ X0 @ sk_D_1 ) )
      | ( r2_hidden @ ( sk_E @ sk_D_1 @ sk_D_1 @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    r1_tarski @ sk_B_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('24',plain,(
    ! [X33: $i,X35: $i] :
      ( ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( r1_tarski @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('25',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X36: $i,X37: $i,X38: $i] :
      ( ~ ( r2_hidden @ X36 @ X37 )
      | ~ ( m1_subset_1 @ X37 @ ( k1_zfmisc_1 @ X38 ) )
      | ( m1_subset_1 @ X36 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( sk_D_1
        = ( k8_relat_1 @ X0 @ sk_D_1 ) )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ( m1_subset_1 @ ( sk_E @ sk_D_1 @ sk_D_1 @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['22','27'])).

thf('29',plain,(
    ! [X31: $i,X32: $i] :
      ( ( r2_hidden @ X31 @ X32 )
      | ( v1_xboole_0 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ X32 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('30',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ( sk_D_1
        = ( k8_relat_1 @ X0 @ sk_D_1 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( r2_hidden @ ( sk_E @ sk_D_1 @ sk_D_1 @ X0 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['28','29'])).

thf('31',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X0 @ X1 ) @ ( sk_E @ X0 @ X0 @ X1 ) ) @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('32',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X0 @ X1 ) @ ( sk_E @ X0 @ X0 @ X1 ) ) @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('33',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X5 @ X4 ) @ ( sk_E @ X3 @ X5 @ X4 ) ) @ X3 )
      | ~ ( r2_hidden @ ( sk_E @ X3 @ X5 @ X4 ) @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X5 @ X4 ) @ ( sk_E @ X3 @ X5 @ X4 ) ) @ X5 )
      | ( X3
        = ( k8_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d12_relat_1])).

thf('34',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X0 @ X1 ) @ ( sk_E @ X0 @ X0 @ X1 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_E @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['32','33'])).

thf('35',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_E @ X0 @ X0 @ X1 ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X0 @ X1 ) @ ( sk_E @ X0 @ X0 @ X1 ) ) @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['34'])).

thf('36',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( r2_hidden @ ( sk_E @ X0 @ X0 @ X1 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['31','35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_E @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('38',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( sk_D_1
      = ( k8_relat_1 @ sk_C @ sk_D_1 ) )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ( sk_D_1
      = ( k8_relat_1 @ sk_C @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['30','37'])).

thf('39',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('40',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( sk_D_1
      = ( k8_relat_1 @ sk_C @ sk_D_1 ) )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( sk_D_1
      = ( k8_relat_1 @ sk_C @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['38','39'])).

thf('41',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( sk_D_1
      = ( k8_relat_1 @ sk_C @ sk_D_1 ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['40'])).

thf(t6_boole,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
     => ( A = k1_xboole_0 ) ) )).

thf('42',plain,(
    ! [X42: $i] :
      ( ( X42 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('43',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( sk_D_1
      = ( k8_relat_1 @ sk_C @ sk_D_1 ) )
    | ( ( k2_zfmisc_1 @ sk_A @ sk_B_1 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['41','42'])).

thf('44',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,(
    ! [X33: $i,X34: $i] :
      ( ( r1_tarski @ X33 @ X34 )
      | ~ ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X34 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('46',plain,(
    r1_tarski @ sk_D_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ),
    inference('sup-',[status(thm)],['44','45'])).

thf('47',plain,
    ( ( r1_tarski @ sk_D_1 @ k1_xboole_0 )
    | ( sk_D_1
      = ( k8_relat_1 @ sk_C @ sk_D_1 ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup+',[status(thm)],['43','46'])).

thf('48',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ ( k8_relat_1 @ sk_C @ sk_D_1 ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('49',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_D_1 )
    | ( v1_xboole_0 @ sk_C )
    | ( r1_tarski @ sk_D_1 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['47','48'])).

thf('50',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('51',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r2_relset_1 @ X20 @ X21 @ X22 @ X22 )
      | ~ ( m1_subset_1 @ X22 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) )
      | ~ ( m1_subset_1 @ X23 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X20 @ X21 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('52',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['51'])).

thf('53',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['50','52'])).

thf('54',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( r1_tarski @ sk_D_1 @ k1_xboole_0 ) ),
    inference(demod,[status(thm)],['49','53'])).

thf('55',plain,(
    ! [X33: $i,X35: $i] :
      ( ( m1_subset_1 @ X33 @ ( k1_zfmisc_1 @ X35 ) )
      | ~ ( r1_tarski @ X33 @ X35 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('56',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('57',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X39 @ X40 )
      | ~ ( v1_xboole_0 @ X41 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('58',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf(dt_o_0_0_xboole_0,axiom,(
    v1_xboole_0 @ o_0_0_xboole_0 )).

thf('59',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('60',plain,(
    v1_xboole_0 @ o_0_0_xboole_0 ),
    inference(cnf,[status(esa)],[dt_o_0_0_xboole_0])).

thf('61',plain,(
    ! [X42: $i] :
      ( ( X42 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('62',plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['60','61'])).

thf('63',plain,(
    v1_xboole_0 @ k1_xboole_0 ),
    inference(demod,[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['58','63'])).

thf('65',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['7','64'])).

thf('66',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X0 @ X1 ) @ ( sk_E @ X0 @ X0 @ X1 ) ) @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf(t7_boole,axiom,(
    ! [A: $i,B: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( v1_xboole_0 @ B ) ) )).

thf('67',plain,(
    ! [X43: $i,X44: $i] :
      ( ~ ( r2_hidden @ X43 @ X44 )
      | ~ ( v1_xboole_0 @ X44 ) ) ),
    inference(cnf,[status(esa)],[t7_boole])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['66','67'])).

thf('69',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ ( k8_relat_1 @ sk_C @ sk_D_1 ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('70',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_D_1 )
    | ~ ( v1_xboole_0 @ sk_D_1 )
    | ~ ( v1_relat_1 @ sk_D_1 ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['50','52'])).

thf('72',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('73',plain,(
    ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('74',plain,(
    v1_xboole_0 @ sk_C ),
    inference(clc,[status(thm)],['65','73'])).

thf('75',plain,(
    ! [X42: $i] :
      ( ( X42 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('76',plain,(
    sk_C = k1_xboole_0 ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_1 @ ( k8_relat_1 @ k1_xboole_0 @ sk_D_1 ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['4','76'])).

thf('78',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('79',plain,(
    m1_subset_1 @ sk_B_1 @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('80',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X39 @ X40 )
      | ~ ( v1_xboole_0 @ X41 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('81',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    v1_xboole_0 @ sk_C ),
    inference(clc,[status(thm)],['65','73'])).

thf('83',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B_1 ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    v1_xboole_0 @ sk_B_1 ),
    inference('sup-',[status(thm)],['78','83'])).

thf('85',plain,(
    ! [X42: $i] :
      ( ( X42 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X42 ) ) ),
    inference(cnf,[status(esa)],[t6_boole])).

thf('86',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_B @ X0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','6'])).

thf('88',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ( sk_D_1
        = ( k8_relat_1 @ X0 @ sk_D_1 ) )
      | ( r2_hidden @ ( sk_E @ sk_D_1 @ sk_D_1 @ X0 ) @ sk_B_1 ) ) ),
    inference('sup-',[status(thm)],['20','21'])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_E @ X0 @ X0 @ X1 ) @ X1 )
      | ( X0
        = ( k8_relat_1 @ X1 @ X0 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['36'])).

thf('90',plain,
    ( ( sk_D_1
      = ( k8_relat_1 @ sk_B_1 @ sk_D_1 ) )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ( sk_D_1
      = ( k8_relat_1 @ sk_B_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['88','89'])).

thf('91',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['15','16'])).

thf('92',plain,
    ( ( sk_D_1
      = ( k8_relat_1 @ sk_B_1 @ sk_D_1 ) )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( sk_D_1
      = ( k8_relat_1 @ sk_B_1 @ sk_D_1 ) ) ),
    inference(demod,[status(thm)],['90','91'])).

thf('93',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
    | ( sk_D_1
      = ( k8_relat_1 @ sk_B_1 @ sk_D_1 ) ) ),
    inference(simplify,[status(thm)],['92'])).

thf('94',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('95',plain,(
    ! [X39: $i,X40: $i,X41: $i] :
      ( ~ ( r2_hidden @ X39 @ X40 )
      | ~ ( v1_xboole_0 @ X41 )
      | ~ ( m1_subset_1 @ X40 @ ( k1_zfmisc_1 @ X41 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('96',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_A @ sk_B_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( ( sk_D_1
        = ( k8_relat_1 @ sk_B_1 @ sk_D_1 ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['93','96'])).

thf('98',plain,
    ( ( v1_xboole_0 @ sk_D_1 )
    | ( sk_D_1
      = ( k8_relat_1 @ sk_B_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['87','97'])).

thf('99',plain,(
    ~ ( v1_xboole_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['70','71','72'])).

thf('100',plain,
    ( sk_D_1
    = ( k8_relat_1 @ sk_B_1 @ sk_D_1 ) ),
    inference(clc,[status(thm)],['98','99'])).

thf('101',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['84','85'])).

thf('102',plain,
    ( sk_D_1
    = ( k8_relat_1 @ k1_xboole_0 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['100','101'])).

thf('103',plain,(
    ~ ( r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_D_1 @ sk_D_1 ) ),
    inference(demod,[status(thm)],['77','86','102'])).

thf('104',plain,(
    r2_relset_1 @ sk_A @ sk_B_1 @ sk_D_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['50','52'])).

thf('105',plain,(
    sk_B_1 = k1_xboole_0 ),
    inference('sup-',[status(thm)],['84','85'])).

thf('106',plain,(
    r2_relset_1 @ sk_A @ k1_xboole_0 @ sk_D_1 @ sk_D_1 ),
    inference(demod,[status(thm)],['104','105'])).

thf('107',plain,(
    $false ),
    inference(demod,[status(thm)],['103','106'])).


%------------------------------------------------------------------------------
