%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0831+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.bRDFdTQ1hW

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:33 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 308 expanded)
%              Number of leaves         :   27 (  93 expanded)
%              Depth                    :   21
%              Number of atoms          : 1090 (4131 expanded)
%              Number of equality atoms :   56 ( 138 expanded)
%              Maximal formula depth    :   16 (   7 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(k5_relset_1_type,type,(
    k5_relset_1: $i > $i > $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(t34_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
     => ( ( r1_tarski @ B @ C )
       => ( r2_relset_1 @ B @ A @ ( k5_relset_1 @ B @ A @ D @ C ) @ D ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ A ) ) )
       => ( ( r1_tarski @ B @ C )
         => ( r2_relset_1 @ B @ A @ ( k5_relset_1 @ B @ A @ D @ C ) @ D ) ) ) ),
    inference('cnf.neg',[status(esa)],[t34_relset_1])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_B @ sk_A @ ( k5_relset_1 @ sk_B @ sk_A @ sk_D_1 @ sk_C ) @ sk_D_1 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k5_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k5_relset_1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i,X11: $i,X12: $i] :
      ( ~ ( m1_subset_1 @ X9 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X10 @ X11 ) ) )
      | ( ( k5_relset_1 @ X10 @ X11 @ X9 @ X12 )
        = ( k7_relat_1 @ X9 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k5_relset_1 @ sk_B @ sk_A @ sk_D_1 @ X0 )
      = ( k7_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( r2_relset_1 @ sk_B @ sk_A @ ( k7_relat_1 @ sk_D_1 @ sk_C ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(d11_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i,C: $i] :
          ( ( v1_relat_1 @ C )
         => ( ( C
              = ( k7_relat_1 @ A @ B ) )
          <=> ! [D: $i,E: $i] :
                ( ( r2_hidden @ ( k4_tarski @ D @ E ) @ C )
              <=> ( ( r2_hidden @ D @ B )
                  & ( r2_hidden @ ( k4_tarski @ D @ E ) @ A ) ) ) ) ) ) )).

thf('5',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X5 @ X4 ) @ ( sk_E @ X3 @ X5 @ X4 ) ) @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X5 @ X4 ) @ ( sk_E @ X3 @ X5 @ X4 ) ) @ X4 )
      | ( X3
        = ( k7_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d11_relat_1])).

thf('6',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X1 @ X0 ) @ ( sk_E @ X0 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X1 @ X0 ) @ ( sk_E @ X0 @ X1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('8',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X1 @ X0 ) @ ( sk_E @ X0 @ X1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X1 @ X0 ) @ ( sk_E @ X0 @ X1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('10',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('11',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( m1_subset_1 @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('12',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( sk_D_1
        = ( k7_relat_1 @ sk_D_1 @ X0 ) )
      | ( m1_subset_1 @ ( k4_tarski @ ( sk_D @ sk_D_1 @ X0 @ sk_D_1 ) @ ( sk_E @ sk_D_1 @ X0 @ sk_D_1 ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['9','12'])).

thf('14',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('16',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('17',plain,(
    ! [X0: $i] :
      ( ( sk_D_1
        = ( k7_relat_1 @ sk_D_1 @ X0 ) )
      | ( m1_subset_1 @ ( k4_tarski @ ( sk_D @ sk_D_1 @ X0 @ sk_D_1 ) @ ( sk_E @ sk_D_1 @ X0 @ sk_D_1 ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference(demod,[status(thm)],['13','16'])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('18',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r2_hidden @ X22 @ X23 )
      | ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('19',plain,(
    ! [X0: $i] :
      ( ( sk_D_1
        = ( k7_relat_1 @ sk_D_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ sk_D_1 @ X0 @ sk_D_1 ) @ ( sk_E @ sk_D_1 @ X0 @ sk_D_1 ) ) @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ) ),
    inference('sup-',[status(thm)],['17','18'])).

thf(t106_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('20',plain,(
    ! [X17: $i,X18: $i,X19: $i,X20: $i] :
      ( ( r2_hidden @ X17 @ X18 )
      | ~ ( r2_hidden @ ( k4_tarski @ X17 @ X19 ) @ ( k2_zfmisc_1 @ X18 @ X20 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('21',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
      | ( sk_D_1
        = ( k7_relat_1 @ sk_D_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ X0 @ sk_D_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X1 @ X0 ) @ ( sk_E @ X0 @ X1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X1 @ X0 ) @ ( sk_E @ X0 @ X1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('24',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X5 @ X4 ) @ ( sk_E @ X3 @ X5 @ X4 ) ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X5 @ X4 ) @ ( sk_E @ X3 @ X5 @ X4 ) ) @ X4 )
      | ( X3
        = ( k7_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d11_relat_1])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X1 @ X0 ) @ ( sk_E @ X0 @ X1 @ X0 ) ) @ X0 )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['23','24'])).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X1 @ X0 ) @ ( sk_E @ X0 @ X1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['25'])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['22','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('29',plain,
    ( ( sk_D_1
      = ( k7_relat_1 @ sk_D_1 @ sk_B ) )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ( sk_D_1
      = ( k7_relat_1 @ sk_D_1 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['21','28'])).

thf('30',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('31',plain,
    ( ( sk_D_1
      = ( k7_relat_1 @ sk_D_1 @ sk_B ) )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( sk_D_1
      = ( k7_relat_1 @ sk_D_1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['29','30'])).

thf('32',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( sk_D_1
      = ( k7_relat_1 @ sk_D_1 @ sk_B ) ) ),
    inference(simplify,[status(thm)],['31'])).

thf('33',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t5_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ~ ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) )
        & ( v1_xboole_0 @ C ) ) )).

thf('34',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ~ ( v1_xboole_0 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('35',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('36',plain,(
    ! [X0: $i] :
      ( ( sk_D_1
        = ( k7_relat_1 @ sk_D_1 @ sk_B ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['32','35'])).

thf('37',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( sk_D_1
        = ( k7_relat_1 @ sk_D_1 @ X0 ) )
      | ( sk_D_1
        = ( k7_relat_1 @ sk_D_1 @ sk_B ) ) ) ),
    inference('sup-',[status(thm)],['8','36'])).

thf('38',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('39',plain,(
    ! [X0: $i] :
      ( ( sk_D_1
        = ( k7_relat_1 @ sk_D_1 @ X0 ) )
      | ( sk_D_1
        = ( k7_relat_1 @ sk_D_1 @ sk_B ) ) ) ),
    inference(demod,[status(thm)],['37','38'])).

thf('40',plain,
    ( sk_D_1
    = ( k7_relat_1 @ sk_D_1 @ sk_B ) ),
    inference(condensation,[status(thm)],['39'])).

thf('41',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( X3
       != ( k7_relat_1 @ X4 @ X5 ) )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d11_relat_1])).

thf('42',plain,(
    ! [X4: $i,X5: $i,X6: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k7_relat_1 @ X4 @ X5 ) )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_D_1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D_1 @ sk_B ) )
      | ( r2_hidden @ X1 @ sk_B )
      | ~ ( v1_relat_1 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['40','42'])).

thf('44',plain,
    ( sk_D_1
    = ( k7_relat_1 @ sk_D_1 @ sk_B ) ),
    inference(condensation,[status(thm)],['39'])).

thf('45',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('46',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('47',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X1 @ X0 ) @ sk_D_1 )
      | ( r2_hidden @ X1 @ sk_B ) ) ),
    inference(demod,[status(thm)],['43','44','45','46'])).

thf('48',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( sk_D_1
        = ( k7_relat_1 @ sk_D_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ X0 @ sk_D_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['7','47'])).

thf('49',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( sk_D_1
        = ( k7_relat_1 @ sk_D_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ X0 @ sk_D_1 ) @ sk_B ) ) ),
    inference(demod,[status(thm)],['48','49'])).

thf('51',plain,(
    r1_tarski @ sk_B @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('52',plain,(
    ! [X24: $i,X26: $i] :
      ( ( m1_subset_1 @ X24 @ ( k1_zfmisc_1 @ X26 ) )
      | ~ ( r1_tarski @ X24 @ X26 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('53',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,(
    ! [X30: $i,X31: $i,X32: $i] :
      ( ~ ( r2_hidden @ X30 @ X31 )
      | ~ ( v1_xboole_0 @ X32 )
      | ~ ( m1_subset_1 @ X31 @ ( k1_zfmisc_1 @ X32 ) ) ) ),
    inference(cnf,[status(esa)],[t5_subset])).

thf('55',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['53','54'])).

thf('56',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X1 @ X0 ) @ ( sk_E @ X0 @ X1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['6'])).

thf('57',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
      | ( sk_D_1
        = ( k7_relat_1 @ sk_D_1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ X0 @ sk_D_1 ) @ sk_B ) ) ),
    inference('sup-',[status(thm)],['19','20'])).

thf('58',plain,(
    m1_subset_1 @ sk_B @ ( k1_zfmisc_1 @ sk_C ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('59',plain,(
    ! [X27: $i,X28: $i,X29: $i] :
      ( ~ ( r2_hidden @ X27 @ X28 )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ X29 ) )
      | ( m1_subset_1 @ X27 @ X29 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('60',plain,(
    ! [X0: $i] :
      ( ( m1_subset_1 @ X0 @ sk_C )
      | ~ ( r2_hidden @ X0 @ sk_B ) ) ),
    inference('sup-',[status(thm)],['58','59'])).

thf('61',plain,(
    ! [X0: $i] :
      ( ( sk_D_1
        = ( k7_relat_1 @ sk_D_1 @ X0 ) )
      | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
      | ( m1_subset_1 @ ( sk_D @ sk_D_1 @ X0 @ sk_D_1 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['57','60'])).

thf('62',plain,(
    ! [X22: $i,X23: $i] :
      ( ( r2_hidden @ X22 @ X23 )
      | ( v1_xboole_0 @ X23 )
      | ~ ( m1_subset_1 @ X22 @ X23 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('63',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
      | ( sk_D_1
        = ( k7_relat_1 @ sk_D_1 @ X0 ) )
      | ( v1_xboole_0 @ sk_C )
      | ( r2_hidden @ ( sk_D @ sk_D_1 @ X0 @ sk_D_1 ) @ sk_C ) ) ),
    inference('sup-',[status(thm)],['61','62'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['27'])).

thf('65',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( sk_D_1
      = ( k7_relat_1 @ sk_D_1 @ sk_C ) )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ~ ( v1_relat_1 @ sk_D_1 )
    | ( sk_D_1
      = ( k7_relat_1 @ sk_D_1 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('67',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( sk_D_1
      = ( k7_relat_1 @ sk_D_1 @ sk_C ) )
    | ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( sk_D_1
      = ( k7_relat_1 @ sk_D_1 @ sk_C ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,
    ( ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
    | ( sk_D_1
      = ( k7_relat_1 @ sk_D_1 @ sk_C ) )
    | ( v1_xboole_0 @ sk_C ) ),
    inference(simplify,[status(thm)],['67'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['33','34'])).

thf('70',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_C )
      | ( sk_D_1
        = ( k7_relat_1 @ sk_D_1 @ sk_C ) )
      | ~ ( r2_hidden @ X0 @ sk_D_1 ) ) ),
    inference('sup-',[status(thm)],['68','69'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_1 )
      | ( sk_D_1
        = ( k7_relat_1 @ sk_D_1 @ X0 ) )
      | ( sk_D_1
        = ( k7_relat_1 @ sk_D_1 @ sk_C ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference('sup-',[status(thm)],['56','70'])).

thf('72',plain,(
    v1_relat_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['14','15'])).

thf('73',plain,(
    ! [X0: $i] :
      ( ( sk_D_1
        = ( k7_relat_1 @ sk_D_1 @ X0 ) )
      | ( sk_D_1
        = ( k7_relat_1 @ sk_D_1 @ sk_C ) )
      | ( v1_xboole_0 @ sk_C ) ) ),
    inference(demod,[status(thm)],['71','72'])).

thf('74',plain,
    ( ( v1_xboole_0 @ sk_C )
    | ( sk_D_1
      = ( k7_relat_1 @ sk_D_1 @ sk_C ) ) ),
    inference(condensation,[status(thm)],['73'])).

thf('75',plain,(
    ~ ( r2_relset_1 @ sk_B @ sk_A @ ( k7_relat_1 @ sk_D_1 @ sk_C ) @ sk_D_1 ) ),
    inference(demod,[status(thm)],['0','3'])).

thf('76',plain,
    ( ~ ( r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ sk_D_1 )
    | ( v1_xboole_0 @ sk_C ) ),
    inference('sup-',[status(thm)],['74','75'])).

thf('77',plain,(
    m1_subset_1 @ sk_D_1 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_A ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( ( r2_relset_1 @ A @ B @ C @ D )
      <=> ( C = D ) ) ) )).

thf('78',plain,(
    ! [X13: $i,X14: $i,X15: $i,X16: $i] :
      ( ~ ( m1_subset_1 @ X13 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) )
      | ( r2_relset_1 @ X14 @ X15 @ X13 @ X16 )
      | ( X13 != X16 ) ) ),
    inference(cnf,[status(esa)],[redefinition_r2_relset_1])).

thf('79',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ( r2_relset_1 @ X14 @ X15 @ X16 @ X16 )
      | ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X14 @ X15 ) ) ) ) ),
    inference(simplify,[status(thm)],['78'])).

thf('80',plain,(
    r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['77','79'])).

thf('81',plain,(
    v1_xboole_0 @ sk_C ),
    inference(demod,[status(thm)],['76','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ~ ( r2_hidden @ X0 @ sk_B ) ),
    inference(demod,[status(thm)],['55','81'])).

thf('83',plain,(
    ! [X0: $i] :
      ( sk_D_1
      = ( k7_relat_1 @ sk_D_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['50','82'])).

thf('84',plain,(
    r2_relset_1 @ sk_B @ sk_A @ sk_D_1 @ sk_D_1 ),
    inference('sup-',[status(thm)],['77','79'])).

thf('85',plain,(
    $false ),
    inference(demod,[status(thm)],['4','83','84'])).


%------------------------------------------------------------------------------
