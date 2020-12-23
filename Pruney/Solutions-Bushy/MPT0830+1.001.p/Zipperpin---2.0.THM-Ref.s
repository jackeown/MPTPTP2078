%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0830+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox2/benchmark/theBenchmark.p /export/starexec/sandbox2/tmp/tmp.WefqoY8yhq

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:52:33 EST 2020

% Result     : Theorem 11.82s
% Output     : Refutation 11.82s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 691 expanded)
%              Number of leaves         :   25 ( 190 expanded)
%              Depth                    :   38
%              Number of atoms          : 1630 (10374 expanded)
%              Number of equality atoms :   41 ( 243 expanded)
%              Maximal formula depth    :   16 (   9 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_C_1_type,type,(
    sk_C_1: $i )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(sk_C_type,type,(
    sk_C: $i > $i > $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_E_type,type,(
    sk_E: $i > $i > $i > $i )).

thf(k5_relset_1_type,type,(
    k5_relset_1: $i > $i > $i > $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k7_relat_1_type,type,(
    k7_relat_1: $i > $i > $i )).

thf(v1_relat_1_type,type,(
    v1_relat_1: $i > $o )).

thf(sk_D_2_type,type,(
    sk_D_2: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_D_1_type,type,(
    sk_D_1: $i > $i > $i )).

thf(t33_relset_1,conjecture,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
     => ( m1_subset_1 @ ( k5_relset_1 @ A @ C @ D @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i,D: $i] :
        ( ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ C ) ) )
       => ( m1_subset_1 @ ( k5_relset_1 @ A @ C @ D @ B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ B @ C ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t33_relset_1])).

thf('0',plain,(
    ~ ( m1_subset_1 @ ( k5_relset_1 @ sk_A @ sk_C_1 @ sk_D_2 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(redefinition_k5_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( ( k5_relset_1 @ A @ B @ C @ D )
        = ( k7_relat_1 @ C @ D ) ) ) )).

thf('2',plain,(
    ! [X16: $i,X17: $i,X18: $i,X19: $i] :
      ( ~ ( m1_subset_1 @ X16 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X17 @ X18 ) ) )
      | ( ( k5_relset_1 @ X17 @ X18 @ X16 @ X19 )
        = ( k7_relat_1 @ X16 @ X19 ) ) ) ),
    inference(cnf,[status(esa)],[redefinition_k5_relset_1])).

thf('3',plain,(
    ! [X0: $i] :
      ( ( k5_relset_1 @ sk_A @ sk_C_1 @ sk_D_2 @ X0 )
      = ( k7_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ~ ( m1_subset_1 @ ( k7_relat_1 @ sk_D_2 @ sk_B ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_B @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['0','3'])).

thf(d3_relat_1,axiom,(
    ! [A: $i] :
      ( ( v1_relat_1 @ A )
     => ! [B: $i] :
          ( ( r1_tarski @ A @ B )
        <=> ! [C: $i,D: $i] :
              ( ( r2_hidden @ ( k4_tarski @ C @ D ) @ A )
             => ( r2_hidden @ ( k4_tarski @ C @ D ) @ B ) ) ) ) )).

thf('5',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X9 @ X10 ) @ ( sk_D_1 @ X9 @ X10 ) ) @ X10 )
      | ( r1_tarski @ X10 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf(dt_k7_relat_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( v1_relat_1 @ A )
     => ( v1_relat_1 @ ( k7_relat_1 @ A @ B ) ) ) )).

thf('6',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('7',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

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

thf('8',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X5 @ X4 ) @ ( sk_E @ X3 @ X5 @ X4 ) ) @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X5 @ X4 ) @ ( sk_E @ X3 @ X5 @ X4 ) ) @ X4 )
      | ( X3
        = ( k7_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d11_relat_1])).

thf('9',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X1 @ X0 ) @ ( sk_E @ X0 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(eq_fact,[status(thm)],['8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X1 @ X0 ) @ ( sk_E @ X0 @ X1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('11',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( X3
       != ( k7_relat_1 @ X4 @ X5 ) )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d11_relat_1])).

thf('12',plain,(
    ! [X4: $i,X5: $i,X6: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k7_relat_1 @ X4 @ X5 ) )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( sk_D @ ( k7_relat_1 @ X1 @ X0 ) @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['10','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( sk_D @ ( k7_relat_1 @ X1 @ X0 ) @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ( r2_hidden @ ( sk_D @ ( k7_relat_1 @ X1 @ X0 ) @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['7','14'])).

thf('16',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k7_relat_1 @ X1 @ X0 ) @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('17',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X1 @ X0 ) @ ( sk_E @ X0 @ X1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X1 @ X0 ) @ ( sk_E @ X0 @ X1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['9'])).

thf('19',plain,(
    ! [X3: $i,X4: $i,X5: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X5 @ X4 ) @ ( sk_E @ X3 @ X5 @ X4 ) ) @ X3 )
      | ~ ( r2_hidden @ ( sk_D @ X3 @ X5 @ X4 ) @ X5 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X3 @ X5 @ X4 ) @ ( sk_E @ X3 @ X5 @ X4 ) ) @ X4 )
      | ( X3
        = ( k7_relat_1 @ X4 @ X5 ) )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d11_relat_1])).

thf('20',plain,(
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
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ ( k4_tarski @ ( sk_D @ X0 @ X1 @ X0 ) @ ( sk_E @ X0 @ X1 @ X0 ) ) @ X0 )
      | ( X0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['20'])).

thf('22',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 )
      | ( X0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 ) ) ),
    inference('sup-',[status(thm)],['17','21'])).

thf('23',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('24',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['16','23'])).

thf('25',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['24'])).

thf('26',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('27',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('29',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('30',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('31',plain,(
    ! [X25: $i,X26: $i] :
      ( ( r1_tarski @ X25 @ X26 )
      | ~ ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X26 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('32',plain,(
    r1_tarski @ sk_D_2 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ),
    inference('sup-',[status(thm)],['30','31'])).

thf('33',plain,(
    ! [X14: $i,X15: $i] :
      ( ~ ( v1_relat_1 @ X14 )
      | ( v1_relat_1 @ ( k7_relat_1 @ X14 @ X15 ) ) ) ),
    inference(cnf,[status(esa)],[dt_k7_relat_1])).

thf('34',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X9 @ X10 ) @ ( sk_D_1 @ X9 @ X10 ) ) @ X10 )
      | ( r1_tarski @ X10 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('35',plain,(
    ! [X3: $i,X4: $i,X5: $i,X6: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X3 )
      | ( X3
       != ( k7_relat_1 @ X4 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ X3 )
      | ~ ( v1_relat_1 @ X4 ) ) ),
    inference(cnf,[status(esa)],[d11_relat_1])).

thf('36',plain,(
    ! [X4: $i,X5: $i,X6: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k7_relat_1 @ X4 @ X5 ) )
      | ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ X4 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['35'])).

thf('37',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['34','36'])).

thf('38',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ X1 )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['37'])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ X1 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference('sup-',[status(thm)],['33','38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) @ ( sk_D_1 @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) ) @ X1 )
      | ( r1_tarski @ ( k7_relat_1 @ X1 @ X0 ) @ X2 )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['39'])).

thf('41',plain,(
    ! [X10: $i,X11: $i,X12: $i,X13: $i] :
      ( ~ ( r1_tarski @ X10 @ X11 )
      | ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ X11 )
      | ~ ( r2_hidden @ ( k4_tarski @ X12 @ X13 ) @ X10 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('42',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( v1_relat_1 @ X0 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( sk_D_1 @ X2 @ ( k7_relat_1 @ X0 @ X1 ) ) ) @ X3 )
      | ~ ( r1_tarski @ X0 @ X3 ) ) ),
    inference('sup-',[status(thm)],['40','41'])).

thf('43',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ~ ( r1_tarski @ X0 @ X3 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X2 @ ( k7_relat_1 @ X0 @ X1 ) ) @ ( sk_D_1 @ X2 @ ( k7_relat_1 @ X0 @ X1 ) ) ) @ X3 )
      | ( r1_tarski @ ( k7_relat_1 @ X0 @ X1 ) @ X2 )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['42'])).

thf('44',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ sk_D_2 )
      | ( r1_tarski @ ( k7_relat_1 @ sk_D_2 @ X1 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k7_relat_1 @ sk_D_2 @ X1 ) ) @ ( sk_D_1 @ X0 @ ( k7_relat_1 @ sk_D_2 @ X1 ) ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['32','43'])).

thf('45',plain,(
    m1_subset_1 @ sk_D_2 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc1_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
     => ( v1_relat_1 @ C ) ) )).

thf('46',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('47',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('48',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D_2 @ X1 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k7_relat_1 @ sk_D_2 @ X1 ) ) @ ( sk_D_1 @ X0 @ ( k7_relat_1 @ sk_D_2 @ X1 ) ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['44','47'])).

thf('49',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X9 @ X10 ) @ ( sk_D_1 @ X9 @ X10 ) ) @ X9 )
      | ( r1_tarski @ X10 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('50',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) )
      | ( r1_tarski @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['48','49'])).

thf('51',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) )
      | ( r1_tarski @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(simplify,[status(thm)],['50'])).

thf('52',plain,(
    ! [X0: $i] :
      ( ~ ( v1_relat_1 @ sk_D_2 )
      | ( r1_tarski @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['29','51'])).

thf('53',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('54',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ),
    inference(demod,[status(thm)],['52','53'])).

thf('55',plain,(
    ! [X25: $i,X27: $i] :
      ( ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( r1_tarski @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('56',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_relat_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X2 ) ) ) ) ),
    inference(cnf,[status(esa)],[cc1_relset_1])).

thf('58',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ X1 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 ) ) ) ),
    inference(clc,[status(thm)],['25','26'])).

thf('60',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k7_relat_1 @ X1 @ X0 ) @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ( ( k7_relat_1 @ X1 @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X2 ) )
      | ~ ( v1_relat_1 @ X1 ) ) ),
    inference(simplify,[status(thm)],['15'])).

thf('61',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 ) @ X2 @ ( k7_relat_1 @ X1 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ X1 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ X1 @ X0 ) @ X0 ) @ X2 ) ) ) ),
    inference('sup+',[status(thm)],['59','60'])).

thf('62',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X0 ) @ X1 ) )
      | ~ ( v1_relat_1 @ sk_D_2 )
      | ( r2_hidden @ ( sk_D @ ( k7_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X0 ) @ X1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['58','61'])).

thf('63',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('64',plain,(
    ! [X0: $i,X1: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X0 ) @ X1 ) )
      | ( r2_hidden @ ( sk_D @ ( k7_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X0 ) @ X1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['62','63'])).

thf('65',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) ) @ X0 )
      | ~ ( v1_relat_1 @ sk_D_2 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X0 ) @ X1 ) ) ) ),
    inference('sup+',[status(thm)],['28','64'])).

thf('66',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('67',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r2_hidden @ ( sk_D @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) ) @ X0 )
      | ( ( k7_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X0 ) @ X1 ) ) ) ),
    inference(demod,[status(thm)],['65','66'])).

thf('68',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ ( sk_D @ X0 @ X1 @ X0 ) @ X1 )
      | ( X0
        = ( k7_relat_1 @ X0 @ X1 ) )
      | ~ ( v1_relat_1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['22'])).

thf('69',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) )
      | ( ( k7_relat_1 @ sk_D_2 @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['67','68'])).

thf('70',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('71',plain,(
    ! [X0: $i] :
      ( ( ( k7_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X0 ) @ X0 ) )
      | ( ( k7_relat_1 @ sk_D_2 @ X0 )
        = ( k7_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X0 )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X0 ) @ X0 ) ) ),
    inference(condensation,[status(thm)],['71'])).

thf('73',plain,(
    ! [X4: $i,X5: $i,X6: $i,X8: $i] :
      ( ~ ( v1_relat_1 @ X4 )
      | ~ ( r2_hidden @ ( k4_tarski @ X6 @ X8 ) @ ( k7_relat_1 @ X4 @ X5 ) )
      | ( r2_hidden @ X6 @ X5 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ X4 @ X5 ) ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('74',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k7_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X0 ) @ X0 ) )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['72','73'])).

thf('75',plain,(
    ! [X0: $i] :
      ( ( k7_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X0 )
      = ( k7_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X0 ) @ X0 ) ) ),
    inference(condensation,[status(thm)],['71'])).

thf('76',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k7_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X0 ) )
      | ( r2_hidden @ X2 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X0 ) ) ) ),
    inference(demod,[status(thm)],['74','75'])).

thf('77',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X2 @ X0 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X0 ) )
      | ~ ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k7_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X0 ) ) ) ),
    inference(simplify,[status(thm)],['76'])).

thf('78',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k7_relat_1 @ sk_D_2 @ X0 ) )
      | ~ ( v1_relat_1 @ sk_D_2 )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X0 ) )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['27','77'])).

thf('79',plain,(
    v1_relat_1 @ sk_D_2 ),
    inference('sup-',[status(thm)],['45','46'])).

thf('80',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ X2 @ X1 ) @ ( k7_relat_1 @ sk_D_2 @ X0 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X0 ) )
      | ( r2_hidden @ X2 @ X0 ) ) ),
    inference(demod,[status(thm)],['78','79'])).

thf('81',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) )
      | ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ ( k7_relat_1 @ sk_D_2 @ X0 ) ) ) ),
    inference('sup-',[status(thm)],['6','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('83',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ X1 @ X0 )
      | ~ ( r2_hidden @ ( k4_tarski @ X1 @ X2 ) @ ( k7_relat_1 @ sk_D_2 @ X0 ) ) ) ),
    inference(demod,[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) )
      | ( r1_tarski @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['5','83'])).

thf('85',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('86',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_C @ X1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) ) @ X0 ) ) ),
    inference(demod,[status(thm)],['84','85'])).

thf('87',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D_2 @ X1 ) @ X0 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X0 @ ( k7_relat_1 @ sk_D_2 @ X1 ) ) @ ( sk_D_1 @ X0 @ ( k7_relat_1 @ sk_D_2 @ X1 ) ) ) @ ( k2_zfmisc_1 @ sk_A @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['44','47'])).

thf(t106_zfmisc_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( r2_hidden @ ( k4_tarski @ A @ B ) @ ( k2_zfmisc_1 @ C @ D ) )
    <=> ( ( r2_hidden @ A @ C )
        & ( r2_hidden @ B @ D ) ) ) )).

thf('88',plain,(
    ! [X20: $i,X21: $i,X22: $i,X23: $i] :
      ( ( r2_hidden @ X22 @ X23 )
      | ~ ( r2_hidden @ ( k4_tarski @ X20 @ X22 ) @ ( k2_zfmisc_1 @ X21 @ X23 ) ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('89',plain,(
    ! [X0: $i,X1: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X1 )
      | ( r2_hidden @ ( sk_D_1 @ X1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) ) @ sk_C_1 ) ) ),
    inference('sup-',[status(thm)],['87','88'])).

thf('90',plain,(
    ! [X20: $i,X21: $i,X22: $i,X24: $i] :
      ( ( r2_hidden @ ( k4_tarski @ X20 @ X22 ) @ ( k2_zfmisc_1 @ X21 @ X24 ) )
      | ~ ( r2_hidden @ X22 @ X24 )
      | ~ ( r2_hidden @ X20 @ X21 ) ) ),
    inference(cnf,[status(esa)],[t106_zfmisc_1])).

thf('91',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X1 )
      | ~ ( r2_hidden @ X3 @ X2 )
      | ( r2_hidden @ ( k4_tarski @ X3 @ ( sk_D_1 @ X1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) ) ) @ ( k2_zfmisc_1 @ X2 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['89','90'])).

thf('92',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ X1 )
      | ( r2_hidden @ ( k4_tarski @ ( sk_C @ X1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) ) @ ( sk_D_1 @ X3 @ ( k7_relat_1 @ sk_D_2 @ X2 ) ) ) @ ( k2_zfmisc_1 @ X0 @ sk_C_1 ) )
      | ( r1_tarski @ ( k7_relat_1 @ sk_D_2 @ X2 ) @ X3 ) ) ),
    inference('sup-',[status(thm)],['86','91'])).

thf('93',plain,(
    ! [X9: $i,X10: $i] :
      ( ~ ( r2_hidden @ ( k4_tarski @ ( sk_C @ X9 @ X10 ) @ ( sk_D_1 @ X9 @ X10 ) ) @ X9 )
      | ( r1_tarski @ X10 @ X9 )
      | ~ ( v1_relat_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[d3_relat_1])).

thf('94',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ sk_C_1 ) )
      | ( r1_tarski @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ sk_C_1 ) )
      | ~ ( v1_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) )
      | ( r1_tarski @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    ! [X0: $i] :
      ( v1_relat_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) ) ),
    inference('sup-',[status(thm)],['56','57'])).

thf('96',plain,(
    ! [X0: $i] :
      ( ( r1_tarski @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ sk_C_1 ) )
      | ( r1_tarski @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ sk_C_1 ) )
      | ( r1_tarski @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ sk_C_1 ) ) ) ),
    inference(demod,[status(thm)],['94','95'])).

thf('97',plain,(
    ! [X0: $i] :
      ( r1_tarski @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ ( k2_zfmisc_1 @ X0 @ sk_C_1 ) ) ),
    inference(simplify,[status(thm)],['96'])).

thf('98',plain,(
    ! [X25: $i,X27: $i] :
      ( ( m1_subset_1 @ X25 @ ( k1_zfmisc_1 @ X27 ) )
      | ~ ( r1_tarski @ X25 @ X27 ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('99',plain,(
    ! [X0: $i] :
      ( m1_subset_1 @ ( k7_relat_1 @ sk_D_2 @ X0 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X0 @ sk_C_1 ) ) ) ),
    inference('sup-',[status(thm)],['97','98'])).

thf('100',plain,(
    $false ),
    inference(demod,[status(thm)],['4','99'])).


%------------------------------------------------------------------------------
