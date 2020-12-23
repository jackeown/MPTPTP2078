%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZZENKE4Nw4

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:59:04 EST 2020

% Result     : Theorem 0.56s
% Output     : Refutation 0.56s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 216 expanded)
%              Number of leaves         :   30 (  75 expanded)
%              Depth                    :   17
%              Number of atoms          :  882 (2774 expanded)
%              Number of equality atoms :   66 ( 177 expanded)
%              Maximal formula depth    :   17 (   6 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(r1_tarski_type,type,(
    r1_tarski: $i > $i > $o )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(sk_B_3_type,type,(
    sk_B_3: $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(r2_relset_1_type,type,(
    r2_relset_1: $i > $i > $i > $i > $o )).

thf(k4_tarski_type,type,(
    k4_tarski: $i > $i > $i )).

thf(sk_B_2_type,type,(
    sk_B_2: $i > $i )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(sk_C_type,type,(
    sk_C: $i )).

thf(r1_partfun1_type,type,(
    r1_partfun1: $i > $i > $o )).

thf(v1_partfun1_type,type,(
    v1_partfun1: $i > $i > $o )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(k1_xboole_0_type,type,(
    k1_xboole_0: $i )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(sk_B_type,type,(
    sk_B: $i > $i )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(t142_funct_2,conjecture,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( v1_funct_2 @ D @ A @ B )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( r1_partfun1 @ C @ D )
           => ( ( ( B = k1_xboole_0 )
                & ( A != k1_xboole_0 ) )
              | ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i,C: $i] :
        ( ( ( v1_funct_1 @ C )
          & ( v1_funct_2 @ C @ A @ B )
          & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
       => ! [D: $i] :
            ( ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
           => ( ( r1_partfun1 @ C @ D )
             => ( ( ( B = k1_xboole_0 )
                  & ( A != k1_xboole_0 ) )
                | ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ),
    inference('cnf.neg',[status(esa)],[t142_funct_2])).

thf('0',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_3 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('1',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('2',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(cc5_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ! [C: $i] :
          ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
         => ( ( ( v1_funct_1 @ C )
              & ( v1_funct_2 @ C @ A @ B ) )
           => ( ( v1_funct_1 @ C )
              & ( v1_partfun1 @ C @ A ) ) ) ) ) )).

thf('3',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( v1_partfun1 @ X32 @ X33 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( v1_funct_1 @ X32 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('4',plain,
    ( ( v1_xboole_0 @ sk_B_3 )
    | ~ ( v1_funct_1 @ sk_D )
    | ~ ( v1_funct_2 @ sk_D @ sk_A @ sk_B_3 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference('sup-',[status(thm)],['2','3'])).

thf('5',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('6',plain,(
    v1_funct_2 @ sk_D @ sk_A @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('7',plain,
    ( ( v1_xboole_0 @ sk_B_3 )
    | ( v1_partfun1 @ sk_D @ sk_A ) ),
    inference(demod,[status(thm)],['4','5','6'])).

thf('8',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(t148_partfun1,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( v1_funct_1 @ C )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ! [D: $i] :
          ( ( ( v1_funct_1 @ D )
            & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
         => ( ( ( v1_partfun1 @ C @ A )
              & ( v1_partfun1 @ D @ A )
              & ( r1_partfun1 @ C @ D ) )
           => ( C = D ) ) ) ) )).

thf('9',plain,(
    ! [X35: $i,X36: $i,X37: $i,X38: $i] :
      ( ~ ( v1_funct_1 @ X35 )
      | ~ ( m1_subset_1 @ X35 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ( X38 = X35 )
      | ~ ( r1_partfun1 @ X38 @ X35 )
      | ~ ( v1_partfun1 @ X35 @ X36 )
      | ~ ( v1_partfun1 @ X38 @ X36 )
      | ~ ( m1_subset_1 @ X38 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X36 @ X37 ) ) )
      | ~ ( v1_funct_1 @ X38 ) ) ),
    inference(cnf,[status(esa)],[t148_partfun1])).

thf('10',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D )
      | ~ ( v1_funct_1 @ sk_D ) ) ),
    inference('sup-',[status(thm)],['8','9'])).

thf('11',plain,(
    v1_funct_1 @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('12',plain,(
    ! [X0: $i] :
      ( ~ ( v1_funct_1 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( v1_partfun1 @ sk_D @ sk_A )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ( X0 = sk_D ) ) ),
    inference(demod,[status(thm)],['10','11'])).

thf('13',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ sk_B_3 )
      | ( X0 = sk_D )
      | ~ ( r1_partfun1 @ X0 @ sk_D )
      | ~ ( v1_partfun1 @ X0 @ sk_A )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) )
      | ~ ( v1_funct_1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['7','12'])).

thf('14',plain,
    ( ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_partfun1 @ sk_C @ sk_A )
    | ~ ( r1_partfun1 @ sk_C @ sk_D )
    | ( sk_C = sk_D )
    | ( v1_xboole_0 @ sk_B_3 ) ),
    inference('sup-',[status(thm)],['1','13'])).

thf('15',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('16',plain,(
    r1_partfun1 @ sk_C @ sk_D ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('17',plain,
    ( ~ ( v1_partfun1 @ sk_C @ sk_A )
    | ( sk_C = sk_D )
    | ( v1_xboole_0 @ sk_B_3 ) ),
    inference(demod,[status(thm)],['14','15','16'])).

thf('18',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('19',plain,(
    ! [X32: $i,X33: $i,X34: $i] :
      ( ~ ( m1_subset_1 @ X32 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X33 @ X34 ) ) )
      | ( v1_partfun1 @ X32 @ X33 )
      | ~ ( v1_funct_2 @ X32 @ X33 @ X34 )
      | ~ ( v1_funct_1 @ X32 )
      | ( v1_xboole_0 @ X34 ) ) ),
    inference(cnf,[status(esa)],[cc5_funct_2])).

thf('20',plain,
    ( ( v1_xboole_0 @ sk_B_3 )
    | ~ ( v1_funct_1 @ sk_C )
    | ~ ( v1_funct_2 @ sk_C @ sk_A @ sk_B_3 )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf('21',plain,(
    v1_funct_1 @ sk_C ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('22',plain,(
    v1_funct_2 @ sk_C @ sk_A @ sk_B_3 ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('23',plain,
    ( ( v1_xboole_0 @ sk_B_3 )
    | ( v1_partfun1 @ sk_C @ sk_A ) ),
    inference(demod,[status(thm)],['20','21','22'])).

thf('24',plain,
    ( ( v1_xboole_0 @ sk_B_3 )
    | ( sk_C = sk_D ) ),
    inference(clc,[status(thm)],['17','23'])).

thf(t9_mcart_1,axiom,(
    ! [A: $i] :
      ~ ( ( A != k1_xboole_0 )
        & ! [B: $i] :
            ~ ( ( r2_hidden @ B @ A )
              & ! [C: $i,D: $i] :
                  ~ ( ( ( r2_hidden @ C @ A )
                      | ( r2_hidden @ D @ A ) )
                    & ( B
                      = ( k4_tarski @ C @ D ) ) ) ) ) )).

thf('25',plain,(
    ! [X29: $i] :
      ( ( X29 = k1_xboole_0 )
      | ( r2_hidden @ ( sk_B_2 @ X29 ) @ X29 ) ) ),
    inference(cnf,[status(esa)],[t9_mcart_1])).

thf(d1_xboole_0,axiom,(
    ! [A: $i] :
      ( ( v1_xboole_0 @ A )
    <=> ! [B: $i] :
          ~ ( r2_hidden @ B @ A ) ) )).

thf('26',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('27',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('28',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('29',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('30',plain,(
    ! [X0: $i,X1: $i] :
      ( ( X1 = X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference('sup+',[status(thm)],['27','28'])).

thf('31',plain,
    ( ( sk_B_3 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('32',plain,
    ( ( sk_B_3 != k1_xboole_0 )
   <= ( sk_B_3 != k1_xboole_0 ) ),
    inference(split,[status(esa)],['31'])).

thf('33',plain,
    ( ! [X0: $i] :
        ( ( X0 != k1_xboole_0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ sk_B_3 ) )
   <= ( sk_B_3 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['30','32'])).

thf('34',plain,
    ( ( ~ ( v1_xboole_0 @ sk_B_3 )
      | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_B_3 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['33'])).

thf('35',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ X0 )
        | ~ ( v1_xboole_0 @ sk_B_3 )
        | ~ ( v1_xboole_0 @ k1_xboole_0 ) )
   <= ( sk_B_3 != k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['29','34'])).

thf('36',plain,
    ( ! [X0: $i] :
        ( ~ ( v1_xboole_0 @ k1_xboole_0 )
        | ~ ( v1_xboole_0 @ sk_B_3 )
        | ~ ( v1_xboole_0 @ X0 ) )
   <= ( sk_B_3 != k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['35'])).

thf(t4_subset_1,axiom,(
    ! [A: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ) )).

thf('37',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(reflexivity_r2_relset_1,axiom,(
    ! [A: $i,B: $i,C: $i,D: $i] :
      ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) )
        & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) )
     => ( r2_relset_1 @ A @ B @ C @ C ) ) )).

thf('38',plain,(
    ! [X25: $i,X26: $i,X27: $i,X28: $i] :
      ( ( r2_relset_1 @ X25 @ X26 @ X27 @ X27 )
      | ~ ( m1_subset_1 @ X27 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) )
      | ~ ( m1_subset_1 @ X28 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X25 @ X26 ) ) ) ) ),
    inference(cnf,[status(esa)],[reflexivity_r2_relset_1])).

thf('39',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['38'])).

thf('40',plain,(
    ! [X0: $i,X1: $i] :
      ( r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['37','39'])).

thf(t113_zfmisc_1,axiom,(
    ! [A: $i,B: $i] :
      ( ( ( k2_zfmisc_1 @ A @ B )
        = k1_xboole_0 )
    <=> ( ( A = k1_xboole_0 )
        | ( B = k1_xboole_0 ) ) ) )).

thf('41',plain,(
    ! [X7: $i,X8: $i] :
      ( ( ( k2_zfmisc_1 @ X7 @ X8 )
        = k1_xboole_0 )
      | ( X7 != k1_xboole_0 ) ) ),
    inference(cnf,[status(esa)],[t113_zfmisc_1])).

thf('42',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('43',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['31'])).

thf('44',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('45',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_3 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['43','44'])).

thf('46',plain,
    ( ( m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['42','45'])).

thf(t3_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) )
    <=> ( r1_tarski @ A @ B ) ) )).

thf('47',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('48',plain,
    ( ( r1_tarski @ sk_C @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['46','47'])).

thf('49',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf('50',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('51',plain,(
    ! [X0: $i] :
      ( r1_tarski @ k1_xboole_0 @ X0 ) ),
    inference('sup-',[status(thm)],['49','50'])).

thf(d10_xboole_0,axiom,(
    ! [A: $i,B: $i] :
      ( ( A = B )
    <=> ( ( r1_tarski @ A @ B )
        & ( r1_tarski @ B @ A ) ) ) )).

thf('52',plain,(
    ! [X3: $i,X5: $i] :
      ( ( X3 = X5 )
      | ~ ( r1_tarski @ X5 @ X3 )
      | ~ ( r1_tarski @ X3 @ X5 ) ) ),
    inference(cnf,[status(esa)],[d10_xboole_0])).

thf('53',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('54',plain,
    ( ( sk_C = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['48','53'])).

thf('55',plain,(
    ~ ( r2_relset_1 @ sk_A @ sk_B_3 @ sk_C @ sk_D ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('56',plain,
    ( ~ ( r2_relset_1 @ sk_A @ sk_B_3 @ k1_xboole_0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['54','55'])).

thf('57',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['31'])).

thf('58',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_3 @ k1_xboole_0 @ sk_D )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['56','57'])).

thf('59',plain,(
    ! [X8: $i] :
      ( ( k2_zfmisc_1 @ k1_xboole_0 @ X8 )
      = k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['41'])).

thf('60',plain,
    ( ( sk_A = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['31'])).

thf('61',plain,(
    m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('62',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ k1_xboole_0 @ sk_B_3 ) ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['60','61'])).

thf('63',plain,
    ( ( m1_subset_1 @ sk_D @ ( k1_zfmisc_1 @ k1_xboole_0 ) )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['59','62'])).

thf('64',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('65',plain,
    ( ( r1_tarski @ sk_D @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['63','64'])).

thf('66',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('67',plain,
    ( ( sk_D = k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['65','66'])).

thf('68',plain,
    ( ~ ( r2_relset_1 @ k1_xboole_0 @ sk_B_3 @ k1_xboole_0 @ k1_xboole_0 )
   <= ( sk_A = k1_xboole_0 ) ),
    inference(demod,[status(thm)],['58','67'])).

thf('69',plain,(
    sk_A != k1_xboole_0 ),
    inference('sup-',[status(thm)],['40','68'])).

thf('70',plain,
    ( ( sk_B_3 != k1_xboole_0 )
    | ( sk_A = k1_xboole_0 ) ),
    inference(split,[status(esa)],['31'])).

thf('71',plain,(
    sk_B_3 != k1_xboole_0 ),
    inference('sat_resolution*',[status(thm)],['69','70'])).

thf('72',plain,(
    ! [X0: $i] :
      ( ~ ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ sk_B_3 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(simpl_trail,[status(thm)],['36','71'])).

thf('73',plain,
    ( ~ ( v1_xboole_0 @ k1_xboole_0 )
    | ~ ( v1_xboole_0 @ sk_B_3 ) ),
    inference(condensation,[status(thm)],['72'])).

thf('74',plain,(
    ! [X0: $i] :
      ( ( X0 = k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference('sup-',[status(thm)],['25','26'])).

thf('75',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('76',plain,(
    ! [X10: $i] :
      ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t4_subset_1])).

thf(t4_subset,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( ( r2_hidden @ A @ B )
        & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) )
     => ( m1_subset_1 @ A @ C ) ) )).

thf('77',plain,(
    ! [X14: $i,X15: $i,X16: $i] :
      ( ~ ( r2_hidden @ X14 @ X15 )
      | ~ ( m1_subset_1 @ X15 @ ( k1_zfmisc_1 @ X16 ) )
      | ( m1_subset_1 @ X14 @ X16 ) ) ),
    inference(cnf,[status(esa)],[t4_subset])).

thf('78',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_subset_1 @ X1 @ X0 )
      | ~ ( r2_hidden @ X1 @ k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['76','77'])).

thf('79',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( m1_subset_1 @ ( sk_B @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['75','78'])).

thf('80',plain,(
    ! [X11: $i,X12: $i] :
      ( ( r1_tarski @ X11 @ X12 )
      | ~ ( m1_subset_1 @ X11 @ ( k1_zfmisc_1 @ X12 ) ) ) ),
    inference(cnf,[status(esa)],[t3_subset])).

thf('81',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ( r1_tarski @ ( sk_B @ k1_xboole_0 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['79','80'])).

thf('82',plain,(
    ! [X0: $i] :
      ( ~ ( r1_tarski @ X0 @ k1_xboole_0 )
      | ( X0 = k1_xboole_0 ) ) ),
    inference('sup-',[status(thm)],['51','52'])).

thf('83',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( ( sk_B @ k1_xboole_0 )
      = k1_xboole_0 ) ),
    inference('sup-',[status(thm)],['81','82'])).

thf('84',plain,(
    ! [X2: $i] :
      ( ( v1_xboole_0 @ X2 )
      | ( r2_hidden @ ( sk_B @ X2 ) @ X2 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('85',plain,
    ( ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ k1_xboole_0 )
    | ( v1_xboole_0 @ k1_xboole_0 ) ),
    inference('sup+',[status(thm)],['83','84'])).

thf('86',plain,
    ( ( v1_xboole_0 @ k1_xboole_0 )
    | ( r2_hidden @ k1_xboole_0 @ k1_xboole_0 ) ),
    inference(simplify,[status(thm)],['85'])).

thf('87',plain,(
    ! [X0: $i] :
      ( ( r2_hidden @ k1_xboole_0 @ X0 )
      | ~ ( v1_xboole_0 @ X0 )
      | ( v1_xboole_0 @ k1_xboole_0 ) ) ),
    inference('sup+',[status(thm)],['74','86'])).

thf('88',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( r2_hidden @ X0 @ X1 )
      | ~ ( v1_xboole_0 @ X1 ) ) ),
    inference(cnf,[status(esa)],[d1_xboole_0])).

thf('89',plain,(
    ! [X0: $i] :
      ( ( v1_xboole_0 @ k1_xboole_0 )
      | ~ ( v1_xboole_0 @ X0 ) ) ),
    inference(clc,[status(thm)],['87','88'])).

thf('90',plain,(
    ~ ( v1_xboole_0 @ sk_B_3 ) ),
    inference(clc,[status(thm)],['73','89'])).

thf('91',plain,(
    sk_C = sk_D ),
    inference(clc,[status(thm)],['24','90'])).

thf('92',plain,(
    m1_subset_1 @ sk_C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ sk_A @ sk_B_3 ) ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('93',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_relset_1 @ X2 @ X1 @ X0 @ X0 )
      | ~ ( m1_subset_1 @ X0 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) ) ) ),
    inference(condensation,[status(thm)],['38'])).

thf('94',plain,(
    r2_relset_1 @ sk_A @ sk_B_3 @ sk_C @ sk_C ),
    inference('sup-',[status(thm)],['92','93'])).

thf('95',plain,(
    $false ),
    inference(demod,[status(thm)],['0','91','94'])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.ZZENKE4Nw4
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:21:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running portfolio for 600 s
% 0.13/0.34  % File         : /export/starexec/sandbox/benchmark/theBenchmark.p
% 0.13/0.34  % Number of cores: 8
% 0.13/0.34  % Python version: Python 3.6.8
% 0.13/0.35  % Running in FO mode
% 0.56/0.75  % Running /export/starexec/sandbox/solver/bin/fo/fo7.sh for 78
% 0.56/0.75  % Solved by: fo/fo7.sh
% 0.56/0.75  To remain in the chosen logic fragment, unification with booleans has been disabled.
% 0.56/0.75  % done 633 iterations in 0.302s
% 0.56/0.75  % SZS status Theorem for '/export/starexec/sandbox/benchmark/theBenchmark.p'
% 0.56/0.75  % SZS output start Refutation
% 0.56/0.75  thf(sk_D_type, type, sk_D: $i).
% 0.56/0.75  thf(r2_hidden_type, type, r2_hidden: $i > $i > $o).
% 0.56/0.75  thf(r1_tarski_type, type, r1_tarski: $i > $i > $o).
% 0.56/0.75  thf(k2_zfmisc_1_type, type, k2_zfmisc_1: $i > $i > $i).
% 0.56/0.75  thf(sk_B_3_type, type, sk_B_3: $i).
% 0.56/0.75  thf(sk_A_type, type, sk_A: $i).
% 0.56/0.75  thf(r2_relset_1_type, type, r2_relset_1: $i > $i > $i > $i > $o).
% 0.56/0.75  thf(k4_tarski_type, type, k4_tarski: $i > $i > $i).
% 0.56/0.75  thf(sk_B_2_type, type, sk_B_2: $i > $i).
% 0.56/0.75  thf(v1_xboole_0_type, type, v1_xboole_0: $i > $o).
% 0.56/0.75  thf(sk_C_type, type, sk_C: $i).
% 0.56/0.75  thf(r1_partfun1_type, type, r1_partfun1: $i > $i > $o).
% 0.56/0.75  thf(v1_partfun1_type, type, v1_partfun1: $i > $i > $o).
% 0.56/0.75  thf(v1_funct_1_type, type, v1_funct_1: $i > $o).
% 0.56/0.75  thf(k1_xboole_0_type, type, k1_xboole_0: $i).
% 0.56/0.75  thf(m1_subset_1_type, type, m1_subset_1: $i > $i > $o).
% 0.56/0.75  thf(v1_funct_2_type, type, v1_funct_2: $i > $i > $i > $o).
% 0.56/0.75  thf(sk_B_type, type, sk_B: $i > $i).
% 0.56/0.75  thf(k1_zfmisc_1_type, type, k1_zfmisc_1: $i > $i).
% 0.56/0.75  thf(t142_funct_2, conjecture,
% 0.56/0.75    (![A:$i,B:$i,C:$i]:
% 0.56/0.75     ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.56/0.75         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.56/0.75       ( ![D:$i]:
% 0.56/0.75         ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.56/0.75             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.56/0.75           ( ( r1_partfun1 @ C @ D ) =>
% 0.56/0.75             ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.56/0.75               ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ))).
% 0.56/0.75  thf(zf_stmt_0, negated_conjecture,
% 0.56/0.75    (~( ![A:$i,B:$i,C:$i]:
% 0.56/0.75        ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) & 
% 0.56/0.75            ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.56/0.75          ( ![D:$i]:
% 0.56/0.75            ( ( ( v1_funct_1 @ D ) & ( v1_funct_2 @ D @ A @ B ) & 
% 0.56/0.75                ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.56/0.75              ( ( r1_partfun1 @ C @ D ) =>
% 0.56/0.75                ( ( ( ( B ) = ( k1_xboole_0 ) ) & ( ( A ) != ( k1_xboole_0 ) ) ) | 
% 0.56/0.75                  ( r2_relset_1 @ A @ B @ C @ D ) ) ) ) ) ) )),
% 0.56/0.75    inference('cnf.neg', [status(esa)], [t142_funct_2])).
% 0.56/0.75  thf('0', plain, (~ (r2_relset_1 @ sk_A @ sk_B_3 @ sk_C @ sk_D)),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf('1', plain,
% 0.56/0.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf('2', plain,
% 0.56/0.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf(cc5_funct_2, axiom,
% 0.56/0.75    (![A:$i,B:$i]:
% 0.56/0.75     ( ( ~( v1_xboole_0 @ B ) ) =>
% 0.56/0.75       ( ![C:$i]:
% 0.56/0.75         ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) =>
% 0.56/0.75           ( ( ( v1_funct_1 @ C ) & ( v1_funct_2 @ C @ A @ B ) ) =>
% 0.56/0.75             ( ( v1_funct_1 @ C ) & ( v1_partfun1 @ C @ A ) ) ) ) ) ))).
% 0.56/0.75  thf('3', plain,
% 0.56/0.75      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.56/0.75         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.56/0.75          | (v1_partfun1 @ X32 @ X33)
% 0.56/0.75          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 0.56/0.75          | ~ (v1_funct_1 @ X32)
% 0.56/0.75          | (v1_xboole_0 @ X34))),
% 0.56/0.75      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.56/0.75  thf('4', plain,
% 0.56/0.75      (((v1_xboole_0 @ sk_B_3)
% 0.56/0.75        | ~ (v1_funct_1 @ sk_D)
% 0.56/0.75        | ~ (v1_funct_2 @ sk_D @ sk_A @ sk_B_3)
% 0.56/0.75        | (v1_partfun1 @ sk_D @ sk_A))),
% 0.56/0.75      inference('sup-', [status(thm)], ['2', '3'])).
% 0.56/0.75  thf('5', plain, ((v1_funct_1 @ sk_D)),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf('6', plain, ((v1_funct_2 @ sk_D @ sk_A @ sk_B_3)),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf('7', plain, (((v1_xboole_0 @ sk_B_3) | (v1_partfun1 @ sk_D @ sk_A))),
% 0.56/0.75      inference('demod', [status(thm)], ['4', '5', '6'])).
% 0.56/0.75  thf('8', plain,
% 0.56/0.75      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf(t148_partfun1, axiom,
% 0.56/0.75    (![A:$i,B:$i,C:$i]:
% 0.56/0.75     ( ( ( v1_funct_1 @ C ) & 
% 0.56/0.75         ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.56/0.75       ( ![D:$i]:
% 0.56/0.75         ( ( ( v1_funct_1 @ D ) & 
% 0.56/0.75             ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.56/0.75           ( ( ( v1_partfun1 @ C @ A ) & ( v1_partfun1 @ D @ A ) & 
% 0.56/0.75               ( r1_partfun1 @ C @ D ) ) =>
% 0.56/0.75             ( ( C ) = ( D ) ) ) ) ) ))).
% 0.56/0.75  thf('9', plain,
% 0.56/0.75      (![X35 : $i, X36 : $i, X37 : $i, X38 : $i]:
% 0.56/0.75         (~ (v1_funct_1 @ X35)
% 0.56/0.75          | ~ (m1_subset_1 @ X35 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.56/0.75          | ((X38) = (X35))
% 0.56/0.75          | ~ (r1_partfun1 @ X38 @ X35)
% 0.56/0.75          | ~ (v1_partfun1 @ X35 @ X36)
% 0.56/0.75          | ~ (v1_partfun1 @ X38 @ X36)
% 0.56/0.75          | ~ (m1_subset_1 @ X38 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X36 @ X37)))
% 0.56/0.75          | ~ (v1_funct_1 @ X38))),
% 0.56/0.75      inference('cnf', [status(esa)], [t148_partfun1])).
% 0.56/0.75  thf('10', plain,
% 0.56/0.75      (![X0 : $i]:
% 0.56/0.75         (~ (v1_funct_1 @ X0)
% 0.56/0.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))
% 0.56/0.75          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.56/0.75          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.56/0.75          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.56/0.75          | ((X0) = (sk_D))
% 0.56/0.75          | ~ (v1_funct_1 @ sk_D))),
% 0.56/0.75      inference('sup-', [status(thm)], ['8', '9'])).
% 0.56/0.75  thf('11', plain, ((v1_funct_1 @ sk_D)),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf('12', plain,
% 0.56/0.75      (![X0 : $i]:
% 0.56/0.75         (~ (v1_funct_1 @ X0)
% 0.56/0.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))
% 0.56/0.75          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.56/0.75          | ~ (v1_partfun1 @ sk_D @ sk_A)
% 0.56/0.75          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.56/0.75          | ((X0) = (sk_D)))),
% 0.56/0.75      inference('demod', [status(thm)], ['10', '11'])).
% 0.56/0.75  thf('13', plain,
% 0.56/0.75      (![X0 : $i]:
% 0.56/0.75         ((v1_xboole_0 @ sk_B_3)
% 0.56/0.75          | ((X0) = (sk_D))
% 0.56/0.75          | ~ (r1_partfun1 @ X0 @ sk_D)
% 0.56/0.75          | ~ (v1_partfun1 @ X0 @ sk_A)
% 0.56/0.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))
% 0.56/0.75          | ~ (v1_funct_1 @ X0))),
% 0.56/0.75      inference('sup-', [status(thm)], ['7', '12'])).
% 0.56/0.75  thf('14', plain,
% 0.56/0.75      ((~ (v1_funct_1 @ sk_C)
% 0.56/0.75        | ~ (v1_partfun1 @ sk_C @ sk_A)
% 0.56/0.75        | ~ (r1_partfun1 @ sk_C @ sk_D)
% 0.56/0.75        | ((sk_C) = (sk_D))
% 0.56/0.75        | (v1_xboole_0 @ sk_B_3))),
% 0.56/0.75      inference('sup-', [status(thm)], ['1', '13'])).
% 0.56/0.75  thf('15', plain, ((v1_funct_1 @ sk_C)),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf('16', plain, ((r1_partfun1 @ sk_C @ sk_D)),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf('17', plain,
% 0.56/0.75      ((~ (v1_partfun1 @ sk_C @ sk_A)
% 0.56/0.75        | ((sk_C) = (sk_D))
% 0.56/0.75        | (v1_xboole_0 @ sk_B_3))),
% 0.56/0.75      inference('demod', [status(thm)], ['14', '15', '16'])).
% 0.56/0.75  thf('18', plain,
% 0.56/0.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf('19', plain,
% 0.56/0.75      (![X32 : $i, X33 : $i, X34 : $i]:
% 0.56/0.75         (~ (m1_subset_1 @ X32 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X33 @ X34)))
% 0.56/0.75          | (v1_partfun1 @ X32 @ X33)
% 0.56/0.75          | ~ (v1_funct_2 @ X32 @ X33 @ X34)
% 0.56/0.75          | ~ (v1_funct_1 @ X32)
% 0.56/0.75          | (v1_xboole_0 @ X34))),
% 0.56/0.75      inference('cnf', [status(esa)], [cc5_funct_2])).
% 0.56/0.75  thf('20', plain,
% 0.56/0.75      (((v1_xboole_0 @ sk_B_3)
% 0.56/0.75        | ~ (v1_funct_1 @ sk_C)
% 0.56/0.75        | ~ (v1_funct_2 @ sk_C @ sk_A @ sk_B_3)
% 0.56/0.75        | (v1_partfun1 @ sk_C @ sk_A))),
% 0.56/0.75      inference('sup-', [status(thm)], ['18', '19'])).
% 0.56/0.75  thf('21', plain, ((v1_funct_1 @ sk_C)),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf('22', plain, ((v1_funct_2 @ sk_C @ sk_A @ sk_B_3)),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf('23', plain, (((v1_xboole_0 @ sk_B_3) | (v1_partfun1 @ sk_C @ sk_A))),
% 0.56/0.75      inference('demod', [status(thm)], ['20', '21', '22'])).
% 0.56/0.75  thf('24', plain, (((v1_xboole_0 @ sk_B_3) | ((sk_C) = (sk_D)))),
% 0.56/0.75      inference('clc', [status(thm)], ['17', '23'])).
% 0.56/0.75  thf(t9_mcart_1, axiom,
% 0.56/0.75    (![A:$i]:
% 0.56/0.75     ( ~( ( ( A ) != ( k1_xboole_0 ) ) & 
% 0.56/0.75          ( ![B:$i]:
% 0.56/0.75            ( ~( ( r2_hidden @ B @ A ) & 
% 0.56/0.75                 ( ![C:$i,D:$i]:
% 0.56/0.75                   ( ~( ( ( r2_hidden @ C @ A ) | ( r2_hidden @ D @ A ) ) & 
% 0.56/0.75                        ( ( B ) = ( k4_tarski @ C @ D ) ) ) ) ) ) ) ) ) ))).
% 0.56/0.75  thf('25', plain,
% 0.56/0.75      (![X29 : $i]:
% 0.56/0.75         (((X29) = (k1_xboole_0)) | (r2_hidden @ (sk_B_2 @ X29) @ X29))),
% 0.56/0.75      inference('cnf', [status(esa)], [t9_mcart_1])).
% 0.56/0.75  thf(d1_xboole_0, axiom,
% 0.56/0.75    (![A:$i]:
% 0.56/0.75     ( ( v1_xboole_0 @ A ) <=> ( ![B:$i]: ( ~( r2_hidden @ B @ A ) ) ) ))).
% 0.56/0.75  thf('26', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.56/0.75      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.56/0.75  thf('27', plain,
% 0.56/0.75      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.56/0.75      inference('sup-', [status(thm)], ['25', '26'])).
% 0.56/0.75  thf('28', plain,
% 0.56/0.75      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.56/0.75      inference('sup-', [status(thm)], ['25', '26'])).
% 0.56/0.75  thf('29', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]:
% 0.56/0.75         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.56/0.75      inference('sup+', [status(thm)], ['27', '28'])).
% 0.56/0.75  thf('30', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]:
% 0.56/0.75         (((X1) = (X0)) | ~ (v1_xboole_0 @ X0) | ~ (v1_xboole_0 @ X1))),
% 0.56/0.75      inference('sup+', [status(thm)], ['27', '28'])).
% 0.56/0.75  thf('31', plain, ((((sk_B_3) != (k1_xboole_0)) | ((sk_A) = (k1_xboole_0)))),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.75  thf('32', plain,
% 0.56/0.75      ((((sk_B_3) != (k1_xboole_0))) <= (~ (((sk_B_3) = (k1_xboole_0))))),
% 0.56/0.75      inference('split', [status(esa)], ['31'])).
% 0.56/0.75  thf('33', plain,
% 0.56/0.75      ((![X0 : $i]:
% 0.56/0.75          (((X0) != (k1_xboole_0))
% 0.56/0.75           | ~ (v1_xboole_0 @ X0)
% 0.56/0.75           | ~ (v1_xboole_0 @ sk_B_3)))
% 0.56/0.75         <= (~ (((sk_B_3) = (k1_xboole_0))))),
% 0.56/0.75      inference('sup-', [status(thm)], ['30', '32'])).
% 0.56/0.75  thf('34', plain,
% 0.56/0.75      (((~ (v1_xboole_0 @ sk_B_3) | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.56/0.75         <= (~ (((sk_B_3) = (k1_xboole_0))))),
% 0.56/0.75      inference('simplify', [status(thm)], ['33'])).
% 0.56/0.75  thf('35', plain,
% 0.56/0.75      ((![X0 : $i]:
% 0.56/0.75          (~ (v1_xboole_0 @ X0)
% 0.56/0.75           | ~ (v1_xboole_0 @ X0)
% 0.56/0.75           | ~ (v1_xboole_0 @ sk_B_3)
% 0.56/0.75           | ~ (v1_xboole_0 @ k1_xboole_0)))
% 0.56/0.75         <= (~ (((sk_B_3) = (k1_xboole_0))))),
% 0.56/0.75      inference('sup-', [status(thm)], ['29', '34'])).
% 0.56/0.75  thf('36', plain,
% 0.56/0.75      ((![X0 : $i]:
% 0.56/0.75          (~ (v1_xboole_0 @ k1_xboole_0)
% 0.56/0.75           | ~ (v1_xboole_0 @ sk_B_3)
% 0.56/0.75           | ~ (v1_xboole_0 @ X0)))
% 0.56/0.75         <= (~ (((sk_B_3) = (k1_xboole_0))))),
% 0.56/0.75      inference('simplify', [status(thm)], ['35'])).
% 0.56/0.75  thf(t4_subset_1, axiom,
% 0.56/0.75    (![A:$i]: ( m1_subset_1 @ k1_xboole_0 @ ( k1_zfmisc_1 @ A ) ))).
% 0.56/0.75  thf('37', plain,
% 0.56/0.75      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.56/0.75      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.56/0.75  thf(reflexivity_r2_relset_1, axiom,
% 0.56/0.75    (![A:$i,B:$i,C:$i,D:$i]:
% 0.56/0.75     ( ( ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) & 
% 0.56/0.75         ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) =>
% 0.56/0.75       ( r2_relset_1 @ A @ B @ C @ C ) ))).
% 0.56/0.75  thf('38', plain,
% 0.56/0.75      (![X25 : $i, X26 : $i, X27 : $i, X28 : $i]:
% 0.56/0.75         ((r2_relset_1 @ X25 @ X26 @ X27 @ X27)
% 0.56/0.75          | ~ (m1_subset_1 @ X27 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26)))
% 0.56/0.75          | ~ (m1_subset_1 @ X28 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X25 @ X26))))),
% 0.56/0.75      inference('cnf', [status(esa)], [reflexivity_r2_relset_1])).
% 0.56/0.75  thf('39', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.75         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.56/0.75          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.56/0.75      inference('condensation', [status(thm)], ['38'])).
% 0.56/0.75  thf('40', plain,
% 0.56/0.75      (![X0 : $i, X1 : $i]: (r2_relset_1 @ X1 @ X0 @ k1_xboole_0 @ k1_xboole_0)),
% 0.56/0.75      inference('sup-', [status(thm)], ['37', '39'])).
% 0.56/0.75  thf(t113_zfmisc_1, axiom,
% 0.56/0.75    (![A:$i,B:$i]:
% 0.56/0.75     ( ( ( k2_zfmisc_1 @ A @ B ) = ( k1_xboole_0 ) ) <=>
% 0.56/0.75       ( ( ( A ) = ( k1_xboole_0 ) ) | ( ( B ) = ( k1_xboole_0 ) ) ) ))).
% 0.56/0.75  thf('41', plain,
% 0.56/0.75      (![X7 : $i, X8 : $i]:
% 0.56/0.75         (((k2_zfmisc_1 @ X7 @ X8) = (k1_xboole_0)) | ((X7) != (k1_xboole_0)))),
% 0.56/0.75      inference('cnf', [status(esa)], [t113_zfmisc_1])).
% 0.56/0.75  thf('42', plain,
% 0.56/0.75      (![X8 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 0.56/0.75      inference('simplify', [status(thm)], ['41'])).
% 0.56/0.75  thf('43', plain,
% 0.56/0.75      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.56/0.75      inference('split', [status(esa)], ['31'])).
% 0.56/0.75  thf('44', plain,
% 0.56/0.75      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))),
% 0.56/0.75      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.76  thf('45', plain,
% 0.56/0.76      (((m1_subset_1 @ sk_C @ 
% 0.56/0.76         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_3))))
% 0.56/0.76         <= ((((sk_A) = (k1_xboole_0))))),
% 0.56/0.76      inference('sup+', [status(thm)], ['43', '44'])).
% 0.56/0.76  thf('46', plain,
% 0.56/0.76      (((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.56/0.76         <= ((((sk_A) = (k1_xboole_0))))),
% 0.56/0.76      inference('sup+', [status(thm)], ['42', '45'])).
% 0.56/0.76  thf(t3_subset, axiom,
% 0.56/0.76    (![A:$i,B:$i]:
% 0.56/0.76     ( ( m1_subset_1 @ A @ ( k1_zfmisc_1 @ B ) ) <=> ( r1_tarski @ A @ B ) ))).
% 0.56/0.76  thf('47', plain,
% 0.56/0.76      (![X11 : $i, X12 : $i]:
% 0.56/0.76         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.56/0.76      inference('cnf', [status(esa)], [t3_subset])).
% 0.56/0.76  thf('48', plain,
% 0.56/0.76      (((r1_tarski @ sk_C @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.56/0.76      inference('sup-', [status(thm)], ['46', '47'])).
% 0.56/0.76  thf('49', plain,
% 0.56/0.76      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.56/0.76      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.56/0.76  thf('50', plain,
% 0.56/0.76      (![X11 : $i, X12 : $i]:
% 0.56/0.76         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.56/0.76      inference('cnf', [status(esa)], [t3_subset])).
% 0.56/0.76  thf('51', plain, (![X0 : $i]: (r1_tarski @ k1_xboole_0 @ X0)),
% 0.56/0.76      inference('sup-', [status(thm)], ['49', '50'])).
% 0.56/0.76  thf(d10_xboole_0, axiom,
% 0.56/0.76    (![A:$i,B:$i]:
% 0.56/0.76     ( ( ( A ) = ( B ) ) <=> ( ( r1_tarski @ A @ B ) & ( r1_tarski @ B @ A ) ) ))).
% 0.56/0.76  thf('52', plain,
% 0.56/0.76      (![X3 : $i, X5 : $i]:
% 0.56/0.76         (((X3) = (X5)) | ~ (r1_tarski @ X5 @ X3) | ~ (r1_tarski @ X3 @ X5))),
% 0.56/0.76      inference('cnf', [status(esa)], [d10_xboole_0])).
% 0.56/0.76  thf('53', plain,
% 0.56/0.76      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.56/0.76      inference('sup-', [status(thm)], ['51', '52'])).
% 0.56/0.76  thf('54', plain,
% 0.56/0.76      ((((sk_C) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.56/0.76      inference('sup-', [status(thm)], ['48', '53'])).
% 0.56/0.76  thf('55', plain, (~ (r2_relset_1 @ sk_A @ sk_B_3 @ sk_C @ sk_D)),
% 0.56/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.76  thf('56', plain,
% 0.56/0.76      ((~ (r2_relset_1 @ sk_A @ sk_B_3 @ k1_xboole_0 @ sk_D))
% 0.56/0.76         <= ((((sk_A) = (k1_xboole_0))))),
% 0.56/0.76      inference('sup-', [status(thm)], ['54', '55'])).
% 0.56/0.76  thf('57', plain,
% 0.56/0.76      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.56/0.76      inference('split', [status(esa)], ['31'])).
% 0.56/0.76  thf('58', plain,
% 0.56/0.76      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B_3 @ k1_xboole_0 @ sk_D))
% 0.56/0.76         <= ((((sk_A) = (k1_xboole_0))))),
% 0.56/0.76      inference('demod', [status(thm)], ['56', '57'])).
% 0.56/0.76  thf('59', plain,
% 0.56/0.76      (![X8 : $i]: ((k2_zfmisc_1 @ k1_xboole_0 @ X8) = (k1_xboole_0))),
% 0.56/0.76      inference('simplify', [status(thm)], ['41'])).
% 0.56/0.76  thf('60', plain,
% 0.56/0.76      ((((sk_A) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.56/0.76      inference('split', [status(esa)], ['31'])).
% 0.56/0.76  thf('61', plain,
% 0.56/0.76      ((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))),
% 0.56/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.76  thf('62', plain,
% 0.56/0.76      (((m1_subset_1 @ sk_D @ 
% 0.56/0.76         (k1_zfmisc_1 @ (k2_zfmisc_1 @ k1_xboole_0 @ sk_B_3))))
% 0.56/0.76         <= ((((sk_A) = (k1_xboole_0))))),
% 0.56/0.76      inference('sup+', [status(thm)], ['60', '61'])).
% 0.56/0.76  thf('63', plain,
% 0.56/0.76      (((m1_subset_1 @ sk_D @ (k1_zfmisc_1 @ k1_xboole_0)))
% 0.56/0.76         <= ((((sk_A) = (k1_xboole_0))))),
% 0.56/0.76      inference('sup+', [status(thm)], ['59', '62'])).
% 0.56/0.76  thf('64', plain,
% 0.56/0.76      (![X11 : $i, X12 : $i]:
% 0.56/0.76         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.56/0.76      inference('cnf', [status(esa)], [t3_subset])).
% 0.56/0.76  thf('65', plain,
% 0.56/0.76      (((r1_tarski @ sk_D @ k1_xboole_0)) <= ((((sk_A) = (k1_xboole_0))))),
% 0.56/0.76      inference('sup-', [status(thm)], ['63', '64'])).
% 0.56/0.76  thf('66', plain,
% 0.56/0.76      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.56/0.76      inference('sup-', [status(thm)], ['51', '52'])).
% 0.56/0.76  thf('67', plain,
% 0.56/0.76      ((((sk_D) = (k1_xboole_0))) <= ((((sk_A) = (k1_xboole_0))))),
% 0.56/0.76      inference('sup-', [status(thm)], ['65', '66'])).
% 0.56/0.76  thf('68', plain,
% 0.56/0.76      ((~ (r2_relset_1 @ k1_xboole_0 @ sk_B_3 @ k1_xboole_0 @ k1_xboole_0))
% 0.56/0.76         <= ((((sk_A) = (k1_xboole_0))))),
% 0.56/0.76      inference('demod', [status(thm)], ['58', '67'])).
% 0.56/0.76  thf('69', plain, (~ (((sk_A) = (k1_xboole_0)))),
% 0.56/0.76      inference('sup-', [status(thm)], ['40', '68'])).
% 0.56/0.76  thf('70', plain,
% 0.56/0.76      (~ (((sk_B_3) = (k1_xboole_0))) | (((sk_A) = (k1_xboole_0)))),
% 0.56/0.76      inference('split', [status(esa)], ['31'])).
% 0.56/0.76  thf('71', plain, (~ (((sk_B_3) = (k1_xboole_0)))),
% 0.56/0.76      inference('sat_resolution*', [status(thm)], ['69', '70'])).
% 0.56/0.76  thf('72', plain,
% 0.56/0.76      (![X0 : $i]:
% 0.56/0.76         (~ (v1_xboole_0 @ k1_xboole_0)
% 0.56/0.76          | ~ (v1_xboole_0 @ sk_B_3)
% 0.56/0.76          | ~ (v1_xboole_0 @ X0))),
% 0.56/0.76      inference('simpl_trail', [status(thm)], ['36', '71'])).
% 0.56/0.76  thf('73', plain,
% 0.56/0.76      ((~ (v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ sk_B_3))),
% 0.56/0.76      inference('condensation', [status(thm)], ['72'])).
% 0.56/0.76  thf('74', plain,
% 0.56/0.76      (![X0 : $i]: (((X0) = (k1_xboole_0)) | ~ (v1_xboole_0 @ X0))),
% 0.56/0.76      inference('sup-', [status(thm)], ['25', '26'])).
% 0.56/0.76  thf('75', plain,
% 0.56/0.76      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.56/0.76      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.56/0.76  thf('76', plain,
% 0.56/0.76      (![X10 : $i]: (m1_subset_1 @ k1_xboole_0 @ (k1_zfmisc_1 @ X10))),
% 0.56/0.76      inference('cnf', [status(esa)], [t4_subset_1])).
% 0.56/0.76  thf(t4_subset, axiom,
% 0.56/0.76    (![A:$i,B:$i,C:$i]:
% 0.56/0.76     ( ( ( r2_hidden @ A @ B ) & ( m1_subset_1 @ B @ ( k1_zfmisc_1 @ C ) ) ) =>
% 0.56/0.76       ( m1_subset_1 @ A @ C ) ))).
% 0.56/0.76  thf('77', plain,
% 0.56/0.76      (![X14 : $i, X15 : $i, X16 : $i]:
% 0.56/0.76         (~ (r2_hidden @ X14 @ X15)
% 0.56/0.76          | ~ (m1_subset_1 @ X15 @ (k1_zfmisc_1 @ X16))
% 0.56/0.76          | (m1_subset_1 @ X14 @ X16))),
% 0.56/0.76      inference('cnf', [status(esa)], [t4_subset])).
% 0.56/0.76  thf('78', plain,
% 0.56/0.76      (![X0 : $i, X1 : $i]:
% 0.56/0.76         ((m1_subset_1 @ X1 @ X0) | ~ (r2_hidden @ X1 @ k1_xboole_0))),
% 0.56/0.76      inference('sup-', [status(thm)], ['76', '77'])).
% 0.56/0.76  thf('79', plain,
% 0.56/0.76      (![X0 : $i]:
% 0.56/0.76         ((v1_xboole_0 @ k1_xboole_0)
% 0.56/0.76          | (m1_subset_1 @ (sk_B @ k1_xboole_0) @ X0))),
% 0.56/0.76      inference('sup-', [status(thm)], ['75', '78'])).
% 0.56/0.76  thf('80', plain,
% 0.56/0.76      (![X11 : $i, X12 : $i]:
% 0.56/0.76         ((r1_tarski @ X11 @ X12) | ~ (m1_subset_1 @ X11 @ (k1_zfmisc_1 @ X12)))),
% 0.56/0.76      inference('cnf', [status(esa)], [t3_subset])).
% 0.56/0.76  thf('81', plain,
% 0.56/0.76      (![X0 : $i]:
% 0.56/0.76         ((v1_xboole_0 @ k1_xboole_0) | (r1_tarski @ (sk_B @ k1_xboole_0) @ X0))),
% 0.56/0.76      inference('sup-', [status(thm)], ['79', '80'])).
% 0.56/0.76  thf('82', plain,
% 0.56/0.76      (![X0 : $i]: (~ (r1_tarski @ X0 @ k1_xboole_0) | ((X0) = (k1_xboole_0)))),
% 0.56/0.76      inference('sup-', [status(thm)], ['51', '52'])).
% 0.56/0.76  thf('83', plain,
% 0.56/0.76      (((v1_xboole_0 @ k1_xboole_0) | ((sk_B @ k1_xboole_0) = (k1_xboole_0)))),
% 0.56/0.76      inference('sup-', [status(thm)], ['81', '82'])).
% 0.56/0.76  thf('84', plain,
% 0.56/0.76      (![X2 : $i]: ((v1_xboole_0 @ X2) | (r2_hidden @ (sk_B @ X2) @ X2))),
% 0.56/0.76      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.56/0.76  thf('85', plain,
% 0.56/0.76      (((r2_hidden @ k1_xboole_0 @ k1_xboole_0)
% 0.56/0.76        | (v1_xboole_0 @ k1_xboole_0)
% 0.56/0.76        | (v1_xboole_0 @ k1_xboole_0))),
% 0.56/0.76      inference('sup+', [status(thm)], ['83', '84'])).
% 0.56/0.76  thf('86', plain,
% 0.56/0.76      (((v1_xboole_0 @ k1_xboole_0) | (r2_hidden @ k1_xboole_0 @ k1_xboole_0))),
% 0.56/0.76      inference('simplify', [status(thm)], ['85'])).
% 0.56/0.76  thf('87', plain,
% 0.56/0.76      (![X0 : $i]:
% 0.56/0.76         ((r2_hidden @ k1_xboole_0 @ X0)
% 0.56/0.76          | ~ (v1_xboole_0 @ X0)
% 0.56/0.76          | (v1_xboole_0 @ k1_xboole_0))),
% 0.56/0.76      inference('sup+', [status(thm)], ['74', '86'])).
% 0.56/0.76  thf('88', plain,
% 0.56/0.76      (![X0 : $i, X1 : $i]: (~ (r2_hidden @ X0 @ X1) | ~ (v1_xboole_0 @ X1))),
% 0.56/0.76      inference('cnf', [status(esa)], [d1_xboole_0])).
% 0.56/0.76  thf('89', plain,
% 0.56/0.76      (![X0 : $i]: ((v1_xboole_0 @ k1_xboole_0) | ~ (v1_xboole_0 @ X0))),
% 0.56/0.76      inference('clc', [status(thm)], ['87', '88'])).
% 0.56/0.76  thf('90', plain, (~ (v1_xboole_0 @ sk_B_3)),
% 0.56/0.76      inference('clc', [status(thm)], ['73', '89'])).
% 0.56/0.76  thf('91', plain, (((sk_C) = (sk_D))),
% 0.56/0.76      inference('clc', [status(thm)], ['24', '90'])).
% 0.56/0.76  thf('92', plain,
% 0.56/0.76      ((m1_subset_1 @ sk_C @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ sk_A @ sk_B_3)))),
% 0.56/0.76      inference('cnf', [status(esa)], [zf_stmt_0])).
% 0.56/0.76  thf('93', plain,
% 0.56/0.76      (![X0 : $i, X1 : $i, X2 : $i]:
% 0.56/0.76         ((r2_relset_1 @ X2 @ X1 @ X0 @ X0)
% 0.56/0.76          | ~ (m1_subset_1 @ X0 @ (k1_zfmisc_1 @ (k2_zfmisc_1 @ X2 @ X1))))),
% 0.56/0.76      inference('condensation', [status(thm)], ['38'])).
% 0.56/0.76  thf('94', plain, ((r2_relset_1 @ sk_A @ sk_B_3 @ sk_C @ sk_C)),
% 0.56/0.76      inference('sup-', [status(thm)], ['92', '93'])).
% 0.56/0.76  thf('95', plain, ($false),
% 0.56/0.76      inference('demod', [status(thm)], ['0', '91', '94'])).
% 0.56/0.76  
% 0.56/0.76  % SZS output end Refutation
% 0.56/0.76  
% 0.59/0.76  % Zipperpin 1.5 exiting
%------------------------------------------------------------------------------
