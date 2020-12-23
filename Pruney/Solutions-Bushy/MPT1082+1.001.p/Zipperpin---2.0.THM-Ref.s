%------------------------------------------------------------------------------
% File       : Zipperpin---2.0
% Problem    : MPT1082+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_portfolio.sh /export/starexec/sandbox/benchmark/theBenchmark.p /export/starexec/sandbox/tmp/tmp.VnS4PKPYSg

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:53:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   42 (  57 expanded)
%              Number of leaves         :   17 (  25 expanded)
%              Depth                    :   12
%              Number of atoms          :  386 ( 583 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   8 average)

% Comments   : 
%------------------------------------------------------------------------------
thf(sk_D_type,type,(
    sk_D: $i > $i > $i > $i )).

thf(sk_B_type,type,(
    sk_B: $i )).

thf(k2_zfmisc_1_type,type,(
    k2_zfmisc_1: $i > $i > $i )).

thf(m1_funct_2_type,type,(
    m1_funct_2: $i > $i > $i > $o )).

thf(v1_xboole_0_type,type,(
    v1_xboole_0: $i > $o )).

thf(r2_hidden_type,type,(
    r2_hidden: $i > $i > $o )).

thf(k1_zfmisc_1_type,type,(
    k1_zfmisc_1: $i > $i )).

thf(k1_funct_2_type,type,(
    k1_funct_2: $i > $i > $i )).

thf(sk_A_type,type,(
    sk_A: $i )).

thf(v1_funct_1_type,type,(
    v1_funct_1: $i > $o )).

thf(v1_funct_2_type,type,(
    v1_funct_2: $i > $i > $i > $o )).

thf(m1_subset_1_type,type,(
    m1_subset_1: $i > $i > $o )).

thf(t199_funct_2,conjecture,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ( m1_funct_2 @ ( k1_funct_2 @ A @ B ) @ A @ B ) ) )).

thf(zf_stmt_0,negated_conjecture,(
    ~ ! [A: $i,B: $i] :
        ( ~ ( v1_xboole_0 @ B )
       => ( m1_funct_2 @ ( k1_funct_2 @ A @ B ) @ A @ B ) ) ),
    inference('cnf.neg',[status(esa)],[t199_funct_2])).

thf('0',plain,(
    ~ ( v1_xboole_0 @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf(d13_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ~ ( v1_xboole_0 @ C )
     => ( ( m1_funct_2 @ C @ A @ B )
      <=> ! [D: $i] :
            ( ( m1_subset_1 @ D @ C )
           => ( ( v1_funct_1 @ D )
              & ( v1_funct_2 @ D @ A @ B )
              & ( m1_subset_1 @ D @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) ) ) )).

thf('1',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( m1_subset_1 @ ( sk_D @ X0 @ X1 @ X2 ) @ X0 )
      | ( m1_funct_2 @ X0 @ X2 @ X1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_2])).

thf(t2_subset,axiom,(
    ! [A: $i,B: $i] :
      ( ( m1_subset_1 @ A @ B )
     => ( ( v1_xboole_0 @ B )
        | ( r2_hidden @ A @ B ) ) ) )).

thf('2',plain,(
    ! [X9: $i,X10: $i] :
      ( ( r2_hidden @ X9 @ X10 )
      | ( v1_xboole_0 @ X10 )
      | ~ ( m1_subset_1 @ X9 @ X10 ) ) ),
    inference(cnf,[status(esa)],[t2_subset])).

thf('3',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( v1_xboole_0 @ X0 )
      | ( m1_funct_2 @ X0 @ X1 @ X2 )
      | ( v1_xboole_0 @ X0 )
      | ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X0 ) ) ),
    inference('sup-',[status(thm)],['1','2'])).

thf('4',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X0 )
      | ( m1_funct_2 @ X0 @ X1 @ X2 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf(t121_funct_2,axiom,(
    ! [A: $i,B: $i,C: $i] :
      ( ( r2_hidden @ C @ ( k1_funct_2 @ A @ B ) )
     => ( ( v1_funct_1 @ C )
        & ( v1_funct_2 @ C @ A @ B )
        & ( m1_subset_1 @ C @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ A @ B ) ) ) ) ) )).

thf('5',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_funct_2 @ X6 @ X7 @ X8 )
      | ~ ( r2_hidden @ X6 @ ( k1_funct_2 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t121_funct_2])).

thf('6',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ ( k1_funct_2 @ X1 @ X0 ) )
      | ( m1_funct_2 @ ( k1_funct_2 @ X1 @ X0 ) @ X2 @ X3 )
      | ( v1_funct_2 @ ( sk_D @ ( k1_funct_2 @ X1 @ X0 ) @ X3 @ X2 ) @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['4','5'])).

thf('7',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X0 )
      | ( m1_funct_2 @ X0 @ X1 @ X2 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('8',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( m1_subset_1 @ X6 @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X7 @ X8 ) ) )
      | ~ ( r2_hidden @ X6 @ ( k1_funct_2 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t121_funct_2])).

thf('9',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ ( k1_funct_2 @ X1 @ X0 ) )
      | ( m1_funct_2 @ ( k1_funct_2 @ X1 @ X0 ) @ X2 @ X3 )
      | ( m1_subset_1 @ ( sk_D @ ( k1_funct_2 @ X1 @ X0 ) @ X3 @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X1 @ X0 ) ) ) ) ),
    inference('sup-',[status(thm)],['7','8'])).

thf('10',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ~ ( m1_subset_1 @ ( sk_D @ X0 @ X1 @ X2 ) @ ( k1_zfmisc_1 @ ( k2_zfmisc_1 @ X2 @ X1 ) ) )
      | ~ ( v1_funct_2 @ ( sk_D @ X0 @ X1 @ X2 ) @ X2 @ X1 )
      | ~ ( v1_funct_1 @ ( sk_D @ X0 @ X1 @ X2 ) )
      | ( m1_funct_2 @ X0 @ X2 @ X1 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(cnf,[status(esa)],[d13_funct_2])).

thf('11',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_funct_2 @ ( k1_funct_2 @ X1 @ X0 ) @ X1 @ X0 )
      | ( v1_xboole_0 @ ( k1_funct_2 @ X1 @ X0 ) )
      | ( v1_xboole_0 @ ( k1_funct_2 @ X1 @ X0 ) )
      | ( m1_funct_2 @ ( k1_funct_2 @ X1 @ X0 ) @ X1 @ X0 )
      | ~ ( v1_funct_1 @ ( sk_D @ ( k1_funct_2 @ X1 @ X0 ) @ X0 @ X1 ) )
      | ~ ( v1_funct_2 @ ( sk_D @ ( k1_funct_2 @ X1 @ X0 ) @ X0 @ X1 ) @ X1 @ X0 ) ) ),
    inference('sup-',[status(thm)],['9','10'])).

thf('12',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_2 @ ( sk_D @ ( k1_funct_2 @ X1 @ X0 ) @ X0 @ X1 ) @ X1 @ X0 )
      | ~ ( v1_funct_1 @ ( sk_D @ ( k1_funct_2 @ X1 @ X0 ) @ X0 @ X1 ) )
      | ( v1_xboole_0 @ ( k1_funct_2 @ X1 @ X0 ) )
      | ( m1_funct_2 @ ( k1_funct_2 @ X1 @ X0 ) @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['11'])).

thf('13',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_funct_2 @ ( k1_funct_2 @ X1 @ X0 ) @ X1 @ X0 )
      | ( v1_xboole_0 @ ( k1_funct_2 @ X1 @ X0 ) )
      | ( m1_funct_2 @ ( k1_funct_2 @ X1 @ X0 ) @ X1 @ X0 )
      | ( v1_xboole_0 @ ( k1_funct_2 @ X1 @ X0 ) )
      | ~ ( v1_funct_1 @ ( sk_D @ ( k1_funct_2 @ X1 @ X0 ) @ X0 @ X1 ) ) ) ),
    inference('sup-',[status(thm)],['6','12'])).

thf('14',plain,(
    ! [X0: $i,X1: $i] :
      ( ~ ( v1_funct_1 @ ( sk_D @ ( k1_funct_2 @ X1 @ X0 ) @ X0 @ X1 ) )
      | ( v1_xboole_0 @ ( k1_funct_2 @ X1 @ X0 ) )
      | ( m1_funct_2 @ ( k1_funct_2 @ X1 @ X0 ) @ X1 @ X0 ) ) ),
    inference(simplify,[status(thm)],['13'])).

thf('15',plain,(
    ! [X0: $i,X1: $i,X2: $i] :
      ( ( r2_hidden @ ( sk_D @ X0 @ X2 @ X1 ) @ X0 )
      | ( m1_funct_2 @ X0 @ X1 @ X2 )
      | ( v1_xboole_0 @ X0 ) ) ),
    inference(simplify,[status(thm)],['3'])).

thf('16',plain,(
    ! [X6: $i,X7: $i,X8: $i] :
      ( ( v1_funct_1 @ X6 )
      | ~ ( r2_hidden @ X6 @ ( k1_funct_2 @ X7 @ X8 ) ) ) ),
    inference(cnf,[status(esa)],[t121_funct_2])).

thf('17',plain,(
    ! [X0: $i,X1: $i,X2: $i,X3: $i] :
      ( ( v1_xboole_0 @ ( k1_funct_2 @ X1 @ X0 ) )
      | ( m1_funct_2 @ ( k1_funct_2 @ X1 @ X0 ) @ X2 @ X3 )
      | ( v1_funct_1 @ ( sk_D @ ( k1_funct_2 @ X1 @ X0 ) @ X3 @ X2 ) ) ) ),
    inference('sup-',[status(thm)],['15','16'])).

thf('18',plain,(
    ! [X0: $i,X1: $i] :
      ( ( m1_funct_2 @ ( k1_funct_2 @ X1 @ X0 ) @ X1 @ X0 )
      | ( v1_xboole_0 @ ( k1_funct_2 @ X1 @ X0 ) ) ) ),
    inference(clc,[status(thm)],['14','17'])).

thf('19',plain,(
    ~ ( m1_funct_2 @ ( k1_funct_2 @ sk_A @ sk_B ) @ sk_A @ sk_B ) ),
    inference(cnf,[status(esa)],[zf_stmt_0])).

thf('20',plain,(
    v1_xboole_0 @ ( k1_funct_2 @ sk_A @ sk_B ) ),
    inference('sup-',[status(thm)],['18','19'])).

thf(fc1_funct_2,axiom,(
    ! [A: $i,B: $i] :
      ( ~ ( v1_xboole_0 @ B )
     => ~ ( v1_xboole_0 @ ( k1_funct_2 @ A @ B ) ) ) )).

thf('21',plain,(
    ! [X4: $i,X5: $i] :
      ( ~ ( v1_xboole_0 @ ( k1_funct_2 @ X4 @ X5 ) )
      | ( v1_xboole_0 @ X5 ) ) ),
    inference(cnf,[status(esa)],[fc1_funct_2])).

thf('22',plain,(
    v1_xboole_0 @ sk_B ),
    inference('sup-',[status(thm)],['20','21'])).

thf('23',plain,(
    $false ),
    inference(demod,[status(thm)],['0','22'])).


%------------------------------------------------------------------------------
